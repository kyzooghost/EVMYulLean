import EvmYul.CrossChainReplay.ProtocolState
import EvmYul.CrossChainReplay.Observations

namespace EvmYul.CrossChainReplay

def currentStamp (height : Nat) : Nat := height + 1

def currentEntry (height : Nat) (row : LoadedEntry) : Bool :=
  row.loadedBlock == currentStamp height && !row.consumed

def bucketFor (hash : Hash32) (state : ProtocolState) : Option EntryBucket :=
  state.buckets.find? (fun bucket => bucket.hash == hash)

def nextFreshHead (height : Nat) (hash : Hash32) (state : ProtocolState) : Nat :=
  match bucketFor hash state with
  | none => 0
  | some bucket =>
      ((List.range bucket.rows.length).drop bucket.head).find?
        (fun index => (bucket.rows[index]?).any (currentEntry height))
        |>.getD bucket.rows.length

def hasDuplicateLookupHash (rows : List TopLevelLookup) : Bool :=
  match rows with
  | [] => false
  | row :: rest => rest.any (fun other => other.crossChainCallHash == row.crossChainCallHash) ||
      hasDuplicateLookupHash rest

def checkCalls (peer : Word) (allowRoot : Bool) (calls : List IncomingCall) :
    Except ProtocolError Unit := do
  for h : i in [:calls.length] do
    let call := calls[i]
    if call.sourceRollupId != peer then
      throw (.entrySpansMultiplePeers peer call.sourceRollupId)
    if call.isStatic then
      if call.value.toNat != 0 then throw .staticCallWithValue
      if call.revertSpan.toNat != 0 then throw .staticCallWithRevertSpan
    else if !allowRoot || i != 0 then
      if call.value.toNat != 0 then throw .nonRootCallWithValue

def checkNestedLookups (rows : List NestedLookup) : Except ProtocolError Unit := do
  for row in rows do
    let peer := (row.incomingCalls.head?).map (·.sourceRollupId)
    match peer with
    | none => pure ()
    | some p => checkCalls p false row.incomingCalls

def checkEntry (allowRoot : Bool) (row : Entry) : Except ProtocolError Unit := do
  checkCalls row.declaredPeerRollup allowRoot row.incomingCalls
  checkNestedLookups row.expectedLookups

def checkLookup (row : TopLevelLookup) : Except ProtocolError Unit := do
  checkCalls row.declaredPeerRollup false row.incomingCalls
  checkNestedLookups row.expectedLookups

def replaceBucket (state : ProtocolState) (bucket : EntryBucket) : ProtocolState :=
  { state with buckets := bucket :: state.buckets.filter (fun old => old.hash != bucket.hash) }

def replaceLookup (state : ProtocolState) (row : LoadedLookup) : ProtocolState :=
  { state with lookups := row :: (state.lookups.filter
      (fun old => old.row.crossChainCallHash != row.row.crossChainCallHash)) }

/-- Loader preflight happens before all writes; current FIFO remainders survive a reload. -/
def loadBatch (_p : Parameters) (context : LoadContext) (batch : LoadBatch)
    (state : ProtocolState) : Except ProtocolError LoadResult := do
  if context.route == .systemInbound && batch.entries.isEmpty then throw .emptyEntries
  if context.route == .systemInbound then
    let some first := batch.entries.head? | throw .emptyEntries
    if first.incomingCalls.isEmpty then throw .emptyIncomingCalls
  if hasDuplicateLookupHash batch.lookups then
    let duplicate := batch.lookups.find? fun row =>
      (batch.lookups.filter (fun other => other.crossChainCallHash == row.crossChainCallHash)).length > 1
    throw (.duplicateLookupHash (duplicate.map (·.crossChainCallHash) |>.getD zeroHash))
  for i in [:batch.entries.length] do
    let some entry := batch.entries[i]? | throw .arrayOutOfBounds
    checkEntry (context.route == .systemInbound && i == 0) entry
  for row in batch.lookups do checkLookup row
  let mut next := state
  let mut ids : List EntryId := []
  for i in [:batch.entries.length] do
    let some entry := batch.entries[i]? | throw .arrayOutOfBounds
    let hash := entry.proxyEntryHash
    let existing := (bucketFor hash next).getD { hash := hash, rows := [], head := 0 }
    let fresh := nextFreshHead context.height hash next
    let retained := if fresh < existing.rows.length then existing else { existing with rows := [], head := 0 }
    let id := EntryId.driverLoaded context.loadIndex i
    next := replaceBucket next { retained with rows := retained.rows ++
      [{ id := id, row := entry, loadedBlock := currentStamp context.height, consumed := false }] }
    ids := ids ++ [id]
  for row in batch.lookups do
    next := replaceLookup next { row := row, loadedBlock := currentStamp context.height, id := .topLevelLookup context.loadIndex row.crossChainCallHash }
  if context.route == .systemInbound then
    let some first := batch.entries.head? | throw .emptyEntries
    let some root := first.incomingCalls.head? | throw .emptyIncomingCalls
    if root.value != context.attachedValue then throw .valueMismatch
  return { state := next, newlyLoaded := ids, batch := batch, context := context }

def selectProxyEntry (_p : Parameters) (height : Nat) (hash : Hash32) (peer : Word)
    (state : ProtocolState) : Except ProtocolError (EntryId × ProtocolState) := do
  let some bucket := bucketFor hash state | throw .executionNotFound
  let index := nextFreshHead height hash state
  let some row := bucket.rows[index]? | throw .executionNotFound
  if row.row.declaredPeerRollup != peer then
    throw (.entrySpansMultiplePeers row.row.declaredPeerRollup peer)
  let updated := { bucket with head := index + 1 }
  return (row.id, { (replaceBucket state updated) with activeEntry := some row.id })

def selectInboundEntry (p : Parameters) (expectedHash : Hash32) (loaded : LoadResult) :
    Except ProtocolError (EntryId × ProtocolState) := do
  let some entry := loaded.batch.entries.head? | throw .emptyEntries
  let some root := entry.incomingCalls.head? | throw .emptyIncomingCalls
  let identity : CallIdentity :=
    { isStatic := root.isStatic, sourceAddress := root.sourceAddress,
      sourceRollupId := root.sourceRollupId, targetAddress := root.targetAddress,
      targetRollupId := p.localRollup, value := root.value, data := root.data }
  if callHash p.keccak identity != expectedHash || entry.proxyEntryHash != expectedHash then
    throw .entryHashMismatch
  if root.value != loaded.context.attachedValue then throw .valueMismatch
  let some id := loaded.newlyLoaded.head? | throw .emptyEntries
  let some bucket := bucketFor entry.proxyEntryHash loaded.state | throw .executionNotFound
  let rows := bucket.rows.map fun row => if row.id == id then { row with consumed := true, loadedBlock := 0 } else row
  let state := replaceBucket loaded.state { bucket with rows := rows }
  return (id, { state with activeEntry := some id })

def findNestedLookup (staticMode : Bool) (key : LookupKey) (rows : List NestedLookup) :
    Option (Nat × NestedLookup) :=
  ((rows.zipIdx).find? fun (row, _) =>
    row.crossChainCallHash == key.callHash && row.callNumber == key.callNumber &&
    row.lastOutgoingCallConsumed == key.outgoingCursor &&
    row.executingLookupIndex == key.contextIndex && (staticMode || row.failed)).map
      fun (row, index) => (index, row)

/-- Each context-key component is cast to uint64 by the source implementation. -/
def lookupKeyRepresentable (key : LookupKey) : Prop :=
  key.callNumber < 2 ^ 64 ∧ key.outgoingCursor < 2 ^ 64 ∧
  key.contextIndex < 2 ^ 64

def nestedContextRepresentable (rowIndex : Nat) : Prop := rowIndex + 1 < 2 ^ 64

def clearConsumed (_height : Nat) (hash : Hash32) (index : Nat) (state : ProtocolState) : ProtocolState :=
  match bucketFor hash state with
  | none => state
  | some bucket =>
      let rows := bucket.rows.zipIdx.map fun (row, i) =>
        if i == index then { row with consumed := true, loadedBlock := 0 } else row
      let next := { bucket with rows := rows }
      let next := if next.head >= rows.length then { next with rows := [], head := 0 } else next
      replaceBucket state next

def activeEntryRow (state : ProtocolState) (id : EntryId) : Option (Nat × Entry) := do
  let bucket ← state.buckets.find? fun bucket => bucket.rows.any (fun row => row.id == id)
  let (_, index) ← bucket.rows.zipIdx.find? fun (row, _) => row.id == id
  let row ← bucket.rows[index]?
  return (index, row.row)

inductive ProtocolAction where
  | noAction
  | dispatchSpan (state : ProtocolState) (context : ProtocolContext)
      (span : Nat) (events : List ProtocolObservation)
  | spanResult (state : ProtocolState) (context : ProtocolContext)
      (result : ContextResult) (events : List ProtocolObservation)
  | adoptSpan (state : ProtocolState) (context : ProtocolContext)
      (result : ContextResult) (events : List ProtocolObservation)
  | dispatchSystem (state : ProtocolState) (context : ProtocolContext)
      (value : Word) (events : List ProtocolObservation)
  | local (state : ProtocolState) (context : ProtocolContext) (events : List ProtocolObservation)
  | dispatchIncoming (state : ProtocolState) (context : ProtocolContext)
      (row : IncomingCall) (events : List ProtocolObservation)
  | dispatchStatic (state : ProtocolState) (context : ProtocolContext)
      (row : IncomingCall) (events : List ProtocolObservation)
  | returned (state : ProtocolState) (context : ProtocolContext)
      (data : Bytes) (events : List ProtocolObservation)
  | failed (state : ProtocolState) (context : ProtocolContext)
      (error : ProtocolError) (events : List ProtocolObservation)
  | revertedBytes (state : ProtocolState) (context : ProtocolContext)
      (data : Bytes) (events : List ProtocolObservation)

def protocolFailure (state : ProtocolState) (context : ProtocolContext)
    (error : ProtocolError) (events : List ProtocolObservation := []) : ProtocolAction :=
  .failed state context error events

/-- A reverted lookup replaces the active call arrays, while retaining its host table. -/
def activeCalls (context : ProtocolContext) (entry : Entry) : List IncomingCall :=
  match context.activeLookupIndex with
  | none => entry.incomingCalls
  | some index => (entry.expectedLookups[index]?).map (·.incomingCalls) |>.getD []

def activeOutgoing (context : ProtocolContext) (entry : Entry) : List OutgoingCall :=
  match context.activeLookupIndex with
  | none => entry.expectedOutgoingCalls
  | some index => (entry.expectedLookups[index]?).map (·.expectedOutgoingCalls) |>.getD []

def topLookupEntry (row : TopLevelLookup) : Entry :=
  { declaredPeerRollup := row.declaredPeerRollup, proxyEntryHash := row.crossChainCallHash, incomingCalls := row.incomingCalls, expectedOutgoingCalls := row.expectedOutgoingCalls, expectedLookups := row.expectedLookups, callCount := row.callCount, returnData := row.returnData, rollingHash := row.rollingHash, crossChainRollingHash := row.crossChainRollingHash }

def topLookupNested (row : TopLevelLookup) : NestedLookup :=
  { crossChainCallHash := row.crossChainCallHash, returnData := row.returnData, failed := row.failed, callNumber := 0, lastOutgoingCallConsumed := 0, executingLookupIndex := 0, incomingCalls := row.incomingCalls, expectedOutgoingCalls := row.expectedOutgoingCalls, callCount := row.callCount, rollingHash := row.rollingHash, crossChainRollingHash := row.crossChainRollingHash }

def activeHostEntry (context : ProtocolContext) (state : ProtocolState) (id : EntryId) : Option Entry :=
  match context.lookupHost with
  | some hash => (state.lookups.find? (fun loaded => loaded.row.crossChainCallHash == hash)).map (fun loaded => topLookupEntry loaded.row)
  | none => (activeEntryRow state id).map Prod.snd

def updateIncomingSpan (calls : List IncomingCall) (cursor span : Nat) : List IncomingCall :=
  calls.zipIdx.map fun (row, index) =>
    if index == cursor then { row with revertSpan := EvmYul.UInt256.ofNat span } else row

/-- Update the active storage array through its host and optional nested-row reference. -/
def setIncomingSpan (context : ProtocolContext) (scope : ScopeId) (cursor span : Nat)
    (state : ProtocolState) : ProtocolState :=
  let updateNested := fun (rows : List NestedLookup) (active : Nat) =>
    rows.zipIdx.map fun (row, index) =>
      if index == active then { row with incomingCalls := updateIncomingSpan row.incomingCalls cursor span } else row
  let updateEntry := fun (entry : Entry) => match context.activeLookupIndex with
    | none => { entry with incomingCalls := updateIncomingSpan entry.incomingCalls cursor span }
    | some active => { entry with expectedLookups := updateNested entry.expectedLookups active }
  match context.lookupHost with
  | none => { state with buckets := state.buckets.map fun bucket => { bucket with rows := bucket.rows.map fun loaded => if loaded.id == scope.entry then { loaded with row := updateEntry loaded.row } else loaded } }
  | some hash =>
      { state with lookups := state.lookups.map fun loaded =>
          if loaded.row.crossChainCallHash != hash then loaded
          else match context.activeLookupIndex with
            | none => { loaded with row := { loaded.row with incomingCalls := updateIncomingSpan loaded.row.incomingCalls cursor span } }
            | some active => { loaded with row := { loaded.row with expectedLookups := updateNested loaded.row.expectedLookups active } } }

def managerCallHash (p : Parameters) (invocation : ManagerInvocation)
    (registered : ProxyRegistration) : Hash32 :=
  callHash p.keccak { isStatic := invocation.isStatic, sourceAddress := invocation.source, sourceRollupId := p.localRollup, targetAddress := registered.originalAddress, targetRollupId := registered.originalRollup, value := if invocation.isStatic then EvmYul.UInt256.ofNat 0 else invocation.value, data := invocation.data }

def proxyIdentityError (p : Parameters) (original : Address) (rollup : Word)
    (creating : Bool) : Option ProtocolError :=
  if original == 0 then some .invalidOriginalAddress
  else if rollup.toNat > maxRollupId then some (.rollupIdOutOfRange rollup)
  else if creating && rollup == p.localRollup then some (.sameNetworkProxy rollup)
  else none

def proxyRegistered (p : Parameters) (state : ProtocolState) (row : IncomingCall) : Bool :=
  (state.registry.find? (fun registered => registered.proxy == proxyAddress p row.sourceAddress row.sourceRollupId)).any
    (fun registered => registered.originalAddress != 0)

def incomingProxyError (p : Parameters) (state : ProtocolState) (row : IncomingCall) : Option ProtocolError :=
  match proxyIdentityError p row.sourceAddress row.sourceRollupId true with
  | some error => some error
  | none =>
      if proxyRegistered p state row && row.isStatic && row.value.toNat != 0 then some .staticCallWithValue
      else none

def registerIncomingProxy (p : Parameters) (state : ProtocolState) (row : IncomingCall) : ProtocolState :=
  let address := proxyAddress p row.sourceAddress row.sourceRollupId
  let registered : ProxyRegistration := { proxy := address, originalAddress := row.sourceAddress, originalRollup := EvmYul.UInt256.ofNat (row.sourceRollupId.toNat % 2^64) }
  { state with registry := registered :: state.registry.filter (fun old => old.proxy != address) }

/-- One concrete manager operation, stopping at each external EVM effect. -/
def advanceProtocol (p : Parameters) (context : ProtocolContext) (state : ProtocolState)
    (control : ProtocolControl) : ProtocolAction :=
  match control with
  | .invoke invocation =>
      match state.registry.find? (fun row => row.proxy == invocation.proxy) with
      | none => protocolFailure state context .unauthorizedProxy
      | some registered =>
          if registered.originalAddress == 0 then protocolFailure state context .unauthorizedProxy
          else if !invocation.isStatic && invocation.value.toNat > 0 then
            .dispatchSystem state { context with control := .resumeSystem invocation registered false } invocation.value []
          else .local state { context with control := .managerRoute invocation registered } []
  | .resumeSystem invocation registered success =>
      if !success then protocolFailure state context .etherTransferFailed
      else .local state { context with control := .managerRoute invocation registered } []
  | .managerRoute invocation registered =>
      let hash := managerCallHash p invocation registered
      if state.incomingCursor != 0 then
        match context.activeScope with
        | none => protocolFailure state context .executionNotFound
        | some scope =>
            let key : LookupKey := { callHash := hash, callNumber := state.incomingCursor % 2^64, outgoingCursor := state.outgoingCursor % 2^64, contextIndex := context.lookupContext % 2^64 }
            let next := if invocation.isStatic then .resolveLookup scope key true registered.originalRollup
                        else .consumeOutgoing scope hash registered.originalRollup
            .local state { context with control := next } []
      else
        let next := if invocation.isStatic then .resolveTopLookup hash registered.originalRollup true
                    else .selectProxy hash registered.originalRollup
        .local state { context with control := next } []
  | .resolveTopLookup hash peer staticMode =>
      match state.lookups.find? (fun loaded => loaded.row.crossChainCallHash == hash) with
      | none => protocolFailure state context .executionNotFound
      | some loaded =>
          if loaded.loadedBlock != currentStamp context.height || (!staticMode && !loaded.row.failed) then
            protocolFailure state context .executionNotFound
          else if loaded.row.declaredPeerRollup != peer then
            protocolFailure state context (.entrySpansMultiplePeers loaded.row.declaredPeerRollup peer)
          else
            let scope : ScopeId := { entry := loaded.id, invocationPath := [context.invocationSerial] }
            let lookup := topLookupNested loaded.row
            if staticMode then
              match checkCalls peer false lookup.incomingCalls with
              | .error error => protocolFailure state context error
              | .ok () => .local state { context with activeScope := some scope, control := .staticRows scope lookup 0 zeroHash zeroHash } []
            else
              .local { state with structuralHash := zeroHash, crossChainHash := zeroHash, incomingCursor := 0, outgoingCursor := 0 }
                { context with activeScope := some scope, hostEntry := some loaded.id, lookupHost := some hash, activeLookupIndex := none, activeLookupPeer := some peer, lookupContext := 0, control := .processIncoming scope lookup.callCount.toNat 0 (.lookupValidation lookup) } []
  | .load batch loadContext =>
      match loadBatch p loadContext batch state with
      | .error error => protocolFailure state context error
      | .ok loaded => .local loaded.state { context with control := .idle } []
  | .selectProxy hash peer =>
      match selectProxyEntry p context.height hash peer state with
      | .error .executionNotFound => .local state { context with control := .resolveTopLookup hash peer false } []
      | .error error => protocolFailure state context error
      | .ok (id, selected) =>
          let selected := { selected with structuralHash := zeroHash, crossChainHash := zeroHash, incomingCursor := 0, outgoingCursor := 0 }
          let scope : ScopeId := { entry := id, invocationPath := [context.invocationSerial] }
          match activeEntryRow selected id with
          | none => protocolFailure state context .executionNotFound
          | some (_, row) => .local selected
              { context with activeScope := some scope, hostEntry := some id, route := .proxy, control := .processIncoming scope row.callCount.toNat 0 .entryValidation } []
  | .selectInbound hash loaded =>
      match selectInboundEntry p hash loaded with
      | .error error => protocolFailure state context error
      | .ok (id, selected) =>
          let selected := { selected with crossChainHash := zeroHash }
          let scope : ScopeId := { entry := id, invocationPath := [context.invocationSerial] }
          match activeEntryRow selected id with
          | none => protocolFailure state context .executionNotFound
          | some (_, row) => .local selected
              { context with activeScope := some scope, hostEntry := some id, route := .systemInbound, control := .processIncoming scope row.callCount.toNat 0 .entryValidation } []
  | .processIncoming scope count processed destination =>
      if processed >= count then
        match destination with
        | .entryValidation => .local state { context with control := .validate scope } []
        | .lookupValidation lookup => .local state { context with control := .validateLookup scope lookup } []
        | .spanTransport =>
            let result : ContextResult := { rollingHash := state.structuralHash, outgoingCursor := EvmYul.UInt256.ofNat state.outgoingCursor, incomingCursor := EvmYul.UInt256.ofNat state.incomingCursor, ignoredFlagWord := EvmYul.UInt256.ofNat 0, crossChainHash := state.crossChainHash }
            .spanResult state { context with control := .finished } result []
        | .outgoingCompletion hash data number =>
            let endEvent := StructuralEvent.nestedEnd number
            let record : BoundaryRecord := { callHash := hash, success := true, returnData := data }
            let state := { state with structuralHash := foldStructural p.keccak state.structuralHash endEvent, crossChainHash := foldBoundary p.keccak state.crossChainHash record }
            .returned state { context with control := .finished } data
              [.structural scope endEvent, .boundary scope hash true data]
      else
        match activeHostEntry context state scope.entry with
        | none => protocolFailure state context .executionNotFound
        | some entry =>
            match (activeCalls context entry)[state.incomingCursor]? with
            | none => protocolFailure state context .arrayOutOfBounds
            | some row =>
                if row.isStatic && row.revertSpan.toNat != 0 then
                  protocolFailure state context .staticCallWithRevertSpan
                else if row.revertSpan.toNat != 0 then
                  let span := row.revertSpan.toNat
                  if span > count - processed then
                    protocolFailure state context (.revertSpanOutOfBounds (EvmYul.UInt256.ofNat processed) row.revertSpan (EvmYul.UInt256.ofNat count))
                  else
                    .dispatchSpan (setIncomingSpan context scope state.incomingCursor 0 state)
                      { context with control := .resumeSpan scope count processed destination state.incomingCursor span false [] } span []
                else
                let identity : CallIdentity :=
                  { isStatic := row.isStatic, sourceAddress := row.sourceAddress, sourceRollupId := row.sourceRollupId, targetAddress := row.targetAddress, targetRollupId := p.localRollup, value := row.value, data := row.data }
                let number := state.incomingCursor + 1
                let beginEvent := StructuralEvent.callBegin number
                let state := { state with incomingCursor := number, structuralHash := foldStructural p.keccak state.structuralHash beginEvent }
                .dispatchIncoming state { context with control := .resumeIncoming scope count (processed + 1) destination (callHash p.keccak identity) false [] } row [.structural scope beginEvent]
  | .resumeSpan scope count processed destination savedCursor span success data =>
      let restored := setIncomingSpan context scope savedCursor span state
      let next := { context with control := .processIncoming scope count (processed + span) destination }
      if success then .local restored next []
      else
        let selectorOk := data.take 4 == selector p.keccak contextResultSignature
        let lengthOk := data.length >= 164
        let events := [ProtocolObservation.check scope .transportSelector selectorOk,
          .check scope .transportLength lengthOk]
        match decodeContextResult p.keccak data with
        | .error error => protocolFailure state context error events
        | .ok result =>
            let adopted := { restored with structuralHash := result.rollingHash, outgoingCursor := result.outgoingCursor.toNat, incomingCursor := result.incomingCursor.toNat, crossChainHash := result.crossChainHash }
            .adoptSpan adopted next result events
  | .readyIncoming row scope count processed destination hash =>
      .dispatchIncoming state { context with control := .resumeIncoming scope count processed destination hash false [] } row []
  | .resumeIncoming scope count processed destination hash success data =>
      let record : BoundaryRecord := { callHash := hash, success := success, returnData := data }
      let number := state.incomingCursor
      let state := { state with structuralHash := foldStructural p.keccak state.structuralHash (.callEnd number success data), crossChainHash := foldBoundary p.keccak state.crossChainHash record }
      .local state { context with control := .processIncoming scope count processed destination }
        [.structural scope (.callEnd number success data), .boundary scope hash success data]
  | .consumeOutgoing scope hash callerPeer =>
      match activeHostEntry context state scope.entry with
      | none => protocolFailure state context .executionNotFound
      | some entry =>
          let index := state.outgoingCursor
          let peer := context.activeLookupPeer.getD entry.declaredPeerRollup
          let fallback : ProtocolAction :=
            .local { state with outgoingCursor := index + 1 }
              { context with control := .resolveLookup scope { callHash := hash, callNumber := state.incomingCursor % 2^64, outgoingCursor := index % 2^64, contextIndex := context.lookupContext % 2^64 } false callerPeer } []
          match (activeOutgoing context entry)[index]? with
          | some row =>
              if row.crossChainCallHash != hash then
                fallback
              else if callerPeer != peer then
                protocolFailure { state with outgoingCursor := index + 1 } context (.entrySpansMultiplePeers peer callerPeer)
              else
                let number := index + 1
                let beginEvent := StructuralEvent.nestedBegin number
                let state := { state with outgoingCursor := number, structuralHash := foldStructural p.keccak state.structuralHash beginEvent }
                .local state { context with control := .processIncoming scope row.callCount.toNat 0 (.outgoingCompletion hash row.returnData number) }
                  [.structural scope beginEvent]
          | none => fallback
  | .resolveLookup host key staticMode callerPeer =>
        match activeHostEntry context state host.entry with
        | none => protocolFailure state context .executionNotFound
        | some entry =>
            match findNestedLookup staticMode key entry.expectedLookups with
            | none => protocolFailure state context .executionNotFound
            | some (lookupIndex, lookup) =>
                let scope := { host with invocationPath := host.invocationPath ++ [context.invocationSerial, lookupIndex] }
                if !staticMode then
                  match lookup.incomingCalls.head? with
                  | some first =>
                      if first.sourceRollupId != callerPeer then
                        protocolFailure state context (.entrySpansMultiplePeers first.sourceRollupId callerPeer)
                      else
                        .local { state with structuralHash := zeroHash, crossChainHash := zeroHash, incomingCursor := 0, outgoingCursor := 0 }
                          { context with activeScope := some scope, activeLookupIndex := some lookupIndex, activeLookupPeer := some first.sourceRollupId, lookupContext := lookupIndex + 1, control := .processIncoming scope lookup.callCount.toNat 0 (.lookupValidation lookup) } []
                  | none =>
                      .local { state with structuralHash := zeroHash, crossChainHash := zeroHash, incomingCursor := 0, outgoingCursor := 0 }
                        { context with activeScope := some scope, activeLookupIndex := some lookupIndex, activeLookupPeer := some callerPeer, lookupContext := lookupIndex + 1, control := .processIncoming scope lookup.callCount.toNat 0 (.lookupValidation lookup) } []
                else
                match lookup.incomingCalls.head? with
                | some first =>
                    if first.sourceRollupId != callerPeer then
                      protocolFailure state context (.entrySpansMultiplePeers first.sourceRollupId callerPeer)
                    else
                      match checkCalls first.sourceRollupId false lookup.incomingCalls with
                      | .error error => protocolFailure state context error
                      | .ok () =>
                          let scope := { host with invocationPath := host.invocationPath ++ [context.invocationSerial, lookupIndex] }
                          .local state { context with activeScope := some scope, control := .staticRows scope lookup 0 zeroHash zeroHash } []
                | none =>
                    let scope := { host with invocationPath := host.invocationPath ++ [context.invocationSerial, lookupIndex] }
                    .local state { context with activeScope := some scope, control := .staticRows scope lookup 0 zeroHash zeroHash } []
  | .staticRows scope lookup index rolling cross =>
      match lookup.incomingCalls[index]? with
      | some row =>
          if !row.isStatic then protocolFailure state context .nonStaticSubCall
          else .dispatchStatic state { context with control := .resumeStatic scope lookup index rolling cross zeroHash false [] } row []
      | none =>
          let rollingOk := rolling == lookup.rollingHash
          let structuralEvents := [.check scope .structuralHash rollingOk]
          if !rollingOk then protocolFailure state context .rollingHashMismatch structuralEvents
          else
            let finalRecord : BoundaryRecord := { callHash := lookup.crossChainCallHash, success := !lookup.failed, returnData := lookup.returnData }
            let finalCross := foldBoundary p.keccak cross finalRecord
            let crossOk := finalCross == lookup.crossChainRollingHash
            let events := structuralEvents ++ [.boundary scope finalRecord.callHash finalRecord.success finalRecord.returnData, .check scope .crossChainHash crossOk]
            if !crossOk then protocolFailure state context .crossChainRollingHashMismatch events
            else if lookup.failed then .revertedBytes state { context with control := .finished } lookup.returnData events
            else .returned state { context with control := .finished } lookup.returnData events
  | .resumeStatic scope lookup index rolling cross _ success data =>
      let row := lookup.incomingCalls[index]?
      match row with
      | none => protocolFailure state context .arrayOutOfBounds
      | some call =>
          let identity : CallIdentity := { isStatic := true, sourceAddress := call.sourceAddress, sourceRollupId := call.sourceRollupId, targetAddress := call.targetAddress, targetRollupId := p.localRollup, value := call.value, data := call.data }
          let hash := callHash p.keccak identity
          let nextRolling := foldStatic p.keccak rolling success data
          let nextCross := foldBoundary p.keccak cross { callHash := hash, success := success, returnData := data }
          .local state { context with control := .staticRows scope lookup (index + 1) nextRolling nextCross }
            [.staticResult scope success data, .boundary scope hash success data]
  | .validateLookup scope lookup =>
      let structuralOk := state.structuralHash == lookup.rollingHash
      let firstChecks := [ProtocolObservation.check scope .structuralHash structuralOk]
      if !structuralOk then protocolFailure state context .rollingHashMismatch firstChecks
      else
        let record : BoundaryRecord := { callHash := lookup.crossChainCallHash, success := !lookup.failed, returnData := lookup.returnData }
        let cross := foldBoundary p.keccak state.crossChainHash record
        let state := { state with crossChainHash := cross }
        let crossOk := cross == lookup.crossChainRollingHash
        let incomingOk := state.incomingCursor == lookup.incomingCalls.length
        let outgoingOk := state.outgoingCursor == lookup.expectedOutgoingCalls.length
        let crossChecks := firstChecks ++ [.boundary scope record.callHash record.success record.returnData, .check scope .crossChainHash crossOk]
        let incomingChecks := crossChecks ++ [.check scope .incomingConsumed incomingOk]
        let checks := incomingChecks ++ [.check scope .outgoingConsumed outgoingOk]
        if !crossOk then protocolFailure state context .crossChainRollingHashMismatch crossChecks
        else if !incomingOk then protocolFailure state context .unconsumedIncomingCalls incomingChecks
        else if !outgoingOk then protocolFailure state context .unconsumedOutgoingCalls checks
        else .revertedBytes state { context with control := .finished } lookup.returnData checks
  | .validate scope =>
      match activeEntryRow state scope.entry with
      | none => protocolFailure state context .executionNotFound
      | some (index, entry) =>
          let rootFold := context.route == .proxy
          let rootRecord : BoundaryRecord :=
            { callHash := entry.proxyEntryHash, success := true, returnData := entry.returnData }
          let cross := if rootFold then foldBoundary p.keccak state.crossChainHash rootRecord
                       else state.crossChainHash
          let state := { state with crossChainHash := cross }
          let rootEvents := if rootFold then
            [ProtocolObservation.boundary scope rootRecord.callHash true rootRecord.returnData] else []
          let structuralOk := state.structuralHash == entry.rollingHash
          let crossOk := cross == entry.crossChainRollingHash
          let incomingOk := state.incomingCursor == entry.incomingCalls.length
          let outgoingOk := state.outgoingCursor == entry.expectedOutgoingCalls.length
          let structuralEvents := rootEvents ++ [.check scope .structuralHash structuralOk]
          let crossEvents := structuralEvents ++ [.check scope .crossChainHash crossOk]
          let incomingEvents := crossEvents ++ [.check scope .incomingConsumed incomingOk]
          let checks := incomingEvents ++ [.check scope .outgoingConsumed outgoingOk]
          if !structuralOk then protocolFailure state context .rollingHashMismatch structuralEvents
          else if !crossOk then protocolFailure state context .crossChainRollingHashMismatch crossEvents
          else if !incomingOk then protocolFailure state context .unconsumedIncomingCalls incomingEvents
          else if !outgoingOk then protocolFailure state context .unconsumedOutgoingCalls checks
          else
            let validation : ValidationResult :=
              { selected := scope.entry, structuralHash := state.structuralHash, crossChainHash := cross, incomingConsumed := state.incomingCursor, outgoingConsumed := state.outgoingCursor }
            let cleaned := clearConsumed context.height entry.proxyEntryHash index state
            .returned { cleaned with incomingCursor := 0 }
              { context with control := .finished } entry.returnData
              (checks ++ [.validation validation])
  | _ => .noAction

end EvmYul.CrossChainReplay
