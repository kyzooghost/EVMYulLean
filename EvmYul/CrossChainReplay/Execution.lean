import EvmYul.CrossChainReplay.ExecutionState

namespace EvmYul.CrossChainReplay

def appendScopeEvent (records : List ScopeRecord) (event : ProtocolObservation) : List ScopeRecord :=
  match event with
  | .boundary scope hash success data =>
      let record : BoundaryRecord := { callHash := hash, success := success, returnData := data }
      if records.any (fun r => r.id == scope) then
        records.map (fun r => if r.id == scope then { r with effective := r.effective ++ [record] } else r)
      else records ++ [{ id := scope, effective := [record], structural := [], staticOutcomes := [], transportedWitness := none }]
  | .structural scope structuralEvent =>
      if records.any (fun r => r.id == scope) then
        records.map (fun r => if r.id == scope then { r with structural := r.structural ++ [structuralEvent] } else r)
      else records ++ [{ id := scope, effective := [], structural := [structuralEvent], staticOutcomes := [], transportedWitness := none }]
  | .staticResult scope success data =>
      if records.any (fun r => r.id == scope) then
        records.map (fun r => if r.id == scope then { r with staticOutcomes := r.staticOutcomes ++ [(success, data)] } else r)
      else records ++ [{ id := scope, effective := [], structural := [], staticOutcomes := [(success, data)], transportedWitness := none }]
  | _ => records

def appendScopeEvents (records : List ScopeRecord) (events : List ProtocolObservation) : List ScopeRecord :=
  events.foldl appendScopeEvent records

/-- Completed lookup scopes are audit history and survive their expected terminal revert. -/
def completedLookupScope (context : ProtocolContext) (records : List ScopeRecord) : List ScopeRecord :=
  let scope := match context.control with
    | .staticRows scope _ _ _ _ => some scope
    | .validateLookup scope _ => some scope
    | _ => none
  match scope with
  | none => []
  | some id => (records.find? (fun record => record.id == id)).toList

def protocolTrace (events : List ProtocolObservation) : Trace := events.map Observation.protocol

def engineTrace (events : List EngineObservation) : Trace := events.map Observation.engine
def engineLogs (events : List EngineObservation) : List Bytes := events.flatMap EngineObservation.rawLogs

/-- Every protocol error remains observable, including errors before scope selection. -/
def failureTrace (context : ProtocolContext) (error : ProtocolError)
    (events : List ProtocolObservation) : Trace :=
  protocolTrace (events ++ [.failure context.activeScope error.signature])

def incomingProxyRequest (p : Parameters) (proxy : Address) (row : IncomingCall) : CallRequest :=
  { target := proxy, value := row.value, data := encodeExecuteOnBehalf p.keccak row.targetAddress row.data, gasCap := none, staticPermission := row.isStatic, kind := if row.isStatic then .staticcall else .call }

/-- The proxy's self-call attempts TSTORE under the inherited static permission. -/
def proxyProbeRequest (p : Parameters) (proxy : Address) (inheritedStatic : Bool) : CallRequest :=
  { target := proxy, value := EvmYul.UInt256.ofNat 0,
    data := selector p.keccak "staticCheck()", gasCap := some proxyProbeGas,
    staticPermission := inheritedStatic }

def exitSuccess : FrameOutcome → Bool
  | .returned _ => true
  | _ => false

def exitBytes : FrameOutcome → Bytes
  | .returned data => data
  | .reverted data => data
  | .exceptional _ => []

/-- The source selects static lookup for every unsuccessful probe outcome. -/
def probeUsesLookup (outcome : FrameOutcome) : Bool := !exitSuccess outcome

def proxyInvocation (view : MachineView) (probe : ProbeResult) : ManagerInvocation :=
  { proxy := view.address, source := view.caller, value := if probeUsesLookup probe.outcome then EvmYul.UInt256.ofNat 0 else view.value, data := view.calldata, isStatic := probeUsesLookup probe.outcome }

def managerRequest (p : Parameters) (view : MachineView) (probe : ProbeResult) : CallRequest :=
  let invocation := proxyInvocation view probe
  { target := p.manager, value := invocation.value, data := encodeManagerInvoke p.keccak invocation.isStatic invocation.source invocation.data, gasCap := none, staticPermission := invocation.isStatic || view.staticPermission, kind := if invocation.isStatic then .staticcall else .call }

def systemRequest (p : Parameters) (value : Word) : CallRequest :=
  { target := p.system, value := value, data := [], gasCap := none, staticPermission := false }

def spanRequest (p : Parameters) (span : Nat) : CallRequest :=
  { target := p.manager, value := EvmYul.UInt256.ofNat 0, data := selector p.keccak "executeInContextAndRevert(uint256)" ++ wordBytes span, gasCap := none, staticPermission := false }

def spanScopeAdoption (scope : Option ScopeId) (result : ContextResult)
    (evidence : Option TransportEvidence) (restored : List ScopeRecord) : List ScopeRecord :=
  match evidence with
  | some candidate =>
      if candidate.result == result then candidate.scopes.map fun record =>
        if some record.id == scope then { record with transportedWitness := some record.effective } else record
      else restored.map fun record =>
        if some record.id == scope then { record with transportedWitness := none } else record
  | none => restored.map fun record =>
      if some record.id == scope then { record with transportedWitness := none } else record

def systemCallObservation (p : Parameters) (frame : Nat) (value : Word) : EngineObservation :=
  { frame := frame, instruction := "CALL", accesses := [], accounts := [p.manager, p.system], nativeOperation := none, resources := [.transfer p.manager p.system value], rawLogs := [] }

def childFrameRole (p : Parameters) (state : ProtocolState) (request : CallRequest) : FrameRole :=
  if request.kind == .delegatecall || request.kind == .callcode then .application
  else if request.target == p.manager then .manager
  else if request.target == p.system then .system
  else if state.registry.any (fun registered => registered.proxy == request.target) then .proxy
  else .application

def staticProxyError (M : EvmModel) (p : Parameters) (world : M.World)
    (row : IncomingCall) : Option ProtocolError :=
  match proxyIdentityError p row.sourceAddress row.sourceRollupId false with
  | some error => some error
  | none =>
      let address := proxyAddress p row.sourceAddress row.sourceRollupId
      if (M.accountView world address).storedCode.isEmpty then some (.lookupCallProxyNotDeployed address)
      else none

def creationFailureBytes : CreationResult → Bytes
  | .reverted data => data
  | _ => []

def proxyCreationFailureReason : String := "ProxyCreationFailed"

/-- One composed operation. Every EVM step is witnessed by the adapter's primitive relation. -/
inductive Step (M : EvmModel) (p : Parameters) :
    ExecutionState M → List Observation → ExecutionState M → Prop where
  | protocolSpanResult (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (result : ContextResult) (events : List ProtocolObservation)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .spanResult ps next result events) :
      Step M p s (protocolTrace events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents s.scopes events, pendingOutcome := some (.reverted (encodeContextResult p.keccak result)), pendingTransport := some { result := result, scopes := appendScopeEvents s.scopes events } }
  | protocolAdoptSpan (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (result : ContextResult) (events : List ProtocolObservation)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .adoptSpan ps next result events) :
      Step M p s (protocolTrace events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents (spanScopeAdoption s.protocol.activeScope result s.pendingTransport s.scopes) events, pendingTransport := none }
  | protocolLocal (s : ExecutionState M) (ps : ProtocolState)
      (next : ProtocolContext) (events : List ProtocolObservation)
      (hActive : s.phase = .inTransaction)
      (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (h : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .local ps next events) :
      Step M p s (protocolTrace events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents s.scopes events }
  | protocolReturned (s : ExecutionState M) (ps : ProtocolState)
      (next : ProtocolContext) (data : Bytes) (events : List ProtocolObservation)
      (hActive : s.phase = .inTransaction)
      (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (h : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .returned ps next data events) :
      Step M p s (protocolTrace events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents s.scopes events, pendingOutcome := some (.returned (encodeBytesReturn data)), completedScopes := s.completedScopes ++ completedLookupScope s.protocol (appendScopeEvents s.scopes events) }
  | protocolFailed (s : ExecutionState M) (ps : ProtocolState)
      (next : ProtocolContext) (error : ProtocolError) (events : List ProtocolObservation)
      (hActive : s.phase = .inTransaction)
      (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (h : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .failed ps next error events) :
      Step M p s (failureTrace s.protocol error events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ failureTrace s.protocol error events, scopes := appendScopeEvents s.scopes events, pendingOutcome := some (.reverted (error.abiBytes p.keccak)), pendingTransport := none }
  | protocolRevertedBytes (s : ExecutionState M) (ps : ProtocolState)
      (next : ProtocolContext) (data : Bytes) (events : List ProtocolObservation)
      (hActive : s.phase = .inTransaction)
      (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (h : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .revertedBytes ps next data events) :
      Step M p s (protocolTrace events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents s.scopes events, pendingOutcome := some (.reverted data), pendingTransport := none, completedScopes := s.completedScopes ++ completedLookupScope s.protocol (appendScopeEvents s.scopes events) }
  | engineContinue (s : ExecutionState M) (f f' : M.Frame) (rest : List M.Frame)
      (role : FrameRole) (restRoles : List FrameRole)
      (w' : M.World) (obs : EngineObservation)
      (hActive : s.phase = .inTransaction)
      (hPending : s.pendingOutcome = none)
      (hFrames : s.frames = f :: rest)
      (hRoles : s.roles = role :: restRoles) (hRole : role ≠ .manager)
      (hStep : M.primitiveStep s.world f s.environment .continue w' f' obs) :
      Step M p s [.engine obs]
        { s with world := w', frames := f' :: rest, attempted := s.attempted ++ [.engine obs], liveLogs := s.liveLogs ++ obs.rawLogs }
  | engineExit (s : ExecutionState M) (f f' : M.Frame) (rest : List M.Frame)
      (role : FrameRole) (restRoles : List FrameRole)
      (w' : M.World) (obs : EngineObservation) (outcome : FrameOutcome)
      (hActive : s.phase = .inTransaction)
      (hPending : s.pendingOutcome = none)
      (hFrames : s.frames = f :: rest)
      (hRoles : s.roles = role :: restRoles) (hRole : role ≠ .manager)
      (hStep : M.primitiveStep s.world f s.environment (.frameExit outcome) w' f' obs) :
      Step M p s [.engine obs]
        { s with world := w', frames := f' :: rest, attempted := s.attempted ++ [.engine obs], liveLogs := s.liveLogs ++ obs.rawLogs, pendingOutcome := some outcome, pendingTransport := none }
  | engineCall (s : ExecutionState M) (f f' child : M.Frame) (rest : List M.Frame)
      (role : FrameRole) (restRoles : List FrameRole)
      (w' childWorld : M.World) (obs : EngineObservation) (request : CallRequest)
      (hActive : s.phase = .inTransaction)
      (hPending : s.pendingOutcome = none)
      (hFrames : s.frames = f :: rest)
      (hRoles : s.roles = role :: restRoles) (hRole : role ≠ .manager)
      (hNotManager : request.target ≠ p.manager ∨ request.kind = .delegatecall ∨ request.kind = .callcode)
      (hNotProbe : role ≠ .proxy ∨ request ≠ proxyProbeRequest p
        (M.machineView f s.environment).address (M.machineView f s.environment).staticPermission)
      (hStep : M.primitiveStep s.world f s.environment (.call request) w' f' obs)
      (hEnter : M.enterFrame w' f' request childWorld child) :
      Step M p s [.engine obs]
        { s with world := childWorld, frames := child :: f' :: rest, roles := childFrameRole p (M.readProtocol childWorld) request :: role :: restRoles, attempted := s.attempted ++ [.engine obs], liveLogs := s.liveLogs ++ obs.rawLogs, checkpoints := { kind := .applicationCall, world := w', frames := f' :: rest, roles := role :: restRoles, protocol := s.protocol, scopes := s.scopes, liveLogs := s.liveLogs ++ obs.rawLogs, probe := s.probe } :: s.checkpoints, probe := none }
  | engineCreate2 (s : ExecutionState M) (f f' suspended child : M.Frame)
      (rest : List M.Frame) (role : FrameRole) (restRoles : List FrameRole)
      (salt : Hash32) (initCode : Bytes) (value : Word)
      (w' savedWorld childWorld : M.World) (obs : EngineObservation)
      (creationEvents : List EngineObservation)
      (hActive : s.phase = .inTransaction) (hPending : s.pendingOutcome = none)
      (hFrames : s.frames = f :: rest) (hRoles : s.roles = role :: restRoles)
      (hRole : role ≠ .manager)
      (hStep : M.primitiveStep s.world f s.environment (.create2 salt initCode value) w' f' obs)
      (hEnter : M.enterCreation w' f'
        (create2Address p.keccak (M.machineView f s.environment).address salt initCode)
        salt initCode value savedWorld childWorld suspended child creationEvents) :
      Step M p s (engineTrace (obs :: creationEvents))
        { s with world := childWorld, frames := child :: suspended :: rest, roles := .application :: role :: restRoles, attempted := s.attempted ++ engineTrace (obs :: creationEvents), liveLogs := s.liveLogs ++ engineLogs (obs :: creationEvents), checkpoints := { kind := .applicationCreation (create2Address p.keccak (M.machineView f s.environment).address salt initCode), world := savedWorld, frames := suspended :: rest, roles := role :: restRoles, protocol := s.protocol, scopes := s.scopes, liveLogs := s.liveLogs ++ engineLogs (obs :: creationEvents), probe := s.probe } :: s.checkpoints, probe := none, pendingTransport := none }
  | rejectCreate2 (s : ExecutionState M) (f f' resumed : M.Frame)
      (rest : List M.Frame) (role : FrameRole) (restRoles : List FrameRole)
      (salt : Hash32) (initCode : Bytes) (value : Word)
      (w' finalWorld : M.World) (obs : EngineObservation)
      (result : CreationResult) (creationEvents : List EngineObservation)
      (hActive : s.phase = .inTransaction) (hPending : s.pendingOutcome = none)
      (hFrames : s.frames = f :: rest) (hRoles : s.roles = role :: restRoles)
      (hRole : role ≠ .manager)
      (hStep : M.primitiveStep s.world f s.environment (.create2 salt initCode value) w' f' obs)
      (hReject : M.rejectCreation w' f'
        (create2Address p.keccak (M.machineView f s.environment).address salt initCode)
        salt initCode value finalWorld resumed result creationEvents)
      (hFailed : result.succeeded = false) :
      Step M p s (engineTrace (obs :: creationEvents))
        { s with world := finalWorld, frames := resumed :: rest, attempted := s.attempted ++ engineTrace (obs :: creationEvents), liveLogs := s.liveLogs ++ engineLogs (obs :: creationEvents), probe := none, pendingTransport := none }
  | resumeCreation (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (target : Address) (outcome : FrameOutcome)
      (finalWorld : M.World) (result : CreationResult) (events : List EngineObservation)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .applicationCreation target)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : s.roles = .application :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hExit : M.exitCreation checkpoint.world s.world child parent target outcome
        finalWorld resumed result events) :
      Step M p s (engineTrace events)
        { s with world := finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := checkpoint.protocol, attempted := s.attempted ++ engineTrace events, scopes := if result.succeeded then s.scopes else checkpoint.scopes, liveLogs := (if result.succeeded then s.liveLogs else checkpoint.liveLogs) ++ engineLogs events, checkpoints := otherCheckpoints, pendingOutcome := none, probe := checkpoint.probe, pendingTransport := none }
  | managerCall (s : ExecutionState M) (f f' child : M.Frame) (rest : List M.Frame)
      (restRoles : List FrameRole) (probe : ProbeResult) (w' childWorld : M.World)
      (obs : EngineObservation)
      (hActive : s.phase = .inTransaction) (hPending : s.pendingOutcome = none)
      (hFrames : s.frames = f :: rest) (hRoles : s.roles = .proxy :: restRoles)
      (hProbe : s.probe = some probe)
      (hOwner : probe.proxy = (M.machineView f s.environment).address ∧ probe.depth = s.frames.length)
      (hStep : M.primitiveStep s.world f s.environment
        (.call (managerRequest p (M.machineView f s.environment) probe)) w' f' obs)
      (hEnter : M.enterFrame w' f' (managerRequest p (M.machineView f s.environment) probe) childWorld child) :
      Step M p s [.engine obs]
        { s with world := childWorld, frames := child :: f' :: rest, roles := .manager :: .proxy :: restRoles, protocol := { s.protocol with control := .invoke (proxyInvocation (M.machineView f s.environment) probe), invocationSerial := s.nextInvocation }, attempted := s.attempted ++ [.engine obs], liveLogs := s.liveLogs ++ obs.rawLogs, checkpoints := { kind := .applicationCall, world := w', frames := f' :: rest, roles := .proxy :: restRoles, protocol := s.protocol, scopes := s.scopes, liveLogs := s.liveLogs ++ obs.rawLogs, probe := none } :: s.checkpoints, probe := none, nextInvocation := s.nextInvocation + 1 }
  | proxyProbe (s : ExecutionState M) (f f' child : M.Frame) (rest : List M.Frame)
      (restRoles : List FrameRole) (w' childWorld : M.World) (obs : EngineObservation)
      (hActive : s.phase = .inTransaction) (hPending : s.pendingOutcome = none)
      (hFrames : s.frames = f :: rest) (hRoles : s.roles = .proxy :: restRoles)
      (hStep : M.primitiveStep s.world f s.environment
        (.call (proxyProbeRequest p (M.machineView f s.environment).address
          (M.machineView f s.environment).staticPermission)) w' f' obs)
      (hEnter : M.enterFrame w' f'
        (proxyProbeRequest p (M.machineView f s.environment).address
          (M.machineView f s.environment).staticPermission) childWorld child) :
      Step M p s [.engine obs]
        { s with world := childWorld, frames := child :: f' :: rest, roles := .proxy :: .proxy :: restRoles, attempted := s.attempted ++ [.engine obs], liveLogs := s.liveLogs ++ obs.rawLogs, checkpoints := { kind := .proxyProbe, world := w', frames := f' :: rest, roles := .proxy :: restRoles, protocol := s.protocol, scopes := s.scopes, liveLogs := s.liveLogs ++ obs.rawLogs, probe := s.probe } :: s.checkpoints, probe := none }
  | resumeProbe (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (outcome : FrameOutcome) (finalWorld : M.World)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .proxyProbe)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : s.roles = .proxy :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hExit : M.exitFrame checkpoint.world s.world child parent outcome finalWorld resumed) :
      Step M p s []
        { s with world := finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := checkpoint.protocol, scopes := if exitSuccess outcome then s.scopes else checkpoint.scopes, liveLogs := if exitSuccess outcome then s.liveLogs else checkpoint.liveLogs, checkpoints := otherCheckpoints, pendingOutcome := none, probe := some { proxy := (M.machineView resumed s.environment).address, depth := rest.length + 1, outcome := outcome } }
  | dispatchSpan (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (span : Nat) (events : List ProtocolObservation) (scope : ScopeId)
      (count processed : Nat) (destination : ProcessDestination) (savedCursor : Nat)
      (f child : M.Frame) (rest : List M.Frame) (childWorld : M.World)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none) (hFrames : s.frames = f :: rest)
      (hSelf : (M.machineView f s.environment).address = p.manager)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchSpan ps next span events)
      (hControl : next.control = .resumeSpan scope count processed destination savedCursor span false [])
      (hEnter : M.enterFrame (M.writeProtocol s.world ps) f (spanRequest p span) childWorld child) :
      Step M p s (protocolTrace events)
        { s with world := childWorld, frames := child :: f :: rest, roles := .manager :: s.roles, protocol := { next with control := .processIncoming scope span 0 .spanTransport }, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents s.scopes events, checkpoints := { kind := .protocolSpan, world := M.writeProtocol s.world ps, frames := f :: rest, roles := s.roles, protocol := next, scopes := appendScopeEvents s.scopes events, liveLogs := s.liveLogs, probe := s.probe } :: s.checkpoints, probe := none, pendingTransport := none }
  | resumeSpan (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (outcome : FrameOutcome) (finalWorld : M.World)
      (scope : ScopeId) (count processed : Nat) (destination : ProcessDestination)
      (savedCursor span : Nat)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .protocolSpan)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : s.roles = .manager :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hControl : checkpoint.protocol.control = .resumeSpan scope count processed destination savedCursor span false [])
      (hExit : M.exitFrame checkpoint.world s.world child parent outcome finalWorld resumed) :
      Step M p s []
        { s with world := finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := { checkpoint.protocol with control := .resumeSpan scope count processed destination savedCursor span (exitSuccess outcome) (exitBytes outcome) }, scopes := checkpoint.scopes, liveLogs := checkpoint.liveLogs, checkpoints := otherCheckpoints, pendingOutcome := none, probe := checkpoint.probe, pendingTransport := if exitSuccess outcome then none else s.pendingTransport }
  | dispatchSystem (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (value : Word) (events : List ProtocolObservation) (f child : M.Frame)
      (rest : List M.Frame) (childWorld : M.World)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none) (hFrames : s.frames = f :: rest)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchSystem ps next value events)
      (hEnter : M.enterFrame (M.writeProtocol s.world ps) f (systemRequest p value) childWorld child) :
      Step M p s (protocolTrace events ++ [.engine (systemCallObservation p (M.machineView f s.environment).depth value)])
        { s with world := childWorld, frames := child :: f :: rest, roles := .system :: s.roles, protocol := next, attempted := s.attempted ++ protocolTrace events ++ [.engine (systemCallObservation p (M.machineView f s.environment).depth value)], scopes := appendScopeEvents s.scopes events, checkpoints := { kind := .protocolSystem, world := M.writeProtocol s.world ps, frames := f :: rest, roles := s.roles, protocol := next, scopes := appendScopeEvents s.scopes events, liveLogs := s.liveLogs, probe := s.probe } :: s.checkpoints, probe := none }
  | resumeSystem (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (outcome : FrameOutcome) (finalWorld : M.World)
      (invocation : ManagerInvocation) (registered : ProxyRegistration)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .protocolSystem)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : s.roles = .system :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hControl : checkpoint.protocol.control = .resumeSystem invocation registered false)
      (hExit : M.exitFrame checkpoint.world s.world child parent outcome finalWorld resumed) :
      Step M p s []
        { s with world := finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := { checkpoint.protocol with control := .resumeSystem invocation registered (exitSuccess outcome) }, scopes := if exitSuccess outcome then s.scopes else checkpoint.scopes, liveLogs := if exitSuccess outcome then s.liveLogs else checkpoint.liveLogs, checkpoints := otherCheckpoints, pendingOutcome := none, probe := checkpoint.probe, pendingTransport := none }
  | incomingProxyFailure (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (row : IncomingCall) (events : List ProtocolObservation) (error : ProtocolError)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchIncoming ps next row events)
      (hError : incomingProxyError p ps row = some error) :
      Step M p s (failureTrace s.protocol error events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ failureTrace s.protocol error events, scopes := appendScopeEvents s.scopes events, pendingOutcome := some (.reverted (error.abiBytes p.keccak)), pendingTransport := none }
  | staticProxyFailure (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (row : IncomingCall) (events : List ProtocolObservation) (error : ProtocolError)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchStatic ps next row events)
      (hError : staticProxyError M p (M.writeProtocol s.world ps) row = some error) :
      Step M p s (failureTrace s.protocol error events)
        { s with world := M.writeProtocol s.world ps, protocol := next, attempted := s.attempted ++ failureTrace s.protocol error events, scopes := appendScopeEvents s.scopes events, pendingOutcome := some (.reverted (error.abiBytes p.keccak)), pendingTransport := none }
  | deployIncomingProxy (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (row : IncomingCall) (events : List ProtocolObservation)
      (f suspended child : M.Frame) (rest : List M.Frame)
      (savedWorld childWorld : M.World) (creationEvents : List EngineObservation)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none) (hFrames : s.frames = f :: rest)
      (hSelf : (M.machineView f s.environment).address = p.manager)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchIncoming ps next row events)
      (hError : incomingProxyError p ps row = none)
      (hMissing : proxyRegistered p ps row = false)
      (hEnter : M.enterCreation (M.writeProtocol s.world ps) f
        (proxyAddress p row.sourceAddress row.sourceRollupId) (proxySalt p row.sourceAddress row.sourceRollupId)
        (proxyInitCode p row.sourceAddress row.sourceRollupId) (EvmYul.UInt256.ofNat 0)
        savedWorld childWorld suspended child creationEvents) :
      Step M p s (protocolTrace events ++ engineTrace creationEvents)
        { s with world := childWorld, frames := child :: suspended :: rest, roles := .application :: s.roles, protocol := next, attempted := s.attempted ++ protocolTrace events ++ engineTrace creationEvents, scopes := appendScopeEvents s.scopes events, liveLogs := s.liveLogs ++ engineLogs creationEvents, checkpoints := { kind := .proxyCreation row, world := savedWorld, frames := suspended :: rest, roles := s.roles, protocol := next, scopes := appendScopeEvents s.scopes events, liveLogs := s.liveLogs ++ engineLogs creationEvents, probe := s.probe } :: s.checkpoints, probe := none, pendingTransport := none }
  | rejectIncomingProxy (s : ExecutionState M) (ps : ProtocolState) (next : ProtocolContext)
      (row : IncomingCall) (events : List ProtocolObservation)
      (f resumed : M.Frame) (rest : List M.Frame) (finalWorld : M.World)
      (result : CreationResult) (creationEvents : List EngineObservation)
      (hActive : s.phase = .inTransaction) (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none) (hFrames : s.frames = f :: rest)
      (hSelf : (M.machineView f s.environment).address = p.manager)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchIncoming ps next row events)
      (hError : incomingProxyError p ps row = none) (hMissing : proxyRegistered p ps row = false)
      (hReject : M.rejectCreation (M.writeProtocol s.world ps) f
        (proxyAddress p row.sourceAddress row.sourceRollupId) (proxySalt p row.sourceAddress row.sourceRollupId)
        (proxyInitCode p row.sourceAddress row.sourceRollupId) (EvmYul.UInt256.ofNat 0)
        finalWorld resumed result creationEvents)
      (hFailed : result.succeeded = false) :
      Step M p s (protocolTrace events ++ engineTrace creationEvents ++ [.protocol (.failure s.protocol.activeScope proxyCreationFailureReason)])
        { s with world := finalWorld, frames := resumed :: rest, protocol := next, attempted := s.attempted ++ protocolTrace events ++ engineTrace creationEvents ++ [.protocol (.failure s.protocol.activeScope proxyCreationFailureReason)], scopes := appendScopeEvents s.scopes events, liveLogs := s.liveLogs ++ engineLogs creationEvents, pendingOutcome := some (.reverted (creationFailureBytes result)), pendingTransport := none }
  | resumeProxyCreation (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (row : IncomingCall) (outcome : FrameOutcome)
      (scope : ScopeId) (count processed : Nat) (destination : ProcessDestination) (hash : Hash32)
      (finalWorld : M.World) (result : CreationResult) (events : List EngineObservation)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .proxyCreation row)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : s.roles = .application :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hControl : checkpoint.protocol.control = .resumeIncoming scope count processed destination hash false [])
      (hExit : M.exitCreation checkpoint.world s.world child parent
        (proxyAddress p row.sourceAddress row.sourceRollupId) outcome finalWorld resumed result events) :
      Step M p s (engineTrace events ++ (if result.succeeded then [] else [.protocol (.failure checkpoint.protocol.activeScope proxyCreationFailureReason)]))
        { s with world := if result.succeeded then M.writeProtocol finalWorld (registerIncomingProxy p (M.readProtocol finalWorld) row) else finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := if result.succeeded then { checkpoint.protocol with control := .readyIncoming row scope count processed destination hash } else checkpoint.protocol, attempted := s.attempted ++ engineTrace events ++ (if result.succeeded then [] else [.protocol (.failure checkpoint.protocol.activeScope proxyCreationFailureReason)]), scopes := if result.succeeded then s.scopes else checkpoint.scopes, liveLogs := (if result.succeeded then s.liveLogs else checkpoint.liveLogs) ++ engineLogs events, checkpoints := otherCheckpoints, pendingOutcome := if result.succeeded then none else some (.reverted (creationFailureBytes result)), probe := checkpoint.probe, pendingTransport := none }
  | dispatchIncoming (s : ExecutionState M) (ps : ProtocolState)
      (next : ProtocolContext) (row : IncomingCall) (events : List ProtocolObservation)
      (f child : M.Frame) (rest : List M.Frame)
      (childWorld : M.World)
      (hActive : s.phase = .inTransaction)
      (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchIncoming ps next row events)
      (hFrames : s.frames = f :: rest)
      (hError : incomingProxyError p ps row = none)
      (hRegistered : proxyRegistered p ps row = true)
      (hEnter : M.enterFrame (M.writeProtocol s.world ps) f
        (incomingProxyRequest p (proxyAddress p row.sourceAddress row.sourceRollupId) row) childWorld child) :
      Step M p s (protocolTrace events)
        { s with world := childWorld, frames := child :: f :: rest, roles := .proxy :: s.roles, protocol := next, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents s.scopes events, checkpoints := { kind := .protocolIncoming, world := M.writeProtocol s.world ps, frames := f :: rest, roles := s.roles, protocol := next, scopes := appendScopeEvents s.scopes events, liveLogs := s.liveLogs, probe := s.probe } :: s.checkpoints, probe := none }
  | dispatchStatic (s : ExecutionState M) (ps : ProtocolState)
      (next : ProtocolContext) (row : IncomingCall) (events : List ProtocolObservation)
      (f child : M.Frame) (rest : List M.Frame)
      (childWorld : M.World)
      (hActive : s.phase = .inTransaction)
      (hManager : s.roles.head? = some .manager)
      (hPending : s.pendingOutcome = none)
      (hAction : advanceProtocol p s.protocol (M.readProtocol s.world) s.protocol.control =
        .dispatchStatic ps next row events)
      (hFrames : s.frames = f :: rest)
      (hError : staticProxyError M p (M.writeProtocol s.world ps) row = none)
      (hEnter : M.enterFrame (M.writeProtocol s.world ps) f
        (incomingProxyRequest p (proxyAddress p row.sourceAddress row.sourceRollupId) row) childWorld child) :
      Step M p s (protocolTrace events)
        { s with world := childWorld, frames := child :: f :: rest, roles := .proxy :: s.roles, protocol := next, attempted := s.attempted ++ protocolTrace events, scopes := appendScopeEvents s.scopes events, checkpoints := { kind := .protocolStatic, world := M.writeProtocol s.world ps, frames := f :: rest, roles := s.roles, protocol := next, scopes := appendScopeEvents s.scopes events, liveLogs := s.liveLogs, probe := s.probe } :: s.checkpoints, probe := none }
  | resumeIncoming (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (outcome : FrameOutcome)
      (scope : ScopeId) (count processed : Nat) (destination : ProcessDestination) (hash : Hash32)
      (finalWorld : M.World)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .protocolIncoming)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : ∃ childRole, s.roles = childRole :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hControl : checkpoint.protocol.control = .resumeIncoming scope count processed destination hash false [])
      (hExit : M.exitFrame checkpoint.world s.world child parent outcome finalWorld resumed) :
      Step M p s []
        { s with world := finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := { checkpoint.protocol with control := .resumeIncoming scope count processed destination hash (exitSuccess outcome) (exitBytes outcome) }, scopes := if exitSuccess outcome then s.scopes else checkpoint.scopes, liveLogs := if exitSuccess outcome then s.liveLogs else checkpoint.liveLogs, checkpoints := otherCheckpoints, pendingOutcome := none, probe := checkpoint.probe, pendingTransport := none }
  | resumeApplication (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (outcome : FrameOutcome) (finalWorld : M.World)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .applicationCall)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : ∃ childRole, s.roles = childRole :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hExit : M.exitFrame checkpoint.world s.world child parent outcome finalWorld resumed) :
      Step M p s []
        { s with world := finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := checkpoint.protocol, scopes := if exitSuccess outcome then s.scopes else checkpoint.scopes, liveLogs := if exitSuccess outcome then s.liveLogs else checkpoint.liveLogs, checkpoints := otherCheckpoints, pendingOutcome := none, probe := checkpoint.probe, pendingTransport := none }
  | resumeStatic (s : ExecutionState M) (checkpoint : FrameCheckpoint M)
      (otherCheckpoints : List (FrameCheckpoint M)) (child parent resumed : M.Frame)
      (rest : List M.Frame) (outcome : FrameOutcome)
      (scope : ScopeId) (lookup : NestedLookup) (index : Nat)
      (rolling cross hash : Hash32) (finalWorld : M.World)
      (hActive : s.phase = .inTransaction)
      (hCheckpoint : s.checkpoints = checkpoint :: otherCheckpoints)
      (hKind : checkpoint.kind = .protocolStatic)
      (hFrames : s.frames = child :: parent :: rest)
      (hRoles : ∃ childRole, s.roles = childRole :: checkpoint.roles)
      (hPending : s.pendingOutcome = some outcome)
      (hControl : checkpoint.protocol.control = .resumeStatic scope lookup index rolling cross hash false [])
      (hExit : M.exitFrame checkpoint.world s.world child parent outcome finalWorld resumed) :
      Step M p s []
        { s with world := finalWorld, frames := resumed :: rest, roles := checkpoint.roles, protocol := { checkpoint.protocol with control := .resumeStatic scope lookup index rolling cross hash (exitSuccess outcome) (exitBytes outcome) }, scopes := if exitSuccess outcome then s.scopes else checkpoint.scopes, liveLogs := if exitSuccess outcome then s.liveLogs else checkpoint.liveLogs, checkpoints := otherCheckpoints, pendingOutcome := none, probe := checkpoint.probe, pendingTransport := none }
  | topLevelExit (s : ExecutionState M) (f : M.Frame) (outcome : FrameOutcome)
      (hActive : s.phase = .inTransaction)
      (hFrames : s.frames = [f]) (hRoles : s.roles.length = 1)
      (hCheckpoints : s.checkpoints = [])
      (hPending : s.pendingOutcome = some outcome) :
      Step M p s [] { s with frames := [], roles := [], phase := .afterTransaction, pendingOutcome := none }

end EvmYul.CrossChainReplay
