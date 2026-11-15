import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Checks.Fixtures

/-!
Task 8 driver checks. `DriverToy` is a finite toy EVM, not an Osaka or Glamsterdam
instantiation. Its proxy frame returns fixed bytes instead of forwarding to a destination.
The positive run derives its committed result from composed steps; no result is supplied.
-/

open EvmYul.CrossChainReplay

namespace DriverCheck

def managerAddress : Address := 7
def systemAddress : Address := 9

def row : IncomingCall :=
  { isStatic := false, targetAddress := 3, value := EvmYul.UInt256.ofNat 0, data := [4],
    sourceAddress := 2, sourceRollupId := EvmYul.UInt256.ofNat 1,
    revertSpan := EvmYul.UInt256.ofNat 0 }

def rowHash : Hash32 := callHash toyHash
  { isStatic := row.isStatic, sourceAddress := row.sourceAddress,
    sourceRollupId := row.sourceRollupId, targetAddress := row.targetAddress,
    targetRollupId := EvmYul.UInt256.ofNat 2, value := row.value, data := row.data }

/-- Bytes returned by the toy proxy frame for row zero. -/
def rowResult : Bytes := [6]

def rowRecord : BoundaryRecord := { callHash := rowHash, success := true, returnData := rowResult }

/-- Expected hashes are computed with the same deterministic toy fold; the run must derive them. -/
def entry : Entry :=
  { declaredPeerRollup := row.sourceRollupId, proxyEntryHash := rowHash, incomingCalls := [row],
    expectedOutgoingCalls := [], expectedLookups := [], callCount := EvmYul.UInt256.ofNat 1,
    returnData := [5],
    rollingHash := foldStructural toyHash (foldStructural toyHash zeroHash (.callBegin 1))
      (.callEnd 1 true rowResult),
    crossChainRollingHash := foldBoundary toyHash zeroHash rowRecord }

def inboundCalldata : Bytes := [1]

def params : Parameters :=
  { toyParams with
    manager := managerAddress, system := systemAddress,
    revision := { toyParams.revision with enabledOperations := ["RETURN"] },
    decodeManagerEntry := fun data =>
      if data == inboundCalldata then some (.executeInbound rowHash [entry] []) else none }

def registration : ProxyRegistration :=
  { proxy := proxyAddress params row.sourceAddress row.sourceRollupId,
    originalAddress := row.sourceAddress, originalRollup := row.sourceRollupId }

def initialProtocol : ProtocolState := { registry := [registration] }
def world0 : ToyWorld := { protocol := initialProtocol, steps := 0 }

def exitObservation : EngineObservation := { toyObservation with instruction := "RETURN" }

/-- The toy proxy frame exits with `rowResult`; worlds and frames are otherwise unchanged. -/
def DriverToy : EvmModel :=
  { Toy with
    primitiveStep := fun w f _ action w' f' obs =>
      action = .frameExit (.returned rowResult) ∧ w' = w ∧ f' = f ∧ obs = exitObservation }

def envelope : DriverEnvelope :=
  { kind := .call, sender := systemAddress, nonce := 0, destination := some managerAddress,
    value := EvmYul.UInt256.ofNat 0, data := inboundCalldata, gasLimit := 50,
    gasPrice := 1, blockPosition := 0 }

def config : Configuration DriverToy :=
  { initialWorld := world0, environment := (), envelopes := [envelope], height := 10,
    blockCapacity := 30000000, bundle := { entries := [entry], lookups := [] },
    selected := .driverLoaded 0 0, selectedEntry := entry,
    request := {
      route := .systemInbound, caller := systemAddress, originalCaller := 2,
      target := 3, value := EvmYul.UInt256.ofNat 0, data := [4], isStatic := false } }

def entryId : EntryId := .driverLoaded 0 0
def scope : ScopeId := { entry := entryId, invocationPath := [0] }

def batch : LoadBatch := { entries := [entry], lookups := [] }
def loadContext : LoadContext :=
  { height := 10, loadIndex := 0, route := .systemInbound, caller := systemAddress,
    attachedValue := EvmYul.UInt256.ofNat 0 }

def loadedRow : LoadedEntry := { id := entryId, row := entry, loadedBlock := 11, consumed := false }
def loadedBucket : EntryBucket := { hash := rowHash, rows := [loadedRow], head := 0 }
def protocol2 : ProtocolState := { initialProtocol with buckets := [loadedBucket] }
def loaded : LoadResult :=
  { state := protocol2, newlyLoaded := [entryId], batch := batch, context := loadContext }

def consumedBucket : EntryBucket :=
  { loadedBucket with rows := [{ loadedRow with consumed := true, loadedBlock := 0 }] }
def protocol3 : ProtocolState :=
  { protocol2 with
    buckets := [consumedBucket], activeEntry := some entryId,
    crossChainHash := zeroHash }
def protocol4 : ProtocolState :=
  { protocol3 with
    incomingCursor := 1,
    structuralHash := foldStructural toyHash zeroHash (.callBegin 1) }
def protocol7 : ProtocolState :=
  { protocol4 with
    structuralHash := entry.rollingHash,
    crossChainHash := entry.crossChainRollingHash }

def validation : ValidationResult :=
  { selected := entryId, entryHash := rowHash, declaredPeer := row.sourceRollupId,
    structuralHash := entry.rollingHash, crossChainHash := entry.crossChainRollingHash,
    incomingConsumed := 1, outgoingConsumed := 0 }
/-- Cleanup drains the bucket: no current row remains at or after the head. -/
def protocol9 : ProtocolState :=
  { protocol7 with incomingCursor := 0, buckets := [{ consumedBucket with rows := [], head := 0 }] }

def context1 : ProtocolContext :=
  transactionContext params 10 0 .systemInbound envelope managerAddress
def context2 : ProtocolContext := { context1 with control := .selectInbound rowHash loaded }
def context3 : ProtocolContext :=
  { context2 with
    activeScope := some scope, hostEntry := some entryId, route := .systemInbound,
    control := .processIncoming scope 1 0 .entryValidation }
def context4 : ProtocolContext :=
  { context3 with control := .resumeIncoming scope 1 1 .entryValidation rowHash false [] }
def context6 : ProtocolContext :=
  { context4 with control := .resumeIncoming scope 1 1 .entryValidation rowHash true rowResult }
def context7 : ProtocolContext := { context6 with control := .processIncoming scope 1 1 .entryValidation }
def context8 : ProtocolContext := { context7 with control := .validate scope }
def context9 : ProtocolContext := { context8 with control := .finished }

def beginEvents : List ProtocolObservation := [.structural scope (.callBegin 1)]
def endEvents : List ProtocolObservation :=
  [.structural scope (.callEnd 1 true rowResult), .boundary scope rowHash true rowResult]
def validateEvents : List ProtocolObservation :=
  [.check scope .structuralHash true, .check scope .crossChainHash true,
   .check scope .incomingConsumed true, .check scope .outgoingConsumed true,
   .validation validation]

def state0 : ExecutionState DriverToy := initialState config
def state1 : ExecutionState DriverToy :=
  { state0 with
    frames := [(0 : Nat)], roles := [.manager], protocol := context1,
    phase := .inTransaction, transactionStart := some world0, nextInvocation := 1 }
def state2 : ExecutionState DriverToy :=
  { state1 with world := { world0 with protocol := protocol2 }, protocol := context2 }
def state3 : ExecutionState DriverToy :=
  { state2 with world := { world0 with protocol := protocol3 }, protocol := context3 }
def world4 : ToyWorld := { world0 with protocol := protocol4 }
def checkpoint4 : FrameCheckpoint DriverToy :=
  { kind := .protocolIncoming, world := world4, frames := [(0 : Nat)], roles := [.manager],
    protocol := context4, scopes := appendScopeEvents [] beginEvents, liveLogs := [],
    probe := none, liveValidations := [] }
def state4 : ExecutionState DriverToy :=
  { state3 with
    world := world4, frames := [(0 : Nat), (0 : Nat)], roles := [.proxy, .manager],
    protocol := context4, attempted := protocolTrace beginEvents,
    scopes := appendScopeEvents [] beginEvents, checkpoints := [checkpoint4] }
def state5 : ExecutionState DriverToy :=
  { state4 with
    attempted := state4.attempted ++ [.engine exitObservation],
    pendingOutcome := some (.returned rowResult) }
def state6 : ExecutionState DriverToy :=
  { state5 with
    frames := [(0 : Nat)], roles := [.manager], protocol := context6,
    checkpoints := [], pendingOutcome := none }
def state7 : ExecutionState DriverToy :=
  { state6 with
    world := { world0 with protocol := protocol7 }, protocol := context7,
    attempted := state6.attempted ++ protocolTrace endEvents,
    scopes := appendScopeEvents state6.scopes endEvents }
def state8 : ExecutionState DriverToy := { state7 with protocol := context8 }
def state9 : ExecutionState DriverToy :=
  { state8 with
    world := { world0 with protocol := protocol9 }, protocol := context9,
    attempted := state8.attempted ++ protocolTrace validateEvents,
    scopes := appendScopeEvents state8.scopes validateEvents,
    pendingOutcome := some (.returned (encodeBytesReturn entry.returnData)),
    liveValidations := [validation] }
def transaction : TransactionResult :=
  { index := 0, envelope := envelope, outcome := .returned (encodeBytesReturn entry.returnData),
    committedValidations := [validation], committedLogs := [], settlement := [] }
def state10 : ExecutionState DriverToy :=
  { state9 with
    world := { world0 with protocol := clearTransientProtocol protocol9 },
    frames := [], roles := [], phase := .done, driverIndex := 1, pendingOutcome := none, liveValidations := [],
    transactionStart := none, transactions := [transaction] }

/-- `toyPrimitiveExit`: the toy relations allow an application step and a frame exit. A
    primitive returns only an engine action and engine observation, never a protocol result. -/
theorem toyPrimitiveExit :
    Toy.primitiveStep initialToyWorld (0 : Nat) () .continue
      { initialToyWorld with steps := 1 } (0 : Nat) toyObservation ∧
    DriverToy.primitiveStep world4 (0 : Nat) () (.frameExit (.returned rowResult)) world4 (0 : Nat)
      exitObservation :=
  ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

theorem step1 : Step DriverToy params state0 [] state1 := by
  apply Step.beginTransaction state0 envelope managerAddress world0 (0 : Nat) []
  · rfl
  · rfl
  · rfl
  · exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem step2 : Step DriverToy params state1 [] state2 := by
  apply Step.protocolLocal state1 protocol2 context2 []
  · rfl
  · rfl
  · rfl
  · rfl

set_option maxRecDepth 100000 in
theorem step3 : Step DriverToy params state2 [] state3 := by
  apply Step.protocolLocal state2 protocol3 context3 []
  · rfl
  · rfl
  · rfl
  · rfl

set_option maxRecDepth 100000 in
theorem step4 : Step DriverToy params state3 (protocolTrace beginEvents) state4 := by
  apply Step.dispatchIncoming state3 protocol4 context4 row beginEvents (0 : Nat) (0 : Nat) [] world4
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨rfl, rfl⟩

theorem step5 : Step DriverToy params state4 [.engine exitObservation] state5 := by
  apply Step.engineExit state4 (0 : Nat) (0 : Nat) [(0 : Nat)] .proxy [.manager] world4
    exitObservation (.returned rowResult)
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem step6 : Step DriverToy params state5 [] state6 := by
  apply Step.resumeIncoming state5 checkpoint4 [] (0 : Nat) (0 : Nat) (0 : Nat) []
    (.returned rowResult) scope 1 1 .entryValidation rowHash world4
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨.proxy, rfl⟩
  · rfl
  · rfl
  · exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem step7 : Step DriverToy params state6 (protocolTrace endEvents) state7 := by
  apply Step.protocolLocal state6 protocol7 context7 endEvents
  · rfl
  · rfl
  · rfl
  · rfl

theorem step8 : Step DriverToy params state7 [] state8 := by
  apply Step.protocolLocal state7 protocol7 context8 []
  · rfl
  · rfl
  · rfl
  · rfl

set_option maxRecDepth 100000 in
theorem step9 : Step DriverToy params state8 (protocolTrace validateEvents) state9 := by
  apply Step.protocolReturned state8 protocol9 context9 entry.returnData validateEvents
  · rfl
  · rfl
  · rfl
  · rfl

theorem step10 : Step DriverToy params state9 [] state10 := by
  apply Step.settleTransaction state9 (0 : Nat) (.returned (encodeBytesReturn entry.returnData))
    world0 state9.world envelope []
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact ⟨rfl, rfl⟩

def committedResult : SuccessResult :=
  { validation := validation, returnedBytes := encodeBytesReturn entry.returnData,
    scopes := state10.scopes, completedScopes := [], attempted := state10.attempted }

def record : ExecutionRecord DriverToy :=
  { transitions := [([], state1), ([], state2), ([], state3), (protocolTrace beginEvents, state4),
      ([.engine exitObservation], state5), ([], state6), (protocolTrace endEvents, state7),
      ([], state8), (protocolTrace validateEvents, state9), ([], state10)],
    outcome := .success committedResult }

set_option maxRecDepth 100000 in
/-- `committedToyDriver`: a finite composed run with a retained selected validation. -/
theorem committedToyDriver :
    Run DriverToy params config record ∧
    selectedValidation record entryId = some validation ∧
    driverReturnedBytes record = some (encodeBytesReturn entry.returnData) := by
  refine ⟨⟨?_, rfl, rfl⟩, rfl, rfl⟩
  exact .cons _ _ _ _ _ step1 <| .cons _ _ _ _ _ step2 <| .cons _ _ _ _ _ step3 <|
    .cons _ _ _ _ _ step4 <| .cons _ _ _ _ _ step5 <| .cons _ _ _ _ _ step6 <|
    .cons _ _ _ _ _ step7 <| .cons _ _ _ _ _ step8 <| .cons _ _ _ _ _ step9 <|
    .cons _ _ _ _ _ step10 <| .nil _

/-- The committed hashes equal the bundle's expected values, so the reference is valid. -/
theorem committedToyDriverValid : ValidAtX DriverToy params config record := by
  refine ⟨committedToyDriver.1, by simp [config], committedResult, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [PrescribedChecksPassed, committedResult, state10, state9, state8, state7, state6, state5,
    state4, state3, state2, state1, state0, initialState, config, protocolTrace, validateEvents,
    endEvents, beginEvents]

/-- An altered outcome field is not a run: `Run` derives the outcome from the final state. -/
theorem alteredOutcomeRejected :
    ¬ Run DriverToy params config { record with outcome := .failure [] } := by
  intro h
  have h3 := h.2.2
  have : deriveOutcome config (recordFinal config record) = .success committedResult := rfl
  rw [show recordFinal config { record with outcome := .failure [] } = recordFinal config record
    from rfl, this] at h3
  cases h3

/-- Validation provenance comes only from protocol `.validation` events. A raw log carrying the
    same fields does not populate committed validations. -/
example : validationEvents [.access { location := {
    chain := EvmYul.UInt256.ofNat 2, owner := 0,
    slot := EvmYul.UInt256.ofNat 0 }, kind := .functionalRead } []] = [] := rfl

/-! ### Negative controls -/

/-- The top-level caller reverts after the entry validated: the suffix discards the result. -/
def suffixState : ExecutionState DriverToy :=
  { state9 with roles := [.application], pendingOutcome := some (.reverted []) }

theorem suffixRevert : ∃ next, Step DriverToy params suffixState [] next ∧
    next.phase = .done ∧ (∃ trace, deriveOutcome config next = .failure trace) ∧
    next.transactions.map (·.committedValidations) = [[]] ∧
    Observation.protocol (.validation validation) ∈ next.attempted := by
  refine ⟨_, Step.settleTransaction suffixState (0 : Nat) (.reverted []) world0 world0 envelope []
    rfl rfl rfl rfl rfl rfl ⟨rfl, rfl⟩, rfl, ⟨_, rfl⟩, rfl, ?_⟩
  simp [suffixState, state9, protocolTrace, validateEvents]

def applicationCheckpoint (validations : List ValidationResult) : FrameCheckpoint DriverToy :=
  { kind := .applicationCall, world := world0, frames := [(0 : Nat)], roles := [.application],
    protocol := context1, scopes := [], liveLogs := [], probe := none,
    liveValidations := validations }

def failedCheck : ProtocolObservation := .check scope .crossChainHash false

/-- An entry fails a prescribed check; its application caller catches the revert. -/
def caughtState : ExecutionState DriverToy :=
  { state1 with
    frames := [(1 : Nat), (0 : Nat)], roles := [.manager, .application],
    attempted := [.protocol failedCheck], checkpoints := [applicationCheckpoint []],
    pendingOutcome := some (.reverted (ProtocolError.crossChainRollingHashMismatch.abiBytes toyHash)) }

theorem caughtEntryFailure : ∃ next, Step DriverToy params caughtState [] next ∧
    next.liveValidations = [] ∧ next.pendingOutcome = none ∧
    ¬ PrescribedChecksPassed next.attempted := by
  refine ⟨_, Step.resumeApplication caughtState (applicationCheckpoint []) [] (1 : Nat) (0 : Nat)
    (0 : Nat) [] (.reverted (ProtocolError.crossChainRollingHashMismatch.abiBytes toyHash)) world0
    rfl rfl rfl rfl ⟨.manager, rfl⟩ rfl ⟨rfl, rfl⟩, rfl, rfl, ?_⟩
  intro h
  exact absurd (h (.protocol failedCheck) (by simp [caughtState])) (by simp [failedCheck])

/-- A nested entry validated, then its enclosing frame reverted and the caller caught it. -/
def rolledBackState : ExecutionState DriverToy :=
  { caughtState with
    attempted := [.protocol (.validation validation)], liveValidations := [validation],
    pendingOutcome := some (.reverted []) }

theorem caughtRolledBackValidation : ∃ next, Step DriverToy params rolledBackState [] next ∧
    next.liveValidations = [] ∧ Observation.protocol (.validation validation) ∈ next.attempted := by
  refine ⟨_, Step.resumeApplication rolledBackState (applicationCheckpoint []) [] (1 : Nat) (0 : Nat)
    (0 : Nat) [] (.reverted []) world0 rfl rfl rfl rfl ⟨.manager, rfl⟩ rfl ⟨rfl, rfl⟩, rfl, ?_⟩
  simp [rolledBackState]

/-- A committed setup transaction loaded the table; the driving transaction then fails. -/
def setupWorld : ToyWorld := { world0 with protocol := protocol2 }
def setupTransaction : TransactionResult :=
  { index := 0, envelope := envelope, outcome := .returned [], committedValidations := [],
    committedLogs := [], settlement := [] }
def twoEnvelopeConfig : Configuration DriverToy :=
  { config with envelopes := [envelope, envelope] }
def failingDriverState : ExecutionState DriverToy :=
  { state1 with
    world := setupWorld, envelopes := [envelope, envelope], driverIndex := 1,
    roles := [.application], transactionStart := some setupWorld,
    transactions := [setupTransaction], pendingOutcome := some (.reverted []) }

theorem setupThenFailingDriver : ∃ next, Step DriverToy params failingDriverState [] next ∧
    next.phase = .done ∧ (∃ trace, deriveOutcome twoEnvelopeConfig next = .failure trace) ∧
    next.world.protocol.buckets = [loadedBucket] := by
  refine ⟨_, Step.settleTransaction failingDriverState (0 : Nat) (.reverted []) setupWorld setupWorld
    envelope [] rfl rfl rfl rfl rfl rfl ⟨rfl, rfl⟩, rfl, ⟨_, rfl⟩, rfl⟩

end DriverCheck
