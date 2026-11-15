import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

namespace ProxyDispatchCheck

#check Step.deployIncomingProxy
#check Step.resumeProxyCreation
#check staticProxyError

private def row : IncomingCall :=
  { isStatic := false, targetAddress := 3, value := EvmYul.UInt256.ofNat 0, data := [4], sourceAddress := 2, sourceRollupId := EvmYul.UInt256.ofNat 1, revertSpan := EvmYul.UInt256.ofNat 0 }
private def target : Address := proxyAddress toyParams row.sourceAddress row.sourceRollupId
private def entryId : EntryId := .preloaded 0
private def scope : ScopeId := { entry := entryId, invocationPath := [0] }
private def entry : Entry :=
  { declaredPeerRollup := row.sourceRollupId, proxyEntryHash := zeroHash, incomingCalls := [row], expectedOutgoingCalls := [], expectedLookups := [], callCount := EvmYul.UInt256.ofNat 1, returnData := [], rollingHash := zeroHash, crossChainRollingHash := zeroHash }
private def state : ProtocolState :=
  { buckets := [{ hash := zeroHash, rows := [{ id := entryId, row := entry, loadedBlock := 11, consumed := false }], head := 1 }], activeEntry := some entryId }
private def context : ProtocolContext :=
  { toyContext with activeScope := some scope, hostEntry := some entryId, control := .processIncoming scope 1 0 .entryValidation }
private def rowHash : Hash32 := callHash toyParams.keccak
  { isStatic := row.isStatic, sourceAddress := row.sourceAddress, sourceRollupId := row.sourceRollupId, targetAddress := row.targetAddress, targetRollupId := toyParams.localRollup, value := row.value, data := row.data }
private def prepared : ProtocolState :=
  { state with incomingCursor := 1, structuralHash := foldStructural toyParams.keccak zeroHash (.callBegin 1) }
private def continuation : ProtocolContext :=
  { context with control := .resumeIncoming scope 1 1 .entryValidation rowHash false [] }
private def beginEvents : List ProtocolObservation := [.structural scope (.callBegin 1)]
private def nonceObservation : EngineObservation :=
  { toyObservation with instruction := "CREATE2_SETUP", accounts := [toyParams.manager, target], resources := [.incrementNonce toyParams.manager] }
private def exitObservation : EngineObservation := { toyObservation with instruction := "RETURN" }

/-- A finite deployment adapter. The installed STOP byte is a fixture, not proxy bytecode. -/
private def ProxyToy : EvmModel :=
  { Toy with
    accountView := fun w address =>
      if address == toyParams.manager then { toyAccount with nonce := w.factoryNonce }
      else if w.deployed.contains address then { toyAccount with storedCode := [0], resolvedCode := [0] }
      else { toyAccount with present := false, nonce := 0, empty := true, creationEligible := true }
    primitiveStep := fun w f _ action w' f' obs =>
      action = .frameExit (.returned [0]) ∧ w' = w ∧ f' = f ∧ obs = exitObservation
    enterCreation := fun w f address salt code value saved childWorld suspended child events =>
      address = target ∧ salt = proxySalt toyParams row.sourceAddress row.sourceRollupId ∧
      code = proxyInitCode toyParams row.sourceAddress row.sourceRollupId ∧ value.toNat = 0 ∧
      saved = { w with factoryNonce := w.factoryNonce + 1 } ∧ childWorld = saved ∧
      suspended = f ∧ child = (1 : Nat) ∧ events = [nonceObservation]
    exitCreation := fun _ childWorld _ parent address outcome final resumed result events =>
      address = target ∧ outcome = .returned [0] ∧
      final = { childWorld with deployed := address :: childWorld.deployed } ∧
      resumed = parent ∧ result = .deployed ∧ events = [] }
private def start : ExecutionState ProxyToy :=
  { world := { initialToyWorld with protocol := state }, environment := (), frames := [(0 : Nat)], roles := [.manager], protocol := context, driverIndex := 0, phase := .inTransaction, attempted := [], scopes := [], liveLogs := [], checkpoints := [], pendingOutcome := none, probe := none }
private def savedWorld : ToyWorld := { initialToyWorld with protocol := prepared, factoryNonce := 2 }
private def savedScopes : List ScopeRecord := appendScopeEvents [] beginEvents
private def saved : FrameCheckpoint ProxyToy :=
  { kind := .proxyCreation row, world := savedWorld, frames := [(0 : Nat)], roles := [.manager], protocol := continuation, scopes := savedScopes, liveLogs := [], probe := none }
private def entered : ExecutionState ProxyToy :=
  { start with world := savedWorld, frames := [(1 : Nat), (0 : Nat)], roles := [.application, .manager], protocol := continuation, scopes := savedScopes, attempted := protocolTrace beginEvents ++ [.engine nonceObservation], checkpoints := [saved] }

example : Step ProxyToy toyParams start (protocolTrace beginEvents ++ [.engine nonceObservation]) entered := by
  apply Step.deployIncomingProxy start prepared continuation row beginEvents
    (0 : Nat) (0 : Nat) (1 : Nat) [] savedWorld savedWorld [nonceObservation]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [ProxyToy, Toy, start, savedWorld, initialToyWorld, target, EvmYul.UInt256.toNat, EvmYul.UInt256.ofNat]
    rfl

private def exiting : ExecutionState ProxyToy :=
  { entered with attempted := entered.attempted ++ [.engine exitObservation], pendingOutcome := some (.returned [0]) }
example : Step ProxyToy toyParams entered [.engine exitObservation] exiting := by
  apply Step.engineExit entered (1 : Nat) (1 : Nat) [(0 : Nat)] .application [.manager]
    entered.world exitObservation (.returned [0])
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
  · simp [ProxyToy, Toy]

private def installedWorld : ToyWorld := { savedWorld with deployed := [target] }
private def registeredWorld : ToyWorld :=
  { installedWorld with protocol := registerIncomingProxy toyParams prepared row }
private def readyContext : ProtocolContext :=
  { continuation with control := .readyIncoming row scope 1 1 .entryValidation rowHash }
private def ready : ExecutionState ProxyToy :=
  { exiting with world := registeredWorld, frames := [(0 : Nat)], roles := [.manager], protocol := readyContext, checkpoints := [], pendingOutcome := none }

example : Step ProxyToy toyParams exiting [] ready := by
  apply Step.resumeProxyCreation exiting saved [] (1 : Nat) (0 : Nat) (0 : Nat) [] row
    (.returned [0]) scope 1 1 .entryValidation rowHash installedWorld .deployed []
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [ProxyToy, Toy, installedWorld, savedWorld, saved, exiting, entered, target, initialToyWorld]

#guard ready.world.factoryNonce == 2
#guard (ProxyToy.accountView ready.world target).storedCode == [0]
#guard proxyRegistered toyParams ready.world.protocol row
#guard ready.world.protocol.incomingCursor == 1

example : ∃ next, Step ProxyToy toyParams ready [] next := by
  refine ⟨_, Step.dispatchIncoming ready ready.world.protocol continuation row []
    (0 : Nat) (0 : Nat) [] ready.world ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · native_decide
  · native_decide
  · simp [ProxyToy, Toy, ready, registeredWorld]

private def staticRow : IncomingCall := { row with isStatic := true }
private def staticLookup : NestedLookup :=
  { crossChainCallHash := zeroHash, returnData := [], failed := false, callNumber := 0, lastOutgoingCallConsumed := 0, executingLookupIndex := 0, incomingCalls := [staticRow], expectedOutgoingCalls := [], callCount := EvmYul.UInt256.ofNat 0, rollingHash := zeroHash, crossChainRollingHash := zeroHash }
private def staticContext : ProtocolContext :=
  { context with control := .staticRows scope staticLookup 0 zeroHash zeroHash }
private def staticNext : ProtocolContext :=
  { staticContext with control := .resumeStatic scope staticLookup 0 zeroHash zeroHash zeroHash false [] }
private def staticStart : ExecutionState ProxyToy :=
  { start with world := { initialToyWorld with deployed := [target] }, protocol := staticContext }

#guard !proxyRegistered toyParams staticStart.world.protocol staticRow
#guard staticProxyError ProxyToy toyParams staticStart.world staticRow == none
example : ∃ next, Step ProxyToy toyParams staticStart [] next := by
  refine ⟨_, Step.dispatchStatic staticStart {} staticNext staticRow []
    (0 : Nat) (0 : Nat) [] staticStart.world ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · native_decide
  · simp [ProxyToy, Toy, staticStart, initialToyWorld]

private def missingStatic : ExecutionState ProxyToy :=
  { staticStart with world := initialToyWorld }
example : ∃ next, Step ProxyToy toyParams missingStatic
    (failureTrace staticContext (.lookupCallProxyNotDeployed target) []) next := by
  refine ⟨_, Step.staticProxyFailure missingStatic {} staticNext staticRow []
    (.lookupCallProxyNotDeployed target) ?_ ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · native_decide

#guard proxyIdentityError toyParams 0 (EvmYul.UInt256.ofNat (maxRollupId + 1)) true == some .invalidOriginalAddress
#guard proxyIdentityError toyParams 2 toyParams.localRollup false == none
#guard proxyIdentityError toyParams 2 toyParams.localRollup true == some (.sameNetworkProxy toyParams.localRollup)

private def FailureToy : EvmModel :=
  { ProxyToy with exitCreation := fun saved _ _ parent address outcome final resumed result events =>
      address = target ∧ outcome = .reverted [9] ∧ final = saved ∧ resumed = parent ∧ result = .reverted [9] ∧ events = [] }
private def failureSaved : FrameCheckpoint FailureToy :=
  { kind := .proxyCreation row, world := savedWorld, frames := [(0 : Nat)], roles := [.manager], protocol := continuation, scopes := savedScopes, liveLogs := [], probe := none }
private def failureExiting : ExecutionState FailureToy :=
  { world := savedWorld, environment := (), frames := [(1 : Nat), (0 : Nat)], roles := [.application, .manager], protocol := continuation, driverIndex := 0, phase := .inTransaction, attempted := protocolTrace beginEvents ++ [.engine nonceObservation], scopes := savedScopes, liveLogs := [], checkpoints := [failureSaved], pendingOutcome := some (.reverted [9]), probe := none }
private def failureResumed : ExecutionState FailureToy :=
  { failureExiting with frames := [(0 : Nat)], roles := [.manager], attempted := failureExiting.attempted ++ [.protocol (.failure continuation.activeScope proxyCreationFailureReason)], checkpoints := [] }
example : Step FailureToy toyParams failureExiting
    [.protocol (.failure continuation.activeScope proxyCreationFailureReason)] failureResumed := by
  apply Step.resumeProxyCreation failureExiting failureSaved [] (1 : Nat) (0 : Nat) (0 : Nat) [] row
    (.reverted [9]) scope 1 1 .entryValidation rowHash savedWorld (.reverted [9]) []
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [FailureToy, ProxyToy, Toy, target, failureSaved]
#guard failureResumed.world.factoryNonce == 2
#guard failureResumed.world.deployed.isEmpty
#guard failureResumed.world.protocol.registry.isEmpty
#guard failureResumed.pendingOutcome == some (.reverted [9])

end ProxyDispatchCheck
