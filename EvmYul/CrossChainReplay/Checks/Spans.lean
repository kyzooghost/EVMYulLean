import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Rollback
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

deriving instance DecidableEq for Except

#check ProtocolAction.dispatchSpan
#check ProtocolAction.spanResult
#check ProtocolAction.adoptSpan

private def entryId : EntryId := .preloaded 0
private def scope : ScopeId := { entry := entryId, invocationPath := [] }
private def row (span : Nat) : IncomingCall :=
  { isStatic := false, targetAddress := 1, value := EvmYul.UInt256.ofNat 0, data := [], sourceAddress := 2, sourceRollupId := EvmYul.UInt256.ofNat 1, revertSpan := EvmYul.UInt256.ofNat span }
private def entry : Entry :=
  { declaredPeerRollup := EvmYul.UInt256.ofNat 1, proxyEntryHash := zeroHash, incomingCalls := [row 0, row 0, row 2, row 0], expectedOutgoingCalls := [], expectedLookups := [], callCount := EvmYul.UInt256.ofNat 3, returnData := [], rollingHash := zeroHash, crossChainRollingHash := zeroHash }
private def state : ProtocolState :=
  { buckets := [{ hash := zeroHash, rows := [{ id := entryId, row := entry, loadedBlock := 11, consumed := false }], head := 1 }], activeEntry := some entryId, incomingCursor := 2, outgoingCursor := 1, structuralHash := toyHash [1], crossChainHash := toyHash [2] }
private def context : ProtocolContext :=
  { toyContext with activeScope := some scope, hostEntry := some entryId, control := .processIncoming scope 3 1 .entryValidation }
private def cleared : ProtocolState := setIncomingSpan context scope 2 0 state
private def parentContext : ProtocolContext :=
  { context with control := .resumeSpan scope 3 1 .entryValidation 2 2 false [] }

#guard match advanceProtocol toyParams context state context.control with
  | .dispatchSpan ps next 2 [] =>
      ps == cleared && next == parentContext && ps.incomingCursor == 2 &&
      ps.crossChainHash == state.crossChainHash &&
      ((activeHostEntry next ps entryId).bind (fun host => host.incomingCalls[2]?)).any
        (fun call => call.revertSpan.toNat == 0)
  | _ => false

#guard match advanceProtocol toyParams context state (.processIncoming scope 2 1 .entryValidation) with
  | .failed _ _ (.revertSpanOutOfBounds processed span count) [] =>
      processed.toNat == 1 && span.toNat == 2 && count.toNat == 2
  | _ => false

private def result : ContextResult :=
  { rollingHash := toyHash [7], outgoingCursor := EvmYul.UInt256.ofNat 8,
    incomingCursor := EvmYul.UInt256.ofNat 999, ignoredFlagWord := EvmYul.UInt256.ofNat 2,
    crossChainHash := toyHash [9] }
private def payload : Bytes := encodeContextResult toyParams.keccak result
private def afterPayload (bytes : Bytes) : ProtocolAction :=
  advanceProtocol toyParams parentContext cleared (.resumeSpan scope 3 1 .entryValidation 2 2 false bytes)

private def acceptedPayload (bytes : Bytes) : Bool :=
  match afterPayload bytes with
  | .adoptSpan adopted next decoded [.check _ .transportSelector true, .check _ .transportLength true] =>
      decoded == result && adopted.structuralHash == result.rollingHash &&
      adopted.crossChainHash == result.crossChainHash && adopted.incomingCursor == 999 &&
      adopted.outgoingCursor == 8 && next.control == .processIncoming scope 3 3 .entryValidation &&
      ((activeHostEntry next adopted entryId).bind (fun host => host.incomingCalls[2]?)).any
        (fun call => call.revertSpan.toNat == 2)
  | _ => false
#guard acceptedPayload payload
#guard acceptedPayload (payload ++ [1])
#guard match afterPayload (payload.take 163) with
  | .failed _ _ (.unexpectedContextRevert _) _ => true
  | _ => false

#guard match advanceProtocol toyParams parentContext cleared
    (.resumeSpan scope 3 1 .entryValidation 2 2 true []) with
  | .local restored next [] =>
      restored == state && next.control == .processIncoming scope 3 3 .entryValidation
  | _ => false

private def completed : ProtocolState :=
  { cleared with structuralHash := result.rollingHash, crossChainHash := result.crossChainHash, incomingCursor := 999, outgoingCursor := 8 }
private def completedContext : ProtocolContext :=
  { context with control := .processIncoming scope 2 2 .spanTransport }
#guard match advanceProtocol toyParams completedContext completed completedContext.control with
  | .spanResult _ _ emitted [] =>
      emitted.rollingHash == result.rollingHash && emitted.incomingCursor.toNat == 999 &&
      emitted.ignoredFlagWord.toNat == 0
  | _ => false

private def start : ExecutionState Toy :=
  { toyState with world := { initialToyWorld with protocol := state }, roles := [.manager], protocol := context }
example : ∃ next, Step Toy toyParams start [] next := by
  refine ⟨_, Step.dispatchSpan start cleared parentContext 2 [] scope 3 1 .entryValidation 2
    (0 : Nat) (0 : Nat) [] { initialToyWorld with protocol := cleared } ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Toy, start, initialToyWorld]

private def scopeRecord : ScopeRecord :=
  { id := scope, effective := [], structural := [], staticOutcomes := [], transportedWitness := none }
#guard (spanScopeAdoption (some scope) result none [scopeRecord]).head? == some scopeRecord
#guard ((spanScopeAdoption (some scope) result (some { result := result, scopes := [scopeRecord] }) []).head?).bind ScopeRecord.transportedWitness == some []

private def emittedResult : ContextResult :=
  { result with ignoredFlagWord := EvmYul.UInt256.ofNat 0 }
private def savedSpan : FrameCheckpoint Toy :=
  checkpointWithKind Toy .protocolSpan
    { start with world := { initialToyWorld with protocol := cleared }, protocol := parentContext }
private def childCompleted : ExecutionState Toy :=
  { start with world := { initialToyWorld with protocol := completed, steps := 99 }, frames := [(0 : Nat), (0 : Nat)], roles := [.manager, .manager], protocol := completedContext, scopes := [scopeRecord], liveLogs := [[9]], checkpoints := [savedSpan], attempted := [.engine toyObservation] }
private def childReverting : ExecutionState Toy :=
  { childCompleted with protocol := { completedContext with control := .finished }, pendingOutcome := some (.reverted (encodeContextResult toyParams.keccak emittedResult)), pendingTransport := some { result := emittedResult, scopes := childCompleted.scopes } }

example : Step Toy toyParams childCompleted [] childReverting := by
  apply Step.protocolSpanResult childCompleted completed
    { completedContext with control := .finished } emittedResult []
  · rfl
  · rfl
  · rfl
  · rfl

private def spanResumed : ExecutionState Toy :=
  { childReverting with world := savedSpan.world, frames := [(0 : Nat)], roles := [.manager], protocol := { parentContext with control := .resumeSpan scope 3 1 .entryValidation 2 2 false (encodeContextResult toyParams.keccak emittedResult) }, scopes := savedSpan.scopes, liveLogs := savedSpan.liveLogs, checkpoints := [], pendingOutcome := none, probe := none }

example : Step Toy toyParams childReverting [] spanResumed := by
  apply Step.resumeSpan childReverting savedSpan [] (0 : Nat) (0 : Nat) (0 : Nat) []
    (.reverted (encodeContextResult toyParams.keccak emittedResult)) savedSpan.world
    scope 3 1 .entryValidation 2 2
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Toy]

#guard spanResumed.world.steps == 0
#guard spanResumed.liveLogs.isEmpty
#guard spanResumed.attempted == [.engine toyObservation]
#guard spanResumed.pendingTransport.any (fun evidence => evidence.result == emittedResult)

private def decodedResult : ContextResult :=
  match decodeContextResult toyParams.keccak (encodeContextResult toyParams.keccak emittedResult) with
  | .ok decoded => decoded
  | .error _ => emittedResult
private def adoptedProtocol : ProtocolState :=
  { (setIncomingSpan spanResumed.protocol scope 2 2 cleared) with structuralHash := decodedResult.rollingHash, crossChainHash := decodedResult.crossChainHash, incomingCursor := decodedResult.incomingCursor.toNat, outgoingCursor := decodedResult.outgoingCursor.toNat }
private def adoptedContext : ProtocolContext :=
  { parentContext with control := .processIncoming scope 3 3 .entryValidation }

example : ∃ next, Step Toy toyParams spanResumed
    [.protocol (.check scope .transportSelector true), .protocol (.check scope .transportLength true)] next := by
  refine ⟨_, Step.protocolAdoptSpan spanResumed adoptedProtocol adoptedContext decodedResult
    [.check scope .transportSelector true, .check scope .transportLength true] ?_ ?_ ?_ ?_⟩
  · rfl
  · rfl
  · rfl
  · have decoded : decodeContextResult toyParams.keccak (encodeContextResult toyParams.keccak emittedResult) = .ok decodedResult := by native_decide
    have selectorChecked : ((encodeContextResult toyParams.keccak emittedResult).take 4 == selector toyParams.keccak contextResultSignature) = true := by native_decide
    have lengthChecked : decide ((encodeContextResult toyParams.keccak emittedResult).length >= 164) = true := by native_decide
    change advanceProtocol toyParams spanResumed.protocol cleared
      (.resumeSpan scope 3 1 .entryValidation 2 2 false (encodeContextResult toyParams.keccak emittedResult)) = _
    simp only [advanceProtocol, Bool.false_eq_true, ↓reduceIte]
    rw [decoded]
    simp only [selectorChecked, lengthChecked]
    rfl

#guard decodedResult == emittedResult
#guard adoptedProtocol.incomingCursor == 999
#guard adoptedProtocol.outgoingCursor == 8

private def nested : NestedLookup :=
  { crossChainCallHash := zeroHash, returnData := [], failed := true, callNumber := 0, lastOutgoingCallConsumed := 0, executingLookupIndex := 0, incomingCalls := [row 2], expectedOutgoingCalls := [], callCount := EvmYul.UInt256.ofNat 1, rollingHash := zeroHash, crossChainRollingHash := zeroHash }
private def nestedState : ProtocolState :=
  { state with buckets := [{ hash := zeroHash, rows := [{ id := entryId, row := { entry with expectedLookups := [nested] }, loadedBlock := 11, consumed := false }], head := 1 }] }
private def nestedContext : ProtocolContext := { context with activeLookupIndex := some 0 }
private def clearedNested : ProtocolState := setIncomingSpan nestedContext scope 0 0 nestedState
#guard ((activeHostEntry nestedContext clearedNested entryId).map
  (fun host => (activeCalls nestedContext host).head?.any (fun call => call.revertSpan.toNat == 0))).getD false
#guard ((activeHostEntry nestedContext clearedNested entryId).map
  (fun host => host.incomingCalls == entry.incomingCalls)).getD false

private def topHost : TopLevelLookup :=
  { declaredPeerRollup := entry.declaredPeerRollup, crossChainCallHash := zeroHash, returnData := [], failed := true, incomingCalls := [row 2], expectedOutgoingCalls := [], expectedLookups := [nested], callCount := EvmYul.UInt256.ofNat 1, rollingHash := zeroHash, crossChainRollingHash := zeroHash }
private def topContext : ProtocolContext := { context with lookupHost := some zeroHash }
private def topState : ProtocolState := { lookups := [{ row := topHost, loadedBlock := 11 }] }
private def clearedTop : ProtocolState := setIncomingSpan topContext scope 0 0 topState
#guard ((activeHostEntry topContext clearedTop entryId).map
  (fun host => (activeCalls topContext host).head?.any (fun call => call.revertSpan.toNat == 0))).getD false
#guard (clearedTop.lookups.head?).any (fun host => host.row.expectedLookups == [nested])

#guard (spanScopeAdoption (some scope) result
  (some { result := emittedResult, scopes := [scopeRecord] }) [scopeRecord]).head? == some scopeRecord
