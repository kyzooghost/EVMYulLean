import EvmYul.CrossChainReplay.Protocol

open EvmYul.CrossChainReplay

private def hash (bytes : Bytes) : Hash32 :=
  Vector.ofFn fun i => UInt8.ofNat (bytes.length + i.val)

private def parameters : Parameters :=
  { keccak := hash, revision := { name := "toy", specificationId := "toy", enabledOperations := [], nativeOperations := [] }, localRollup := EvmYul.UInt256.ofNat 2, manager := 0, system := 0, proxyCreationCode := [] }

private def outgoingHash : Hash32 := hash [9]
private def entryId : EntryId := .preloaded 0
private def scope : ScopeId := { entry := entryId, invocationPath := [] }
private def peer : Word := EvmYul.UInt256.ofNat 1
private def row : OutgoingCall :=
  { crossChainCallHash := outgoingHash, callCount := EvmYul.UInt256.ofNat 0, returnData := [6] }
private def entry : Entry :=
  { declaredPeerRollup := peer, proxyEntryHash := hash [1], incomingCalls := [], expectedOutgoingCalls := [row], expectedLookups := [], callCount := EvmYul.UInt256.ofNat 0, returnData := [], rollingHash := zeroHash, crossChainRollingHash := zeroHash }
private def state : ProtocolState :=
  { buckets := [{ hash := entry.proxyEntryHash, rows := [{ id := entryId, row := entry, loadedBlock := 11, consumed := false }], head := 1 }], activeEntry := some entryId }
private def context : ProtocolContext :=
  { activeScope := some scope, hostEntry := some entryId, route := .proxy, height := 10, lookupContext := 0, control := .consumeOutgoing scope outgoingHash peer }

private def beginAction : ProtocolAction :=
  advanceProtocol parameters context state context.control

private def outgoingSequence : Bool :=
  match beginAction with
  | .local started next [.structural observedScope (.nestedBegin 1)] =>
      observedScope == scope && started.outgoingCursor == 1 &&
      match advanceProtocol parameters next started next.control with
      | .returned completed _ [6] [.structural _ (.nestedEnd 1), .boundary _ observedHash true [6]] =>
          observedHash == outgoingHash &&
          completed.crossChainHash == foldBoundary hash zeroHash
            { callHash := outgoingHash, success := true, returnData := [6] }
      | _ => false
  | _ => false
#guard outgoingSequence

private def wrongPeerRejected : Bool :=
  match advanceProtocol parameters context state (.consumeOutgoing scope outgoingHash (EvmYul.UInt256.ofNat 3)) with
  | .failed _ _ (.entrySpansMultiplePeers _ _) _ => true
  | _ => false
#guard wrongPeerRejected

private def wrongHashRejected : Bool :=
  match advanceProtocol parameters context state (.consumeOutgoing scope (hash [8, 8]) peer) with
  | .local bumped fallback [] =>
      match advanceProtocol parameters fallback bumped fallback.control with
      | .failed _ _ .executionNotFound _ => true
      | _ => false
  | _ => false
#guard wrongHashRejected

private def incoming (data : Bytes) : IncomingCall :=
  { isStatic := false, targetAddress := 0, value := EvmYul.UInt256.ofNat 0,
    data := data, sourceAddress := 1, sourceRollupId := peer,
    revertSpan := EvmYul.UInt256.ofNat 0 }

private def rowHash (call : IncomingCall) : Hash32 :=
  callHash hash { isStatic := call.isStatic, sourceAddress := call.sourceAddress, sourceRollupId := call.sourceRollupId, targetAddress := call.targetAddress, targetRollupId := parameters.localRollup, value := call.value, data := call.data }

private def a : IncomingCall := incoming [1]
private def b : IncomingCall := incoming [2]
private def expectedEvents : List StructuralEvent :=
  [.callBegin 1, .nestedBegin 1, .callBegin 2, .callEnd 2 true [5],
    .nestedEnd 1, .callEnd 2 true [7]]
private def expectedCross : Hash32 :=
  crossHash hash [
    { callHash := rowHash b, success := true, returnData := [5] },
    { callHash := outgoingHash, success := true, returnData := [6] },
    { callHash := rowHash a, success := true, returnData := [7] },
    { callHash := entry.proxyEntryHash, success := true, returnData := [] }]
private def nestedEntry : Entry :=
  { entry with incomingCalls := [a, b], callCount := EvmYul.UInt256.ofNat 1, expectedOutgoingCalls := [{ row with callCount := EvmYul.UInt256.ofNat 1 }], rollingHash := expectedEvents.foldl (foldStructural hash) zeroHash, crossChainRollingHash := expectedCross }
private def nestedState : ProtocolState :=
  { state with buckets := [{ hash := nestedEntry.proxyEntryHash, rows := [{ id := entryId, row := nestedEntry, loadedBlock := 11, consumed := false }], head := 1 }] }

private def boundaryHashes (events : List ProtocolObservation) : List Hash32 :=
  events.filterMap fun event => match event with
    | .boundary _ h _ _ => some h
    | _ => none

private def nestedOrderBQAroot : Bool :=
  let start := { context with control := .processIncoming scope 1 0 .entryValidation }
  match advanceProtocol parameters start nestedState start.control with
  | .dispatchIncoming afterA suspendedA _ _ =>
      match advanceProtocol parameters suspendedA afterA (.consumeOutgoing scope outgoingHash peer) with
      | .local afterQbegin qContext _ =>
          match advanceProtocol parameters qContext afterQbegin qContext.control with
          | .dispatchIncoming afterB suspendedB _ _ =>
              let bResumed := { suspendedB with control := .resumeIncoming scope 1 1 (.outgoingCompletion outgoingHash [6] 1) (rowHash b) true [5] }
              match advanceProtocol parameters bResumed afterB bResumed.control with
              | .local afterBend bContext bEvents =>
                  match advanceProtocol parameters bContext afterBend bContext.control with
                  | .returned afterQend _ [6] qEvents =>
                      let aResumed := { suspendedA with control := .resumeIncoming scope 1 1 .entryValidation (rowHash a) true [7] }
                      match advanceProtocol parameters aResumed afterQend aResumed.control with
                      | .local afterAend aContext aEvents =>
                          match advanceProtocol parameters aContext afterAend aContext.control with
                          | .local beforeValidation validateContext _ =>
                              match advanceProtocol parameters validateContext beforeValidation validateContext.control with
                              | .returned _ _ [] rootEvents =>
                                  boundaryHashes (bEvents ++ qEvents ++ aEvents ++ rootEvents) ==
                                    [rowHash b, outgoingHash, rowHash a, entry.proxyEntryHash]
                              | _ => false
                          | _ => false
                      | _ => false
                  | _ => false
              | _ => false
          | _ => false
      | _ => false
  | _ => false
#guard nestedOrderBQAroot
