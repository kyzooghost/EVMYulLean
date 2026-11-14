import EvmYul.CrossChainReplay.Protocol

open EvmYul.CrossChainReplay

private def toyHash (bytes : Bytes) : Hash32 :=
  Vector.ofFn fun i => UInt8.ofNat (bytes.length + i.val)

private def params : Parameters :=
  { keccak := toyHash
    revision := { name := "fixture", specificationId := "fixture", enabledOperations := [], nativeOperations := [] }
    localRollup := EvmYul.UInt256.ofNat 2
    manager := 0
    system := 0
    proxyCreationCode := [] }

private def rootHash : Hash32 := toyHash [1, 2, 3]
private def identity : EntryId := .driverLoaded 0 0
private def scope : ScopeId := { entry := identity, invocationPath := [] }

private def context (route : RequestRoute) : ProtocolContext :=
  { activeScope := some scope, hostEntry := some identity, route := route,
    height := 10, lookupContext := 0, control := .validate scope }

private def proxyEntry : Entry :=
  { declaredPeerRollup := EvmYul.UInt256.ofNat 1
    proxyEntryHash := rootHash
    incomingCalls := []
    expectedOutgoingCalls := []
    expectedLookups := []
    callCount := EvmYul.UInt256.ofNat 0
    returnData := [7]
    rollingHash := zeroHash
    crossChainRollingHash := foldBoundary toyHash zeroHash
      { callHash := rootHash, success := true, returnData := [7] } }

private def loadedEntry (entry : Entry) : LoadedEntry :=
  { id := identity, row := entry, loadedBlock := 11, consumed := false }

private def loadedBucket (entry : Entry) : EntryBucket :=
  { hash := entry.proxyEntryHash, rows := [loadedEntry entry], head := 1 }

private def loadedState (entry : Entry) : ProtocolState :=
  { buckets := [loadedBucket entry], activeEntry := some identity }

private def proxyRootFold : Bool :=
  match advanceProtocol params (context .proxy) (loadedState proxyEntry) (.validate scope) with
  | .returned state _ _ [ .boundary _ hash true bytes,
      .check _ .structuralHash true, .check _ .crossChainHash true,
      .check _ .incomingConsumed true, .check _ .outgoingConsumed true,
      .validation result ] =>
      hash == rootHash && bytes == [7] && result.crossChainHash == proxyEntry.crossChainRollingHash &&
      state.crossChainHash == proxyEntry.crossChainRollingHash
  | _ => false
#guard proxyRootFold

private def inboundRow : IncomingCall :=
  { isStatic := false, targetAddress := 0, value := EvmYul.UInt256.ofNat 0,
    data := [3], sourceAddress := 0, sourceRollupId := EvmYul.UInt256.ofNat 1,
    revertSpan := EvmYul.UInt256.ofNat 0 }

private def inboundCallHash : Hash32 := callHash toyHash
  { isStatic := false, sourceAddress := inboundRow.sourceAddress,
    sourceRollupId := inboundRow.sourceRollupId, targetAddress := inboundRow.targetAddress,
    targetRollupId := params.localRollup, value := inboundRow.value, data := inboundRow.data }

private def inboundStructural : Hash32 :=
  foldStructural toyHash (foldStructural toyHash zeroHash (.callBegin 1)) (.callEnd 1 true [5])
private def inboundCross : Hash32 :=
  foldBoundary toyHash zeroHash { callHash := inboundCallHash, success := true, returnData := [5] }

private def inboundEntry : Entry :=
  { proxyEntry with proxyEntryHash := inboundCallHash, incomingCalls := [inboundRow], callCount := EvmYul.UInt256.ofNat 1, rollingHash := inboundStructural, crossChainRollingHash := inboundCross }

private def inboundState : ProtocolState :=
  { (loadedState inboundEntry) with incomingCursor := 1, structuralHash := inboundStructural, crossChainHash := inboundCross }

private def inboundHasNoRootFold : Bool :=
  match advanceProtocol params (context .systemInbound) inboundState (.validate scope) with
  | .returned state _ _ [ .check _ .structuralHash true, .check _ .crossChainHash true,
      .check _ .incomingConsumed true, .check _ .outgoingConsumed true,
      .validation result ] =>
      result.crossChainHash == inboundCross && state.crossChainHash == inboundCross
  | _ => false
#guard inboundHasNoRootFold

private def firstFailedCheckStops : Bool :=
  let broken := { proxyEntry with rollingHash := rootHash }
  match advanceProtocol params (context .proxy) (loadedState broken) (.validate scope) with
  | .failed _ _ .rollingHashMismatch [ .boundary _ _ true _,
      .check _ .structuralHash false ] => true
  | _ => false
#guard firstFailedCheckStops

#guard match selectProxyEntry params 10 rootHash (EvmYul.UInt256.ofNat 3)
    { buckets := [{ (loadedBucket proxyEntry) with head := 0 }] } with
  | .error (.entrySpansMultiplePeers expected found) =>
      expected == proxyEntry.declaredPeerRollup && found == EvmYul.UInt256.ofNat 3
  | _ => false
