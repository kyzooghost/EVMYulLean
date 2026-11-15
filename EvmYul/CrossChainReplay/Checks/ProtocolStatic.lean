import EvmYul.CrossChainReplay.Protocol
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

namespace ProtocolStaticCheck

private def lookupHash : Hash32 := toyHash [9]
private def selected : EntryId := .driverLoaded 0 0
private def hostScope : ScopeId := { entry := selected, invocationPath := [] }
private def nested : NestedLookup :=
  { crossChainCallHash := lookupHash, returnData := [7], failed := false,
    callNumber := 0, lastOutgoingCallConsumed := 0, executingLookupIndex := 0,
    incomingCalls := [], expectedOutgoingCalls := [], callCount := EvmYul.UInt256.ofNat 0,
    rollingHash := zeroHash,
    crossChainRollingHash := foldBoundary toyHash zeroHash
      { callHash := lookupHash, success := true, returnData := [7] } }
private def entry : Entry :=
  { declaredPeerRollup := EvmYul.UInt256.ofNat 1, proxyEntryHash := toyHash [3],
    incomingCalls := [], expectedOutgoingCalls := [], expectedLookups := [nested],
    callCount := EvmYul.UInt256.ofNat 0, returnData := [], rollingHash := zeroHash,
    crossChainRollingHash := zeroHash }
private def loaded : LoadedEntry :=
  { id := selected, row := entry, loadedBlock := 11, consumed := false }
private def bucket : EntryBucket :=
  { hash := entry.proxyEntryHash, rows := [loaded], head := 0 }
private def state : ProtocolState :=
  { buckets := [bucket], activeEntry := some selected }
private def key : LookupKey :=
  { callHash := lookupHash, callNumber := 0, outgoingCursor := 0, contextIndex := 0 }
private def context : ProtocolContext :=
  { activeScope := some hostScope, hostEntry := some selected, route := .staticLookup,
    height := 10, lookupContext := 0,
    control := .resolveLookup hostScope key true (EvmYul.UInt256.ofNat 1) }

private def emptyLookupFinalFold : Bool :=
  match advanceProtocol toyParams context state context.control with
  | .local ps next [] =>
      match advanceProtocol toyParams next ps next.control with
      | .returned _ _ [7] [ .check _ .structuralHash true,
          .boundary _ hash true [7], .check _ .crossChainHash true ] =>
          hash == lookupHash
      | _ => false
  | _ => false
#guard emptyLookupFinalFold

#guard match advanceProtocol toyParams context state context.control with
  | .local _ next _ => next.lookupContext == context.lookupContext
  | _ => false

private def failedCross : Hash32 :=
  foldBoundary toyHash zeroHash { callHash := lookupHash, success := false, returnData := [7] }
private def failedNested : NestedLookup :=
  { nested with failed := true, crossChainRollingHash := failedCross }
private def failedEntry : Entry := { entry with expectedLookups := [failedNested] }
private def failedState : ProtocolState :=
  { state with buckets := [{ bucket with rows := [{ loaded with row := failedEntry }] }] }

private def cachedRevertIsExpected : Bool :=
  match advanceProtocol toyParams context failedState context.control with
  | .local ps next [] =>
      match advanceProtocol toyParams next ps next.control with
      | .revertedBytes _ _ [7] [ .check _ .structuralHash true,
          .boundary _ hash false [7], .check _ .crossChainHash true ] => hash == lookupHash
      | _ => false
  | _ => false
#guard cachedRevertIsExpected

private def staticRow : IncomingCall :=
  { isStatic := true, targetAddress := 0, value := EvmYul.UInt256.ofNat 0,
    data := [], sourceAddress := 0, sourceRollupId := EvmYul.UInt256.ofNat 2,
    revertSpan := EvmYul.UInt256.ofNat 0 }
private def wrongPeerEntry : Entry :=
  { entry with expectedLookups := [{ nested with incomingCalls := [staticRow] }] }
private def wrongPeerState : ProtocolState :=
  { state with buckets := [{ bucket with rows := [{ loaded with row := wrongPeerEntry }] }] }

#guard match advanceProtocol toyParams context wrongPeerState context.control with
  | .failed _ _ (.entrySpansMultiplePeers expected found) _ =>
      expected == EvmYul.UInt256.ofNat 2 && found == EvmYul.UInt256.ofNat 1
  | _ => false

end ProtocolStaticCheck
