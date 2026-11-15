import EvmYul.CrossChainReplay.Protocol
import EvmYul.CrossChainReplay.Checks.Fixtures

open EvmYul.CrossChainReplay

namespace ProtocolRevertedCheck

#check ProtocolControl.validateLookup
#check ProtocolContext.activeLookupIndex

private def entryId : EntryId := .preloaded 0
private def scope : ScopeId := { entry := entryId, invocationPath := [] }
private def lookupHash : Hash32 := toyHash [1, 2]
private def lookup : NestedLookup :=
  { crossChainCallHash := lookupHash, returnData := [9], failed := true,
    callNumber := 3, lastOutgoingCallConsumed := 0, executingLookupIndex := 0,
    incomingCalls := [], expectedOutgoingCalls := [], callCount := EvmYul.UInt256.ofNat 0,
    rollingHash := zeroHash, crossChainRollingHash := foldBoundary toyHash zeroHash
      { callHash := lookupHash, success := false, returnData := [9] } }
private def entry : Entry :=
  { declaredPeerRollup := EvmYul.UInt256.ofNat 1, proxyEntryHash := toyHash [],
    incomingCalls := [], expectedOutgoingCalls := [], expectedLookups := [lookup],
    callCount := EvmYul.UInt256.ofNat 0, returnData := [], rollingHash := zeroHash,
    crossChainRollingHash := zeroHash }
private def state : ProtocolState :=
  { buckets := [{ hash := entry.proxyEntryHash, rows := [{ id := entryId, row := entry, loadedBlock := 11, consumed := false }], head := 1 }], activeEntry := some entryId, incomingCursor := 3, structuralHash := toyHash [4], crossChainHash := toyHash [5] }
private def context : ProtocolContext :=
  { activeScope := some scope, hostEntry := some entryId, route := .proxy, height := 10,
    lookupContext := 0, control := .consumeOutgoing scope lookupHash (EvmYul.UInt256.ofNat 1) }

private def fallbackResetsAndReverts : Bool :=
  match advanceProtocol toyParams context state context.control with
  | .local bumped fallback [] =>
      bumped.outgoingCursor == 1 &&
      match fallback.control with
      | .resolveLookup _ key false _ =>
          key.outgoingCursor == 0 && key.callNumber == 3 &&
          match advanceProtocol toyParams fallback bumped fallback.control with
          | .local reset executing [] =>
              reset.incomingCursor == 0 && reset.outgoingCursor == 0 &&
              reset.crossChainHash == zeroHash && reset.structuralHash == zeroHash &&
              executing.hostEntry == context.hostEntry && executing.lookupContext == 1 &&
              executing.activeLookupIndex == some 0 &&
              match advanceProtocol toyParams executing reset executing.control with
              | .local beforeCheck checking [] =>
                  match advanceProtocol toyParams checking beforeCheck checking.control with
                  | .revertedBytes _ _ [9] [.check _ .structuralHash true,
                      .boundary _ h false [9], .check _ .crossChainHash true,
                      .check _ .incomingConsumed true, .check _ .outgoingConsumed true] => h == lookupHash
                  | _ => false
              | _ => false
          | _ => false
      | _ => false
  | _ => false
#guard fallbackResetsAndReverts

private def structuralFailurePrecedesFold : Bool :=
  match advanceProtocol toyParams context state (.validateLookup scope lookup) with
  | .failed unchanged _ .rollingHashMismatch [.check _ .structuralHash false] =>
      unchanged.crossChainHash == state.crossChainHash
  | _ => false
#guard structuralFailurePrecedesFold

private def incompleteConsumptionRejects : Bool :=
  let reset := { state with structuralHash := zeroHash, crossChainHash := zeroHash }
  match advanceProtocol toyParams context reset (.validateLookup scope lookup) with
  | .failed _ _ .unconsumedIncomingCalls _ => true
  | _ => false
#guard incompleteConsumptionRejects

#guard activeCalls { context with activeLookupIndex := some 0 } entry == []
#guard activeOutgoing { context with activeLookupIndex := some 0 } entry == []

private def hostOutgoing : OutgoingCall :=
  { crossChainCallHash := toyHash [3], callCount := EvmYul.UInt256.ofNat 0, returnData := [] }
#guard activeOutgoing context { entry with expectedOutgoingCalls := [hostOutgoing] } == [hostOutgoing]
#guard activeOutgoing { context with activeLookupIndex := some 0 }
  { entry with expectedOutgoingCalls := [hostOutgoing] } == []

private def failedFilterPreserved : Bool :=
  let successful := { lookup with failed := false }
  let key : LookupKey := { callHash := lookupHash, callNumber := 3, outgoingCursor := 0, contextIndex := 0 }
  (findNestedLookup false key [successful, lookup]).map Prod.fst == some 1 &&
    (findNestedLookup true key [successful, lookup]).map Prod.fst == some 0
#guard failedFilterPreserved

end ProtocolRevertedCheck
