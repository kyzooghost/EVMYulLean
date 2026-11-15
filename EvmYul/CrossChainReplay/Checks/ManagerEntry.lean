import EvmYul.CrossChainReplay.Checks.Driver

/-! Manager entry-point guards, against `EEZL2.sol` `loadExecutionTable` and
`executeIncomingCrossChainCall`. -/

open EvmYul.CrossChainReplay DriverCheck

namespace ManagerEntryCheck

def failureOf : ProtocolAction → Option ProtocolError
  | .failed _ _ error _ => some error
  | _ => none

def isStaticViolation : ProtocolAction → Bool
  | .staticWriteViolation _ _ => true
  | _ => false

def isRejected : ProtocolAction → Bool
  | .revertedBytes _ _ [] [] => true
  | _ => false

def run (context : ProtocolContext) : ProtocolAction :=
  advanceProtocol params context initialProtocol context.control

def entryContext (caller : Address) (value : Nat) (call : Option ManagerEntryCall) : ProtocolContext :=
  { context1 with control := managerEntryControl 10 0 caller (EvmYul.UInt256.ofNat value) call }

def duplicateLookup : TopLevelLookup :=
  { declaredPeerRollup := row.sourceRollupId, crossChainCallHash := zeroHash, returnData := [],
    failed := true, incomingCalls := [], expectedOutgoingCalls := [], expectedLookups := [],
    callCount := EvmYul.UInt256.ofNat 0, rollingHash := zeroHash, crossChainRollingHash := zeroHash }

-- `onlySystemAddress` guards both table-loading entry points.
#guard failureOf (run (entryContext 5 0 (some (.loadTable [entry] [])))) == some .unauthorized
#guard failureOf (run (entryContext 5 0 (some (.executeInbound rowHash [entry] [])))) ==
  some .unauthorized

-- Inbound binding precedes duplicate-lookup preflight, as in the source.
#guard failureOf (run (entryContext systemAddress 0
  (some (.executeInbound zeroHash [entry] [duplicateLookup, duplicateLookup])))) ==
  some .entryHashMismatch
#guard failureOf (run (entryContext systemAddress 1 (some (.executeInbound rowHash [entry] [])))) ==
  some .valueMismatch

-- A normal load still rejects duplicates before peer/value checks.
#guard failureOf (run (entryContext systemAddress 0
  (some (.loadTable [entry] [duplicateLookup, duplicateLookup])))) ==
  some (.duplicateLookupHash zeroHash)

-- `loadExecutionTable` is nonpayable; unknown selectors revert with empty data.
#guard isRejected (run (entryContext systemAddress 1 (some (.loadTable [entry] []))))
#guard isRejected (run (entryContext systemAddress 0 none))

-- Under inherited static permission, a successful load halts at its first write.
#guard isStaticViolation (run {
  entryContext systemAddress 0 (some (.loadTable [entry] [])) with
  staticPermission := true })
-- Authorization still fails first under static permission.
#guard failureOf (run {
  entryContext 5 0 (some (.loadTable [entry] [])) with
  staticPermission := true }) == some .unauthorized

-- A direct application call to `executeCrossChainCall` is checked against the registry.
#guard failureOf (run (entryContext 5 0 (some (.executeCrossChain 2 [4])))) ==
  some .unauthorizedProxy

end ManagerEntryCheck
