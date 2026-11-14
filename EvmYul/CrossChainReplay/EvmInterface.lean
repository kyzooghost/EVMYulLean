import EvmYul.CrossChainReplay.Protocol
import EvmYul.CrossChainReplay.Observations

namespace EvmYul.CrossChainReplay

inductive CallKind where
  | call | callcode | delegatecall | staticcall
  deriving Repr, BEq, DecidableEq

structure CallRequest where
  target : Address
  value : Word
  data : Bytes
  gasCap : Option Nat
  staticPermission : Bool
  kind : CallKind := .call
  deriving Repr, BEq

inductive HaltCause where
  | outOfGas | staticViolation | invalidOpcode | callDepth
  | other (description : String)
  deriving Repr, BEq

inductive FrameOutcome where
  | returned (data : Bytes)
  | reverted (data : Bytes)
  | exceptional (cause : HaltCause)
  deriving Repr, BEq

inductive CreationResult where
  | deployed
  | reverted (data : Bytes)
  | exceptional (cause : HaltCause)
  deriving Repr, BEq

def CreationResult.succeeded : CreationResult → Bool
  | .deployed => true
  | _ => false

inductive EngineAction where
  | continue
  | call (request : CallRequest)
  | create2 (salt : Hash32) (initCode : Bytes) (value : Word)
  | frameExit (outcome : FrameOutcome)
  deriving Repr, BEq

inductive PrimitiveEffect where
  | local
  | enteredFrame
  | exitedFrame (outcome : FrameOutcome)
  | beganTransaction
  | settledTransaction
  deriving Repr, BEq

/-- Resource inputs excluded from ordinary machine equality. -/
structure ResourceValuation where
  balance : Address → Nat
  nonce : Address → Nat
  gasRemaining : Nat
  stateGasRemaining : Nat
  warmedAccounts : List Address
  warmedStorage : List StorageLocation
  refund : Nat
  meteringValues : StorageLocation → Word
  savedGas : List Nat
  savedStateGas : List Nat

structure ResourceDemand where
  minimumGas : Nat
  minimumStateGas : Nat
  requiredFunds : List (Address × Nat)
  nonceHeadroom : List Address
  childGasReserve : Nat

/-- Only local primitives are supplied here; protocol runs and result checks are composed later. -/
structure EvmModel where
  World : Type
  Frame : Type
  Environment : Type
  readProtocol : World → ProtocolState
  writeProtocol : World → ProtocolState → World
  storageValue : World → StorageLocation → Word
  accountView : World → Address → AccountView
  machineView : Frame → Environment → MachineView
  resourceView : World → Frame → ResourceValuation
  /-- A primitive may request a call or exit; it cannot supply a protocol transcript. -/
  primitiveStep : World → Frame → Environment → EngineAction → World → Frame → EngineObservation → Prop
  /-- Enter a requested child frame under this revision's call rules. -/
  enterFrame : World → Frame → CallRequest → World → Frame → Prop
  /-- Resume a parent after the child frame completes. -/
  exitFrame : World → World → Frame → Frame → FrameOutcome → World → Frame → Prop
  /-- Begin CREATE2 setup. The checkpoint retains parent nonce/gas effects, before child effects.
      Obligations: exact revision checks, funding, nonce increment, checkpoint placement,
      child account initialization, parent suspension, and complete observations. -/
  enterCreation : World → Frame → Address → Hash32 → Bytes → Word →
    World → World → Frame → Frame → List EngineObservation → Prop
  /-- Immediate CREATE2 failure before an initializer frame exists; resume the parent with zero.
      Obligations: source failure precedence, nonce/gas effects and returned-data rules. -/
  rejectCreation : World → Frame → Address → Hash32 → Bytes → Word →
    World → Frame → CreationResult → List EngineObservation → Prop
  /-- Finish initializer execution, including code validation/deposit and installation.
      Obligations: restore child effects on failure while retaining the saved parent
      nonce/gas effects; resume with the address or zero and the specified return data. -/
  exitCreation : World → World → Frame → Frame → Address → FrameOutcome →
    World → Frame → CreationResult → List EngineObservation → Prop
  /-- Start one specified transaction, including its validity check. -/
  transactionBegin : World → Environment → DriverEnvelope → World → Frame → Prop
  /-- Apply the pinned settlement effects and expose their observations. -/
  transactionSettle : World → DriverEnvelope → FrameOutcome → World → List EngineObservation → Prop
  transactionValid : World → DriverEnvelope → Prop
  settlementRecipients : DriverEnvelope → List Address
  localDemand : World → Frame → Environment → ResourceDemand
  resourceTransfer : ResourceValuation → ResourceAction → ResourceValuation → Prop
  /-- Match a logical manager coordinate to its EVM-visible storage slot. -/
  protocolLocation : String → StorageLocation
  protocolWord : ProtocolState → String → Word
  protocolOwned : StorageLocation → Prop

/-- Local semantic laws required of a pinned EVM adapter; no complete replay premise occurs here. -/
def SemanticInterfaceLaws (M : EvmModel) (_p : Parameters) : Prop :=
  (∀ w ps, M.readProtocol (M.writeProtocol w ps) = ps) ∧
  (∀ w ps coordinate,
    M.storageValue (M.writeProtocol w ps) (M.protocolLocation coordinate) =
      M.protocolWord ps coordinate) ∧
  (∀ coordinate, M.protocolOwned (M.protocolLocation coordinate)) ∧
  (∀ w ps loc, ¬ M.protocolOwned loc →
    M.storageValue (M.writeProtocol w ps) loc = M.storageValue w loc) ∧
  (∀ w f env act w₁ f₁ obs₁ w₂ f₂ obs₂,
    M.primitiveStep w f env act w₁ f₁ obs₁ →
    M.primitiveStep w f env act w₂ f₂ obs₂ →
    w₁ = w₂ ∧ f₁ = f₂ ∧ obs₁ = obs₂) ∧
  (∀ w f env action w' f' obs,
    M.primitiveStep w f env action w' f' obs →
    ∀ source target amount,
      .transfer source target amount ∈ obs.resources →
      source ∈ obs.accounts ∧ target ∈ obs.accounts) ∧
  (∀ w f env action w' f' obs,
    M.primitiveStep w f env action w' f' obs →
    ∀ access, access ∈ obs.accesses → access.kind = .functionalRead →
      access.readValue = some (M.storageValue w access.location)) ∧
  (∀ origin childWorld child parent data finalWorld resumed,
    M.exitFrame origin childWorld child parent (.reverted data) finalWorld resumed →
      M.readProtocol finalWorld = M.readProtocol origin ∧
      (∀ loc, M.storageValue finalWorld loc = M.storageValue origin loc)) ∧
  (∀ w env envelope, M.transactionValid w envelope →
    ∃ w' frame, M.transactionBegin w env envelope w' frame) ∧
  (∀ w envelope outcome, ∃ w' observations,
    M.transactionSettle w envelope outcome w' observations) ∧
  (∀ before amount after,
    M.resourceTransfer before (.chargeGas amount) after →
      after.gasRemaining + amount = before.gasRemaining)

end EvmYul.CrossChainReplay
