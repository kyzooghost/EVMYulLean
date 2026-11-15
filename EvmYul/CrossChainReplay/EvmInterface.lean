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
  /-- The one authoritative world state: accounts, code, storage, and transient storage. -/
  World : Type
  /-- One active call frame. -/
  Frame : Type
  /-- Block and chain inputs, fixed for a driver. -/
  Environment : Type
  /-- Protocol view of the manager's storage. Obligation: storage-layout correspondence. -/
  readProtocol : World → ProtocolState
  /-- Synchronized protocol update; `ProtocolViewLaws` constrain it. -/
  writeProtocol : World → ProtocolState → World
  /-- Persistent or transient slot value by `space`; absent slots read zero. -/
  storageValue : World → StorageLocation → Word
  /-- Account fields. Obligation: revision-defined emptiness, delegation, and creation eligibility. -/
  accountView : World → Address → AccountView
  /-- Functional frame state for `Related`. Obligation: matches the revision's machine. -/
  machineView : Frame → Environment → MachineView
  /-- The only functional environment input admitted by spec section 6.1. -/
  chainId : Environment → Word
  /-- Resource view of a frame. Obligation: covers every revision resource dimension. -/
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
  /-- Start one specified transaction: validity check, nonce increment, fee prepayment and
      access-list warming, exposing every account and storage access as observations. -/
  transactionBegin : World → Environment → DriverEnvelope → World → Frame →
    List EngineObservation → Prop
  /-- Apply the pinned settlement effects and expose their observations. -/
  transactionSettle : World → DriverEnvelope → FrameOutcome → World → List EngineObservation → Prop
  /-- Revision validity at submission: signature, nonce, chain, type, fee cap against the
      environment's base fee, and intrinsic gas. -/
  transactionValid : World → Environment → DriverEnvelope → Prop
  /-- Validity expressed on a resource valuation, so resource plans can bound it without a
      replay world. `ProgressLaws` connect it to `transactionValid`. -/
  envelopeValid : Environment → DriverEnvelope → ResourceValuation → Prop
  /-- Resource action lists the next operation can produce at this functional state under the
      valuation: in a frame, or at a transaction boundary with its envelope. This covers cost
      variation such as access warmth and fee prices. -/
  admissibleActions : World → Option Frame → Environment → Option DriverEnvelope →
    ResourceValuation → List ResourceAction → Prop
  /-- Input-derived settlement recipients, such as the fee beneficiary (spec section 3.4). -/
  settlementRecipients : DriverEnvelope → List Address
  /-- Revision-defined intrinsic gas of an envelope. -/
  intrinsicGas : DriverEnvelope → Nat
  /-- Minimum resources for the frame's next operation under the given valuation. Obligation:
      it includes value-bearing call funding, child caps and continuation, and nonce headroom. -/
  localDemand : World → Frame → Environment → ResourceValuation → ResourceDemand
  /-- Pinned arithmetic of one resource action; `ResourceArithmeticLaws` constrain it. -/
  resourceTransfer : ResourceValuation → ResourceAction → ResourceValuation → Prop
  /-- Match a logical manager coordinate to its EVM-visible storage slot. -/
  protocolLocation : String → StorageLocation
  /-- Word stored at a protocol coordinate. Obligation: Solidity storage encoding. -/
  protocolWord : ProtocolState → String → Word
  /-- Locations whose relation is the protocol relation, not literal equality. -/
  protocolOwned : StorageLocation → Prop

/-- Balances and nonces of a world between transactions; frame resources are zero. -/
def initialValuation (M : EvmModel) (world : M.World) : ResourceValuation :=
  { balance := fun address => (M.accountView world address).balance,
    nonce := fun address => (M.accountView world address).nonce,
    gasRemaining := 0, stateGasRemaining := 0, warmedAccounts := [], warmedStorage := [],
    refund := 0, meteringValues := M.storageValue world, savedGas := [], savedStateGas := [] }

/-! ## Local adapter laws

Each group is a local obligation of a pinned EVM instantiation. None mentions a complete run,
a future trace, or replay success. They are hypotheses of the replay statements, so a
contradictory group would make those statements vacuous; `Checks/Laws.lean` exhibits a finite
toy adapter that satisfies every group. -/

/-- Spec sections 4.5 and 5.8: the protocol view is a coherent lens on the one EVM world. -/
def ProtocolViewLaws (M : EvmModel) : Prop :=
  (∀ w ps, M.readProtocol (M.writeProtocol w ps) = ps) ∧
  (∀ w, M.writeProtocol w (M.readProtocol w) = w) ∧
  (∀ w ps coordinate,
    M.storageValue (M.writeProtocol w ps) (M.protocolLocation coordinate) =
      M.protocolWord ps coordinate) ∧
  (∀ coordinate, M.protocolOwned (M.protocolLocation coordinate)) ∧
  (∀ loc, M.protocolOwned loc → ∃ coordinate, loc = M.protocolLocation coordinate) ∧
  (∀ w ps loc, ¬ M.protocolOwned loc →
    M.storageValue (M.writeProtocol w ps) loc = M.storageValue w loc) ∧
  (∀ w ps address, M.accountView (M.writeProtocol w ps) address = M.accountView w address)

/-- Spec section 9: each primitive relation has at most one result. -/
def DeterminismLaws (M : EvmModel) : Prop :=
  (∀ w f env act w₁ f₁ obs₁ w₂ f₂ obs₂,
    M.primitiveStep w f env act w₁ f₁ obs₁ → M.primitiveStep w f env act w₂ f₂ obs₂ →
    w₁ = w₂ ∧ f₁ = f₂ ∧ obs₁ = obs₂) ∧
  (∀ w f env act₁ act₂ w₁ f₁ obs₁ w₂ f₂ obs₂,
    M.primitiveStep w f env act₁ w₁ f₁ obs₁ → M.primitiveStep w f env act₂ w₂ f₂ obs₂ →
    act₁ = act₂) ∧
  (∀ w f req w₁ c₁ w₂ c₂, M.enterFrame w f req w₁ c₁ → M.enterFrame w f req w₂ c₂ →
    w₁ = w₂ ∧ c₁ = c₂) ∧
  (∀ origin cw child parent out w₁ f₁ w₂ f₂,
    M.exitFrame origin cw child parent out w₁ f₁ → M.exitFrame origin cw child parent out w₂ f₂ →
    w₁ = w₂ ∧ f₁ = f₂) ∧
  (∀ origin cw child parent target out w₁ f₁ r₁ e₁ w₂ f₂ r₂ e₂,
    M.exitCreation origin cw child parent target out w₁ f₁ r₁ e₁ →
    M.exitCreation origin cw child parent target out w₂ f₂ r₂ e₂ →
    w₁ = w₂ ∧ f₁ = f₂ ∧ r₁ = r₂ ∧ e₁ = e₂) ∧
  (∀ w env envelope w₁ f₁ e₁ w₂ f₂ e₂,
    M.transactionBegin w env envelope w₁ f₁ e₁ → M.transactionBegin w env envelope w₂ f₂ e₂ →
    w₁ = w₂ ∧ f₁ = f₂ ∧ e₁ = e₂) ∧
  (∀ w envelope out w₁ e₁ w₂ e₂,
    M.transactionSettle w envelope out w₁ e₁ → M.transactionSettle w envelope out w₂ e₂ →
    w₁ = w₂ ∧ e₁ = e₂)

/-- Local progress: a live frame can always take its next primitive transition. A stuck
    adapter would make every replay conclusion unreachable. -/
def ProgressLaws (M : EvmModel) : Prop :=
  (∀ w f env, ∃ act w' f' obs, M.primitiveStep w f env act w' f' obs) ∧
  (∀ w f req, ∃ w' child, M.enterFrame w f req w' child) ∧
  (∀ origin cw child parent out, ∃ w' resumed, M.exitFrame origin cw child parent out w' resumed) ∧
  (∀ w f address salt code value,
    (∃ saved cw suspended child events,
      M.enterCreation w f address salt code value saved cw suspended child events) ∨
    (∃ w' resumed result events, M.rejectCreation w f address salt code value w' resumed result events)) ∧
  (∀ origin cw child parent target out,
    ∃ w' resumed result events, M.exitCreation origin cw child parent target out w' resumed result events) ∧
  (∀ w env envelope, M.transactionValid w env envelope →
    ∃ w' frame events, M.transactionBegin w env envelope w' frame events) ∧
  (∀ w env envelope, M.envelopeValid env envelope (initialValuation M w) →
    M.transactionValid w env envelope) ∧
  (∀ w envelope outcome, ∃ w' events, M.transactionSettle w envelope outcome w' events)

def FrameOutcome.failed : FrameOutcome → Bool
  | .returned _ => false
  | _ => true

/-- Spec section 4.2.3: a failed child frame or initializer restores its checkpoint world. -/
def RollbackLaws (M : EvmModel) : Prop :=
  (∀ origin cw child parent out w' resumed, out.failed = true →
    M.exitFrame origin cw child parent out w' resumed →
    M.readProtocol w' = M.readProtocol origin ∧
    (∀ loc, M.storageValue w' loc = M.storageValue origin loc) ∧
    (∀ address, M.accountView w' address = M.accountView origin address)) ∧
  (∀ origin cw child parent target out w' resumed result events,
    M.exitCreation origin cw child parent target out w' resumed result events →
    result.succeeded = false →
    M.readProtocol w' = M.readProtocol origin ∧
    (∀ loc, M.storageValue w' loc = M.storageValue origin loc)) ∧
  -- Spec section 5.4: transient storage is empty when a transaction begins and ends.
  (∀ w env envelope w' f events, M.transactionBegin w env envelope w' f events →
    ∀ loc, loc.space = .transient → M.storageValue w' loc = EvmYul.UInt256.ofNat 0) ∧
  (∀ w envelope out w' events, M.transactionSettle w envelope out w' events →
    ∀ loc, loc.space = .transient → M.storageValue w' loc = EvmYul.UInt256.ofNat 0)

/-- Spec sections 3.4 and 6: primitive observations are complete for the footprint. -/
def ObservationLaws (M : EvmModel) : Prop :=
  (∀ w f env action w' f' obs, M.primitiveStep w f env action w' f' obs →
    ∀ source target amount, .transfer source target amount ∈ obs.resources →
      source ∈ obs.accounts ∧ target ∈ obs.accounts) ∧
  (∀ w f env action w' f' obs, M.primitiveStep w f env action w' f' obs →
    ∀ access, access ∈ obs.accesses → access.kind = .functionalRead →
      access.readValue = some (M.storageValue w access.location)) ∧
  (∀ w f env action w' f' obs, M.primitiveStep w f env action w' f' obs →
    ∀ loc, M.storageValue w' loc ≠ M.storageValue w loc →
      ∃ access ∈ obs.accesses, access.location = loc ∧ access.kind = .write) ∧
  (∀ w f env action w' f' obs, M.primitiveStep w f env action w' f' obs →
    ∀ address, M.accountView w' address ≠ M.accountView w address → address ∈ obs.accounts) ∧
  (∀ w f env action w' f' obs, M.primitiveStep w f env action w' f' obs →
    ∀ envelope, M.admissibleActions w (some f) env envelope (M.resourceView w f) obs.resources) ∧
  (∀ w env envelope w' f events, M.transactionBegin w env envelope w' f events →
    M.admissibleActions w none env (some envelope) (initialValuation M w)
      (events.flatMap EngineObservation.resources)) ∧
  (∀ w env envelope w' f events, M.transactionBegin w env envelope w' f events →
    ∀ address, M.accountView w' address ≠ M.accountView w address →
      address ∈ events.flatMap EngineObservation.accounts) ∧
  (∀ w envelope out w' events, M.transactionSettle w envelope out w' events →
    ∀ address, M.accountView w' address ≠ M.accountView w address →
      address ∈ events.flatMap EngineObservation.accounts)

/-- Spec section 5.8: the meaning of each resource action used by resource plans. -/
def ResourceArithmeticLaws (M : EvmModel) : Prop :=
  (∀ before amount after, M.resourceTransfer before (.chargeGas amount) after →
    after.gasRemaining + amount = before.gasRemaining) ∧
  (∀ before amount after, M.resourceTransfer before (.forwardGas amount) after →
    after.gasRemaining + amount = before.gasRemaining) ∧
  (∀ before amount after, M.resourceTransfer before (.refund amount) after →
    after.refund = before.refund + amount) ∧
  (∀ before source target amount after,
    M.resourceTransfer before (.transfer source target amount) after → source ≠ target →
    after.balance source + amount.toNat = before.balance source ∧
    after.balance target = before.balance target + amount.toNat ∧
    ∀ other, other ≠ source → other ≠ target → after.balance other = before.balance other) ∧
  (∀ before address after, M.resourceTransfer before (.incrementNonce address) after →
    after.nonce address = before.nonce address + 1 ∧
    ∀ other, other ≠ address → after.nonce other = before.nonce other)

/-- All local laws required of a pinned EVM adapter; no complete replay premise occurs here. -/
def SemanticInterfaceLaws (M : EvmModel) (_p : Parameters) : Prop :=
  ProtocolViewLaws M ∧ DeterminismLaws M ∧ ProgressLaws M ∧ RollbackLaws M ∧
  ObservationLaws M ∧ ResourceArithmeticLaws M

end EvmYul.CrossChainReplay
