import EvmYul.CrossChainReplay.Execution
import EvmYul.CrossChainReplay.Footprints

/-!
Spec section 5.8 resource plans. Envelopes are mathematical sets indexed by reference
checkpoints. The reference record indexes the obligations; nothing here executes or assumes a
replay `Run`, a replay trace, or replay success.
-/

namespace EvmYul.CrossChainReplay

/-- `I i` is the set of permitted resource valuations at reference checkpoint `i`. -/
abbrev ResourcePlan := Nat → ResourceValuation → Prop

/-- States of a stored record, starting from its configuration's initial state. -/
def referenceStates {M : EvmModel} (config : Configuration M) (record : ExecutionRecord M) :
    List (ExecutionState M) :=
  initialState config :: record.transitions.map Prod.snd

/-- The `i`th reference transition: pre-state, observations, and post-state. -/
def referenceStep {M : EvmModel} (config : Configuration M) (record : ExecutionRecord M)
    (i : Nat) : Option (ExecutionState M × List Observation × ExecutionState M) := do
  let pre ← (referenceStates config record)[i]?
  let (obs, post) ← record.transitions[i]?
  return (pre, obs, post)

/-- Apply resource actions in order under the adapter's pinned arithmetic. -/
inductive ApplyActions (M : EvmModel) : ResourceValuation → List ResourceAction → ResourceValuation → Prop where
  | nil (v : ResourceValuation) : ApplyActions M v [] v
  | cons (v mid final : ResourceValuation) (action : ResourceAction) (rest : List ResourceAction)
      (hAction : M.resourceTransfer v action mid) (hRest : ApplyActions M mid rest final) :
      ApplyActions M v (action :: rest) final

/-- Explicit minima compared against one valuation; no generic `safe` oracle. -/
def DemandMet (demand : ResourceDemand) (v : ResourceValuation) : Prop :=
  demand.minimumGas + demand.childGasReserve ≤ v.gasRemaining ∧
  demand.minimumStateGas ≤ v.stateGasRemaining ∧
  (∀ entry ∈ demand.requiredFunds, entry.2 ≤ v.balance entry.1) ∧
  (∀ address ∈ demand.nonceHeadroom, v.nonce address < nonceLimit)

/-- Listed value transfers are funded; listed nonce increments have EIP-2681 headroom. -/
def ActionsFunded (actions : List ResourceAction) (v : ResourceValuation) : Prop :=
  (∀ source target amount, .transfer source target amount ∈ actions →
    amount.toNat ≤ v.balance source) ∧
  (∀ address, .incrementNonce address ∈ actions → v.nonce address < nonceLimit)

/-- Spec section 5.5 at a transaction boundary, for the replay envelope at that position. -/
def EnvelopeFunded (M : EvmModel) (envelope : DriverEnvelope) (v : ResourceValuation) : Prop :=
  M.intrinsicGas envelope ≤ envelope.gasLimit ∧
  envelope.gasLimit * envelope.gasPrice + envelope.value.toNat ≤ v.balance envelope.sender ∧
  v.nonce envelope.sender < nonceLimit

/-- Required block gas capacity for all replay envelopes. -/
def BlockCapacityOK {M : EvmModel} (config : Configuration M) : Prop :=
  (config.envelopes.map DriverEnvelope.gasLimit).sum ≤ config.blockCapacity

/-- Valuation after transaction-boundary effects of one reference step. Initialization grants
    the replay envelope's gas after intrinsic cost; settlement clears frame resources. -/
def stepBaseValuation (M : EvmModel) (replay : Configuration M) (pre post : ExecutionState M)
    (v : ResourceValuation) : ResourceValuation :=
  let granted := match pre.phase, replay.envelopes[pre.driverIndex]? with
    | .beforeTransaction, some envelope =>
        { v with gasRemaining := envelope.gasLimit - M.intrinsicGas envelope }
    | _, _ => v
  if post.phase != .inTransaction && pre.phase == .inTransaction then
    { granted with gasRemaining := 0, refund := 0 } else granted

/-- Resource actions the replay may perform at reference step `pre`, under valuation `v`:
    the adapter's admissible lists for the reference operation, with the replay environment and
    envelope. The reference step's own amounts are not reused. -/
def AdmissibleStepActions (M : EvmModel) (replay : Configuration M) (pre : ExecutionState M)
    (v : ResourceValuation) (actions : List ResourceAction) : Prop :=
  M.admissibleActions pre.world pre.frames.head? replay.environment
    replay.envelopes[pre.driverIndex]? v actions

/-- Resource update across one reference step: boundary effects, then one admissible list. -/
def StepResourceUpdate (M : EvmModel) (replay : Configuration M) (pre post : ExecutionState M)
    (v : ResourceValuation) (actions : List ResourceAction) (v' : ResourceValuation) : Prop :=
  ApplyActions M (stepBaseValuation M replay pre post v) actions v'

/-- Obligation 2 at one reference checkpoint. -/
def LocalResourceBound (M : EvmModel) (replay : Configuration M) (pre : ExecutionState M)
    (v : ResourceValuation) : Prop :=
  (match pre.phase, replay.envelopes[pre.driverIndex]? with
    | .beforeTransaction, some envelope =>
        EnvelopeFunded M envelope v ∧ M.envelopeValid replay.environment envelope v
    | .beforeTransaction, none => False
    | _, _ => True) ∧
  (match pre.frames with
    | frame :: _ => DemandMet (M.localDemand pre.world frame pre.environment v) v
    | [] => True) ∧
  ∀ actions, AdmissibleStepActions M replay pre v actions → ActionsFunded actions v

/-- Resource-dependent account classifications used by `Related`. -/
def resourceClassification (balance nonce : Nat) : Bool × Bool := (balance == 0, nonce == 0)

/-- Obligation 4 at one step: updated valuations keep the reference post-state classifications. -/
def AccountCompatible (M : EvmModel) (accounts : List Address) (post : ExecutionState M)
    (v' : ResourceValuation) : Prop :=
  ∀ address ∈ accounts,
    resourceClassification (v'.balance address) (v'.nonce address) =
      resourceClassification (M.accountView post.world address).balance
        (M.accountView post.world address).nonce

/-- Spec section 5.8 `BudgetOK` for one target configuration: initialization, local bounds,
    transfer closure over every admissible action list, and account compatibility, quantified
    over the finite reference steps. `accounts` is the footprint's account set. Using the
    reference itself as the target states the reference resource conditions. -/
def BudgetOKWith (M : EvmModel) (reference : Configuration M) (referenceRun : ExecutionRecord M)
    (target : Configuration M) (accounts : List Address) (plan : ResourcePlan) : Prop :=
  -- 1. Initialization.
  plan 0 (initialValuation M target.initialWorld) ∧ BlockCapacityOK target ∧
  (∀ i pre obs post, referenceStep reference referenceRun i = some (pre, obs, post) →
    ∀ v, plan i v →
      -- 2. Local bounds.
      LocalResourceBound M target pre v ∧
      ∀ actions, AdmissibleStepActions M target pre v actions →
        ∀ v', StepResourceUpdate M target pre post v actions v' →
          -- 3. Transfer closure.
          plan (i + 1) v' ∧
          -- 4. Account compatibility.
          AccountCompatible M accounts post v')

/-- Spec section 3.4: the reference footprint extended with replay senders, destinations, and
    settlement recipients. These come from specified inputs, not from a replay trace. -/
def replayFootprint (M : EvmModel) (reference : Configuration M) (referenceRun : ExecutionRecord M)
    (replay : Configuration M) : Footprint :=
  extendAccounts (referenceFootprint (recordFinal reference referenceRun).attempted)
    (replay.envelopes.flatMap fun envelope =>
      envelope.sender :: envelope.destination.toList ++ M.settlementRecipients envelope)

def BudgetOK (M : EvmModel) (_p : Parameters) (reference : Configuration M)
    (referenceRun : ExecutionRecord M) (target : Configuration M) (plan : ResourcePlan) : Prop :=
  BudgetOKWith M reference referenceRun target (replayFootprint M reference referenceRun target).accounts plan

end EvmYul.CrossChainReplay
