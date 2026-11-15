import EvmYul.CrossChainReplay.Admissibility
import EvmYul.CrossChainReplay.Checks.Driver

open EvmYul.CrossChainReplay

namespace FootprintCheck

#check referenceFootprint
#check accountProjection

def location : StorageLocation :=
  { chain := EvmYul.UInt256.ofNat 2, owner := 0, slot := EvmYul.UInt256.ofNat 3 }

def engineEvent (kind : AccessKind) : Observation := .engine
  { frame := 1, instruction := "SLOAD", accesses := [{ location := location, kind := kind }],
    accounts := [0], nativeOperation := none, resources := [], rawLogs := [] }

def attemptedReadFootprint : Bool :=
  let trace : Trace :=
    [.protocol (.access { location := location, kind := .write } []),
     engineEvent .functionalRead,
     .protocol (.failure (some { entry := .driverLoaded 0 0, invocationPath := [1] }) "revert"),
     engineEvent .functionalRead]
  (referenceFootprint trace).storageReads.length == 2 &&
  (referenceFootprint trace).storageReads.contains location
#guard attemptedReadFootprint

/-- `meteringOnlyRead`: a metering read is not a functional storage read. -/
def meteringOnlyRead : Bool :=
  ((referenceFootprint [engineEvent .meteringRead]).storageReads.contains location,
   (referenceFootprint [engineEvent .meteringRead]).meteringReads.contains location) == (false, true)
#guard meteringOnlyRead

def feeRecipient : Address := 1
def settlementTrace : Trace := [.engine
  { frame := 0, instruction := "settle", accesses := [], accounts := [], nativeOperation := none,
    resources := [.transfer 0 feeRecipient (EvmYul.UInt256.ofNat 1)], rawLogs := [] }]
#guard (referenceFootprint settlementTrace).accounts.contains feeRecipient

def accountWithNonce (nonce : Nat) : AccountView :=
  { present := true, balance := 1, nonce := nonce, storedCode := [],
    resolvedCode := [], delegationTarget := none, empty := false,
    creationEligible := false }

/-- `nonzeroNonceProjection`: nonzero magnitudes project equally; zero versus nonzero does not. -/
def nonzeroNonceProjection : Bool :=
  (accountProjection (accountWithNonce 3) == accountProjection (accountWithNonce 8),
   accountProjection (accountWithNonce 0) == accountProjection (accountWithNonce 8)) == (true, false)
#guard nonzeroNonceProjection

end FootprintCheck

/-! ## Task 9: admissibility and resource controls -/

namespace AdmissibilityCheck

open DriverCheck

def plainValuation (balance nonce gas : Nat) : ResourceValuation :=
  { toyResource with balance := fun _ => balance, nonce := fun _ => nonce, gasRemaining := gas }

def callEvent (actions : List ResourceAction) : Observation :=
  .engine { toyObservation with instruction := "CALL", resources := actions }

-- `insufficientCallFunds`: an attempted value transfer exceeds the sender's balance.
theorem insufficientCallFunds :
    ¬ ActionsFunded [.transfer 1 2 (EvmYul.UInt256.ofNat 50)] (plainValuation 10 1 100) := by
  intro h
  have := h.1 1 2 (EvmYul.UInt256.ofNat 50) (by simp)
  exact absurd this (by decide)

-- `insufficientChildGas`: a child cap plus the caller's continuation exceeds available gas.
theorem insufficientChildGas :
    ¬ DemandMet { toyDemand with minimumGas := 30, childGasReserve := 80 } (plainValuation 100 1 100) := by
  intro h; have := h.1; simp [plainValuation, toyResource] at this

-- `nonceExhaustion`: a CREATE2 nonce increment at the EIP-2681 limit.
theorem nonceExhaustion :
    ¬ ActionsFunded [.incrementNonce 1] (plainValuation 100 nonceLimit 100) := by
  intro h
  have := h.2 1 (by simp)
  simp [plainValuation] at this

-- `feeRecipientClassification`: a fee credit makes an empty recipient nonzero only in replay.
def feeRecipientWorld : ToyWorld := initialToyWorld
def emptyAccountToy : EvmModel := { Toy with accountView := fun _ _ => { toyAccount with balance := 0 } }
theorem feeRecipientClassification :
    ¬ AccountCompatible emptyAccountToy [1]
      ({
        world := feeRecipientWorld, environment := (), frames := [], roles := [],
        protocol := toyContext, driverIndex := 0, phase := .inTransaction, attempted := [], scopes := [],
        liveLogs := [], checkpoints := [], pendingOutcome := none, probe := none } :
        ExecutionState emptyAccountToy) (plainValuation 5 1 0) := by
  intro h
  have := h 1 (by simp)
  simp [resourceClassification, plainValuation, emptyAccountToy, toyAccount] at this

-- Positive control: differing funded balances and nonzero nonces keep the classification.
theorem differingBalancesCompatible :
    AccountCompatible Toy [1] toyState (plainValuation 250 7 0) := by
  intro address _
  simp [resourceClassification, plainValuation, Toy, toyAccount]

-- `forbiddenRevertedOpcode`: CREATE in a frame whose effects revert is still forbidden.
def revertedCreateTrace : Trace :=
  [.engine { toyObservation with frame := 2, instruction := "CREATE" },
   .engine { toyObservation with frame := 2, instruction := "REVERT" }]
theorem forbiddenRevertedOpcode : ¬ TraceAllowed params revertedCreateTrace := by
  intro h
  have := (h.1 { toyObservation with frame := 2, instruction := "CREATE" }
    (by simp [engineEvents, revertedCreateTrace])).1
  simp [bannedInstructions] at this

-- GAS must be consumed by the immediately following call in its frame.
theorem gasNotForwarded :
    ¬ GasForwardingOnly [{ toyObservation with instruction := "GAS" },
      { toyObservation with instruction := "ADD" }] := by
  intro h
  obtain ⟨next, hNext, -, hCall⟩ := h 0 _ rfl rfl
  simp at hNext; subst hNext; simp [gasForwardingCalls] at hCall

-- `interleavedDriver`: a gap in block positions admits an unrelated transaction.
def interleavedConfig : Configuration DriverToy :=
  { config with envelopes := [envelope, { envelope with blockPosition := 2 }] }
theorem interleavedDriver : ¬ DriverAllowed DriverToy params interleavedConfig := by
  intro h
  have := h.2.2 1 _ rfl
  simp [interleavedConfig, envelope] at this

theorem creationTransactionExcluded :
    ¬ DriverAllowed DriverToy params
      { config with envelopes := [{ envelope with kind := .contractCreation, destination := none }] } := by
  intro h; have := (h.2.1 { envelope with kind := .contractCreation, destination := none } (by simp)).1
  simp at this

theorem authorizationTransactionExcluded :
    ¬ DriverAllowed DriverToy params
      { config with envelopes := [{ envelope with kind := .authorization }] } := by
  intro h; have := (h.2.1 { envelope with kind := .authorization } (by simp)).1; simp at this

-- A read-after-write slot is in the footprint, so a differing prestate value breaks `Related`.
def slot : StorageLocation := { chain := EvmYul.UInt256.ofNat 2, owner := 4, slot := EvmYul.UInt256.ofNat 9 }
def slotToy (value : Nat) : EvmModel :=
  { Toy with storageValue := fun _ loc => if loc == slot then EvmYul.UInt256.ofNat value else EvmYul.UInt256.ofNat 0 }
theorem readAfterWriteMismatch :
    ¬ ∀ location ∈ ({ storageReads := [slot] } : Footprint).storageReads,
      ¬ (slotToy 1).protocolOwned location →
      (slotToy 1).storageValue initialToyWorld location = (slotToy 2).storageValue initialToyWorld location := by
  intro h
  have := h slot (by simp) (by simp [slotToy, Toy, slot, toyProtocolLocation])
  have h2 := congrArg EvmYul.UInt256.toNat this
  revert h2; decide

-- A changed zero/nonzero nonce classification breaks the account projection relation.
#guard accountProjection { toyAccount with nonce := 0 } != accountProjection { toyAccount with nonce := 4 }

/-! ### Positive admissibility witness -/

/-- The replay is later and uses a re-signed envelope with different gas, price, and position. -/
def replayEnvelope : DriverEnvelope := { envelope with gasLimit := 40, gasPrice := 2, blockPosition := 3 }
def replayConfig : Configuration DriverToy := { config with height := 15, envelopes := [replayEnvelope] }

theorem referenceAttempted : (recordFinal config record).attempted =
    protocolTrace beginEvents ++ [.engine exitObservation] ++ protocolTrace endEvents ++
      protocolTrace validateEvents := rfl

theorem referenceEngineEvents : engineEvents (recordFinal config record).attempted = [exitObservation] := by
  rw [referenceAttempted]; rfl

theorem toyTraceAllowed : TraceAllowed params (recordFinal config record).attempted := by
  unfold TraceAllowed; rw [referenceEngineEvents]
  refine ⟨?_, ?_⟩
  · intro event h
    simp at h; subst h
    refine ⟨by decide, by decide, ?_⟩
    intro operation h; simp [exitObservation, toyObservation] at h
  · intro i event h hGas
    match i, h with
    | 0, h => simp at h; subst h; simp [exitObservation, gasInstruction] at hGas

theorem toyNoProtocolAccess :
    NoProtocolCoordinateAccess DriverToy (recordFinal config record).attempted := by
  rw [NoProtocolCoordinateAccess, referenceEngineEvents]
  intro event h access hAccess
  simp at h; subst h; simp [exitObservation, toyObservation] at hAccess

theorem toyDriverAllowed : DriverAllowed DriverToy params config := by
  refine ⟨by simp [config], ?_, ?_⟩
  · intro e h; simp [config] at h; subst h; exact ⟨rfl, rfl⟩
  · intro i e h
    match i, h with
    | 0, h => simp [config] at h; subst h; rfl

theorem toyReplayDriverAllowed : DriverAllowed DriverToy params replayConfig := by
  refine ⟨by simp [replayConfig], ?_, ?_⟩
  · intro e h; simp [replayConfig] at h; subst h; exact ⟨rfl, rfl⟩
  · intro i e h
    match i, h with
    | 0, h => simp [replayConfig] at h; subst h; rfl

theorem toySameInputs : SameLogicalInputs config replayConfig :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem toyProtocolRelated : ProtocolRelated 10 15 initialProtocol initialProtocol := by
  refine ⟨fun hash => ?_, fun hash => ?_, fun _ => rfl, rfl, fun _ h => by simp [initialProtocol] at h,
    rfl, rfl, rfl, rfl⟩
  · simp [bucketView, bucketFor, initialProtocol]
  · simp [lookupView, initialProtocol]

theorem toySetupCompatible : SetupCompatible DriverToy params config replayConfig :=
  ⟨toyProtocolRelated, trivial⟩

theorem referenceStatesList : referenceStates config record =
    [state0, state1, state2, state3, state4, state5, state6, state7, state8, state9, state10] := rfl

theorem toyHeightBounds : HeightBounds DriverToy config record replayConfig := by
  refine ⟨by decide, by decide, ?_⟩
  rw [referenceStatesList]
  intro state h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem toyNoGasInducedFailure : NoGasInducedFailure config record := by
  rw [NoGasInducedFailure, referenceStatesList]
  intro state h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨by simp [state10, state9, state8, state7, state6, state5, state4, state3, state2, state1,
      state0, initialState], by simp [state10, state9, state8, state7, state6, state5, state4, state3,
      state2, state1, state0, initialState]⟩

theorem toyInitialRelated :
    InitialRelated DriverToy params (replayFootprint DriverToy config record replayConfig)
      config replayConfig := by
  unfold InitialRelated Related
  refine ⟨rfl, rfl, rfl, rfl, ⟨rfl, by simp [initialState]⟩,
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, toyProtocolRelated⟩, ⟨rfl, trivial, trivial, trivial⟩, rfl,
    by simp [initialState], by simp [initialState], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Toy balances are 100 and nonces 1; inside the transaction at least one gas unit remains. -/
def toyPlan : ResourcePlan := fun i v =>
  (∀ a, v.balance a = 100) ∧ (∀ a, v.nonce a = 1) ∧ (1 ≤ i → i ≤ 9 → 1 ≤ v.gasRemaining)

theorem noActionUpdate {M : EvmModel} {replay : Configuration M} {pre post : ExecutionState M}
    {v v' : ResourceValuation} (h : StepResourceUpdate M replay pre post v [] v') :
    v' = stepBaseValuation M replay pre post v := by
  cases h; rfl

set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
/-- The same plan serves the reference itself and the later replay. -/
theorem toyBudget (target : Configuration DriverToy) (hTarget : target = config ∨ target = replayConfig) :
    BudgetOK DriverToy params config record target toyPlan := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl, by omega⟩,
    by rcases hTarget with rfl | rfl <;> simp [BlockCapacityOK, replayConfig, replayEnvelope, envelope, config], ?_⟩
  intro i pre obs post h v hv
  obtain ⟨hb, hn, hg⟩ := hv
  rcases Nat.lt_or_ge i 10 with hi | hi
  · rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    rotate_left 10
    · omega
    all_goals
      simp only [referenceStep, referenceStatesList, record, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨⟨?_, ?_, ?_⟩, fun actions hActions v' hv' => ?_⟩
      · rcases hTarget with rfl | rfl <;>
          simp [EnvelopeFunded, state0, state1, state2, state3, state4, state5, state6, state7,
            state8, state9, initialState, config, replayConfig, replayEnvelope, envelope, DriverToy,
            Toy, hb, hn] <;> decide
      · simp [DemandMet, state0, state1, state2, state3, state4, state5, state6, state7, state8,
          state9, initialState, toyDemand, DriverToy, Toy] <;> exact hg (by omega) (by omega)
      · intro actions hActions; rw [show actions = [] from hActions]; simp [ActionsFunded]
      · rw [show actions = [] from hActions] at hv'
        obtain rfl := noActionUpdate hv'
        rcases hTarget with rfl | rfl <;>
          simp [toyPlan, AccountCompatible, resourceClassification, stepBaseValuation, state0,
            state1, state2, state3, state4, state5, state6, state7, state8, state9, state10,
            initialState, config, replayConfig, replayEnvelope, envelope, DriverToy, Toy, toyAccount,
            hb, hn] <;> exact hg (by omega) (by omega)
  · have : record.transitions[i]? = none := List.getElem?_eq_none (by simp [record]; omega)
    simp [referenceStep, this] at h

theorem toyNoUnmodeledEntry : NoUnmodeledManagerEntry config record := by
  rw [NoUnmodeledManagerEntry, referenceStatesList]
  intro state h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> exact fun h => by cases h

theorem toyAllowedReplay : AllowedReplay DriverToy params config record replayConfig :=
  ⟨by simp [RevisionDescriptor.isPinned, params, toyParams], toyDriverAllowed, toyReplayDriverAllowed, toySameInputs, toyTraceAllowed,
    toyNoProtocolAccess, toyInitialRelated, toySetupCompatible, toyHeightBounds,
    toyNoGasInducedFailure, toyNoUnmodeledEntry, ⟨toyPlan, toyBudget config (.inl rfl)⟩, toyPlan,
    toyBudget replayConfig (.inr rfl)⟩

/-- `admissibleToyReplay`: the positive fixture is valid at X and admissible at X + 5. -/
theorem admissibleToyReplay :
    ValidAtX DriverToy params config record ∧
    configurationHeight replayConfig = configurationHeight config + 5 ∧
    AllowedReplay DriverToy params config record replayConfig :=
  ⟨committedToyDriverValid, rfl, toyAllowedReplay⟩

end AdmissibilityCheck
