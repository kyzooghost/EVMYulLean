import EvmYul.CrossChainReplay.Statements
import EvmYul.CrossChainReplay.Checks.Laws
import EvmYul.CrossChainReplay.Checks.Admissibility

/-! Task 10 checks: every named statement elaborates, and the full target's premises are
jointly satisfiable for the toy driver adapter. These are elaboration and non-vacuity checks;
no statement is proved. -/

open EvmYul.CrossChainReplay DriverCheck AdmissibilityCheck

#check @HashPreservationStatement
#check @SetupPreservationStatement
#check @FreshnessPreservationStatement
#check @QueueCorrespondenceStatement
#check @ProtocolInterfaceStatement
#check @LocalProgressStatement
#check @LocalPreservationStatement
#check @ResourceAdequacyStatement
#check @RollbackPreservationStatement
#check @TransportProvenanceStatement
#check @ValidationPreservationStatement
#check @CommitmentStatement
#check @ReplayConclusion
#check @ReplayPreservationStatement
#check @ReplayCompositionStatement

theorem driverToyLaws : SemanticInterfaceLaws DriverToy params := by
  refine ⟨toyProtocolViewLaws, ?_, ?_, toyRollbackLaws, ?_, toyResourceArithmeticLaws⟩
  · obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := toyDeterminismLaws
    refine ⟨?_, ?_, h3, h4, h5, h6, h7⟩
    · rintro w f env act w₁ f₁ o₁ w₂ f₂ o₂ ⟨-, rfl, rfl, rfl⟩ ⟨-, rfl, rfl, rfl⟩; simp
    · rintro w f env a₁ a₂ w₁ f₁ o₁ w₂ f₂ o₂ ⟨rfl, -⟩ ⟨rfl, -⟩; rfl
  · obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := toyProgressLaws
    refine ⟨?_, h2, h3, h4, h5, h6, h7, h8⟩
    intro w f env
    exact ⟨.frameExit (.returned rowResult), w, f, exitObservation, rfl, rfl, rfl, rfl⟩
  · obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := toyObservationLaws
    refine ⟨?_, ?_, ?_, ?_, ?_, h6, h7, h8⟩
    · rintro w f env action w' f' obs ⟨-, -, -, rfl⟩ source target amount h
      simp [exitObservation, toyObservation] at h
    · rintro w f env action w' f' obs ⟨-, -, -, rfl⟩ access h
      simp [exitObservation, toyObservation] at h
    · rintro w f env action w' f' obs - loc h; simp [DriverToy, Toy] at h
    · rintro w f env action w' f' obs - address h; simp [DriverToy, Toy] at h
    · rintro w f env action w' f' obs ⟨-, -, -, rfl⟩ envelope; rfl

/-- `fullTargetPremisesSatisfiable`: one adapter, reference, delay, and replay satisfy every
    premise of `ReplayPreservationStatement`, so its hypotheses are not contradictory. -/
theorem fullTargetPremisesSatisfiable :
    SemanticInterfaceLaws DriverToy params ∧ ValidAtX DriverToy params config record ∧
    configurationHeight replayConfig = configurationHeight config + 5 ∧
    AllowedReplay DriverToy params config record replayConfig :=
  ⟨driverToyLaws, admissibleToyReplay⟩

/-! ### The conclusion is attainable for the toy instance

Each step's target state is determined by its constructor; the replay differs from the
reference in height, freshness stamps, and envelope resources only. -/

/-- Boolean form of `PrescribedChecksPassed`, for closed traces. -/
def checksPassedB (trace : Trace) : Bool :=
  trace.all fun
    | .protocol (.check _ _ passed) => passed
    | .protocol (.failure _ _) => false
    | _ => true

theorem checksPassedB_sound (trace : Trace) (h : checksPassedB trace = true) :
    PrescribedChecksPassed trace := by
  intro event hEvent
  have := List.all_eq_true.mp h event hEvent
  rcases event with event | event
  · trivial
  · cases event <;> simp_all

/-- Boolean form of `SelectedOccurrenceConsumed`, for closed protocol states. -/
def consumedB (state : ProtocolState) (id : EntryId) : Bool :=
  state.buckets.all fun bucket => bucket.rows.all fun row => !(decide (row.id = id)) || row.consumed

theorem consumedB_sound (M : EvmModel) (config : Configuration M) (record : ExecutionRecord M)
    (h : consumedB (M.readProtocol (recordFinal config record).world) config.selected = true) :
    SelectedOccurrenceConsumed M config record := by
  intro bucket hBucket row hRow hId
  have := List.all_eq_true.mp (List.all_eq_true.mp h bucket hBucket) row hRow
  simp_all

/-- Close the premises of an applied constructor, in order. -/
local macro "close_premises" : tactic => `(tactic| all_goals first
    | rfl | decide | exact ⟨_, rfl⟩ | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩
    | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Close one composed step. A constructor is kept only if all of its premises close, so the
    choice is forced by the concrete state; earlier premises assign the states later ones read. -/
local macro "driver_step" : tactic => `(tactic| first
    | (apply Step.beginTransaction; close_premises)
    | (apply Step.settleTransaction; close_premises)
    | (apply Step.dispatchIncoming; close_premises)
    | (apply Step.engineExit; close_premises)
    | (apply Step.resumeIncoming; close_premises)
    | (apply Step.protocolReturned; close_premises)
    | (apply Step.protocolLocal; close_premises))

set_option maxRecDepth 100000 in
/-- `replayConclusionWitness`: the toy replay at height 15 satisfies `ReplayConclusion`. -/
theorem replayConclusionWitness :
    ∃ replayRun, ReplayConclusion DriverToy params config record replayConfig replayRun := by
  refine ⟨⟨_, _⟩, ⟨StepChain.cons (M := DriverToy) (p := params) _ _ _ _ _ (by driver_step) <|
    .cons _ _ _ _ _ (by driver_step) <| .cons _ _ _ _ _ (by driver_step) <|
    .cons _ _ _ _ _ (by driver_step) <| .cons _ _ _ _ _ (by driver_step) <|
    .cons _ _ _ _ _ (by driver_step) <| .cons _ _ _ _ _ (by driver_step) <|
    .cons _ _ _ _ _ (by driver_step) <| .cons _ _ _ _ _ (by driver_step) <|
    .cons _ _ _ _ _ (by driver_step) <| .nil _, by rfl, by dsimp only [recordFinal]⟩, ?_⟩
  refine ⟨committedResult, _, rfl, rfl, checksPassedB_sound _ rfl,
    consumedB_sound _ _ _ rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Regression for the queue-correspondence load formula -/

def staleOnlyState : ProtocolState :=
  { buckets := [{
      hash := zeroHash, head := 0,
      rows := [{ id := .preloaded 0, row := entry, loadedBlock := 3, consumed := false }] }] }

/-- A load without entries for a hash leaves that hash's stale bucket unchanged; the formula's
    reset case applies only to hashes present in the batch. -/
def untouchedStaleBucket : Bool :=
  let context : LoadContext :=
    { height := 10, loadIndex := 7, route := .proxy, caller := systemAddress,
      attachedValue := EvmYul.UInt256.ofNat 0 }
  match loadBatch params context { entries := [], lookups := [] } staleOnlyState with
  | .ok result =>
      bucketView 10 result.state zeroHash == bucketView 10 staleOnlyState zeroHash &&
      (bucketView 10 staleOnlyState zeroHash).length == 1
  | .error _ => false
#guard untouchedStaleBucket
