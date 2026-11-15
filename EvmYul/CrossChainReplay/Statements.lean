import EvmYul.CrossChainReplay.Admissibility

/-!
Named, unproved replay statements for manual review (plan Task 10). Every declaration is a
`def ... : Prop`. Nothing here is assumed or proved. Local statements quantify over one step,
checkpoint, or protocol operation; only the final targets quantify over complete runs.
-/

namespace EvmYul.CrossChainReplay

/-! ## Helpers -/

/-- Resource valuation of a composed state: the top frame's view, or account balances and
    nonces between transactions. -/
def stateValuation (M : EvmModel) (s : ExecutionState M) : ResourceValuation :=
  match s.frames with
  | frame :: _ => M.resourceView s.world frame
  | [] => initialValuation M s.world

/-- Functional content of an observation: resource actions and metering reads removed. -/
def functionalObservation : Observation → Observation
  | .engine event => .engine {
      event with
      resources := [], accesses := event.accesses.filter (·.kind != .meteringRead) }
  | other => other

def ObservationsCorrespond (x y : List Observation) : Prop :=
  x.map functionalObservation = y.map functionalObservation

/-- Two protocol actions take the same branch with related states and equal emitted data. -/
def ActionRelated (hx hy : Nat) : ProtocolAction → ProtocolAction → Prop
  | .noAction, .noAction => True
  | .local a c e, .local b d f
  | .dispatchSpan a c _ e, .dispatchSpan b d _ f
  | .dispatchSystem a c _ e, .dispatchSystem b d _ f =>
      ProtocolRelated hx hy a b ∧ ContextRelated hx hy c d ∧ e = f
  | .spanResult a c r e, .spanResult b d s f
  | .adoptSpan a c r e, .adoptSpan b d s f =>
      ProtocolRelated hx hy a b ∧ ContextRelated hx hy c d ∧ r = s ∧ e = f
  | .dispatchIncoming a c r e, .dispatchIncoming b d s f
  | .dispatchStatic a c r e, .dispatchStatic b d s f =>
      ProtocolRelated hx hy a b ∧ ContextRelated hx hy c d ∧ r = s ∧ e = f
  | .returned a c x e, .returned b d y f
  | .revertedBytes a c x e, .revertedBytes b d y f
  | .returnedRaw a c x e, .returnedRaw b d y f =>
      ProtocolRelated hx hy a b ∧ ContextRelated hx hy c d ∧ x = y ∧ e = f
  | .failed a c x e, .failed b d y f =>
      ProtocolRelated hx hy a b ∧ ContextRelated hx hy c d ∧ x = y ∧ e = f
  | .staticWriteViolation c e, .staticWriteViolation d f => ContextRelated hx hy c d ∧ e = f
  | _, _ => False

/-- The selected occurrence is consumed or drained in the final protocol state. -/
def SelectedOccurrenceConsumed (M : EvmModel) (config : Configuration M)
    (record : ExecutionRecord M) : Prop :=
  ∀ bucket ∈ (M.readProtocol (recordFinal config record).world).buckets,
    ∀ row ∈ bucket.rows, row.id = config.selected → row.consumed = true

def scopedTranscripts (scopes : List ScopeRecord) : List (ScopeId × List BoundaryRecord) :=
  scopes.map fun scope => (scope.id, scope.effective)

def structuralTrace (scopes : List ScopeRecord) :
    List (ScopeId × List StructuralEvent × List (Bool × Bytes)) :=
  scopes.map fun scope => (scope.id, scope.structural, scope.staticOutcomes)

/-- Controls at which the active scope is a non-static entry or reverted-lookup scope and its
    fold is in the protocol accumulator. Static lookups fold into local variables instead, and
    their scope can stay active through `.finished` and nested `.invoke`. -/
def accumulatorControl : ProtocolControl → Bool
  | .processIncoming .. | .readyIncoming .. | .resumeIncoming .. | .consumeOutgoing ..
  | .validate .. | .validateLookup .. => true
  | _ => false

/-- The protocol accumulator of an active, non-static scope folds its effective transcript. -/
def AccumulatorMatchesScope (M : EvmModel) (p : Parameters) (s : ExecutionState M) : Prop :=
  ∀ scope record, s.protocol.activeScope = some scope → record ∈ s.scopes → record.id = scope →
    accumulatorControl s.protocol.control = true →
    (M.readProtocol s.world).crossChainHash = crossHash p.keccak record.effective

/-! ## Encoding and protocol targets -/

/-- Spec section 4.2: folds compose over append, so nested transcripts determine the hash.
    Equal transcripts give equal hashes by determinism alone; no injectivity is used. -/
def HashPreservationStatement (p : Parameters) : Prop :=
  ∀ x y : List BoundaryRecord,
    crossHash p.keccak (x ++ y) = y.foldl (foldBoundary p.keccak) (crossHash p.keccak x)

/-- Spec section 8.2: loading the same batch into related queues at different heights gives
    related queues and the same new occurrences, or the same error. -/
def SetupPreservationStatement (p : Parameters) : Prop :=
  ∀ hx hy x y (batch : LoadBatch) (context : LoadContext), ProtocolRelated hx hy x y →
    match loadBatch p { context with height := hx } batch x,
        loadBatch p { context with height := hy } batch y with
    | .ok a, .ok b => ProtocolRelated hx hy a.state b.state ∧ a.newlyLoaded = b.newlyLoaded
    | .error e, .error f => e = f
    | _, _ => False

/-- Spec section 4.5 law 7: changing the height and every current stamp together preserves
    each protocol decision. Only stamp bytes may differ. -/
def FreshnessPreservationStatement (p : Parameters) : Prop :=
  ∀ hx hy (cx cy : ProtocolContext) x y, cx.height = hx → cy.height = hy →
    ContextRelated hx hy cx cy → ProtocolRelated hx hy x y →
    ActionRelated hx hy (advanceProtocol p cx x cx.control) (advanceProtocol p cy y cy.control)

/-- Spec sections 3.3 and 4.4: logical occurrences survive loading, selection, and cleanup. -/
def QueueCorrespondenceStatement (p : Parameters) : Prop :=
  (∀ (context : LoadContext) batch state result,
    loadBatch p context batch state = .ok result → ∀ hash,
      bucketView context.height result.state hash =
        (if (bucketView context.height state hash).any (·.2.2 == .current) ||
            !batch.entries.any (·.proxyEntryHash == hash)
          then bucketView context.height state hash else []) ++
        ((batch.entries.zipIdx.filter (·.1.proxyEntryHash == hash)).map fun (entry, i) =>
          (EntryId.driverLoaded context.loadIndex i, some entry, Freshness.current))) ∧
  (∀ height hash peer state id selected,
    selectProxyEntry p height hash peer state = .ok (id, selected) →
    ∃ before row after, bucketView height state hash = before ++ (id, some row, .current) :: after ∧
      (∀ earlier ∈ before, earlier.2.2 ≠ .current) ∧
      bucketView height selected hash = after ∧ selected.activeEntry = some id) ∧
  (∀ height hash index state bucket row,
    bucketFor hash state = some bucket → bucket.rows[index]? = some row →
    ∀ entry ∈ bucketView height (clearConsumed height hash index state) hash,
      entry.1 = row.id → entry.2.2 = .consumed)

/-- Spec section 4.5 law 1. -/
def LoaderLaw (p : Parameters) : Prop :=
  (∀ context batch state, hasDuplicateLookupHash batch.lookups = true →
    (∃ error, loadBatch p context batch state = .error error)) ∧
  (∀ context batch state result, loadBatch p context batch state = .ok result →
    ∀ lookup ∈ batch.lookups, lookupView context.height result.state lookup.crossChainCallHash =
      some (.topLevelLookup context.loadIndex lookup.crossChainCallHash, lookup, .current))

/-- Spec section 4.5 law 2: inbound selection binds the request, row zero, and entry hash. -/
def SelectionLaw (p : Parameters) : Prop :=
  ∀ hash (context : LoadContext) batch state loaded id selected,
    loadBatch p context batch state = .ok loaded →
    (∀ bucket ∈ state.buckets, ∀ row ∈ bucket.rows, ∀ i, row.id ≠ .driverLoaded context.loadIndex i) →
    selectInboundEntry p hash loaded = .ok (id, selected) →
    loaded.newlyLoaded.head? = some id ∧ selected.activeEntry = some id ∧
    (∃ entry ∈ loaded.batch.entries.head?, entry.proxyEntryHash = hash) ∧
    ∀ bucket ∈ selected.buckets, ∀ row ∈ bucket.rows, row.id = id → row.consumed = true

/-- Spec section 4.5 law 3: one outer iteration dispatches the row at the shared cursor. -/
def DispatchLaw (p : Parameters) : Prop :=
  ∀ context state scope count processed destination,
    context.control = .processIncoming scope count processed destination → processed < count →
    match advanceProtocol p context state context.control with
    | .dispatchIncoming next _ _ events =>
        next.incomingCursor = state.incomingCursor + 1 ∧
        events = [.structural scope (.callBegin (state.incomingCursor + 1))]
    | .dispatchSpan .. | .failed .. => True
    | _ => False

/-- Spec section 4.5 law 4: first match in array order; the non-static path needs `failed`. -/
def LookupLaw : Prop :=
  ∀ staticMode key rows index row, findNestedLookup staticMode key rows = some (index, row) →
    rows[index]? = some row ∧
    row.crossChainCallHash = key.callHash ∧ row.callNumber = key.callNumber ∧
    row.lastOutgoingCallConsumed = key.outgoingCursor ∧
    row.executingLookupIndex = key.contextIndex ∧ (staticMode = true ∨ row.failed = true) ∧
    ∀ j earlier, j < index → rows[j]? = some earlier →
      ¬ (earlier.crossChainCallHash = key.callHash ∧ earlier.callNumber = key.callNumber ∧
        earlier.lastOutgoingCallConsumed = key.outgoingCursor ∧
        earlier.executingLookupIndex = key.contextIndex ∧ (staticMode = true ∨ earlier.failed = true))

/-- Spec section 4.5 law 5. -/
def GuardLaw : Prop :=
  ∀ peer allowRoot calls, checkCalls peer allowRoot calls = .ok () →
    ∀ i call, calls[i]? = some call →
      call.sourceRollupId = peer ∧
      (call.isStatic = true → call.value.toNat = 0 ∧ call.revertSpan.toNat = 0) ∧
      (call.isStatic = false → (allowRoot = false ∨ i ≠ 0) → call.value.toNat = 0)

/-- Spec section 4.5 law 6: transport decoding checks only the selector and minimum length. -/
def RollbackTransportLaw (p : Parameters) : Prop :=
  ∀ data, (∃ result, decodeContextResult p.keccak data = .ok result) ↔
    (data.take 4 = selector p.keccak contextResultSignature ∧ 164 ≤ data.length)

/-- Spec section 4.5 law 8: validation events come only from `validate`, for the scope's
    occurrence, with that entry's expected hashes. -/
def ObservationLaw (p : Parameters) : Prop :=
  ∀ context state control,
    let events := match advanceProtocol p context state control with
      | .local _ _ e | .dispatchSpan _ _ _ e | .spanResult _ _ _ e | .adoptSpan _ _ _ e
      | .dispatchSystem _ _ _ e | .dispatchIncoming _ _ _ e | .dispatchStatic _ _ _ e
      | .returned _ _ _ e | .failed _ _ _ e | .revertedBytes _ _ _ e | .returnedRaw _ _ _ e
      | .staticWriteViolation _ e => e
      | .noAction => []
    ∀ result, .validation result ∈ events →
      ∃ scope index entry, control = .validate scope ∧
        activeEntryRow state scope.entry = some (index, entry) ∧
        result.selected = scope.entry ∧ result.entryHash = entry.proxyEntryHash ∧
        result.structuralHash = entry.rollingHash ∧
        result.crossChainHash = entry.crossChainRollingHash

/-- Spec section 4.5: the concrete protocol's eight local laws, as proof targets. -/
def ProtocolInterfaceStatement (p : Parameters) : Prop :=
  LoaderLaw p ∧ SelectionLaw p ∧ QueueCorrespondenceStatement p ∧ DispatchLaw p ∧ LookupLaw ∧
  GuardLaw ∧ RollbackTransportLaw p ∧ FreshnessPreservationStatement p ∧ ObservationLaw p

/-- Instantiation obligation, not a replay premise: the manager decoder inverts the proxy's
    forwarding encoding. Both runs use the same decoder. -/
def ManagerDecoderCorrespondence (p : Parameters) : Prop :=
  ∀ staticMode source data,
    p.decodeManagerEntry (encodeManagerInvoke p.keccak staticMode source data) =
      some (if staticMode then .staticLookup source data else .executeCrossChain source data)

/-! ## Local execution targets (one reference step) -/

/-- Common premises of a local claim at reference step `i`. -/
def LocalPremises (M : EvmModel) (p : Parameters) (reference : Configuration M)
    (referenceRun : ExecutionRecord M) (replay : Configuration M) (plan : ResourcePlan)
    (i : Nat) (pre : ExecutionState M) (obs : List Observation) (post : ExecutionState M)
    (y : ExecutionState M) : Prop :=
  ValidAtX M p reference referenceRun ∧ AllowedReplay M p reference referenceRun replay ∧
  BudgetOK M p reference referenceRun replay plan ∧
  referenceStep reference referenceRun i = some (pre, obs, post) ∧
  Related M p (replayFootprint M reference referenceRun replay) pre y ∧
  plan i (stateValuation M y)

/-- Spec sections 8.3 and 9: a related replay state can take a step. Without this, a
    preservation claim alone cannot establish replay existence. -/
def LocalProgressStatement (M : EvmModel) (p : Parameters) : Prop :=
  ∀ reference referenceRun replay plan i pre obs post y,
    LocalPremises M p reference referenceRun replay plan i pre obs post y →
    ∃ obs' y', Step M p y obs' y'

/-- Spec section 8.3: every replay step from a related state corresponds to the reference
    step, re-establishes `Related`, and stays in the next resource envelope. -/
def LocalPreservationStatement (M : EvmModel) (p : Parameters) : Prop :=
  ∀ reference referenceRun replay plan i pre obs post y obs' y',
    LocalPremises M p reference referenceRun replay plan i pre obs post y →
    Step M p y obs' y' →
    ObservationsCorrespond obs obs' ∧
    Related M p (replayFootprint M reference referenceRun replay) post y' ∧
    plan (i + 1) (stateValuation M y')

/-- Spec section 8.4: the resource plan rules out gas-induced inner failures in replay. -/
def ResourceAdequacyStatement (M : EvmModel) (p : Parameters) : Prop :=
  ∀ reference referenceRun replay plan i pre obs post y obs' y',
    LocalPremises M p reference referenceRun replay plan i pre obs post y →
    Step M p y obs' y' →
    y'.pendingOutcome ≠ some (.exceptional .outOfGas) ∧
    ∀ probe, y'.probe = some probe → probe.outcome ≠ .exceptional .outOfGas

/-- Spec section 8.5: restoring related checkpoints yields related states. -/
def RollbackPreservationStatement (M : EvmModel) (p : Parameters) : Prop :=
  ∀ footprint (x y : ExecutionState M) cx cy, Related M p footprint x y →
    CheckpointRelated M footprint x.protocol.height y.protocol.height x.environment y.environment cx cy →
    Related M p footprint (restore M cx x) (restore M cy y)

/-- Spec sections 4.2.3 and 8.5: decoding inverts the span executor's encoding, and on every
    reachable state the accumulator folds the active scope's effective transcript. -/
def TransportProvenanceStatement (M : EvmModel) (p : Parameters) : Prop :=
  (∀ result, decodeContextResult p.keccak (encodeContextResult p.keccak result) = .ok result) ∧
  ∀ config transitions s, StepChain M p (initialState config) transitions s →
    AccumulatorMatchesScope M p s

/-- Spec section 8.6: at a validation step, related states emit the same checks and result. -/
def ValidationPreservationStatement (M : EvmModel) (p : Parameters) : Prop :=
  ∀ footprint (x y : ExecutionState M) scope, Related M p footprint x y →
    x.protocol.control = .validate scope →
    ActionRelated x.protocol.height y.protocol.height
      (advanceProtocol p x.protocol (M.readProtocol x.world) x.protocol.control)
      (advanceProtocol p y.protocol (M.readProtocol y.world) y.protocol.control)

/-- Spec section 8.7: related terminal states derive corresponding outcomes. -/
def CommitmentStatement (M : EvmModel) (p : Parameters) : Prop :=
  ∀ footprint (reference replay : Configuration M) (x y : ExecutionState M),
    SameLogicalInputs reference replay → Related M p footprint x y → x.phase = .done →
    match deriveOutcome reference x, deriveOutcome replay y with
    | .success a, .success b =>
        a.validation = b.validation ∧ a.returnedBytes = b.returnedBytes ∧
        a.scopes = b.scopes ∧ a.completedScopes = b.completedScopes
    | .failure _, .failure _ => True
    | _, _ => False

/-! ## Final targets -/

/-- Spec section 7: the replay conclusion for one reference record and one replay record. -/
def ReplayConclusion (M : EvmModel) (p : Parameters) (reference : Configuration M)
    (referenceRun : ExecutionRecord M) (replay : Configuration M)
    (replayRun : ExecutionRecord M) : Prop :=
  Run M p replay replayRun ∧
  ∃ x y, referenceRun.outcome = .success x ∧ replayRun.outcome = .success y ∧
    PrescribedChecksPassed y.attempted ∧
    SelectedOccurrenceConsumed M replay replayRun ∧
    scopedTranscripts y.scopes = scopedTranscripts x.scopes ∧
    y.completedScopes = x.completedScopes ∧
    structuralTrace y.scopes = structuralTrace x.scopes ∧
    y.validation.crossChainHash = x.validation.crossChainHash ∧
    y.validation.crossChainHash = reference.selectedEntry.crossChainRollingHash ∧
    y.returnedBytes = x.returnedBytes

/-- The full target: the fixed adapter's local laws, reference validity, the height relation,
    and admissibility imply a successful replay with the reference results. The concrete
    protocol's local laws are obligations, not premises. -/
def ReplayPreservationStatement (M : EvmModel) (p : Parameters) : Prop :=
  SemanticInterfaceLaws M p →
  ∀ (reference : Configuration M) (referenceRun : ExecutionRecord M),
    ValidAtX M p reference referenceRun →
    ∀ (delay : Nat) (replay : Configuration M),
      configurationHeight replay = configurationHeight reference + delay →
      AllowedReplay M p reference referenceRun replay →
      ∃ replayRun, ReplayConclusion M p reference referenceRun replay replayRun

/-- Conditional composition: the same conclusion from the named local targets as explicit
    hypotheses. Proving this does not prove those targets. -/
def ReplayCompositionStatement (M : EvmModel) (p : Parameters) : Prop :=
  SemanticInterfaceLaws M p →
  HashPreservationStatement p → SetupPreservationStatement p →
  ProtocolInterfaceStatement p →
  LocalProgressStatement M p → LocalPreservationStatement M p →
  ResourceAdequacyStatement M p → RollbackPreservationStatement M p →
  TransportProvenanceStatement M p → ValidationPreservationStatement M p →
  CommitmentStatement M p →
  ∀ (reference : Configuration M) (referenceRun : ExecutionRecord M),
    ValidAtX M p reference referenceRun →
    ∀ (delay : Nat) (replay : Configuration M),
      configurationHeight replay = configurationHeight reference + delay →
      AllowedReplay M p reference referenceRun replay →
      ∃ replayRun, ReplayConclusion M p reference referenceRun replay replayRun

end EvmYul.CrossChainReplay
