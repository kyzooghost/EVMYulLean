# Cross-chain replay: Lean model and review statements

Status: pressure-tested design for review, ready for implementation planning. No Lean implementation or replay proof is claimed.

## Intent and accepted approach

Translate `docs/cross-chain-rolling-hash-replay-spec.md` into Lean 4 definitions and named propositions for manual review. The first deliverable must distinguish concrete protocol definitions, external EVM semantics, and unproved obligations. It must not assume replay success to obtain hash equality.

The user selected a concrete protocol model with an explicit EVM-semantics interface. The alternative was to bind the model directly to the repository's existing interpreter. That would couple the review to interpreter coverage and the work needed for a newer revision. The selected approach keeps those integration obligations explicit while allowing the protocol and admissibility definitions to be reviewed now.

The semantic target remains a pinned Glamsterdam execution revision, with Osaka acceptable as an initial instantiation. This delivery does not instantiate either revision or claim that the current interpreter supports them.

## Deliverable boundary

Deliver compilable Lean definitions for:

- semantic bundles, logical requests, driver configurations, and occurrence identities;
- exact call-hash encoding and cross-chain and structural folds;
- protocol queues, contexts, cursors, guards, and control transitions;
- frame checkpoints, ordinary rollback, lookup isolation, and revert-span transport;
- complete observation traces, effective hash transcripts, and committed results;
- footprints, state projections, trace restrictions, and replay admissibility;
- mathematical resource plans and their local obligations;
- named propositions for the required lemmas and replay theorem;
- a review index linking declarations to specification sections and external assumptions.

Do not implement the proofs, a Besu admission checker, a new EVM interpreter, a Solidity compiler model, or deployed-bytecode correspondence. Do not change unrelated existing semantics.

Statements are `def ... : Prop := ...`, not `axiom` declarations or theorems with `sorry`. This permits type checking without asserting any statement is true. Interface laws are explicitly quantified assumptions; local preservation results awaiting proof are identified separately from definitions.

## Proposed module layout

Use namespace `EvmYul.CrossChainReplay` and modules under `EvmYul/CrossChainReplay/`:

| Module | Responsibility |
| --- | --- |
| `Types.lean` | Bounded identities, bundles, requests, driver envelopes, and logical occurrences |
| `Hashing.lean` | ABI encoding, packed encodings, and accumulator folds |
| `Observations.lean` | Instruction/access observations, call outcomes, checks, logs, and trace projections |
| `EvmInterface.lean` | Revision parameters, EVM states and projections, primitive transitions, transaction and resource operations |
| `Protocol.lean` | Concrete protocol state, queue/lookup operations, guards, and continuations |
| `Execution.lean` | Composed protocol/EVM steps, frame checkpoints, finite runs, and result extraction |
| `Admissibility.lean` | Footprints, initial/state relations, resource plans, and `AllowedReplay` |
| `Statements.lean` | Local obligations and the final replay proposition |
| `CrossChainReplay.lean` | Aggregate import for the review deliverable |

Place the aggregate at `EvmYul/CrossChainReplay.lean`. Keep dependency direction from data and observations toward execution, admissibility, and statements; avoid importing the entire existing EVM interpreter. Splitting a large module further is an implementation choice, provided the review index stays accurate.

## Representations

Reuse the repository's `AccountAddress` and `UInt256` where their meanings match. Use finite lists of bytes for mathematical byte strings and a length-indexed 32-byte vector for hashes. Keep conversions and big-endian encoding explicit. Do not rely on host endianness or numeric equality for variable-length byte strings.

Heights, positions, and mathematical iteration counts use `Nat`. Named bounds express `uint64` casts, `uint256` encodings, and checked arithmetic. On-chain words use their defined word arithmetic; natural-number counts do not silently model wrapping.

Use ordered lists for semantic rows. Arrays, maps, and cursors in the concrete protocol model must preserve multiplicity and first-match/FIFO behavior. Mathematical storage and account maps may be total functions with explicit absence and zero-read conventions. Decidability or execution efficiency is not a requirement for admissibility predicates.

Logical occurrence identities are independent of physical queue indices. A loaded entry receives an identity based on its driver load position and row position. Invocation scopes additionally identify repeated and reverted attempts. A correspondence relation maps these identities to physical buckets and indices in each run. This prevents duplicate hashes or bucket reuse from identifying distinct executions.

## Hash model

Supply a fixed function `keccak : Bytes -> Hash32` as a parameter. Implement the input encodings and folds concretely. Do not assume injectivity, collision resistance, or a default output length. Correspondence with the existing FFI or an eventual verified Keccak implementation is a separate proposition.

Implement the eight-word ABI head, offset 256, dynamic byte length and padding, address padding, and zero `uint64` gas coordinate. Implement the packed boundary fold and all structural tags separately.

Protocol transitions determine fold locations. A transcript supplied by a caller is not enough to establish that execution produced that transcript. Include the proxy root fold, omission of the extra inbound root fold, lookup final record, and raw-versus-cached return-byte distinction.

## Concrete protocol execution

Define protocol state and transition constructors rather than an arbitrary `Run` parameter. The state contains queues and heads, top-level and nested lookup tables, active peer and host, incoming and outgoing cursors, hash accumulators, and a stack of continuations.

Implement the following operations from the inspected source behavior:

1. Load records with freshness stamps, duplicate-top-level-lookup rejection, peer/value/static checks, bucket retention or replacement, and lookup overwrite.
2. Select proxy entries by FIFO or system inbound entries by the newly loaded occurrence; enforce inbound identity and value binding.
3. Process incoming rows and successful outgoing reentry with shared cursors and frame-local iteration counts.
4. Resolve nested lookups by the four-part key and array-first matching; use the pre-increment outgoing cursor for reverted fallback.
5. Run static lookups with local accumulators and reverted lookups with separate contexts and terminal revert.
6. Process revert spans using self-call checkpoints and checked transport decoding, including the L2 ignored Boolean word.
7. Check hashes and consumption, emit the validation observation, clear consumed entries, and return cached bytes.

Use small-step transitions with explicit continuations so nested calls do not require a termination proof to define the model. Array bounds and protocol failures have explicit failure transitions. If a detail of error precedence affects observable bytes, follow source order and give the error a distinct constructor; byte encoding belongs to the concrete protocol boundary.

The protocol must suspend for EVM calls, proxy creation, and value transfers. Those effects are not successful by construction. Calls can reenter the manager, return, revert, or fail. The model must retain this interaction rather than treating each application call as an atomic oracle returning a chosen transcript.

Cover the supporting proxy behavior needed by those paths: registry validation and updates, `CREATE2` deployment, manager-only raw forwarding, static-context detection, and success-byte unwrapping. In particular, the proxy's 1,000-gas self-probe is an actual nested call that attempts a transient write. Do not replace it with an infallible static-mode oracle. A6 must exclude gas-induced misclassification while allowing the expected static-write failure. Likewise, the manager's value transfer to the system address remains a call with an observable outcome.

## EVM interface and composition

The interface supplies a revision-indexed state type, current-state projections, primitive transitions, call-frame entry/exit, transaction initialization and settlement, and local resource arithmetic. It also identifies decoded instructions, explicit and implicit accesses, code resolution, native operations, and error causes. These are mathematical parameters, not a claim of correspondence with Besu.

The composed execution relation owns protocol transitions and driver sequencing. EVM transitions cannot fabricate protocol validation events or directly supply the selected hash. An authorized entry boundary transfers control to the concrete protocol machine; its continuation later resumes the EVM caller. Ordinary application instructions continue through the EVM interface. Protocol-to-EVM calls use the same shared account state and nested checkpoint discipline.

There must be one authoritative world state at each composed checkpoint. If protocol state is represented separately, an explicit coherence relation connects it to the EVM-visible state. Boundary transitions update both views together, and call checkpoints capture the coupled state. Protocol field reads, public getters, delegated storage access, and ordinary account queries must not see inconsistent copies. Concrete storage-layout correspondence can remain an adapter obligation, but its interface and coherence law must be present in this deliverable. No blanket manager-address exemption is permitted.

State projections and access observations require explicit interface laws connecting them to transitions. List these laws in the review index. Do not substitute unconstrained callbacks for footprint extraction, `Related`, `AllowedReplay`, `ValidAtX`, or result validation.

Distinguish two layers of obligations:

- Semantic interface laws describe local behavior: deterministic next steps, observation/projection soundness, checkpoint behavior, and the revision's resource transfers.
- Preservation statements assert local replay properties under the specified state relation and resource bounds. They remain proof targets. A compositional replay proposition may explicitly take these local statements as hypotheses; it must be labeled conditional on them.

The end-to-end target lists the fixed semantics and its required local laws. A separate instantiation obligation connects that semantics to a pinned EVM implementation. There must be no interface field asserting complete replay, equal future traces, or global success.

Separate local progress from local preservation. A statement that says only "if the replay takes a step, its result matches" cannot establish replay existence. Include an explicit local progress obligation under the admissibility and resource conditions, including required protocol boundaries. Keep these local obligations visible as proof targets or labeled hypotheses of the composition result; do not promote them to trusted Lean axioms.

## Traces, rollback, and results

Maintain separate mathematical records for:

- the full attempted observation trace, including accesses and checks in reverted frames;
- effective per-scope fold transcripts, which follow accumulator rollback and explicit transport;
- EVM log observations with commit/rollback status.

An ordinary revert restores the shared state, cursors, accumulators, and effective enclosing transcript to the relevant checkpoint. It does not erase attempted observations. Reverted lookup scopes retain their checked sub-transcript in the mathematical execution record. A revert span restores the EVM effects but explicitly adopts the validated transported accumulator/cursor state and corresponding effective transcript extension.

Transport decoding must use exactly the source's selector and minimum-length checks; do not add a provenance guard absent from the implementation. Keep decoded accumulator values separate from the mathematical transcript witness. A transport-provenance obligation establishes when those values represent the recorded span execution. On an arbitrary accepted payload, the model records the actual decoded values without inventing a matching transcript. The hash/transcript invariant is a property to establish, not a restriction that silently removes concrete behavior.

Define finite runs as the finite closure of composed transitions. `ValidAtX` ties the reference record to a real finite successful run. Extract successful results from terminal states and retained protocol-generated validation observations. Do not permit arbitrary result records to supply hashes, check status, or returned bytes without that connection.

The complete driving transaction's returned bytes are distinct from an entry's cached bytes. A caught entry failure or an enclosing revert can prevent driver success even when an intermediate hash was computed. Only a retained selected-occurrence validation result qualifies.

## Admissibility and resources

Implement the agreed scope literally:

- Each driver is a consecutive sequence of transactions in one block.
- All driver transactions have destinations and exclude EIP-7702 authorization processing.
- `CREATE` and `SELFDESTRUCT` are banned throughout covered execution; `CREATE2` remains permitted.
- Account nonces need not be equal. Preserve required zero/nonzero classifications, transaction validity, collision status, and nonce headroom.
- Balances and fees may differ. Every attempted value-bearing call or creation has sufficient funds, including attempts in reverted frames.
- Storage equality covers all reference functional reads, including reads after writes and reverted reads. Metering-only inputs belong to resource bounds.
- Restrict environmental opcodes and gas forwarding as specified, including `SLOTNUM` when enabled.

Define footprints by folding the full reference observations, with the specified input-derived replay-account extensions. Define account and machine projections concretely from the EVM interface's typed fields. Define protocol normalization per coordinate and logical occurrence, not by excluding the manager address.

`BudgetOK` has explicit initialization, universal local-bound, arithmetic-transfer-closure, and account-compatibility clauses. Resource envelopes are mathematical sets indexed by reference checkpoints. Resource valuations support multiple revision-specific dimensions and rollback checkpoints. The plan cannot refer to future `Run`, future validation, or transcript equality.

Use a paired `GAS`/call semantic checkpoint for allowed immediate forwarding. Its adapter obligation requires the literal permitted instruction sequence. Do not require equal intermediate gas stack operands or admit general gas dependence.

Reference-step indices organize the proof obligations; they do not assert that the replay already follows those steps. Equality of future accesses and termination remain conclusions.

## Statements and review surface

Provide named propositions for encoding/fold determinism, setup preservation, freshness normalization, queue-occurrence correspondence, local execution preservation, resource adequacy, rollback/transport, validation preservation, commitment, and the final replay result.

The final result includes a finite successful replay, all required checks, corresponding occurrence consumption, scoped transcript equality, structural trace equality, the committed hash equal to the reference and expected hash, and equality of driving-transaction output bytes.

The review index must identify which propositions are direct targets and which are conditional composition results. It must list every abstract semantic parameter and assumed local law, and record that no Osaka/Glamsterdam instantiation or bytecode proof is provided.

## Validation and acceptance

Use the pinned Lean 4.22.0 toolchain and existing dependency versions. Type-check the aggregate module and confirm that every review declaration elaborates. Toolchain setup may be needed because `lake` was not found on PATH during inspection. Avoid changing dependency pins or adding a runtime hash dependency merely to type-check the model.

Check concrete encoding lengths, fold ordering, queue selection, and rollback bookkeeping with small examples where definitions are executable. Use a simple deterministic test hash for fold-bookkeeping examples and label it as such; those examples are not Keccak validation or replay proofs.

Include a small positive composed scenario and negative controls so a model with no successful paths or an always-false admissibility predicate is not accepted merely because it type-checks. Cover duplicate FIFO selection, an empty lookup's final fold, nested completion order, ordinary rollback versus transported rollback, and a caller suffix that reverts after entry validation. These are focused model checks, not a broad conformance suite. Do not turn each implementation helper into a mirrored test.

Acceptance requires:

1. No `sorry`, new axioms, or claimed replay proofs.
2. Concrete definitions for protocol transitions and all named admissibility predicates.
3. A finite-run definition tied to transitions and result extraction.
4. No future-success or future-trace-equality premise hidden in admissibility or interface fields.
5. Explicitly listed semantic assumptions and unproved obligations.
6. A clean type-check result, or an exact report of any toolchain blocker.
7. A concise manual-review map from the prose specification to Lean declarations.
8. Explicit world-state coherence, local progress, and model examples that exercise actual composed transitions rather than prefilled result records.

## Implementation choices left to the builder

Choose helper names, data-structure implementations, and module splits within the boundaries above. Prefer straightforward definitions and readable propositions over automation or optimization. Structural typing and definitional simplification are allowed; substantive theorem proving remains deferred until the user approves the model and statements.

## Pressure-test ledger

The grill-plan review asked zero new human questions. No question passed all four question-gate conditions: consequential uncertainty, meaningfully different alternatives, no answer in prior decisions or local evidence, and a need for human design authority. An interview band was not opened because no first question was needed.

### Human-owned decisions

- The user selected a concrete protocol model with a parameterized EVM interface. Direct integration with the current interpreter is outside this delivery.
- Deliver model definitions and named statements for manual review first. Defer substantive proofs and the Besu admission checker.
- Seek sufficient conservative restrictions, not minimal restrictions. Preserve the previously agreed balance, nonce, creation, storage, transaction, and scheduling policies without reopening them.
- Prefer a pinned Glamsterdam instantiation later, with Osaka acceptable. This delivery makes no fork-support claim.

### Agent-owned decisions

- Keep one coherent world state and explicit coupled rollback. This follows the existing shared account-state model and the requirement to cover callbacks; independent mutable protocol/EVM worlds would change the intended semantics.
- Model proxy routing and static detection from source. A trusted static-mode oracle would hide a resource-sensitive branch that the accepted scope includes.
- State local progress separately from preservation. This is necessary for the existing successful-replay conclusion, not an additional product guarantee.
- Add focused positive and negative model examples. Type checking alone cannot detect vacuous statements or fabricated successful results.
- Build in dependency order: data and hash/protocol operations; execution composition; admissibility and statements. These are implementation stages of one final review package, not separate products or permission checkpoints.
- Preserve the source decoder's acceptance behavior. Transport provenance remains an explicit invariant to establish, not an extra runtime guard.

### Deferred implementation decisions

- The implementation plan chooses detailed transition constructors, continuation representation, and module splits within the agreed semantics.
- The implementer sets up the pinned toolchain and chooses compatible type-check commands without changing dependency versions unnecessarily.
- Proof work after manual model review establishes the local progress/preservation, resource, transport-provenance, and replay statements.
- A later integration pass pins the EVM revision and establishes concrete bytecode, storage-layout, observation, and resource correspondence. The current review index must expose those obligations.

### Residual risks

- An abstract semantic interface can be inconsistent or too weak. Model review must inspect its laws; the later EVM instantiation must demonstrate that the intended implementation satisfies them.
- A type-correct proposition can be false or vacuous. Focused examples reduce obvious modeling mistakes but do not replace proof or establish satisfiability for deployed contracts.
- Glamsterdam rules and the local interpreter's coverage are not pinned together. The later integration owner must reconcile the exact revision before any executable-EVM claim.
- Proxy fixed-cap calls and revert-span transport are sensitive integration points. Their behavior must remain visible in the resource and provenance statements.

Readiness verdict: ready for `writing-plans`. This verdict is not a claim that the model exists, that the theorem is true, or that an EVM instantiation has been verified.
