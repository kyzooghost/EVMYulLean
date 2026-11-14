# Cross-chain Replay Lean Model Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Deliver a compilable Lean 4 model and named, unproved replay statements for manual review.

**Architecture:** Define the protocol, hashing, execution composition, and admissibility concretely. Parameterize revision-specific EVM primitives through a typed interface with visible local laws. Derive finite runs and results from composed transitions; never accept a supplied successful transcript as execution.

**Tech Stack:** Lean `leanprover/lean4:v4.22.0`, the existing mathlib `v4.22.0` dependency and lockfile, Lake, existing `EvmYul.AccountAddress` and `EvmYul.UInt256` types.

**Spec:** `docs/cross-chain-rolling-hash-replay-spec.md`; design: `docs/superpowers/specs/2026-11-12-cross-chain-replay-lean-design.md`. Read both before implementation.

## Global Constraints

- Namespace: `EvmYul.CrossChainReplay`.
- Statements are `def ... : Prop := ...`; no `sorry`, new axioms, or claimed replay proofs. Routine typing obligations and finite example checks are permitted; substantive proofs are deferred.
- Preserve exact bundle order and multiplicity, source hash encoding, lookup selection, rollback, and validation behavior.
- Driver transactions are consecutive in one block; exclude creation transactions and EIP-7702 authorization transactions.
- Ban executed `CREATE` and `SELFDESTRUCT`; retain `CREATE2` with funding, gas, collision, and nonce-headroom conditions. Do not impose exact account-nonce equality.
- Include every reference functional storage read, including overwritten-then-read slots and reverted reads; distinguish metering-only inputs.
- Balances and fees may differ. Every attempted value-bearing call or creation must have sufficient funds.
- Target a later pinned Glamsterdam instantiation, with Osaka acceptable. This delivery supplies neither fork instantiation nor bytecode correspondence.
- Keep the existing dependency pins. Do not modify unrelated EVM/Yul semantics or install project dependencies merely to obtain a hash implementation.
- Keep one authoritative world state and explicit protocol/EVM coherence. No blanket manager exemption or hidden future-run assumption.
- Do not use a successful build or toy model as evidence that the replay proposition is true for an actual EVM.

## Review Focus

1. Duplicate hashes and reused bucket positions must preserve logical occurrence identity. Task 3 checks FIFO, stale prefixes, and inbound tail selection.
2. An accepted revert payload is not automatically authentic. Task 7 checks trailing bytes, truncation, and accepted payloads without transcript provenance.
3. A caught failure or caller-suffix revert can remove validation while leaving attempted observations. Tasks 7 and 8 check both outcomes.
4. Static probing can fail from gas as well as static permission. Tasks 6 and 9 keep those causes distinct and exclude gas-induced routing changes through admissibility.
5. A deterministic but stuck interface or an always-false predicate can make statements useless. Tasks 8–10 require local progress statements and a positive finite toy execution/admissibility fixture.

## Files and dependency direction

Create the following files; the split refines the design to avoid circular imports and large modules.

| File under `EvmYul/CrossChainReplay/` | Responsibility | Depends on |
| --- | --- | --- |
| `Types.lean` | Scalar aliases, bundles, requests, revision description, driver envelopes | Existing scalar types |
| `Hashing.lean` | Concrete encodings, folds, error/transport encodings | Types |
| `Observations.lean` | Accesses, checks, outcomes, scopes, log provenance | Types |
| `ProtocolState.lean` | Queues, lookup tables, registry, contexts, cursors | Types, Hashing |
| `Protocol.lean` | Pure queue operations and protocol control/continuations | ProtocolState, Observations |
| `EvmInterface.lean` | Primitive EVM interface, state views, resource arithmetic, coherence | Protocol, Observations |
| `ExecutionState.lean` | Composed states, checkpoints, configuration data | EvmInterface |
| `Rollback.lean` | Checkpoint restoration, scope/trace bookkeeping, transport adoption | ExecutionState |
| `Execution.lean` | Composed steps, driver control, finite execution records | ExecutionState, Rollback |
| `Footprints.lean` | Reference observation folds and account extensions | Observations |
| `Resources.lean` | Resource envelopes and four `BudgetOK` obligations | Execution, Footprints |
| `Admissibility.lean` | State relation and A1–A8 conjunction | Resources, Protocol |
| `Statements.lean` | Local targets and final replay propositions | Admissibility |
| `Checks/Fixtures.lean` | Small finite toy EVM and data fixtures | Required model modules only |
| `Checks/Hashing.lean`, `Checks/Queues.lean` | Concrete encoding and selection checks | Owning modules |
| `Checks/Execution.lean`, `Checks/Admissibility.lean` | Positive/negative composed examples | Owning modules, Fixtures |
| `Checks.lean` | Aggregate check imports | Checks modules |

Also create `EvmYul/CrossChainReplay.lean` as the model aggregate and `docs/cross-chain-replay-lean-review.md` as the manual-review index. The model aggregate must not import test fixtures. No change to `EvmYul.lean` or `lakefile.lean` is required unless a verified Lake limitation requires it.

The table describes final dependencies. Task 3's queue-only Protocol module imports ProtocolState; Task 6 adds Observations and control transitions. Task 6's Execution module imports ExecutionState; Task 7 adds Rollback. No earlier task imports a module scheduled for a later task.

## Interface conventions

Signatures below describe Lean declarations, with ordinary implicit parameters omitted only where stated. `Bytes := List UInt8`, `Address := EvmYul.AccountAddress`, `Word := EvmYul.UInt256`, `Hash32 := Vector UInt8 32`, and `HashFn := Bytes -> Hash32`. Counts and heights are `Nat` with separate representability predicates.

`Parameters` fixes the hash function, revision descriptor, local rollup, manager/system identities, and proxy creation-code bytes. `EvmModel` supplies primitive semantics and has associated `World`, `Frame`, and `Environment` types. Protocol definitions do not depend on those types. Later signatures use `M : EvmModel` and `p : Parameters` explicitly.

`Configuration M` contains the initial world, environment, ordered driver envelopes, block position/capacity inputs, bundle, selected occurrence, and logical requests. `ExecutionRecord M` is a finite sequence of composed states and transition observations plus a terminal outcome. Its well-formedness is checked by `Run`; storing a record does not establish execution.

All code fragments in this plan are signature contracts or test assertions, not implementation already present in the repository. In signatures using `Configuration M` or `ExecutionRecord M`, bind `{M : EvmModel}` unless an explicit M argument is shown. Paths in task file lists are relative to `EvmYul/CrossChainReplay/`, except explicitly qualified paths.

## Task 1: Typed bundles and the pinned build path

**Files:** create `Types.lean`, the model aggregate, and `Checks/Hashing.lean` with initial type/encoding checks.

**Interfaces:** produces the scalar aliases above; `CallIdentity`, `IncomingCall`, `OutgoingCall`, `NestedLookup`, `TopLevelLookup`, `Entry`, `Bundle`, `EntryId`, `ScopeId`, `LogicalRequest`, `DriverEnvelope`, `RevisionDescriptor`, and `Parameters`.

- [ ] Inspect `git status`, the repository instructions, and the selected execution workflow. Preserve unrelated changes. Apply the worktree skill at execution time if isolation is needed.
- [ ] Establish Lean 4.22.0: inspect installed tools; if absent, install elan through its official distribution after inspecting the installer, then run `elan toolchain install leanprover/lean4:v4.22.0`. Do not change `lean-toolchain`. Run `lake env lean --version`; require version 4.22.0 before claiming checks pass. Fetch the existing mathlib cache with `lake exe cache get` without updating the lockfile.
- [ ] Write a check importing the new Types module and referring to its declarations. Run it and observe the expected missing-module/declaration failure before implementation. Record toolchain/setup failures separately from this expected failure.
- [ ] Define `CallIdentity` with static flag, source/target addresses and rollup words, value, and data. Define semantic row fields exactly from spec §3.3 and `IEEZL2.sol`; omit `loadedBlock` from semantic rows and put it in operational loaded records in Task 3. Nested lookups have the three context-key counts, incoming/outgoing lists, call count, failed flag, cached bytes, and both expected hashes. Top-level lookups also have declared peer and their host nested table.
- [ ] Define `EntryId` as a tagged identity for a preloaded occurrence or a driver load/row occurrence. `ScopeId` adds an invocation path to distinguish repeated attempts. Do not encode these identities by hash alone. Define request route and transaction-kind enums with explicit creation and authorization variants so admissibility can reject them rather than making invalid configurations unrepresentable.
- [ ] Define a revision descriptor with a name and immutable specification identifier plus enabled-opcode/native-operation declarations; an empty identifier is not a supported instantiation. Put numerical limits in shared constants, including rollup maximum `2^63 - 1`, nonce limit `2^64 - 1`, and proxy probe gas `1000`.
- [ ] Run `lake build EvmYul.CrossChainReplay.Types` and `lake env lean EvmYul/CrossChainReplay/Checks/Hashing.lean`. Require successful elaboration. Report any toolchain blocker without replacing the requested version.

## Task 2: Encodings and hash functions

**Files:** create `Hashing.lean`; extend `Checks/Hashing.lean`.

**Interfaces:** consumes Types; produces `encodeCall : CallIdentity -> Bytes`, `callHash : HashFn -> CallIdentity -> Hash32`, `foldBoundary : HashFn -> Hash32 -> BoundaryRecord -> Hash32`, `crossHash : HashFn -> List BoundaryRecord -> Hash32`, `foldStructural : HashFn -> Hash32 -> StructuralEvent -> Hash32`, `foldStatic : HashFn -> Hash32 -> Bool -> Bytes -> Hash32`, and `decodeContextResult : HashFn -> Bytes -> Except ProtocolError ContextResult`. Define `BoundaryRecord`, `StructuralEvent`, `ProtocolError`, and `ContextResult` here or in Types, keeping import direction acyclic.

- [ ] Add failing checks for call-encoding lengths `288`, `320`, `320`, and `352` for data lengths `0`, `1`, `32`, and `33`; word seven's offset must be `256`, and the gas word must be zero. Check address padding and that false/true produce distinct Boolean bytes. Run the check file to confirm the missing definitions fail.
- [ ] Implement unsigned big-endian word/address encoding and dynamic byte padding. Implement all folds from spec §4. Hashing uses the supplied `HashFn`; do not call an opaque FFI or introduce a second crypto implementation.
- [ ] Define typed protocol errors for actual guards and Solidity panic cases used by the modeled paths, preserving their ABI signatures and source precedence. Derive selectors from the hash parameter and exact signature strings. Context transport has five words after its four-byte selector; preserve the ignored word as raw data, not a newly imposed canonical-Boolean check.
- [ ] Add assertions: packed boundary input length is `65 + data.length`; empty transcript gives 32 zero bytes; structural tags are `1,2,3,4`; static structural input has no call hash. A matching `164`-byte transport decodes, a `163`-byte transport rejects, a wrong selector rejects, and matching trailing bytes are accepted. Use a nonconstant deterministic toy hash only for ordering/bookkeeping tests.
- [ ] Name the encoding regression `abiLengthBoundaries`. Define `callWithDataLength : Nat -> CallIdentity` in this check file with zero fixed fields and the requested number of zero data bytes; assert the following exact values. Keep separate assertions for the offset, gas, and byte contents so length alone cannot pass an incorrect encoder.

```lean
def abiLengthBoundaries : Bool :=
  ([0, 1, 32, 33].map fun n => (encodeCall (callWithDataLength n)).length)
    == [288, 320, 320, 352]
#guard abiLengthBoundaries
```

- [ ] Run `lake build EvmYul.CrossChainReplay.Hashing` and `lake env lean EvmYul/CrossChainReplay/Checks/Hashing.lean`; all assertions must pass. These are encoding tests, not verified Keccak vectors.

## Task 3: Concrete protocol storage and selection

**Files:** create `ProtocolState.lean`, `Protocol.lean`, and `Checks/Queues.lean`.

**Interfaces:** produces `ProtocolState`, `LoadedEntry`, `LoadedLookup`, `LoadBatch`, `LoadContext`, `LookupKey`, and `LoadResult`; functions `loadBatch : Parameters -> LoadContext -> LoadBatch -> ProtocolState -> Except ProtocolError LoadResult`, `nextFreshHead : Nat -> Hash32 -> ProtocolState -> Nat`, `selectProxyEntry : Parameters -> Nat -> Hash32 -> Word -> ProtocolState -> Except ProtocolError (EntryId × ProtocolState)`, `selectInboundEntry : Parameters -> Hash32 -> LoadResult -> Except ProtocolError (EntryId × ProtocolState)`, `findNestedLookup : Bool -> LookupKey -> List NestedLookup -> Option (Nat × NestedLookup)`, and `clearConsumed : Nat -> Hash32 -> Nat -> ProtocolState -> ProtocolState`. `LoadContext` includes height, load occurrence identity, normal/inbound route, caller, and attached value; it supplies the information needed for load authorization and value guards. `LoadResult` contains the updated state and newly loaded entry identities/indices. Inbound selection checks the three-way hash binding after load preflight; it does not replace that preflight.

- [ ] Write failing queue checks: load two same-hash occurrences and consume in FIFO order; retain a live remainder behind a stale prefix; reset a wholly stale bucket; consume the newly pushed inbound occurrence despite an older same-hash head. Assert logical identities, not just list lengths.
- [ ] Implement loaded metadata, registry, buckets/heads, and active contexts. Perform duplicate top-level lookup rejection before peer/value preflight and before writes. Reject static value and static revert spans; allow value only at the inbound root coordinate under the atomic inbound route.
- [ ] Implement the functions above from spec §4.5. Preserve source distinctions between consumed markers, head advancement, and final cleanup. Overwrite top-level lookups across loads, while rejecting duplicates within one batch.
- [ ] Test four-part nested keys, first-match order, host-table reuse, and the `failed = true` filter for non-static fallback. A matching static lookup may have either failed flag. Test the pre-increment outgoing-key convention and the `uint64` boundary as separate well-formedness checks.
- [ ] Run `lake build EvmYul.CrossChainReplay.Protocol` and `lake env lean EvmYul/CrossChainReplay/Checks/Queues.lean`; require all assertions to pass.

## Task 4: Observation data and footprint extraction

**Files:** create `Observations.lean`, `Footprints.lean`, and initial `Checks/Admissibility.lean`.

**Interfaces:** produces `EngineObservation`, `ProtocolObservation`, `Observation`, `Trace := List Observation`, `StorageLocation`, `AccessKind`, `Footprint`, `MachineView`, `AccountView`, `AccountProjection`, and `ResourceAction`; functions `referenceFootprint : Trace -> Footprint`, `extendAccounts : Footprint -> List Address -> Footprint`, and `accountProjection : AccountView -> AccountProjection`.

- [ ] Add failing checks that a read after a write and a read in a reverted frame remain in the footprint, while a metering-only read does not independently require storage equality. An address accessed implicitly for fee settlement must remain included.
- [ ] Define separate engine and protocol observation variants. Only protocol observations can carry a validation/check identity. Engine observations include decoded instruction, frame identity, accesses, native effects, resource actions, and raw logs; raw logs are never automatically validation results.
- [ ] Define explicit account projection fields from §5.8, including code/delegation, presence, emptiness, nonce-zero status, and creation eligibility. Keep exact balances/nonzero nonce magnitudes in AccountView but out of AccountProjection. MachineView includes functional frame data; distinguish ordinary instruction checkpoints from the permitted paired GAS/call checkpoint.
- [ ] Implement footprint folds over the attempted history. Define deduplicated membership with ordering immaterial for sets; do not filter rolled-back observations. Replay account extensions come from supplied envelope/settlement inputs, not a future trace.
- [ ] Run the owning module builds and `lake env lean EvmYul/CrossChainReplay/Checks/Admissibility.lean`. Check that accounts with different nonzero nonces can have equal projections, while a relevant zero/nonzero or creation-eligibility change is detected.

## Task 5: EVM interface and coherent state views

**Files:** create `EvmInterface.lean`, `ExecutionState.lean`, and `Checks/Fixtures.lean`; extend `ProtocolState.lean` with the context and continuation data used by ExecutionState.

**Interfaces:** consumes protocol and observation types; produces `EvmModel`, `EngineAction`, `PrimitiveEffect`, `CallRequest`, `FrameOutcome`, `ResourceValuation`, `ResourceDemand`, `Configuration M`, `ExecutionState M`, `FrameCheckpoint M`, and `SemanticInterfaceLaws : (M : EvmModel) -> Parameters -> Prop`.

- [ ] Write a finite toy interface fixture that takes one application step and reaches an exit boundary; it must not supply a final protocol result. Type-checking must fail before the required interface exists.
- [ ] Define `EvmModel` fields: associated World/Frame/Environment types; account/storage/transient/machine/resource projections; primitive next-step relation; frame enter/exit; transaction begin/settle; protocol read/write views; protocol-coordinate/raw-location correspondence; input-derived settlement recipients; and local resource demand/transfer operations. Give each field a typed input/output contract and a docstring listing its unproved correspondence obligation.
- [ ] Primitive steps return an `EngineAction` for internal continuation, a call/protocol boundary request, or a frame exit, together with only engine observations. No primitive can return an `ExecutionRecord`, chosen protocol transcript, or selected-entry hash. Requests remain subject to concrete authorization and dispatch rules.
- [ ] Store one World in ExecutionState. Its protocol view is obtained through `readProtocol : World -> ProtocolState`; updates use `writeProtocol : World -> ProtocolState -> World`. State explicit read-after-write, unaffected-account/slot, and coupled-checkpoint laws. Projected manager storage must not be separately mutable without synchronization. Treat layout correspondence as an exposed adapter obligation, not a blanket exclusion from footprints.
- [ ] Define local laws as named propositions for determinism, observation completeness, frame/rollback behavior, state coherence, and arithmetic meaning. Keep them distinct from local replay progress/preservation statements in Task 10. Define ResourceValuation with balances, nonces, resource vectors, access/refund/metering data, and saved resource checkpoints; ResourceDemand contains explicit minima/funding/headroom requirements rather than a generic `safe : Prop` oracle.
- [ ] Run `lake build EvmYul.CrossChainReplay.EvmInterface`, `lake build EvmYul.CrossChainReplay.ExecutionState`, and the fixture type-check. Inspect the field list for hidden global replay assumptions.

## Task 6: Protocol control, proxy routing, and EVM composition

**Files:** extend `Protocol.lean`; create `Execution.lean` and initial `Checks/Execution.lean`; extend Fixtures.

**Interfaces:** produces `ProtocolContext`, `ProtocolControl`, `ProtocolAction`, `advanceProtocol : Parameters -> ProtocolContext -> ProtocolState -> ProtocolControl -> ProtocolAction`, and `Step : (M : EvmModel) -> Parameters -> ExecutionState M -> List Observation -> ExecutionState M -> Prop`. ProtocolAction carries local state updates/checks, EVM effect requests with continuations, or return/revert. It does not recursively execute an entire application call. Put the ProtocolContext/ProtocolControl type declarations in ProtocolState during Task 5, before ExecutionState stores suspended continuations; Task 6 defines their transition behavior.

- [ ] Write failing scenarios for proxy-root final folding and inbound execution without the extra root fold. Include a successful nested order `B, Q, A, root`; verify the observed boundary records, not only the resulting toy digest.
- [ ] Implement explicit continuations for load/select, incoming-call iteration, outgoing reentry, static lookup, reverted lookup, entry checks, cleanup, and returned bytes. Preserve local processed counts versus shared incoming/outgoing cursors and check actual array bounds/error order.
- [ ] Implement call/proxy boundary routing: registry validation, CREATE2 proxy request and subsequent registration, raw execute-on-behalf forwarding, cached-success ABI unwrapping, and raw revert propagation. The manager's value transfer to SYSTEM_ADDRESS is an actual call before its cross-chain dispatch.
- [ ] Represent the proxy's static self-probe as a nested call capped at exactly `1000`, attempting the transient write. Distinguish static-permission failure from out-of-gas even if both make the source branch select lookup. Preserve the source branch; exclude undesired gas failures later through BudgetOK rather than adding a guard absent from source.
- [ ] Compose local protocol actions and primitive EVM steps into Step. Keep callbacks/reentry visible with a shared world, frame stack, and suspended continuations. Protocol operation boundaries generate their own access/check observations; EVM events cannot forge them.
- [ ] Run `lake build EvmYul.CrossChainReplay.Execution` and the execution checks. Include a rejected unauthorized boundary and a lookup whose empty sub-call list still adds its own final record.

## Task 7: Rollback and transport bookkeeping

**Files:** create `Rollback.lean`; update ExecutionState and Execution; extend execution checks.

**Interfaces:** produces `checkpoint : (M : EvmModel) -> ExecutionState M -> FrameCheckpoint M`, `restore : (M : EvmModel) -> FrameCheckpoint M -> ExecutionState M -> ExecutionState M`, and `adoptTransport : (M : EvmModel) -> ContextResult -> ExecutionState M -> ExecutionState M`. Define `ScopeRecord` with actual accumulators and a separate optional provenance witness; do not require decoded hashes to come with a transcript proof.

- [ ] Add a failing case where Q folds successfully inside incoming A, then A reverts: Q's enclosing accumulator update disappears, A's failure folds, and the attempted history remains.
- [ ] Implement checkpoints for world, protocol transient state, effective transcripts, and live logs. Preserve attempted observations on restore. Keep completed lookup sub-scope observations distinct from the enclosing effective transcript.
- [ ] Implement reverted lookup reset/check/revert behavior and the revert-span self-call. The span begins with the enclosing accumulator; validated decoded hashes/cursors are adopted after restoring state effects. Restore the first row's span field and advance only the owning frame's iteration count.
- [ ] Test matching-selector payloads of lengths `163`, `164`, and `165`, plus arbitrary decoded hashes. Accepted bytes update actual state even without provenance; they must not manufacture a matching transcript witness. No extra success/failure boundary record is added for ContextResult itself.
- [ ] Test that a failed frame restores any tentative outgoing-cursor increment and all correlated state, while retaining its failed check observation. Run module builds and execution checks.

## Task 8: Finite runs, driver outcomes, and reference validity

**Files:** extend Execution and Fixtures; extend execution checks.

**Interfaces:** produces `ExecutionRecord M`, `DriverOutcome`, `Run : (M : EvmModel) -> Parameters -> Configuration M -> ExecutionRecord M -> Prop`, `ValidAtX : (M : EvmModel) -> Parameters -> Configuration M -> ExecutionRecord M -> Prop`, `selectedValidation : ExecutionRecord M -> EntryId -> Option ValidationResult`, and `driverReturnedBytes : ExecutionRecord M -> Option Bytes`.

- [ ] Define Run as initial-state correspondence, a finite indexed chain of Step transitions and matching observations, and terminal-outcome correspondence. Transaction sequencing must cover every setup and the complete driving transaction, including initialization and settlement. No unrelated transition can be inserted between driver transactions.
- [ ] Derive retained validation results from protocol-generated events with frame-commit provenance and selected logical occurrence. Do not trust prefilled result fields or a raw event with the same ABI signature. Define success/failure exactly as spec §2; `ValidAtX` additionally checks the required reference validations and expected hashes.
- [ ] Add a positive finite toy driver containing a real protocol entry and a derived committed hash. Supply its transition chain through constructors or finite checks, not through an assumed Run proof. Label the fixture as a toy EVM, not an Osaka/Glamsterdam instantiation.
- [ ] Add negative controls: a caller catches entry failure and commits; a caller suffix reverts after validation; a successful setup is followed by a failing driver. Selected validation must be absent when rolled back, while attempted checks remain available and earlier setup transactions retain their committed effects.
- [ ] Build Execution and run execution checks. Verify that the positive example yields actual driving output bytes and that altered trace/result fields fail record validation.

## Task 9: Concrete admissibility and resource plans

**Files:** create `Resources.lean`, `Admissibility.lean`; extend admissibility checks and Fixtures.

**Interfaces:** produces `ResourcePlan := Nat -> ResourceValuation -> Prop`; `BudgetOK : (M : EvmModel) -> Parameters -> Configuration M -> ExecutionRecord M -> Configuration M -> ResourcePlan -> Prop`; `Related : (M : EvmModel) -> Parameters -> Footprint -> ExecutionState M -> ExecutionState M -> Prop`; `TraceAllowed : Parameters -> Trace -> Prop`; `DriverAllowed : (M : EvmModel) -> Parameters -> Configuration M -> Prop`; `InitialRelated`, `SetupCompatible`, and `AllowedReplay : (M : EvmModel) -> Parameters -> Configuration M -> ExecutionRecord M -> Configuration M -> Prop`.

- [ ] Write failing tests for a banned opcode in a reverted frame, a read-after-write slot mismatch, a changed relevant nonce-zero classification, and a zero-to-funded fee-recipient classification change. Ordinary opcode restrictions cannot be bypassed by a manager address label.
- [ ] Implement Related field by field from §5.8. Protocol equality is normalized by logical occurrences and freshness classifications; exact fee, gas, balance, physical index, and nonzero nonce equality are not required. Define InitialRelated at the driver prestate and SetupCompatible from queue/load invariants, not postulated successful setup.
- [ ] Implement the full opcode ban and the narrow GAS/call pair rule, including initialization code and all failed/reverted frames. Enforce creation/authorization transaction exclusions, same-block consecutive driver positions, same logical inputs and semantic bundle, unchanged revision parameters, and representation bounds. Freshness exceptions refer to exact protocol operations/coordinates.
- [ ] Implement BudgetOK's four quantified obligations from §5.8. Compare explicit resource-demand minima against valuations; universally quantify local arithmetic transfers into the next envelope. Include all attempted value-bearing calls, nonce headroom, transaction fees/capacity, and resource-dependent account projections. No clause may call Run or assert a future trace matches.
- [ ] Define AllowedReplay as the named conjunction from the spec, with an existential resource plan. Reference validity remains a separate theorem premise. Include the reference resource restrictions as well as replay bounds.
- [ ] Extend the finite toy fixture with a positive admissibility witness using finite/definitional checks only. Add negative controls for insufficient call funds, insufficient child gas, nonce exhaustion, interleaving, CREATE, and EIP-7702; add positive controls for differing funded balances and differing nonzero nonces satisfying classifications/headroom. If a fixture fails, repair its arithmetic or the model instead of replacing the predicate with True/False or adding an axiom.
- [ ] Build Resources and Admissibility and run the admissibility checks. Review field dependencies to ensure no future execution is used to compute the footprint or validate the resource plan.

## Task 10: Review statements, assumptions index, and final checks

**Files:** create `Statements.lean`, `Checks.lean`, and `docs/cross-chain-replay-lean-review.md`; finish model aggregate.

**Interfaces:** produces named Prop definitions `HashPreservationStatement`, `SetupPreservationStatement`, `FreshnessPreservationStatement`, `QueueCorrespondenceStatement`, `ProtocolInterfaceStatement`, `LocalProgressStatement`, `LocalPreservationStatement`, `ResourceAdequacyStatement`, `RollbackPreservationStatement`, `TransportProvenanceStatement`, `ValidationPreservationStatement`, `CommitmentStatement`, `ReplayConclusion`, `ReplayPreservationStatement`, and `ReplayCompositionStatement`. Each is parameterized by M/p and only the data relevant to that statement; local claims quantify over one step/checkpoint, not complete future runs. ProtocolInterfaceStatement collects the concrete protocol's eight local laws in spec §4.5 as proof targets. QueueCorrespondenceStatement preserves selected logical occurrences through loading, selection, and cleanup.

- [ ] Define ReplayConclusion with successful Run, all required checks, corresponding occurrence consumption, scoped transcript and structural-trace equality, selected committed hash equal to reference and expected hash, and equality of driving-transaction output bytes. Preserve the natural-number delay, exact height relation, and all admissibility premises.
- [ ] Define the final target over the fixed semantic interface and its explicit local laws. Define the composition statement separately with named local progress/preservation/resource/rollback/commitment statements as hypotheses. The review document must distinguish this conditional composition claim from the full target and from a future concrete-EVM instantiation.
- [ ] Use the following quantifier shape for the full target. Define `configurationHeight : Configuration M -> Nat` in ExecutionState and `ReplayConclusion : (M : EvmModel) -> Parameters -> Configuration M -> ExecutionRecord M -> Configuration M -> ExecutionRecord M -> Prop` in Statements. The concrete protocol's local laws are obligations to establish, not additional assumed facts in this full target; expose them as hypotheses only in the separate composition statement.

```lean
def ReplayPreservationStatement (M : EvmModel) (p : Parameters) : Prop :=
  SemanticInterfaceLaws M p →
  ∀ (reference : Configuration M) (referenceRun : ExecutionRecord M),
    ValidAtX M p reference referenceRun →
    ∀ (delay : Nat) (replay : Configuration M),
      configurationHeight replay = configurationHeight reference + delay →
      AllowedReplay M p reference referenceRun replay →
      ∃ replayRun, ReplayConclusion M p reference referenceRun replay replayRun
```

- [ ] Give every interface law and every named proposition a spec-section docstring. Create a review table of declaration, source section, concrete definition versus parameter versus proof target, and remaining instantiation obligation. List all abstract fields; include hash implementation, storage-layout correspondence, opcode/access soundness, resource arithmetic, and transaction/frame semantics.
- [ ] Run `lake build EvmYul.CrossChainReplay EvmYul.CrossChainReplay.Checks`. Run each check file with `lake env lean` to re-evaluate assertions, rather than relying only on cached build artifacts. Require no failed assertions or elaboration errors.
- [ ] Run `rg -n '\b(sorry|admit|axiom)\b' EvmYul/CrossChainReplay` and inspect any matches; only explanatory comments may mention forbidden constructs. Inspect public declarations for accidental trusted opaque placeholders and inspect the admissibility dependency path for references to future Run or replay success.
- [ ] Verify no unrelated files or dependency pins changed with `git status --short` and the relevant diffs. Report actual commands and results, named residual assumptions, and the aggregate/review-document paths. State explicitly that propositions are unproved and no concrete fork or deployed contract has been verified.

## Review checkpoints and completion policy

Use these stable check names in the owning check files. Each name must check the preceding task's concrete observations or transition witnesses; a Boolean supplied by a fixture is not evidence. Executable checks use `#guard`; relational examples use named `example`/`def` witnesses with constructor, simplification, or finite arithmetic proofs. Do not require a decision procedure for arbitrary Run or resource-envelope predicates.

| Task | Check names and required assertions |
| --- | --- |
| 2 | `abiLengthBoundaries`: lengths above; `transportDecoderBoundaries`: 163 rejects, 164 and 165 accept with the matching selector |
| 3 | `duplicateFifo`: selected IDs equal the two loaded IDs in order; `stalePrefixRetention`: the live remainder precedes newly loaded rows; `inboundTailSelection`: the newly loaded ID is selected |
| 4 | `attemptedReadFootprint`: overwritten-then-read and reverted slots are members; `meteringOnlyRead`: no independent functional-slot membership; `nonzeroNonceProjection`: different nonzero magnitudes have equal eligible projections |
| 5 | `toyPrimitiveExit`: the toy transition relation admits the stated application step and exit, with no protocol result supplied |
| 6 | `nestedFoldOrder`: records equal `[B, Q, A, root]`; `emptyLookupFinalFold`: one final lookup record; `staticProbeFailureCauses`: static-write and gas failures retain distinct causes |
| 7 | `ordinaryRollback`: Q disappears from the effective enclosing transcript and remains attempted; `transportWithoutProvenance`: accepted decoded values change state without producing a witness |
| 8 | `committedToyDriver`: a finite composed Run and retained selected validation exist; `caughtEntryFailure`: no successful selected validation; `suffixRevert`: no committed selected validation |
| 9 | `admissibleToyReplay`: the positive fixture satisfies AllowedReplay; `insufficientChildGas`, `insufficientCallFunds`, `nonceExhaustion`, `feeRecipientClassification`, `forbiddenRevertedOpcode`, `interleavedDriver`: each violates its named conjunct |

For a check with several outputs, assert their tuple against the expected tuple. Test names are review anchors; helper constructors and local fixture names remain implementation choices. Task 10 checks declaration elaboration and assumption dependencies, not truth of the unproved statements.

Review Tasks 1–4 for faithful data, bytes, selection, and footprints; Tasks 5–8 for non-oracular composition, progress, state coherence, and commitment; Tasks 9–10 for non-circular assumptions and readable statements. Review checkpoints are technical gates, not repeated requests for user permission. The final package is delivered for the user's manual model/statement review before substantive proof work.

If the selected execution workflow uses commits, commit only completed task files after their checks; do not include unrelated user changes. Do not merge or publish as part of this plan.

## Self-review coverage

| Specification area | Owning tasks |
| --- | --- |
| §1–3: success, driver scope, bundles, footprints, transcripts | 1, 4, 7, 8 |
| §4.1–4.3: encodings, folds, other checks | 2, 6, 7 |
| §4.4–4.5: freshness, queues, protocol laws | 3, 5, 6 |
| §5.1–5.4: validity, storage/account relation, transient state | 4, 5, 7, 8, 9 |
| §5.5–5.8: resources, setup, revisions, admissibility | 5, 9 |
| §6: observations and GAS restrictions | 4, 6, 9 |
| §7–9: theorem, decomposition, Lean boundary | 8, 9, 10 |
| §10–12: local claim, audit questions, source correspondence | 10 and review index |

The implementation stages share one state/trace interface. Native execution with one final independent review is recommended to keep those definitions consistent; subagent-driven task execution remains available if the user prefers per-task independent reviews.
