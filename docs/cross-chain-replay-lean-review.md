# Cross-chain replay Lean review index

Status: Tasks 1-10 of the [implementation plan](superpowers/plans/2026-11-12-cross-chain-replay-lean.md)
are implemented and checked with Lean 4.22.0. The replay statements are **named and
unproved**. No Osaka or Glamsterdam instantiation, bytecode correspondence, or deployed
contract is verified. A successful build is not evidence that any replay statement holds for
an actual EVM.

Paths are relative to `EvmYul/CrossChainReplay/`. Spec sections refer to
[`cross-chain-rolling-hash-replay-spec.md`](cross-chain-rolling-hash-replay-spec.md).

## Build and check

```sh
lake build EvmYul.CrossChainReplay EvmYul.CrossChainReplay.Checks
for c in EvmYul/CrossChainReplay/Checks/*.lean; do lake env lean "$c" || exit 1; done
rg -n '\b(sorry|admit|axiom)\b' EvmYul/CrossChainReplay   # expect no matches
```

All three succeed. `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`, and `EvmYul.lean`
are unchanged. `native_decide` appears in 7 closed fixture equalities (`Checks/Spans.lean`,
`Checks/ProxyDispatch.lean`). It trusts compiled evaluation and never discharges a law or a
replay statement.

## Final statements

| Declaration | Kind | Meaning |
| --- | --- | --- |
| `ReplayPreservationStatement M p` | Full target | `SemanticInterfaceLaws M p`, `ValidAtX`, `height Y = height X + delay`, and `AllowedReplay` imply `∃ replayRun, ReplayConclusion`. The concrete protocol's laws are obligations, not premises. |
| `ReplayCompositionStatement M p` | Conditional composition | The same conclusion, with every local target below added as a hypothesis. Proving it proves none of those targets. |
| `ReplayConclusion` | Conclusion (spec section 7) | Successful `Run`, all checks passed, selected occurrence consumed, equal scoped transcripts, lookup sub-transcripts, and structural trace, committed hash equal to the reference and the expected hash, equal driving-transaction output bytes. |

## Local proof targets (`Statements.lean`)

| Declaration | Spec | Scope |
| --- | --- | --- |
| `HashPreservationStatement` | 4.2 | Append decomposition of the fold; no injectivity |
| `SetupPreservationStatement` | 8.2 | `loadBatch` on related queues at two heights |
| `FreshnessPreservationStatement` | 4.5 law 7 | Every `advanceProtocol` decision under related state and context |
| `QueueCorrespondenceStatement` | 3.3, 4.4 | Logical occurrences through load, proxy selection, cleanup |
| `ProtocolInterfaceStatement` | 4.5 | The 8 spec laws as 9 conjuncts (law 2 splits into `SelectionLaw` and part of `QueueCorrespondenceStatement`): `LoaderLaw`, `SelectionLaw`, `QueueCorrespondenceStatement`, `DispatchLaw`, `LookupLaw`, `GuardLaw`, `RollbackTransportLaw`, `FreshnessPreservationStatement`, `ObservationLaw` |
| `LocalProgressStatement` | 8.3, 9 | A related replay state at reference step `i` can step |
| `LocalPreservationStatement` | 8.3 | Every such step corresponds, re-establishes `Related`, stays in the next envelope |
| `ResourceAdequacyStatement` | 8.4 | Such a step causes no out-of-gas outcome or probe |
| `RollbackPreservationStatement` | 8.5 | `restore` of related checkpoints gives related states |
| `TransportProvenanceStatement` | 4.2.3, 8.5 | Decode inverts encode; on reachable states at entry or reverted-lookup controls (`accumulatorControl`), the accumulator folds the active scope's transcript |
| `ValidationPreservationStatement` | 8.6 | Related states at `validate` take the same branch and emit the same events |
| `CommitmentStatement` | 8.7 | Related terminal states derive corresponding outcomes |
| `ManagerDecoderCorrespondence` | 9 | Instantiation obligation for the decoder parameter; not a replay premise |

Local targets take one reference step, checkpoint, or protocol operation. None assumes a
complete future run.

## Spec-to-declaration map

| Spec | Declarations | File | Kind |
| --- | --- | --- | --- |
| 2 | `TransactionResult`, `Step.beginTransaction`, `Step.settleTransaction`, `deriveOutcome`, `DriverOutcome` | `ExecutionState`, `Execution` | Concrete |
| 3.1-3.3 | `Configuration`, `LogicalRequest`, `DriverEnvelope`, `Bundle`, `Entry`, `EntryId`, `ScopeId` | `Types`, `ExecutionState` | Concrete data |
| 3.4 | `referenceFootprint`, `replayFootprint`, `StorageLocation.space`, `AccountProjection` | `Footprints`, `Resources`, `Observations` | Concrete folds |
| 3.5 | `BoundaryRecord`, `ScopeRecord`, `scopedTranscripts` | `Hashing`, `ExecutionState`, `Statements` | Concrete |
| 4.1-4.3 | `encodeCall`, `callHash`, `foldBoundary`, `crossHash`, `foldStructural`, `foldStatic`, `decodeContextResult` | `Hashing` | Concrete over `Parameters.keccak` |
| 4.4-4.5 | `loadBatch`, `selectProxyEntry`, `selectInboundEntry`, `clearConsumed`, `findNestedLookup`, `advanceProtocol`, `managerEntryControl`, `inboundBindingError` | `Protocol` | Concrete |
| 5.1 (A0) | `Run`, `StepChain`, `ValidAtX`, `PrescribedChecksPassed` | `Execution` | Concrete |
| 5.2-5.4 (A2-A4) | `Related`, `WorldRelated`, `FramesRelated`, `CheckpointRelated`, `InitialRelated` | `Admissibility` | Concrete |
| 5.5 (A6) | `ResourcePlan`, `BudgetOK`, `LocalResourceBound`, `AdmissibleStepActions`, `StepResourceUpdate`, `AccountCompatible`, `EnvelopeFunded`, `NoGasInducedFailure` | `Resources`, `Admissibility` | Concrete over adapter `admissibleActions`, `envelopeValid` |
| 5.6 (A7) | `ProtocolRelated`, `bucketView`, `lookupView`, `Freshness`, `SetupCompatible`, `NoProtocolCoordinateAccess`, `NoUnmodeledManagerEntry` | `Admissibility` | Concrete |
| 5.7 (A8) | `HeightBounds`, `RevisionDescriptor.isPinned` | `Admissibility`, `Types` | Concrete |
| 5.8 | `AllowedReplay` | `Admissibility` | Concrete conjunction |
| 6 | `TraceAllowed`, `bannedInstructions`, `GasForwardingOnly`, `DriverAllowed`, `SameLogicalInputs` | `Admissibility` | Concrete |
| 7, 9 | `ReplayConclusion`, `ReplayPreservationStatement` | `Statements` | Targets |

## Abstract parameters and assumed laws

These are the only non-concrete inputs. Each needs a separate instantiation proof.

| Item | Where | Remaining obligation |
| --- | --- | --- |
| `Parameters.keccak` | `Types` | Relate to Keccak-256. Toy hashes only test bookkeeping. |
| `Parameters.decodeManagerEntry` | `Types` | Solidity ABI dispatch and decoding for the four manager entry points; see `ManagerDecoderCorrespondence` |
| `Parameters.revision` | `Types` | Name an immutable execution-spec revision, its enabled instructions and native operations |
| `EvmModel` fields | `EvmInterface` | Every field docstring names its obligation: storage layout (`readProtocol`, `protocolLocation`, `protocolWord`), account rules, frame and creation semantics, transaction validity (`transactionValid`, `envelopeValid`) and settlement, resource arithmetic, demand, and admissible action lists (`admissibleActions`) |
| `ProtocolViewLaws` | `EvmInterface` | One coherent world; protocol writes touch only protocol-owned slots |
| `DeterminismLaws` | `EvmInterface` | Unique primitive, frame, creation, and transaction results |
| `ProgressLaws` | `EvmInterface` | No stuck primitive, frame, creation, or transaction transitions; `envelopeValid` on a world's valuation implies `transactionValid` |
| `RollbackLaws` | `EvmInterface` | Failed frames and initializers restore their checkpoint world; transient storage is empty after begin and settle |
| `ObservationLaws` | `EvmInterface` | Transfers, functional reads, writes, and account changes are reported; primitive and begin resource actions lie in `admissibleActions` |
| `ResourceArithmeticLaws` | `EvmInterface` | Meaning of gas, refund, transfer, and nonce actions |

`SemanticInterfaceLaws` is the conjunction of the six law groups. It is the only adapter
premise of the full target.

## Meaning-sensitive choices

- **Committed result provenance.** Only protocol `.validation` events from `validate` enter
  `liveValidations`. They roll back with frames like logs. `settleTransaction` keeps them only
  when the top-level frame returns. Raw logs never become validations.
- **Driver outcome.** `deriveOutcome` succeeds only when every envelope settles successfully
  and the last transaction retains the selected occurrence's validation. A failed setup ends
  the driver (`phase = done`). `ExecutionRecord.outcome` must equal the derived outcome, so a
  record cannot assert its own result.
- **Transaction boundaries.** A failed top-level frame settles from the post-initialization
  world. Settlement clears transient manager fields, matching the source's `transient` storage.
- **Manager entry.** Application, system, and forwarding proxy frames (no pending probe) reach
  manager entry points through `managerEntryCall`. `loadExecutionTable` and
  `executeIncomingCrossChainCall` require the system caller. `loadExecutionTable` and `staticCallLookup` reject value. Inbound row-zero binding,
  peer, and value checks precede duplicate and peer preflight, as in `EEZL2.sol:313-360`. An
  application calling `executeCrossChainCall` directly fails the registry check.
- **Static permission.** A manager frame entered under static permission halts with a static
  violation at its first persistent write or log: after load preflight, or after the registry
  check for a non-static cross-chain call. Earlier errors still take precedence.
- **Cleanup.** `clearConsumed` follows `_clearConsumedEntryAndDrain`: it persists the advanced
  head and drains the bucket when no current row remains at or after the head.
- **Normalization.** `bucketView` drops rows before the head and compares contents only for
  current rows. It keeps logical identities and freshness classes for every remaining row.
  Because the head passes the active row, `ProtocolRelated` separately compares the active row
  read through `activeEntryRow`. `ContextRelated` zeroes heights inside suspended controls and
  requires each suspended load's height to equal its context height.
- **`GAS` rule.** `GasForwardingOnly` requires the frame's next instruction after `GAS` to be a
  call. A call pops its gas operand first, so adjacency means the `GAS` result is exactly that
  operand. `Related` exempts only the pending top stack word.
- **Resources.** Transaction initialization grants the target envelope's gas minus intrinsic
  gas; settlement clears frame gas. Closure then covers every action list in
  `admissibleActions` for the reference operation under the valuation, so replay costs may
  differ from reference costs. `AllowedReplay` requires `BudgetOK` twice: with the reference as
  target (reference resource conditions) and with the replay as target.
- **Conservative restrictions.** `NoProtocolCoordinateAccess` bans application storage access to
  every protocol-owned location. Manager entry points without a modeled transition (public
  getters such as `executions` and `lookupCalls` that return freshness stamps, the
  permissionless `createCrossChainProxy` and `getOrCreateCrossChainProxy`, unmatched
  selectors) reach `rejectEntry`; `NoUnmodeledManagerEntry` excludes them from the reference.
- Earlier choices remain: probe failures keep distinct causes but take the same lookup branch;
  rollback restores effective scopes and keeps attempted observations; accepted transport
  bytes change state without creating a transcript witness.

## Checks

The plan's stable check names, by task:

| Task | Names | File |
| --- | --- | --- |
| 2 | `abiLengthBoundaries`, `transportDecoderBoundaries` | `Checks/Hashing.lean` |
| 3 | `duplicateFifo`, `stalePrefixRetention`, `inboundTailSelection`, `staleRemainderDrains` | `Checks/Queues.lean` |
| 4 | `attemptedReadFootprint`, `meteringOnlyRead`, `nonzeroNonceProjection` | `Checks/Admissibility.lean` |
| 5 | `toyPrimitiveExit`, `toyInterfaceLaws` | `Checks/Driver.lean`, `Checks/Laws.lean` |
| 6 | `nestedFoldOrder`, `emptyLookupFinalFold`, `staticProbeFailureCauses` | `Checks/ProtocolOutgoing.lean`, `Checks/ProtocolStatic.lean`, `Checks/Execution.lean` |
| 7 | `ordinaryRollback`, `transportWithoutProvenance` | `Checks/Rollback.lean` |
| 8 | `committedToyDriver`, `committedToyDriverValid`, `caughtEntryFailure`, `caughtRolledBackValidation`, `suffixRevert`, `setupThenFailingDriver`, `alteredOutcomeRejected` | `Checks/Driver.lean` |
| 9 | `admissibleToyReplay`, `insufficientChildGas`, `insufficientCallFunds`, `nonceExhaustion`, `feeRecipientClassification`, `forbiddenRevertedOpcode`, `interleavedDriver`, `differingBalancesCompatible`, `readAfterWriteMismatch`, `creationTransactionExcluded`, `authorizationTransactionExcluded` | `Checks/Admissibility.lean` |
| 10 | `fullTargetPremisesSatisfiable`, `replayConclusionWitness`, `untouchedStaleBucket` | `Checks/Statements.lean` |

`Checks/ManagerEntry.lean` covers the entry-point guards above.

## Non-vacuity evidence

- `toyInterfaceLaws` and `driverToyLaws`: finite toy adapters satisfy all six law groups, so
  the law conjunction is consistent and includes progress.
- `committedToyDriver`: a complete 10-step composed `Run` of a system inbound driver derives
  its committed validation from protocol steps. No result is supplied.
- `fullTargetPremisesSatisfiable`: one adapter, reference, delay of 5, and replay satisfy every
  premise of `ReplayPreservationStatement`. The replay uses a re-signed envelope with a
  different gas limit, gas price, and block position.
- `replayConclusionWitness`: for that instance the replay at height 15 has a `Run` satisfying
  `ReplayConclusion`. The conclusion is attainable, not over-constrained.

These are toy instances. They show the definitions are satisfiable and exercise real composed
transitions. They do not prove any statement for an actual EVM.

## Known gaps and residual risks

1. **Frame-exit and settlement resources.** Unused child gas returned on frame exit, and
   settlement's refunds and fee credits, have no admissibility law. `BudgetOK` models gas as
   only decreasing within a transaction. The resource proof must relate actual valuations to
   the envelopes.
2. **Protocol resource effects.** Manager operations expose no resource actions. Their cost
   enters only through `localDemand` of the manager frame.
3. **Creation failures from gas.** `NoGasInducedFailure` inspects frame outcomes and probes. An
   immediate `CREATE2` rejection caused by gas is not recorded in state, so it is not excluded.
4. **Driver fixture scope.** The positive run covers system inbound execution with one incoming
   call through a pre-registered proxy. Proxy-route entries, outgoing reentry, lookups, and
   spans have local step checks, but no complete positive `Run`.
5. **Toy proxy.** The toy proxy frame returns fixed bytes. It does not model `executeOnBehalf`
   forwarding or ABI unwrapping.
6. **Load audit history.** Every transaction begin and every manager call consumes one
   invocation serial. A load's serial is its index in `EntryId.driverLoaded`. Reference and
   replay must therefore make the same sequence of transactions and manager calls before the
   selected load. Review whether this
   identity scheme matches the intended logical occurrence order.
7. **Static-permission timing.** Halts are placed at the first modeled write. The source's exact
   first state-changing opcode inside each entry point has not been compared opcode by opcode.

8. **Unmodeled manager functions.** Proxy creation and getters are excluded, not modeled. A
   driver that needs them is outside this model.

## Independent review

A fresh-context review on 2026-11-15 found no circularity and reported 13 findings. All are
addressed in the code and this index. The high-severity fixes were: active-row comparison in
`ProtocolRelated`; load-height consistency in `ContextRelated`; the corrected
`QueueCorrespondenceStatement` load formula (`untouchedStaleBucket` regression); the
`accumulatorControl` restriction in `TransportProvenanceStatement`; the `envelopeValid` and
nonce premises for A6; and closure over `admissibleActions` instead of the reference step's
own amounts. Medium fixes: reference resource conditions use reference envelopes;
`NoUnmodeledManagerEntry`; a fresh-load premise in `SelectionLaw`; proxy forwarding to the
manager; transient-storage reset laws.

## Not provided

- Proofs of any local target, the composition statement, or the full target.
- An Osaka or Glamsterdam `EvmModel`, or proofs of `SemanticInterfaceLaws` for one.
- Correspondence between `advanceProtocol` and compiled `EEZL2.sol` bytecode, or between the
  hash and decoder parameters and their implementations.
