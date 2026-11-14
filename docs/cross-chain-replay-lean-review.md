# Cross-chain replay Lean review index

Status: partial implementation. Tasks 6 and 7 remain open. The finite-run model,
resource conditions, admissibility predicate, and replay statements from Tasks
8-10 are not implemented. This index does not mark their acceptance checks as passed.

Implementation is paused. See the [handover](superpowers/handover/README.md) and
[fresh-machine setup](superpowers/handover/SETUP.md) for current status and resumption.

## Declarations available for review

Paths below are relative to `EvmYul/CrossChainReplay/`.

| Declaration | File | Purpose | Status |
| --- | --- | --- | --- |
| `Parameters`, semantic row types, `EntryId`, `ScopeId` | `Types.lean` | Fix inputs and distinguish logical occurrences from bucket positions | Concrete data; hash function remains a parameter |
| `encodeCall`, `foldBoundary`, `crossHash`, `foldStructural`, `foldStatic` | `Hashing.lean` | Define source byte encodings and hash folds | Concrete functions over the supplied hash function |
| `proxySalt`, `proxyInitCode`, `proxyAddress` | `Hashing.lean` | Define the proxy CREATE2 address calculation | Concrete encoding; creation-code bytes and hash function are parameters |
| `decodeContextResult` | `Hashing.lean` | Decode the selector and five words, accepting trailing bytes | Concrete; decoding does not establish provenance |
| `loadBatch`, `selectProxyEntry`, `selectInboundEntry`, `findNestedLookup`, `clearConsumed` | `Protocol.lean` | Model queue and lookup selection | Concrete local functions; correctness laws remain unproved |
| `advanceProtocol`, `activeCalls`, `activeOutgoing` | `Protocol.lean` | Advance entry, outgoing-row, and nested static/reverted-lookup control | Partial protocol coverage |
| `referenceFootprint`, `accountProjection` | `Footprints.lean`, `Observations.lean` | Collect attempted functional inputs and compare account classifications | Concrete folds; completeness depends on adapter observations |
| `EvmModel`, `SemanticInterfaceLaws` | `EvmInterface.lean` | Specify the primitive EVM adapter and its local obligations | Abstract interface and unproved law predicate; law set remains incomplete |
| `FrameRole`, `ProbeResult`, `ExecutionState` | `ExecutionState.lean` | Track active frame ownership, probe outcomes, and shared execution state | Concrete bookkeeping over abstract world/frame types |
| `checkpoint`, `restore`, `adoptTransport` | `Rollback.lean` | Restore effective state and adopt decoded transport values | Concrete bookkeeping; world semantics depend on the adapter |
| `Step`, `Step.proxyProbe`, `Step.resumeProbe`, `probeUsesLookup` | `Execution.lean` | Compose local transitions and preserve the probe's failure cause | Partial transition relation |
| `failureTrace` | `Execution.lean` | Retain protocol failures even before scope selection | Concrete; cached expected reverts remain a separate outcome |
| `ManagerInvocation`, `managerCallHash`, `Step.managerCall`, `Step.dispatchSystem`, `Step.resumeSystem` | `ProtocolState.lean`, `Protocol.lean`, `Execution.lean` | Authorize proxy forwarding and compose the system transfer before routing | Concrete control over abstract EVM calls; remaining boundary coverage is open |
| `setIncomingSpan`, `Step.dispatchSpan`, `Step.resumeSpan`, `Step.protocolSpanResult`, `Step.protocolAdoptSpan` | `Protocol.lean`, `Execution.lean` | Clear/restore span storage, execute a self-call, restore world effects, and adopt decoded values | Concrete composition over abstract frame entry/exit |
| `TransportEvidence`, `spanScopeAdoption`, `completedLookupScope` | `ExecutionState.lean`, `Execution.lean` | Track candidate transport provenance and completed lookup audit scopes | Concrete bookkeeping; provenance correctness remains unproved |
| `create2Address`, `CreationResult`, `Step.engineCreate2`, `Step.rejectCreate2`, `Step.resumeCreation` | `Hashing.lean`, `EvmInterface.lean`, `Execution.lean` | Derive CREATE2 addresses and compose creation entry/failure/unwind | Concrete composition; creation setup, code installation, and resource rules remain adapter obligations |
| `proxyIdentityError`, `registerIncomingProxy`, `Step.deployIncomingProxy`, `Step.resumeProxyCreation`, `staticProxyError` | `Protocol.lean`, `Execution.lean` | Create/register missing proxies and dispatch through deterministic proxy addresses | Local composition and fixtures pass; complete boundary/adapter-law audit remains open |

## Meaning-sensitive choices

- Manager control requires a manager frame at the top of the role stack. Application
  and proxy primitive execution cannot independently advance manager control.
- Successful outgoing rows process their assigned local iterations before adding
  their own completion record. The local regression checks `B, Q, A, root`.
- Static lookup resolution preserves the enclosing transient lookup index. It uses
  a separate hash scope and does not reset the enclosing accumulators.
- Reverted nested lookup control resets both hashes and cursors, uses its own call
  and outgoing arrays, and retains the host lookup table. Outgoing fallback matches
  using the cursor value before its tentative increment. Structural validation
  precedes the final lookup fold; hash and consumption checks precede the cached revert.
- A probe call has an exact gas cap of `1000`. Every unsuccessful outcome selects
  the source's lookup branch. The recorded outcome still distinguishes static
  permission failure from out-of-gas. Resource admissibility must later exclude
  gas-induced routing changes.
- Frame restoration discards effective child folds and logs but retains attempted
  observations. A checked example completes Q inside A, then reverts A; only A's
  failure record survives in the enclosing accumulator.
- Accepted transport bytes update actual hashes and cursors without creating a
  transcript witness. Format validity and semantic authenticity remain distinct.
- Span execution keeps its owning frame's count and processed count separately
  from the shared incoming cursor. Active lookup tables use storage references
  into the protocol world. The span self-call inherits the current accumulator;
  its reverted world/log effects are restored before decoded values are adopted.
- A span executor can produce candidate transcript evidence. Arbitrary accepted
  bytes cannot produce that evidence. Completed lookup scopes have separate audit
  history that survives an expected revert.
- Engine observations add their actual raw logs to the live log list. Rollback
  removes live logs and retains attempted observations. Manager entry assigns an
  audit invocation serial that survives rollback; repeated attempts have distinct
  scope paths.
- Creation entry saves a checkpoint after the parent nonce/gas effects and before
  child effects. Failed initialization restores that checkpoint. The resumed parent
  receives the creation result through the adapter; creation failure alone does not
  revert the parent frame.
- Every composed protocol-error transition records its failure in attempted history.
  Its scope is optional because authorization and selection can fail before a scope
  exists. A cached expected lookup revert does not itself record a protocol error.
- Recognized proxy forwarding uses the completed probe outcome, including its failure
  cause. Manager success bytes receive the ABI wrapper. System value transfers enter
  an actual child frame before dispatch. Call requests retain the EVM call kind, so
  delegated execution does not acquire manager-frame ownership by its code target.

## Checks and their limits

The model aggregate builds with Lean 4.22.0. The check files for hashing,
queues, footprints/account projections, protocol entry control, static lookup,
outgoing order, composed execution, and rollback pass when run directly with
`lake env lean`. `Checks/Fixtures.lean` also builds.

The fixtures use deterministic toy hash functions and toy EVM adapters. Probe call
and unwind witnesses demonstrate that these local constructors can execute. They
do not establish TSTORE semantics, real gas costs, or an Osaka/Glamsterdam model.
The build establishes elaboration and the finite assertions establish their stated
examples. Neither establishes the replay theorem or deployed-bytecode correspondence.

## Open acceptance requirements

1. Complete generic manager-boundary coverage, inherited-static failure behavior,
   proxy-deployment audit, return-byte unwrapping, and callback coverage.
2. Audit the complete lookup/span acceptance checks and committed-run provenance.
3. Complete local adapter laws for frame effects, observations, resources, and
   protocol/raw-storage coherence.
4. Define finite driver runs, transaction initialization/settlement, retained
   validation provenance, and successful committed results.
5. Define concrete restrictions and resource envelopes without assuming replay
   execution, then supply a positive finite execution/admissibility fixture.
6. Define the named local statements, full replay target, and separate composition
   target. Their proofs remain deferred for manual model review.

Until these requirements are met, missing transitions can make executions stuck.
An arbitrary adapter can also be stuck or fail the eventual interface laws. Thus
current compilation cannot establish that a future replay proposition is useful
or nonvacuous. No concrete fork or contract implementation has been verified.
