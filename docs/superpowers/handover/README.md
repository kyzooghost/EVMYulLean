# Cross-chain rolling-hash Lean model handover

Recorded: 2026-11-14 UTC. Implementation is **paused at the user's request**.
This is an unfinished model, not a verified replay theorem.

The user requested this handover, a commit, and a push to the fork branch
`kyzooghost/EVMYulLean:cross-chain-rolling-hash`. Do not resume implementation
until the user starts the next session's work.

## Start here on the next machine

1. Follow [SETUP.md](SETUP.md). The original machine's project-specific Lean
   installation and build binaries are being removed after the push.
2. Read the [implementation plan](../plans/2026-11-12-cross-chain-replay-lean.md),
   [design](../specs/2026-11-12-cross-chain-replay-lean-design.md),
   [mathematical specification](../../cross-chain-rolling-hash-replay-spec.md),
   and this handover.
3. Read [the review index](../../cross-chain-replay-lean-review.md) for declarations
   and assumptions. This handover supersedes its older status for proxy deployment.
4. Inspect the current files and run the checks before relying on historical claims.
5. Resume at the remaining Task 5/6/7 acceptance audit, then implement Tasks 8-10.
   Keep the complete plan as the objective.

Use the `superpowers:executing-plans` skill with **native execution**. The user
authorized continuous implementation without approval pauses. Ask only when an
essential design decision requires user input. No such decision was pending here.

At the end of each task, give the user concise explanations of:

1. Main Lean declarations and their purpose.
2. Concrete definitions versus abstract interface dependencies.
3. Choices that affect the theorem's meaning.
4. Compiler and test results.
5. Unproved assumptions and potential vacuity.
6. Build success versus evidence of semantic correctness.

Do not weaken the model or acceptance checks to make Lean compile. Substantive
proofs are deferred until the user reviews the model and named statements.

## Repository state and scope

- Branch: `cross-chain-rolling-hash`, created from local `main` at `902f81c`.
- That pre-existing commit, `902f81c` (`new spec`), contains the 610-line Markdown
  specification. It is retained in the branch history.
- Upstream `origin` points to `NethermindEth/EVMYulLean`; the new `fork` remote
  points to `https://github.com/kyzooghost/EVMYulLean.git`.
- Model code is under `EvmYul/CrossChainReplay/`. The aggregate is
  `EvmYul/CrossChainReplay.lean`.
- Existing interpreter semantics, `EvmYul.lean`, `lakefile.lean`, `lean-toolchain`,
  and `lake-manifest.json` were not changed.
- No merge, PR, deployment, or substantive replay proof was performed.
- The original working ledger was ignored at
  `.superpowers/sdd/2026-11-12-cross-chain-replay-lean/progress.md`.
  A portable [ledger snapshot](progress-ledger.md) is included here. Earlier
  completion claims in it have explicit later corrections; use this status table.

## Agreed mathematical scope

- Deliver concrete protocol definitions plus a typed, abstract EVM adapter and
  named, **unproved** `def ... : Prop` statements for manual review.
- No `sorry`, `admit`, new axioms, or global assumption of future replay success.
- Prefer a later pinned Glamsterdam instantiation; Osaka is acceptable. Neither
  fork is instantiated in this delivery.
- Driver transactions are consecutive in one block. Exclude contract-creation
  transactions and EIP-7702 authorization transactions.
- Ban executed `CREATE` and `SELFDESTRUCT`; allow `CREATE2` with explicit funding,
  collision, resource, and nonce-headroom conditions.
- Do not require equal account nonces or balances. Preserve the relevant account
  classifications and require sufficient resources for every attempted effect.
- Include functional reads after writes and in reverted frames. Keep metering-only
  reads separate. Apply restrictions to all relevant frames without a manager exemption.
- Keep protocol state in one authoritative EVM world through `readProtocol` and
  `writeProtocol`; storage-layout correspondence remains an adapter obligation.
- `ValidAtX` must concern only a finite committed reference execution at X.
  `AllowedReplay` must not assume a future `Run`, matching future trace, or success.
- Return bytes of the complete driving transaction are distinct from cached entry
  bytes. A cached hash or subsequently reverted validation is not a committed result.

## Plan status

| Task | Current implementation | What remains before acceptance |
| --- | --- | --- |
| 1: types/toolchain | Scalar aliases, bundles, requests, bounds, logical IDs, parameters; pinned Lean works | Re-audit all signature/doc requirements and current additions. Plan checkboxes remain unchecked. |
| 2: encodings/hashes | ABI call encoding, packed folds, structural tags, error ABI, transport decoder, CREATE2 address helpers | Local correctness statements and executable-code correspondence remain unproved. Check exact acceptance names. |
| 3: queues/setup | Loader preflight, duplicate FIFO, stale-prefix handling, inbound tail selection, lookup overwrite/first match, cleanup tests | Audit authorization and source error/write order. `loadBatch` currently does not use its `Parameters` argument or caller authorization. |
| 4: observations/footprints | Attempted trace, storage reads, account projections, footprint fold, metering distinction | Adapter observation completeness and protocol-generated implicit accesses still need a full audit. |
| 5: EVM interface | Typed primitive/call/creation/transaction/resource operations, coherent protocol views, some local laws | **Incomplete law set**, especially creation, exceptional rollback, observations, resource arithmetic, determinism/progress, and full field docstrings. |
| 6: composition | Entry/reentry, static/reverted lookups, probe, manager routing, system call, generic CREATE2, proxy deployment/registration and static dispatch now have local transitions | Generic/direct manager ABI coverage, inherited-static behavior, concrete raw forwarding/unwrapping boundary audit, protocol access/resource observations, and end-to-end acceptance witnesses. |
| 7: rollback/spans | Checkpoints, attempted/effective/audit scopes, span self-call, transport decoding/adoption, provenance separation, log collection and retry serials | Perform the complete acceptance audit after Task 6 boundary coverage closes. Do not mark complete based only on local tests. |
| 8: finite runs/results | **Not implemented** | `ExecutionRecord`, `DriverOutcome`, `Run`, `ValidAtX`, retained validation/result extraction, transaction begin/settle, positive committed driver and caught-failure/suffix-revert controls. |
| 9: resources/admissibility | **Not implemented** | `Resources.lean`, `Admissibility.lean`, full A1-A8 relation/restrictions and four resource-envelope obligations, positive/negative admissibility fixtures. The existing check file named `Admissibility.lean` tests footprints/projections only. |
| 10: statements/review | Partial review index only | `Statements.lean`, `Checks.lean`, completed aggregate/index, all named propositions, full target/composition distinction, acceptance-name audit, final checks and independent review. |

## Latest completed implementation work

The paused turn added and locally checked:

- `proxyIdentityError`, `proxyRegistered`, `incomingProxyError`, and
  `registerIncomingProxy` in `Protocol.lean`.
- `ProtocolControl.readyIncoming`, which resumes a row after creation without
  incrementing its incoming cursor or folding its begin record again.
- `Step.deployIncomingProxy`, `Step.rejectIncomingProxy`, and
  `Step.resumeProxyCreation`, with code installation delegated to `exitCreation`
  and registration performed only after a successful result.
- Explicit incoming/static identity/code failure transitions.
- `staticProxyError` and corrected `Step.dispatchStatic`: deterministic address
  plus stored-code-length check, without requiring registry membership.
- Source ordering: invalid original address, rollup range, and applicable
  same-network guard precede creation. Static-value failure occurs after proxy
  availability; a missing proxy is created before that failure is raised.
- `Checks/ProxyDispatch.lean`: finite deployment -> initializer return -> registration
  -> dispatch witnesses; static dispatch with code but no registry entry; missing-code
  failure; identity guards; failed-construction unwind without registration.

The user interrupted while rerunning the final missing-code proof. Its final edit
changed a closed finite equality from `rfl` to `native_decide` to avoid Lean's
recursion-depth limit. The check was rerun successfully during handover validation.
Do not undo this as an unverified interrupted edit.

## Important implementation details

- `HashFn` is a parameter. Fixtures use deterministic toy hashes, not Keccak vectors.
- Boundary inputs are `previous32 || callHash32 || success1 || rawBytes`.
  Hashes start at zero; proxy roots add a final record, inbound roots do not.
- Lookup folds use separate scopes. Successful nested completion order is checked
  as `B, Q, A, root`. Ordinary rollback removes Q from an enclosing transcript if A reverts.
- `processIncoming`/`resumeIncoming` carry both original count and local processed
  count. The shared cursor can also advance through descendants.
- Active lookup tables use an optional nested-row index and optional top-level host
  hash into `ProtocolState`, not independent copies of mutable arrays.
- Span transport accepts the source selector and at least 164 bytes, including trailing
  bytes and a raw ignored Boolean word. Arbitrary accepted values update actual state.
  `TransportEvidence` is a separate candidate provenance record, not a decoding guard.
- `completedScopes` and attempted observations are audit history; rollback restores
  effective scopes and live logs. `nextInvocation` also survives rollback.
- Manager frame roles gate concrete protocol control. Call kinds distinguish `CALL`,
  `STATICCALL`, `DELEGATECALL`, and `CALLCODE`.
- The 1000-gas self-probe is a nested call. Both static violation and out-of-gas route
  to lookup while retaining distinct causes. Later resource conditions must exclude
  gas-induced routing changes.
- Creation has a separate checkpoint after parent nonce/gas effects and before child
  effects. Failed initialization restores child state while retaining parent effects.
- Protocol failures are retained even before a scope exists. Expected cached lookup
  reverts do not themselves add a protocol-failure observation.
- Some finite witnesses use `native_decide`. They establish closed fixture equalities,
  not the substantive local laws or replay theorem.

## Recommended next actions

1. Re-run setup and the available checks. Read `ProxyDispatch.lean` and the creation
   adapter contracts before extending this area.
2. Audit Task 6 against the actual source, with these remaining risks first:
   - Ordinary application calls to manager ABI entry points are not generally routed;
     the modeled gateway currently recognizes proxy forwarding after a probe.
   - Executing mutable manager logic under inherited static permission needs exact
     source failure behavior. Do not add an unstated restriction to hide the gap.
   - Manager-only `executeOnBehalf` forwarding and successful ABI unwrapping need a
     complete concrete-boundary versus EVM-adapter correspondence audit.
   - Protocol operations do not yet expose every functional storage/account access
     or resource effect. Calling `writeProtocol` is not an observation-completeness proof.
   - Check system-only load/inbound entry authorization; the Solidity modifier is
     outside the current pure loader.
   - Review stale-head writes on misses and cleanup against `_nextFreshHead` and
     `_clearConsumedEntryAndDrain`; current error-return interfaces may omit tentative
     writes visible to callbacks. This is an audit risk, not a proved counterexample.
3. Complete Task 5's local law set for the new operations. Determinism alone permits
   stuck or resource-sensitive adapters. Do not silently assume local/global replay.
4. Audit Task 7's full acceptance conditions and stable check names. Then implement
   Task 8 transaction sequencing and committed-result provenance. `topLevelExit`
   currently clears the pending outcome without preserving a driver terminal result.
5. Implement Task 9 literally from spec section 5.8 and section 6. Resource plans must
   quantify local arithmetic transfers and adequate bounds without consulting a future run.
6. Implement all Task 10 proposition definitions with the plan's exact quantifier shape.
   The full target assumes only the stated semantic interface laws plus reference
   validity/admissibility. Concrete protocol lemmas are proof targets, not extra full-target
   assumptions. Keep the separate conditional composition statement.
7. Complete required tests, assumption/vacuity audit, declaration-to-spec mapping,
   and the executing-plans workflow's final independent review. No such final review
   has occurred yet.

## Verification at handover

All commands below exited 0 on the original macOS arm64 machine, before cleanup:

```sh
lake env lean --version  # Lean 4.22.0
lake build EvmYul.CrossChainReplay EvmYul.CrossChainReplay.Checks.Fixtures
```

Each of these 15 files was run directly with `lake env lean` and passed:

```text
Admissibility.lean  Bookkeeping.lean      Creation.lean
Execution.lean      Fixtures.lean         Hashing.lean
Manager.lean        ProtocolControl.lean  ProtocolOutgoing.lean
ProtocolReverted.lean ProtocolStatic.lean ProxyDispatch.lean
Queues.lean         Rollback.lean         Spans.lean
```

They are under `EvmYul/CrossChainReplay/Checks/`. No failed check was suppressed.
The aggregate `EvmYul.CrossChainReplay.Checks` does not exist yet; the plan's final
aggregate command cannot be claimed passed.

The forbidden-placeholder search found no `sorry`, `admit`, or `axiom` in the model
directory. Dependency pins were unchanged. There is no concrete fork instantiation,
bytecode correspondence proof, replay proof, or completed positive `Run`/admissibility
witness. Missing transitions and incomplete laws remain possible sources of vacuity.

## Source contracts needed on the new machine

The Solidity checkout is separate and is not included in this branch. Its old path was:

```text
/Users/jefferson/Desktop/Repos/2026/lineth-enterprise-main/linea-besu-enterprise/
```

The copied source tree had no usable Git metadata, so no commit ID or clean-worktree
claim is available. Obtain those files separately and compare SHA-256 fingerprints:

| Relative path | SHA-256 |
| --- | --- |
| `plugins/xcall/contracts/src/L2/EEZL2.sol` | `7fe5a3e966d7484ee012d79b5cf6977b633d015c24d80ff17ddf6b7b9ba39f39` |
| `plugins/xcall/contracts/src/base/EEZBase.sol` | `b90a9b53979861a26df858391fba5e2d9e768e11d014ca5d026a0e35bdaa5fb2` |
| `plugins/xcall/contracts/src/base/CrossChainProxy.sol` | `f3eda9adc0d86880fedaf8a20f7cc2fc81aacc4c400f087bb31ee800a655e4d7` |
| `plugins/xcall/contracts/src/interfaces/IEEZL2.sol` | `5a7c0d4b0db15b7f94953081b7575939282349c863a9c812358bdfa360f5433f` |

Useful source anchors: EEZL2 system modifier/load at lines 99/118, proxy gateway at
256, inbound entry at 313, outgoing consumption at 475, entry execution at 600,
span executor at 680, incoming loop at 688, reverted lookups at 790-875,
static processing at 889, and static lookup at 933. Recheck line numbers on a new copy.
