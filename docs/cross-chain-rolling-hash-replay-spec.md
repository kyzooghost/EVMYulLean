# Cross-chain rolling hash preservation under delayed execution

Status: proposed theorem specification for independent audit. No formal proof is claimed.

This document defines its terms, protocol behavior, assumptions, and proof obligations. Its hash description follows the inspected `EEZL2.sol` source and inherited helpers identified in Section 12. The description is self-contained; those files are provenance for review, not prerequisites for reading it. Source inspection is not a proof of bytecode correspondence.

## 1. Required result

Assume that an execution bundle is valid for a logical request in a reference execution at block X. Prove that the same semantic bundle and logical request can execute successfully at block X+Y and produce the same validated `crossChainRollingHash`, for every natural number Y whose replay configuration satisfies the conditions below.

Initial bundle validity is an assumption. Proving that a plugin constructs valid bundles is outside this theorem.

Successful replay is part of the conclusion. The theorem must not assume that the future execution succeeds, passes its hash checks, or produces the reference transcript.

The objective is a sufficient set of conservative restrictions, not the smallest possible set or a characterization of every safe replay. The first deliverable is a mathematical theorem. A later Besu plugin may implement checks that imply its premises; this document does not require an executable admission algorithm.

The first theorem uses conservative restrictions on observations. It does not admit otherwise prohibited opcodes through branch-dependency analysis or application-specific proofs that their results are harmless.

## 2. Scope and execution outcomes

The primary theorem concerns one selected occurrence of an execution entry on one chain. Other entries and lookups used by the driving transaction are part of the required bundle and execution scope.

The **driver** is the specified sequence of protocol setup transactions followed by the complete transaction that invokes the selected entry. A receiver-side driver may load and execute atomically in one transaction. A sender-side driver may load the tables in an earlier transaction in the same block.

In each run, the driver transactions are consecutive within one block. No unrelated transaction or external system operation may interleave them. Their own transaction initialization and settlement remain covered. The driver prestate is taken immediately before its first transaction, after any preceding block-level operations.

Coverage includes application code before and after the selected entry, all calls made by the driving transaction, and all required setup. This prevents an unchecked caller prefix from bypassing the entry, or an unchecked caller suffix from reverting after it executes.

The driver has one of two outcomes:

- **Success:** every required setup transaction succeeds, the driving transaction commits successfully, and the selected entry completes its protocol checks. The result contains its committed validation event and hash.
- **Failure:** setup aborts before the driving transaction, the driving transaction fails or reverts, or it commits without a retained validation result for the selected occurrence. The result contains no committed hash for that occurrence from the driving transaction.

A candidate hash computed inside a reverted frame is not a successful result. A hash supplied in the bundle is an expected value, not evidence of successful execution.

A successful transaction receipt alone is insufficient: a caller can catch an entry-call revert, or catch a later revert that rolled back an earlier nested entry result. Success here requires the selected occurrence's validation event to survive in the committed receipt. Separate setup transactions are not rolled back if a later transaction fails.

Inner calls may intentionally revert or fail a static-mode check. Such failures may be caught and represented in the bundle. Driver success does not require every inner call to succeed.

The theorem guarantees execution behavior when the driver runs in an admissible configuration. It does not guarantee transaction inclusion or a bound on waiting time.

## 3. Definitions

### 3.1 Reference and replay configurations

A configuration contains:

- The EVM revision, gas rules, precompile behavior, and chain-specific execution rules.
- Block header, block history, chain identity, and other execution environment inputs.
- Persistent account state: code, storage, balances, nonces, and account structure.
- Concrete transaction envelopes and the protocol driver.
- The initial call context and transaction-local state of each externally specified transaction.

Let `C_X` be the reference configuration at height X. Let `C_Y` be a proposed replay configuration at height X+Y. These are alternative executions from their respective prestates. The reference simulation need not have been included on-chain.

If a sender nonce has advanced, replay uses a newly signed transaction with the correct nonce. It need not reuse the original signed bytes.

### 3.2 Logical request

A logical request fixes the root sender identity, destination, calldata, ETH value, chain identity, execution route, and static or non-static mode. It also fixes any transaction data observable under the selected EVM rules.

The execution route distinguishes a call initiated through an authorized cross-chain proxy from a system-initiated inbound call. The route is preserved during replay.

Concrete nonces, signatures, fee fields, and gas limits may differ where they are unobservable to application behavior and satisfy the remaining conditions. Changing a nonce is not permitted to change an executed contract address or another required input.

Every driver transaction has a destination; contract-creation transactions are excluded. EIP-7702 authorization transactions are also excluded from both setup and execution. Existing delegated accounts remain permitted when their delegation indicators and resolved code satisfy A3. Any additional transaction type introduced by the selected revision requires an explicit initialization, validity, and settlement model before admission.

### 3.3 Execution bundle and selected entry

A semantic execution bundle contains the selected entry, other required entries, and required top-level lookup records. All arrays retain their order and multiplicity.

An execution entry contains:

| Field | Meaning |
| --- | --- |
| `declaredPeerRollup` | Counterparty chain identity for the entry's accumulator. |
| `proxyEntryHash` | Cross-chain call hash identifying the entry's request. |
| `incomingCalls` | Ordered flat table of calls executed locally, including calls assigned to reentrant frames. |
| `expectedOutgoingCalls` | Ordered table of successful outgoing calls, with expected return bytes and local-call counts. |
| `expectedLookups` | Context-keyed static or reverting lookup records, including their sub-executions and expected hashes. |
| `callCount` | Number of outer-frame processing iterations. |
| `returnData` | Expected top-level return bytes. |
| `rollingHash` | Expected structural rolling hash. |
| `crossChainRollingHash` | Expected boundary-call rolling hash. |

Each incoming-call row fixes its target address, value, calldata, source address, source rollup, static mode, and revert-span information.

Outgoing rows fix their call hashes, return bytes, and processing counts. Lookup rows fix their call hashes, return/revert bytes, success/failure modes, context keys, sub-call tables, counts, and expected hashes.

An entry occurrence is identified by its position in the driver's logical consumption order, not merely by its hash. Duplicate hashes may denote separate FIFO occurrences.

The stored `loadedBlock` field is operational metadata. It is excluded from the semantic bundle. Replay reloads the same payload with the current block's freshness stamp.

### 3.4 Storage and account footprints

A persistent storage location is `(chain identity, storage-owning address, slot)`. For delegated execution, the storage owner can differ from the address supplying code.

Let `t_X` be the full finite reference trace, including transaction initialization and settlement and all attempted frames. Its observation history is retained even when EVM state or logs roll back. Define:

| Set | Membership rule |
| --- | --- |
| `StorageReads(t_X)` | Every location read by `SLOAD` or a modeled native/protocol operation for a functional result or decision. Include reads after earlier writes and reads in failed or reverted frames. |
| `MeteringReads(t_X)` | Storage and account inputs consulted only to calculate costs or refunds, including original storage values. These belong to the resource proof; they do not independently require value equality. |
| `Accounts(t_X)` | Every address whose code, account metadata, balance, or nonce is read or changed by a reference transition. Include implicit accesses: senders, recipients, storage owners, code providers, delegation targets, creation targets, fee recipients, and account clearing. |

A slot can belong to both storage sets. Classify accesses by the selected semantics, not by whether an implementation happens to fetch data from its database. For an absent account or missing slot, the storage read value is zero.

Set `S = StorageReads(t_X)`. Set `A` to `Accounts(t_X)` extended with the replay envelopes' senders and destinations and the replay configuration's transaction-initialization and settlement recipients. These extensions are computed from specified inputs, not a future execution trace. A revision with additional implicit account accesses must enumerate their input-derived addresses or prove that they are already covered.

Protocol locations modeled by `P` use its logical state relation, including freshness normalization. All other locations in `S` use literal initial-value equality. This exception is attached to specified protocol coordinates, not to every slot at the manager address. Application access to a normalized-away coordinate remains prohibited.

These finite sets are conservative: an overwritten-then-read slot is still included, and an irrelevant read is not removed. The proof must derive that replay follows the same functional accesses and cannot diverge to an uncovered access. It must not collect a future footprint and assume equality on that footprint.

### 3.5 Boundary completion records

A boundary completion record is:

```text
(crossChainCallHash : 32 bytes,
 success            : Boolean,
 returnData         : finite byte sequence)
```

For a failed boundary call, `returnData` means the exact revert or failure bytes reported at that boundary.

A **scoped transcript** is the effective ordered list of records represented by one accumulator after applying its rollback and transport rules. The selected entry and each lookup sub-execution have their own scopes. Repeated identical records remain separate occurrences. An ordinary frame revert discards its additions to an enclosing accumulator; a validated revert-span transport explicitly restores the transported additions.

Transcripts are mathematical observations of execution. They are not identified with committed EVM logs. A reverted lookup retains a separately checked sub-transcript in the mathematical execution record even though its state and logs are discarded. The audit trace of attempted protocol checks also retains checks from reverted frames; it is distinct from the effective transcript used to compute an enclosing hash.

## 4. Protocol and hash semantics used by the theorem

These definitions fix the relevant protocol behavior for this specification and describe the inspected L2 implementation. The separate `rollingHash` checks execution structure; it must not be substituted for `crossChainRollingHash`. The theorem is parameterized by a protocol transition system `P`, with the interface in Section 4.5. Connecting executable bytecode to a concrete `P` remains a proof obligation.

### 4.1 Cross-chain call identity

The call hash is the Keccak-256 hash of the ABI-encoded tuple:

```text
(isStatic, sourceAddress, sourceRollupId, targetAddress,
 targetRollupId, value, zeroCallGas, data)
```

The types are `(bool, address, uint256, address, uint256, uint256, uint64, bytes)`. `zeroCallGas` is the constant zero. It is not the transaction gas limit or actual gas forwarded to a call.

For this tuple, ABI encoding has eight 32-byte head words. Integers use unsigned big-endian encoding, addresses have 12 leading zero bytes, and a Boolean is zero or one. The last head word is the offset 256. The tail contains a 32-byte data length, the data bytes, and zero padding to a multiple of 32 bytes.

The implementation validates both rollup IDs as at most `2^63 - 1`, although their ABI fields are `uint256`. The local `ROLLUP_ID` must be nonzero; zero is the mainnet sentinel. These are protocol validity checks, not extra bytes in the hash.

The tuple's coordinates depend on the boundary direction:

| Boundary | Source coordinates | Target coordinates | Mode and value |
| --- | --- | --- | --- |
| Incoming row executed locally | Row's `sourceAddress`, `sourceRollupId` | Row's `targetAddress`, local `ROLLUP_ID` | Row's `isStatic`, `value` |
| Outgoing proxy call | Supplied original caller, local `ROLLUP_ID` | Authorized proxy's `originalAddress`, `originalRollupId` | Non-static, manager call's `msg.value` |
| Outgoing static lookup | Supplied original caller, local `ROLLUP_ID` | Authorized proxy's `originalAddress`, `originalRollupId` | Static, zero value |

Incoming rows hash their `data`; outgoing calls and lookups hash the supplied original calldata. Proxy addresses and manager forwarding calldata are not substituted for these logical coordinates.

### 4.2 Cross-chain rolling hash

Let `K` be Keccak-256, `||` be byte concatenation, and `Z` be 32 zero bytes. Define:

```text
F(previous, callHash, success, returnData) =
  K(previous || callHash || BooleanByte(success) || returnData)

crossHash([]) = Z
crossHash(records) = leftFold(F, Z, records)
```

`BooleanByte(false)` is one zero byte. `BooleanByte(true)` is one byte with value one. No length word or padding is added to `returnData` in this fold.

Both `_crossChainRollingHashFold` and `_crossChainRollingHashStaticFold` implement `F` using `keccak256(abi.encodePacked(...))`. Each fold input has `65 + returnData.length` bytes. It has no structural tag, call counter, peer field, freshness stamp, or extra ABI wrapper. The call hash already binds the source and target identities.

#### 4.2.1 Accumulator lifecycle and fold points

| Path | Initial accumulator | Records added, in order | Final action |
| --- | --- | --- | --- |
| Proxy-originated entry: `_consumeAndExecute` | Transient accumulator reset to `Z` | Process assigned incoming calls and reentry; append `(proxyEntryHash, true, entry.returnData)` | Check against `entry.crossChainRollingHash` |
| System inbound entry: `executeIncomingCrossChainCall` | Transient cross-chain accumulator reset to `Z` | Process incoming rows; row zero represents the root inbound call | Check against `entry.crossChainRollingHash`; no extra root fold |
| Matched successful outgoing row: `_consumeNestedAction` | Continue the active transient accumulator | Process the row's assigned local iterations; append `(row.crossChainCallHash, true, row.returnData)` | Return cached bytes; enclosing scope performs the hash check |
| Static lookup: `_resolveStaticLookup` | Local accumulator starts at `Z` | Process every incoming row by static call; append `(lookupHash, !failed, cachedReturnData)` | Check the lookup hash; return cached bytes or revert with them |
| Reverted lookup: `_executeRevertedLookup` | Reset transient hashes and cursors for a separate sub-execution | Process assigned calls and reentry; append `(lookupHash, !failed, cachedReturnData)` | Check lookup hashes and consumption; revert with cached bytes |

The non-static fallback selects only lookup rows with `failed = true`. The static lookup path can select either outcome. The invocation path selects static or reverted execution; `failed` alone does not select the path.

Each ordinary `_processNCalls` iteration advances the incoming cursor, dispatches through the source proxy, then appends `(rowCallHash, actualSuccess, actualReturnData)`. Any surviving reentrant folds occur before that incoming-call completion. The row is hashed even when its call fails. A protocol error before the fold is not a completed boundary record.

Static lookup sub-calls use local hash variables, require static zero-value rows without revert spans, and require already deployed source proxies. They process the entire incoming array in array order without advancing the transient incoming or outgoing cursors. This path does not execute the lookup's `expectedOutgoingCalls` or use its `callCount`; reverted lookup processing does. Even an empty lookup sub-call array gets the final lookup record: its cross-chain hash is `F(Z, lookupHash, !failed, cachedReturnData)`, not `Z`.

`executeIncomingCrossChainCall` resets the cross-chain accumulator but relies on the required clean transient context for the structural accumulator and cursors. `_consumeAndExecute` and reverted lookup processing explicitly reset both hashes and both cursors. The formal model must preserve this distinction.

#### 4.2.2 Which return bytes are hashed

Incoming-call records use the raw bytes returned by the low-level call to the source proxy. Its manager-only `executeOnBehalf` path forwards the destination's return or revert bytes unchanged. It does not ABI-encode those bytes again.

Outgoing and lookup completion records use the cached bytes in the matched row. The manager's successful external `bytes` return has an ABI wrapper, which the outgoing proxy decodes before returning to its caller. That wrapper is not part of the fold. Revert bytes are forwarded without a success wrapper. System inbound execution also returns `entry.returnData`, but its root hash record uses the actual row-zero outcome; it does not separately fold those cached entry bytes.

#### 4.2.3 Rollback, lookup isolation, and revert spans

An ordinary revert restores the transient accumulator and cursors to the frame checkpoint. Suppose incoming call A triggers outgoing call Q, Q completes, and A then reverts. Q's accumulator updates are discarded. The enclosing processor folds A's failure record into its restored accumulator. A transcript that retained Q's discarded fold would compute the wrong hash.

Lookups have separate hash scopes. A static lookup never writes the enclosing accumulator. A reverted lookup resets and checks its own accumulator, then its terminal revert restores the caller's accumulator and cursors. Neither path appends its lookup record directly to the enclosing scope. A later enclosing incoming-call completion may still include bytes or a success flag affected by that lookup.

A positive `revertSpan` is the deliberate exception to ordinary rollback. The processor clears the first row's span temporarily and makes a self-call to process the span. This self-call starts from the active accumulator, not `Z`. It ends by reverting with `ContextResult`, transporting both hashes and the two cursors. The caller validates and decodes that payload, adopts the transported values, restores the span field, and advances its own iteration count by the span. State changes and logs from the self-call remain reverted. No additional failure record for `ContextResult` itself is folded.

The transport selector is the first four bytes of Keccak-256 over the UTF-8 string `ContextResult(bytes32,uint256,uint256,bool,bytes32)`. The L2 executor emits `false` for the Boolean word; the receiving L2 processor ignores that word. The decoder checks the selector and minimum length, accepts trailing bytes, and reads the five words directly. These format checks alone are not an authenticity proof.

The effective transcript therefore follows completion order with rollback and transport, not incoming-array order or committed-log order. For example, if incoming A triggers outgoing Q, whose assigned local call is B, and all succeed, their fold order is B, Q, A. A proxy-originated entry then appends its root record; a system inbound entry does not.

Equal scoped transcripts imply equal cross-chain hashes. This direction requires deterministic hashing, not collision resistance or an injectivity assumption.

### 4.3 Other entry checks

The structural rolling hash starts at `Z`. Its tagged records are:

```text
callBegin(n):        K(previous || byte(1) || word256(n))
callEnd(n, s, d):    K(previous || byte(2) || word256(n) || BooleanByte(s) || d)
nestedBegin(n):      K(previous || byte(3) || word256(n))
nestedEnd(n):        K(previous || byte(4) || word256(n))
```

Here `word256` is a 32-byte unsigned big-endian word. Call and nested-frame numbers are one-indexed. Call-end numbering uses the current shared incoming-call cursor, including any advancement caused by reentry.

Static lookup sub-calls use a separate structural fold `K(previous || BooleanByte(success) || returnData)`.

Normal entry processing checks both expected hashes, complete incoming-call consumption, and complete successful outgoing-call consumption. It also enforces the applicable authorization, peer, call-identity, value, lookup-context, static-mode, and revert-span rules. Reverted lookup processing checks its own hashes and consumption before returning its specified revert result.

After the normal entry checks, `EntryExecuted` reports the bucket-local entry index, declared peer, structural hash, cross-chain hash, final incoming cursor, and outgoing count. Correlate it with `ExecutionConsumed` and the logical occurrence; an index alone can be reused after a bucket drains. Its survival in the driving transaction's receipt is the committed validation result required by Section 2. Lookup hash checks do not emit this entry-validation event.

An expected inner revert that passes its prescribed sub-execution checks is not a protocol failure. A protocol mismatch that can be caught by application code must still be distinguished from an expected application revert when stating that all prescribed checks passed.

### 4.4 Freshness and consumption

Loading at height h assigns `loadedBlock = h + 1`. A current record has that stamp; zero denotes an absent or consumed record. A record left loaded at X cannot be treated as fresh at X+Y without reloading.

Proxy-driven consumption selects the next current, unconsumed occurrence in the matching per-hash FIFO. System-driven inbound execution uses the selected newly loaded occurrence. Inbound execution binds the externally supplied request hash, the first incoming row's call hash, and the selected entry's `proxyEntryHash`.

Loading and consumption occur in the same block of the relevant chain. Top-level lookups must also be current when used.

### 4.5 Protocol transition-system parameter

The protocol parameter is explicit. `P` supplies a deterministic transition function, its initial-state interpretation, the driver entry points, and projections for validation checks and scoped transcripts. `Run` executes these transitions together with the fixed EVM semantics. These functions must be defined before a concrete theorem can be checked in Lean; they are not supplied by an external document.

Protocol state includes the proxy registry, ordered per-hash entry buckets and heads, top-level lookups, active entry or lookup context, incoming and outgoing cursors, and both hash accumulators. Rollback uses the EVM's frame checkpoints. A check projection records each prescribed protocol predicate's identity and Boolean result, including predicates evaluated inside subsequently reverted frames. Expected application failure is a separate observation.

A concrete `P` must prove the following local interface laws. These laws specify protocol operations, not future success or equality of complete executions.

1. **Loader law.** Reject duplicate top-level lookup hashes within a load and malformed peer/value/static rows. For each loaded entry hash, discard its old bucket only if no current unconsumed entry remains at or after its head. Otherwise retain that remainder and append new occurrences in input order. Overwrite each loaded top-level lookup by hash. Assign the current stamp to loaded records.
2. **Selection law.** Proxy consumption skips consumed or non-current rows and selects the first remaining occurrence at or after the head. It advances the head, binds the selected occurrence as active, and rejects missing or peer-mismatched entries. System-driven inbound execution selects its newly pushed occurrence, marks it consumed, and enforces the three-way hash binding in Section 4.4. Successful cleanup clears the selected occurrence and resets a fully drained bucket.
3. **Dispatch and partition law.** Process outer calls according to `callCount`, using one shared incoming cursor. A matched successful outgoing row advances the outgoing cursor and processes that row's assigned incoming-call iterations before returning cached bytes. The same cursor is shared across reentry. Revert spans count iterations of their owning frame, not all descendant flat rows. Enforce the terminal consumption checks in Section 4.3.
4. **Lookup law.** An in-execution lookup selects from its active host's nested table using the tuple `(callHash, incomingCursor, outgoingCursor, lookupContext)`. Context is zero at host level, and one plus the active nested-lookup row index inside a reverted nested lookup. A deeper nested lookup continues to use its host's table. A top-level lookup uses its call hash and requires current freshness. Search nested lookup rows in array order and select the first matching row; non-static fallback additionally requires `failed = true`. Preserve invocation-selected static/reverted mode and peer validation. Reverted outgoing fallback uses the outgoing cursor value from before its tentative increment; failure rolls that increment back.
5. **Guard law.** Authorization uses fixed system/manager identities and the registry's caller identity. Incoming rows have the declared peer; matched successful outgoing calls target the active peer. In a normal table load all incoming values are zero. In atomic system-inbound execution, only the first entry's root incoming row may carry value, and it equals the attached value. Static rows carry zero value and no revert span. A positive revert span must fit within the remaining iterations of its active frame. Lookup call hashes, context keys, declared modes, and expected hashes are checked as described above.
6. **Rollback and transport law.** Reverting a frame restores persistent and transient state according to the fixed EVM rules. Static and reverted lookups check their scoped hashes and return or revert with their specified cached bytes. Revert-span processing temporarily clears its first row's span, invokes the self-only span executor, and obtains a terminal revert payload. The payload has a four-byte context-result selector followed by five ABI words: structural hash, outgoing cursor, incoming cursor, deferred-failure flag, and cross-chain hash. Decode only with the expected selector and at least 164 bytes. Adopt the decoded hashes and cursors as specified, restore the span field, and advance the owning frame by its span. This law does not assume that arbitrary revert bytes are authentic protocol results.
7. **Freshness law.** For states with identical relevant logical records, heads, and current/absent/stale/consumed classifications, changing h and every current stamp together preserves each loader, classifier, selector, and guard decision. Only the stamp bytes may change. Establish this law from local arithmetic, comparisons, and queue updates; do not assume that entry execution or validation succeeds. No normalized-away field may be exposed to application execution.
8. **Observation law.** State changes, cursor changes, context switching, scoped hash updates, and check observations follow Sections 4.1-4.4. The protocol adds no other environment observation or unspecified application callback. All actual value transfers and callbacks, including transfers to a system address, run under the covered EVM semantics and observation restrictions.

The fixed protocol supplies the exact check predicates and transition details within these laws, including error behavior. `PrescribedChecksPassed` means every required protocol check observation is true; a caught protocol mismatch is not silently reclassified as an expected application revert.

Two specification levels are therefore distinct: the parametric replay theorem requires `P` and proofs of these interface laws; an executable-manager theorem additionally instantiates `P` and proves its correspondence with the selected bytecode. Neither level assumes complete future trace equality.

## 5. Explicit conditions

All conditions apply to both the reference configuration and the replay configuration where appropriate. They are premises of a conditional theorem, not assertions that arbitrary future chain states satisfy them.

| ID | Condition | Required meaning |
| --- | --- | --- |
| A0 | Correct precomputation / initial bundle validity, assumed | The bundle is valid in a finite reference execution at X. That execution succeeds, commits the selected entry's validation result, and justifies the bundle's required outcomes and hashes. No proof of the plugin's construction algorithm is required. |
| A1 | Same logical invocation | Preserve externally specified invocation inputs, caller identities, value, static mode, route, and relevant transaction data. Derive equality of later internal call inputs. Concrete envelopes may change only as permitted in Section 3.2. |
| A2 | Stable storage inputs | Relevant initial persistent storage values agree between executions. The execution may perform its own writes. Protocol freshness metadata follows A7 instead of literal equality. |
| A3 | Stable code and account structure | Preserve code and the account projections defined in Section 5.8, including delegation, creation eligibility, and zero/nonzero nonce classification. Exact nonce equality is not required. Establish preservation across transaction initialization and settlement as specified in Section 5.3. Exclude `CREATE` and `SELFDESTRUCT` in this first theorem. |
| A4 | Stable transaction-local inputs | Preserve relevant transient storage, invocation depth, execution permissions, and machine inputs at externally specified starting checkpoints. Derive later relationships with the correct reset and rollback rules. |
| A5 | No unstable observations | Apply the blanket restrictions in Section 6 transitively, including failed and reverted execution. Establish the restricted gas-forwarding rule separately. |
| A6 | Adequate resources and valid envelopes | Establish funding and gas bounds for every required frame, including loading and protocol work. All concrete transactions are valid at their actual submission points. |
| A7 | Equivalent protocol setup | Reload the same semantic bundle with current freshness. Preserve authorization, peer identities, lookup contents and context selection, and the intended FIFO entry occurrence. |
| A8 | Fixed semantics and admissible heights | Use the same EVM and protocol semantics, and block heights for which all required arithmetic and implementation representations are valid. |

### 5.1 A0: meaning of assumed validity

`ValidAtX` means that a finite reference run of the specified driver exists and satisfies the protocol definitions in Section 4. The selected entry's observed hashes equal its supplied expected hashes, and all prescribed entry and lookup checks pass. Required setup and the driving transaction succeed.

Validity is relative to the reference state, invocation, and height. It contains no assertion about X+Y, no storage-stability assumption, and no assertion that replay already succeeds.

This assumption can supply a reference execution as a witness. The theorem need not prove that a simulator generated that witness correctly. A later claim about an actual simulator must separately connect its outputs to this assumption.

### 5.2 A2: prestates, writes, and interference

For each non-normalized location in `S`, its value agrees in the initial states of the reference and replay drivers. This includes every read after an earlier write. An unread location may differ unless another condition constrains it.

This condition does not prohibit the driver from modifying a slot that it later reads. Corresponding writes and rollback must be proved to preserve the relationship between intermediate states.

The consecutive-driver requirement excludes all external interleaving between setup and execution, even if an unrelated transaction would preserve the footprint. Reentrant writes and transaction settlement within the driver remain part of the covered execution.

Equality is required between the two driver prestates; it does not require values to remain constant throughout every intervening block from X to X+Y. A lock or checker may establish the initial equality, but correctness of that mechanism is outside this theorem. Locking after a value has changed does not establish equality.

### 5.3 A3: code, account structure, and deployment

Executed runtime code, embedded immutable values, code-address resolution, and relevant proxy configuration agree. Relevant account-presence and EVM-defined empty/non-empty classifications also agree.

Balance top-ups must not change an account classification that can be observed, for example through an account-code-hash query. Banning explicit balance opcodes does not remove such structural requirements.

Transaction initialization and settlement are covered transitions for every setup transaction and the driving transaction. Establish that these transitions preserve the relevant account-state relation, including account existence, emptiness, code resolution, and required nonce relationships. This obligation includes fee prepayment, sender nonce updates, refunds, fee-recipient credits, account clearing, and other account changes required by the selected transaction type and execution rules.

Equal classifications at the driver's initial state alone do not satisfy this obligation. For example, an address absent in both prestates may receive a setup transaction's priority fee only in replay if the block beneficiary changes. A later `EXTCODEHASH` of that fixed address can then distinguish the executions without executing `COINBASE` or a balance opcode.

Discharge this obligation from concrete account and envelope conditions and local transition lemmas, including bounds on differing fee amounts where needed. Derive the account-state relation at each subsequent transaction boundary; do not assume equal future opcode results, successful replay, or matching transcripts. Exact balances and fee recipients need not agree when these local obligations establish preservation of the relevant relation.

Executed `CREATE` is prohibited throughout the covered trace, including initialization code and reverted frames. `CREATE2` remains permitted for protocol proxies and application contracts. Preserve or derive equal creator addresses, salts, initialization-code bytes, and endowments. Preserve the target's creation-eligibility classification under the selected revision; its exact nonce need not agree. Derive matching created accounts, runtime code, and transaction-local creation status.

`CREATE2` does not use the creator nonce in its address formula, but nonce exhaustion can prevent creation. Require headroom for every attempted creation that could reach the nonce-limit check. Under the Osaka nonce limit, the creator nonce must be below `2^64 - 1` at that point. For multiple attempts, use a bound that covers their increments and rollback. Sender nonces must likewise make each submitted transaction valid. These are bounds and classifications, not equality or a freeze of account nonces.

`SELFDESTRUCT` is excluded from all covered execution in this first theorem. It transfers an account's full balance implicitly. Even without a balance opcode, that transfer can change account existence and a later account-code-hash observation. Initial account classification equality and sufficient funding alone do not prevent this difference.

The sender nonce may differ subject to transaction validity and preservation of the account projections. Contract-creation transactions are excluded because their address derivation uses the sender nonce even without an executed `CREATE` instruction.

### 5.4 A4: transaction-local state

Transient storage begins empty at the start of each transaction. Before entry invocation, a covered caller prefix may have populated it. The proof must derive agreement on relevant transient values there; fresh transactions alone do not imply an empty transient state at every call.

At externally specified starting checkpoints, call depth, static permission, executing address, storage owner, sender, origin, value, calldata, and relevant machine inputs agree. Fresh call frames have the specified initial stack, memory, and return-data buffer. For later frames, these relationships are conclusions of execution preservation, not additional assumptions about an already-known future trace.

The model must preserve transient-storage sharing under delegated calls and rollback under reverted calls. Differences used only for gas accounting need not agree if A6 covers their resource effect.

### 5.5 A6: resources and transaction validity

Every submitted transaction has a valid signature, nonce, chain identity, transaction type, fee parameters, and intrinsic gas budget under its actual inclusion environment. Required block gas capacity is available. A fee cap below the applicable base fee is invalid even if the sender has enough ETH.

Sender balances cover fee prepayment and attached value for every driver transaction. Every attempted value-bearing `CALL`, `CALLCODE`, or permitted creation has sufficient funds, including attempts in caught, failed, and reverted frames. The theorem excludes dependence on insufficient-funds failures. Exact balances and fees may differ subject to these bounds and preservation of the account projections in Section 5.8.

Gas adequacy applies to every frame, not only the top-level gas limit. It includes explicit child-call caps, gas-forwarding limits, static-context probes, storage-cost rules, memory expansion, and deployment work. It must cover differences in access warmth, original storage values used for metering, setup history, and block-derived fee or access initialization.

The first theorem excludes gas-induced inner failures as well as top-level out-of-gas. Expected application reverts and non-gas static-mode failures remain allowed. A reference execution whose intended outcome depends on a child exhausting gas is outside this first theorem.

Adequacy must be established by numeric budgets, bounds, or a separate resource proof. It must not be defined as "the future transaction succeeds," "the future transcript matches," or another restatement of the conclusion.

Any interpreter fuel used by a Lean definition is a mathematical evaluation bound, not EVM gas. The proof must provide sufficient fuel for a finite run, or use an unbounded relational semantics. Fuel exhaustion is not an on-chain outcome.

### 5.6 A7: protocol setup and freshness

The same semantic entries and lookup records are made available, with identical array order, duplicate multiplicity, expected values, and context keys. Registry identities, manager identities, rollup identifiers, and authorization agree.

The concrete pre-load queue state and load order must select the corresponding entry occurrence. An unrelated live same-hash entry must not consume or precede the intended occurrence differently. A later lookup load must not replace a required value with a different record.

Relevant logical protocol state after setup agrees after replacing freshness stamps by the marker `current`. Absent, stale, and consumed states remain distinct where selection depends on them. Relating this state must use concrete queue, stamp, and loader rules, not an assumption that future execution validates.

Only the specified freshness operations may observe the changed height or stamp. Application code may not query a loaded freshness value, stale-record metadata, or another normalized-away protocol coordinate. If such a value is observable outside the specified protocol operations, this first theorem does not apply.

### 5.7 A8: future heights and execution rules

Y ranges over natural numbers, including zero. The theorem applies only when X+Y is a legal height and its freshness arithmetic is representable. For 256-bit checked freshness arithmetic, require `X + Y + 1 < 2^256`. Any narrower representation used by a concrete driver requires its own bound. In the inspected implementation, lookup-key cursors and the active lookup context are cast to `uint64`. Require their mathematical values to be below `2^64` when used, including the nested row index plus one; otherwise the concrete casts truncate and the unbounded logical keys do not describe the implementation.

Opcode semantics, supported transaction types, precompiles, code-resolution rules, gas schedules, and protocol behavior remain fixed. The theorem does not quantify across arbitrary hard forks or upgrades.

The preferred target is Glamsterdam's execution rules; Osaka is an acceptable initial instantiation. A concrete proof must name an immutable execution-spec revision, the enabled EIPs, chain-specific rules, transaction types, precompiles, and resource parameters. A fork name alone is not a semantics definition. Both runs use the same pinned rules; replay across a fork boundary is excluded. Unsupported operations must be excluded explicitly, not assigned placeholder semantics.

Glamsterdam is a target, not a claim of current Lean-model coverage. Its proposed state-gas and pricing changes require revision-specific resource lemmas. The observation ban also includes `SLOTNUM` whenever enabled. The selected Glamsterdam snapshot and its correspondence with Besu must be recorded before claiming a concrete Glamsterdam theorem.

### 5.8 State relation and admissibility predicates

Fix the semantics revision `V`, protocol `P`, reference trace `t_X`, and footprint `F = (S, A)`. At corresponding application-instruction checkpoints or abstract protocol-operation boundaries, define `Related(F, s_X, s_Y)` by the following conjunction:

| Component | Required relation |
| --- | --- |
| Application machine | Equal executing code, program counter, stack, memory, return-data buffer, call depth, addresses, caller, origin, calldata, value, and static permission. Treat allowed `GAS` plus its call as one step, or exempt only its pending gas operand until that call consumes it. |
| Persistent storage | Equal values at every non-normalized location in `S`. |
| Account projection | At every address in `A`, equal account-presence status, stored code bytes, code-resolution/delegation information, zero/nonzero nonce status, empty/nonempty status, and revision-defined creation eligibility. Exact balances and exact nonzero nonces are not compared. |
| Transaction-local functional state | Equal application transient storage and transaction-local creation status; corresponding call-stack and rollback checkpoints. Transient protocol fields use the protocol relation below. |
| Protocol state | Equal semantic records, authorization and identities, logical entry/lookup occurrences, active peer and lookup context, cursors, and hash accumulators. Relate physical queue positions by their logical occurrences; classify freshness as current, absent, stale, or consumed. |
| Environment and resources | Equal chain identity and the fixed functional inputs of A1. Changed height is available only to the named freshness operations. Balances, nonce magnitudes, gas counters, access warmth, refund counters, fees, and metering-only storage inputs satisfy the resource plan below. |

This relation describes current state; it does not assert equality of future accesses, outcomes, or transcripts. For concrete protocol bytecode, prove correspondence at operation boundaries, including internal steps that manipulate physical indices or freshness bytes. The abstraction does not exempt protocol callbacks or application-visible values from the observation restrictions.

`InitialRelated` requires this relation at the initial driver checkpoint, with the specified initial transaction-local state. `SetupCompatible` relates the initial protocol queues and records under the concrete loading and selection rules of Section 4.5. It must imply the required post-load relationship; successful loading is proved, not assumed.

For each reference checkpoint `i`, a mathematical resource plan supplies an envelope `I_i` of permitted resource valuations. A valuation contains the balances, nonce magnitudes, gas quantities, access sets, refund data, metering inputs, and resource rollback checkpoints needed by the pinned semantics. The plan may use intervals, exact values, or other explicitly defined sets; no executable certificate format is required. Define `BudgetOK` by these obligations:

1. **Initialization:** the concrete replay prestate and envelopes satisfy `I_0`. Establish the reference resource conditions as well; A0 alone does not exclude reference gas- or funding-induced inner failures.
2. **Local bounds:** for every valuation in `I_i`, the reference operation's fixed functional operands have sufficient funds, nonce headroom, and execution resources. At transaction boundaries, establish envelope validity, intrinsic costs, fee prepayment, and remaining block capacity.
3. **Transfer closure:** using the pinned arithmetic rules for charging, forwarding, transfer, refunds, nonce updates, and rollback, every permitted resource update maps `I_i` into the envelope for the next reference checkpoint. Cover all admitted cost variation; do not assume the future gas used equals the reference gas used.
4. **Account compatibility:** the same arithmetic updates preserve the resource-dependent parts of the account projections required by `Related`, including effects of fee recipients, account clearing, and differing balances. Code and storage effects are handled by the functional preservation lemmas. Equal initial classifications alone do not discharge this obligation.

The reference operation sequence indexes these obligations; it is not assumed to be the replay sequence. Their local resource calculations do not execute or assume `Run`. The execution-preservation proof establishes the next functional operation from `Related`, then applies the corresponding resource obligation. Costs of child frames include forwarding limits and the caller's continuation. Expected non-gas exceptional halts may consume their full child allotment. Any separate state-gas budget or other resource dimension in `V` must be included; a single top-level gas inequality is insufficient.

`TraceAllowed(V, t_X)` means that every covered instruction and native operation satisfies Section 6, including initialization code and reverted frames. `DriverAllowed(V, C)` means that its transactions have destinations, contain no EIP-7702 authorizations, and run consecutively in one block under `V`. The same logical driver order is used in both runs.

With the common `V`, `P`, and reference footprint implicit, the admissibility predicate is the following conjunction:

```text
AllowedReplay =
  same pinned semantics and protocol
  and DriverAllowed(C_X) and DriverAllowed(C_Y)
  and same logical driver inputs, semantic bundle, and selected occurrence
  and TraceAllowed(t_X)
  and InitialRelated(C_X, C_Y)
  and SetupCompatible(C_X, C_Y, B, e)
  and the height and representation bounds of A8
  and there exists a resource plan I with BudgetOK(I, t_X, C_X, C_Y)
```

Here equality of logical driver inputs applies to each setup transaction as well as the driving transaction, subject to the envelope differences allowed in Section 3.2. General opcode, protocol, and transaction-boundary preservation lemmas remain proof obligations. Neither `Related` at every future checkpoint nor future success is an admissibility premise; their preservation is established by induction over the finite reference execution.


## 6. Conservative observation restrictions

### 6.1 Application execution

In the reference application execution, no executed instruction may be any of:

```text
BLOCKHASH  COINBASE  TIMESTAMP  NUMBER  PREVRANDAO
GASLIMIT   BASEFEE   BLOBBASEFEE
GASPRICE   BLOBHASH
BALANCE    SELFBALANCE
CREATE     SELFDESTRUCT
```

`DIFFICULTY`, where that name denotes the revision-specific predecessor of `PREVRANDAO`, is also prohibited. `SLOTNUM` is prohibited when enabled by the pinned revision. Every newly supported opcode or native mechanism needs an observation analysis before it is admitted.

The ban applies regardless of whether the result affects a branch, reaches return data, or is discarded. It applies to all covered application code, including delegated code, initialization code, static calls, callbacks, and frames whose effects revert.

`CREATE` and `SELFDESTRUCT` are additional conservative operation bans, not claims that they are environment-observation opcodes. Their reasons are stated in Section 5.3. Both are also prohibited in protocol plumbing.

`CHAINID` is permitted because chain identity is fixed. Other contextual inputs are permitted only when A1-A4 fix their observable values. Code and account queries remain subject to A3.

The proof establishes that corresponding future execution cannot introduce a prohibited instruction by diverging onto a different path. It must not assume the future trace or its instruction sequence in advance.

### 6.2 Restricted use of `GAS`

Application use of `gasleft()` to compute a branch, return/revert bytes, a storage value or address, a call target, calldata, or transferred value is prohibited.

The sole allowed `GAS` pattern in this first specification is immediate gas forwarding: its result is consumed only as the requested gas operand of the immediately following `CALL`, `CALLCODE`, `DELEGATECALL`, or `STATICCALL`. It is not duplicated, stored, transformed, or exposed through another operand. Explicit fixed gas operands are also permitted.

This is a local bytecode restriction, not a general dependency-analysis admission rule. It allows ordinary forwarding without allowing arbitrary gas-derived application behavior.

A separate lemma must prove that this pattern preserves functional call behavior under A6. Increasing available gas is not assumed to preserve behavior for unrestricted programs.

### 6.3 Protocol operations

The manager's loader and freshness checks necessarily use block height. These named operations are the only exception to the height-observation ban:

1. Compute the current stamp `height + 1`.
2. Write that stamp while loading records.
3. Compare stored stamps with the current stamp to classify and select records.

Their permitted behavior is exactly Sections 4.4 and 5.6. There is no exception for an entire address or every function of a manager contract. No other protocol operation may use a prohibited observation.

Protocol plumbing may use the same immediate gas-forwarding pattern as application code. Fixed gas caps remain subject to A6.

Any precompile, native operation, or chain-specific mechanism reached by covered execution must be accounted for by the fixed semantics. It may not introduce an unmodeled block-, fee-, balance-, or gas-dependent functional result.

## 7. The theorem to prove

Let:

- `B` be a fixed semantic bundle and `e` its selected entry occurrence.
- `q` be the fixed logical request and execution route.
- `C_X` be the reference configuration at height X.
- `r_X` be the successful reference execution record justified by A0, containing its finite trace and result observations.
- `AllowedReplay(B, e, q, C_X, r_X, C_Y)` mean A1-A8, including the reference observation restrictions and resource conditions.
- `Run(B, e, q, C, outcome)` mean that a finite execution of the specified setup and complete driving transaction reaches that outcome. This is an execution relation, with terminal outcomes defined in Section 2.

Fix the same protocol parameter `P` for both executions and assume its local interface laws from Section 4.5. The notation below suppresses that common parameter. Those laws must be established for the intended protocol instantiation.

Then prove:

```text
For every Y in Nat and every configuration C_Y,

  height(C_Y) = X + Y
  and AllowedReplay(B, e, q, C_X, r_X, C_Y)

imply that there exists a finite successful result r_Y such that:

  Run(B, e, q, C_Y, Success(r_Y)),

  every prescribed entry and lookup validation passes,

  the selected logical entry occurrence is consumed,

  its scoped boundary transcript equals the reference transcript,

  every required lookup sub-transcript equals its reference transcript,

  its structural validation trace equals the reference trace,

  its committed validated cross-chain hash equals
    r_X.selectedEntryHash
    = e.crossChainRollingHash,

  and its driving-transaction output bytes equal the reference output bytes.
```

The structural validation trace records call/nested begin/end events, the counters used for hashing and lookup selection, and their prescribed outcomes. Equality does not require equal gas counters, fee payments, unused account state, or freshness bytes.

The theorem need not prove equality of entire world states, all receipts, all logs, or account balances. It must preserve the intermediate state relationships needed for the stated outcomes.

Failure has no committed selected-entry hash. The conclusion therefore proves both existence of a committed validated hash and equality of that hash; it does not compare hashes from failed attempts.

## 8. Required proof decomposition

1. **Reference validity assumption.** Introduce the valid reference run as a premise. Do not attempt to prove the bundle-construction algorithm.
2. **Setup preservation.** Prove that concrete loading, stamp assignment, registry state, and queue rules establish equivalent logical protocol state and select the corresponding occurrence. Include the account-state effects of setup transaction initialization and settlement required by Section 5.3.
3. **Execution preservation.** Prove corresponding functional steps, calls, storage accesses, writes, and outcomes under A1-A5 and A8. Treat controlled freshness operations and allowed gas forwarding with their dedicated lemmas.
4. **Resource adequacy.** Establish the Section 5.8 resource-plan obligations and use them to rule out gas-, funding-, and nonce-exhaustion-induced divergence. Prove finite execution without assuming future success or a matching future trace.
5. **Reentry and rollback.** Prove preservation of cursors, lookup context, transient state, successful writes, reverted writes, and revert-span transport. Retain outcome dependencies from reverted frames.
6. **Validation preservation.** Derive identical structural validation events and scoped boundary records. Derive every prescribed hash, peer, identity, mode, value, and consumption check from these relationships.
7. **Hash preservation and commitment.** Use deterministic encoding and hashing to derive hash equality, then show the driving transaction commits the selected result and returns the reference bytes. Include its transaction initialization and settlement in the account-state preservation proof required by Section 5.3.

The boundary-transcript equality is an intermediate conclusion. It is not an admissibility premise. Likewise, "all checks pass" must remain a conclusion rather than a definition of compatible future protocol state.

## 9. Lean specification boundary

The formal specification needs types for semantic bundles, selected occurrences, logical requests, configurations, scoped transcripts, structural validation traces, successful results, and failed results.

Use these representation rules without requiring particular Lean type names:

| Concept | Required meaning |
| --- | --- |
| Bytes, addresses, and hashes | Finite byte sequences; addresses contain exactly 20 bytes and hashes exactly 32 bytes. Equality is byte-for-byte. |
| Numbers | Heights and mathematical counts are natural numbers with explicit bounds where encoded or cast. EVM words retain their revision-defined arithmetic. |
| Occurrences and scopes | Identify logical entry and lookup invocation occurrences, including repeated and reverted invocations. Do not identify them solely by hash or physical queue index. |
| Execution record | A finite trace plus terminal observations, including the selected committed result, effective scoped transcripts, and attempted protocol checks. |
| Returned bytes | `ReturnedBytes` means the complete driving transaction's execution output, which a caller wrapper may transform. It is not automatically the bundle's `entry.returnData`, nor a receipt field. |

`ValidAtX` must connect the reference record to `Run`; the record cannot contain arbitrary claimed hashes or traces. `Run` is the finite closure of the specified transitions, not an unconstrained relation. Determinism of those transitions must give a unique terminal outcome. With a fuel-based interpreter, establish the relation using sufficient fuel and prove that additional fuel preserves a completed result. Fuel exhaustion supplies no success or failure witness.

Use the intermediate-state relation and resource-plan obligations defined in Section 5.8. Prove initialization, local preservation, rollback preservation, and finite termination; do not substitute an assumption of corresponding future execution. At an allowed `GAS` instruction, either group `GAS` and its immediately following call into one proof step, or relate their unequal pending gas operands explicitly. Full stack equality at that intermediate point would be incorrect.

Its central predicate has the following mathematical shape. `ProtocolLaws` denotes the local laws in Section 4.5. This is notation, not compiled Lean code:

```text
ProtocolLaws P ->
ValidAtX P B e q C_X r_X ->
  forall Y C_Y,
    height C_Y = height C_X + Y ->
    AllowedReplay B e q C_X r_X C_Y ->
      exists r_Y,
        Run P B e q C_Y (Success r_Y)
        and PrescribedChecksPassed r_Y
        and CorrespondingOccurrenceConsumed e r_Y
        and ScopedTranscripts r_Y = ScopedTranscripts r_X
        and StructuralTrace r_Y = StructuralTrace r_X
        and SelectedHash r_Y = SelectedHash r_X
        and SelectedHash r_Y = ExpectedHash e
        and ReturnedBytes r_Y = ReturnedBytes r_X
```

An executable-EVM claim additionally requires proofs that the modeled manager/proxy behavior matches the pinned bytecode, and that the EVM model covers the selected revision and operations. A high-level protocol proof without those connections must be labeled as such.

Hash primitives may initially be modeled as fixed deterministic functions. Relating them to concrete implementations is a separate obligation. Hash injectivity must not be assumed to prove this forward preservation result.

## 10. Local and multi-chain claims

For this theorem, cached remote outcomes are part of the fixed semantic bundle. Local replay proves that local execution remains compatible with those outcomes and preserves its validated hash.

It does not independently prove that an actual remote execution still produces the cached bytes. To make that claim, establish the corresponding replay theorem and assumptions on every participating chain, with matching requests, bundles, outcomes, and allowed scheduling.

Each chain uses its own reference and replay heights. A shared numerical Y across chains is not required. Cross-chain atomicity, consensus, finality, and bilateral commitment agreement require additional theorems.

## 11. Audit questions

An independent audit should test the following points:

1. Does assumed reference validity stop at X, without assuming replay success or future hash equality?
2. Does the stated driver include the caller prefix and suffix needed for a committed result?
3. Are all application, delegated, static, failed, reverted, and relevant protocol frames covered?
4. Can an allowed opcode or native mechanism observe an unstated changing input?
5. Do stable storage and account footprints suffice to derive the same accesses, rather than assuming them?
6. Are nonce changes, account emptiness, creation, the destruction ban, and proxy resolution handled explicitly?
7. Is gas independence justified for the exact allowed forwarding pattern, with per-frame resource bounds?
8. Are freshness normalization, duplicate FIFO selection, and lookup replacement handled without a blanket manager exemption?
9. Are lookup scopes, nested numbering, and revert-span transport preserved correctly?
10. Are all prescribed validations proved, including protocol failures that application code could otherwise catch?
11. Does the result guarantee a committed successful execution, rather than equality of cached or reverted candidate hashes?
12. Is every executable-code claim distinguished from assumptions and high-level protocol lemmas?

The first proof is complete only when its chosen formalization establishes the theorem in Section 7 under these stated premises. This document alone does not establish that theorem.

## 12. Source provenance

The implementation description was checked against the local source tree rooted at:

```text
/Users/jefferson/Desktop/Repos/2026/lineth-enterprise-main/linea-besu-enterprise/plugins/xcall/contracts/src
```

No Git metadata was available in that tree or its ancestors. The SHA-256 digests below identify the inspected file contents; they are source fingerprints, not protocol hashes. Function bodies take precedence over comments when describing behavior.

| Source file relative to that root | Relevant source lines | Role |
| --- | --- | --- |
| `L2/EEZL2.sol` | 256, 313, 475, 622, 680, 689, 762, 847, 889, 933 | Entry, reentry, lookup, and revert-span fold paths |
| `base/EEZBase.sol` | 230, 274, 285, 328, 369, 453 | Call identity, context keys, transport decoding, and hash helpers |
| `base/CrossChainProxy.sol` | 44, 76 | Raw forwarding and manager-result decoding |
| `base/EEZProtocolConstants.sol` | 5 | Rollup bound and zero gas coordinate |
| `interfaces/IEEZL2.sol` | 42, 62, 91, 152, 207, 319 | Bundle field types and entry events |
| `interfaces/IEEZBase.sol` | 84 | Context-result error signature |

```text
7fe5a3e966d7484ee012d79b5cf6977b633d015c24d80ff17ddf6b7b9ba39f39  L2/EEZL2.sol
b90a9b53979861a26df858391fba5e2d9e768e11d014ca5d026a0e35bdaa5fb2  base/EEZBase.sol
f3eda9adc0d86880fedaf8a20f7cc2fc81aacc4c400f087bb31ee800a655e4d7  base/CrossChainProxy.sol
83e3e40107484aad1a933af206fa6cf48437f4fbfc14f4a95f9a3fe7b9d935a8  base/EEZProtocolConstants.sol
5a7c0d4b0db15b7f94953081b7575939282349c863a9c812358bdfa360f5433f  interfaces/IEEZL2.sol
a85f424ba0aac76962e72d5292d02218db2b96bb7643b9c80f11bc913d411e9b  interfaces/IEEZBase.sol
```

This source mapping covers the hash description. It does not establish a deployed address, compiler configuration, bytecode identity, or a Lean refinement proof. A concrete executable theorem must additionally pin those artifacts and discharge the correspondence obligations in Section 9.

The revision-dependent restrictions additionally refer to [EIP-1014](https://eips.ethereum.org/EIPS/eip-1014) for `CREATE2`, [EIP-2681](https://eips.ethereum.org/EIPS/eip-2681) for nonce limits, and [EIP-7702](https://eips.ethereum.org/EIPS/eip-7702) for authorization processing. Glamsterdam scope is tracked by [EIP-7773](https://eips.ethereum.org/EIPS/eip-7773); the proposed slot observation is defined by [EIP-7843](https://eips.ethereum.org/EIPS/eip-7843). These links identify the design sources; they do not replace the immutable semantics pin required by Section 5.7.
