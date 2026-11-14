# Fresh-machine setup

Use the repository's pinned toolchain and lockfile. Do not upgrade dependencies
while resuming this task.

## Required tools

| Tool/input | Requirement |
| --- | --- |
| Git | Clone this fork branch and fetch locked dependency repositories |
| elan | Lean toolchain manager; install per machine from the official project |
| Lean and Lake | Exactly `leanprover/lean4:v4.22.0`; Lake ships with the toolchain |
| mathlib | `v4.22.0`, locked commit `79e94a093aff4a60fb1b1f92d9681e407124c2ca` |
| Remaining Lean packages | Exact revisions in committed `lake-manifest.json` |
| curl, tar, normal native build tools | Toolchain/cache download and native compilation; provide a C compiler named `cc` |
| Python 3 | Optional, for check automation and diagnostic scripts |
| ripgrep (`rg`) | Source and forbidden-placeholder audit commands |
| Solidity source checkout | Needed for source audit; see fingerprints in [README.md](README.md) |

No Besu, JVM, RPC endpoint, wallet, Foundry, Solidity compiler, or JavaScript package
installation is required for the current Lean model/checks. They may be needed by
later work outside this deliverable.

The verified host was macOS arm64. Linux/WSL can use the same POSIX commands, but
was not tested in this session. On macOS, install Xcode Command Line Tools if `cc`
is missing. On Linux, install your distribution's Git, curl, CA certificates, tar,
and C build tools. Keep these system tools; they are not project-owned binaries.

The original setup occupied roughly 7 GB across elan, dependency sources/builds,
and mathlib cache. Leave additional space for builds.

## Install elan and the pinned toolchain

Use the official [elan repository](https://github.com/leanprover/elan). Download
and inspect the installer before executing it:

```sh
curl --proto '=https' --tlsv1.2 -sSf \
  https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -o /tmp/elan-init.sh
less /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install leanprover/lean4:v4.22.0
```

If elan already exists, preserve the machine's other toolchains and install only
the missing pinned version. Add elan's bin directory to your shell profile only
if wanted; the command above changes PATH for the current shell.

## Clone and restore dependencies

```sh
git clone --branch cross-chain-rolling-hash \
  https://github.com/kyzooghost/EVMYulLean.git
cd EVMYulLean
export PATH="$HOME/.elan/bin:$PATH"
lake env lean --version
lake exe cache get
lake build EvmYul.CrossChainReplay EvmYul.CrossChainReplay.Checks.Fixtures
```

Require version **4.22.0**. Lake resolves dependencies from the committed manifest.
`lake exe cache get` restores mathlib's compiled cache rather than compiling all
of mathlib locally. It can download the `leantar` cache helper automatically.
Do not run `lake update` to resolve an ordinary missing-cache issue.

Check that `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` did not change.
The current model aggregate excludes fixtures. The final `Checks.lean` aggregate
is still a remaining Task 10 deliverable.

Use the narrow targets above. A full repository build can involve unrelated FFI
targets and submodule/native-library setup outside this task's verified path.

## Run every current check

From the repository root:

```sh
for check in EvmYul/CrossChainReplay/Checks/*.lean; do
  lake env lean "$check" || exit 1
done
```

There are 15 files at handover, including `Fixtures.lean`. Successful `#check`
output is normal. Every command must exit 0; do not replace assertions or add
assumptions to obtain a pass.

Also run:

```sh
rg -n '\b(sorry|admit|axiom)\b' EvmYul/CrossChainReplay
git diff --exit-code -- lean-toolchain lake-manifest.json lakefile.lean
git status --short
```

The `rg` command should have no matches and normally exits 1 in that case.
Build/check success does not prove the replay theorem or EVM correspondence.

## Local cleanup requested by the user

Completed on the original machine on 2026-11-14 UTC, after the first branch push:

- Removed `~/.elan`: the session installed it, it contained only Lean 4.22.0,
  and its `known-projects` file listed only this repository.
- This repository's `.lake/build` and dependency `.lake/build` directories.
- Compiled Lake configuration files inside project/dependency `.lake` directories.
- `~/.cache/mathlib` cache archives and its `leantar-0.1.15` binary/download. This
  cache directory was created during this project setup on 2026-11-12.

Repository source, dependency source checkouts, system Git/curl/Python/cc,
and the separate Solidity source tree were retained. No elan lines were found in the checked
shell profile files, so no profile edits are required on the original machine.

Absence of the toolchain, cache, and all listed build directories was verified.
Those local binaries are not committed. Recreate them with the commands above.
The handover validation happened before cleanup; the original machine cannot run
Lean again until it is reinstalled.
