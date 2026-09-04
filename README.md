# ProofForge Psy

[![CI](https://github.com/DaviRain-Su/ProofForgePsy/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForgePsy/actions/workflows/ci.yml)

[中文](README.zh-CN.md)

A Lean 4 → PSY (DPN circuit) contract compiler. Mark entries with `@[pf_entry]`
in ordinary Lean source; ProofForge extracts a checked IR, lowers it to a
target-owned Plan, and emits a canonical **psy-dpn-v1** DPN package (JSON).
This repository is the Psy single-target fork of ProofForge.

Reference targets: [`ProofForgeEvm`](https://github.com/DaviRain-Su/ProofForgeEvm)
(EVM fork of the same architecture) and
[`proof_forge`](https://github.com/DaviRain-Su/proof_forge) (`ProofForgeV2.Targets.Psy`,
source of the DPN package schema, the Counter goldens, and the official
`gen_dapen_contract_function_method_id` algorithm).

## Pipeline

```
Lean source (@[pf_entry])
  → Extract (Lean expression → extensible Core IR, Psy dialect)
  → Psy.Lower (Core ops → target-owned Plan)
  → Psy.Validate (limits, return forms)
  → Psy.Dpn.Lower (Plan → canonical DPN package, psy-dpn-v1)
  → Psy.Dpn.JsonCodec (compact canonical JSON → Name.dpn.json)
```

State leaves are Goldilocks-Felt slots; every `UInt64` arithmetic node is
**checked** (overflow traps as an unsatisfiable assertion at proof time —
there is no faithful wrapping interpretation on Psy). Guard shapes compile to
gated `assertWithMessage false "revert"` trap arms; the DPN trap is a proof
failure, which is the intended rejection semantics.

## Layout

- `ProofForge/Core/` — target-independent value/effect IR, CFG, codec, schema
- `ProofForge/Extract/` — Lean expression → IR extractor (Psy dialect)
- `ProofForge/Psy/` — Psy Ops / Plan / Validate / DPN Lower / Emit / Registry
- `ProofForge/Psy/Dpn/` — DPN package schema (v1), JSON codec, Plan→DPN lowering
- `ProofForge/Cli.lean` — the `pf` CLI (`pf build` / `pf init` / `pf --version`)
- `Examples/Psy/` — Psy contract examples (Counter, Flag)
- `Tests/PsyGolden.lean` — Counter golden structural + method-id + round-trip gates
- `templates/psy-counter/` — `pf init` user project template (placeholder; `pf init` reports its absence)

## Build & test

```text
lake build             # compiler library
lake build pf          # CLI executable
lake build psyGolden   # golden test executable
lake env psyGolden     # run the golden suite
lake build Examples    # example contracts
```

Toolchain: Lean/Lake **v4.31.0** (pinned in `lean-toolchain`). No external
dependencies — `lake-manifest.json` is empty.

## CLI

```text
pf build [--out DIR] [--module MOD] [Contract ...]
pf init <name>
pf --version
```

`pf build` writes `Name.dpn.json` (canonical DPN package JSON) per program.
Bare names map to in-tree `Examples.Psy` fixtures; user projects pass
`--module` or list `[[program]]` entries in `pf.toml`.

## psy-dpn-v1 slice boundaries

Admitted: single-leaf / multi-leaf `UInt64`/`Bool` scalar state, checked
UInt64 arithmetic (add/sub/mul/div/mod), bitwise ops, compares, select,
shl/shr, checked bitwise-not, DPN context reads (`psyUserId`, …),
if/else with select-merged returns and stores, fixed vectors (static index),
and G5-WIDE `UInt128`/`UInt256` state slots (multi-limb fields flatten to one
`UInt64` leaf per 32-bit limb; checked wide mul/div/mod/shift lower through
target-owned `bindWideUint*` bindings, exercised by hand-built Plans).

Fail-closed (rejected at lowering): dynamic vector indices, state loops,
typed error payloads, aggregate/multi-value returns, aggregate parameters,
and source-level UInt128/256 arithmetic that reads a sibling limb inside a
mutating update (e.g. `{ v := { w0 := s.v.w0 + d, w1 := s.v.w1 } }` — the
`w1 := s.v.w1` sibling-limb read in the ok-state is a known extractor FC).
The `bindWideUint*` statements are target-owned — the Lean extractor flattens
`UInt128`/`UInt256` values into scalar limbs rather than emitting wide ops, so
wide arithmetic must be expressed in a hand-built Plan (see `Tests/PsyWide`).
Full-constructor wide updates (`{ v := { w0 := a, w1 := b } }` with literal or
param limbs) and wide views (init/get) work end-to-end (see
`Examples/Psy/WideCounter`).

## Trust boundary

- The DPN package JSON is a **circuit description**; the psy runtime/proof
  stack consumes it. This repo does not prove EVM- or DPN-refinement.
- Counter goldens are structural: the emitted package must stay equal to the
  V2 hand-built `counterPackageGoldenV1` (enforced in CI).
- Method ids come from the official SHA-256 algorithm; the three Counter
  values are pinned as regression goldens.

## License

[MIT](LICENSE)