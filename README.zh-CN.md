# ProofForge Psy

[![CI](https://github.com/DaviRain-Su/ProofForgePsy/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForgePsy/actions/workflows/ci.yml)

[English](README.md)

Lean 4 → PSY（DPN 电路）合约编译器。在普通 Lean 源码里用 `@[pf_entry]` 标记入口；
ProofForge 抽取经过校验的 IR，lower 到目标自有的 Plan，再产出规范的
**psy-dpn-v1** DPN 包（JSON）。本仓库是 ProofForge 的 Psy 单目标 fork。

参考实现：[`ProofForgeEvm`](https://github.com/DaviRain-Su/ProofForgeEvm)
（同一架构的 EVM fork）与
[`proof_forge`](https://github.com/DaviRain-Su/proof_forge)
（`ProofForgeV2.Targets.Psy`，DPN 包 schema、Counter golden 与官方
`gen_dapen_contract_function_method_id` 算法的来源）。

## 流水线

```
Lean 源码（@[pf_entry]）
  → Extract（Lean 表达式 → 可扩展 Core IR，Psy 方言）
  → Psy.Lower（Core ops → 目标自有 Plan）
  → Psy.Validate（限额、返回形式）
  → Psy.Dpn.Lower（Plan → 规范 DPN 包，psy-dpn-v1）
  → Psy.Dpn.JsonCodec（紧凑规范 JSON → Name.dpn.json）
```

状态叶是 Goldilocks-Felt 槽位；所有 `UInt64` 算术节点都是 **checked**
（溢出在证明期变成不可满足断言而 trap —— Psy 上没有忠实的回绕解释）。
guard 形状编译成带门控的 `assertWithMessage false "revert"` trap 臂；
DPN trap 即证明失败，这正是预期的拒绝语义。

## 目录

- `ProofForge/Core/` — 目标无关的值/效果 IR、CFG、codec、schema
- `ProofForge/Extract/` — Lean 表达式 → IR 抽取器（Psy 方言）
- `ProofForge/Psy/` — Psy Ops / Plan / Validate / DPN Lower / Emit / Registry
- `ProofForge/Psy/Dpn/` — DPN 包 schema（v1）、JSON codec、Plan→DPN lowering
- `ProofForge/Cli.lean` — `pf` CLI（`pf build` / `pf init` / `pf --version`）
- `Examples/Psy/` — Psy 合约示例（Counter、Flag）
- `Tests/PsyGolden.lean` — Counter golden 结构 + method-id + round-trip 门禁
- `templates/psy-counter/` — `pf init` 用户项目模板（占位；`pf init` 会提示缺失）

## 构建与测试

```text
lake build             # 编译器库
lake build pf          # CLI 可执行
lake build psyGolden   # golden 测试可执行
lake env psyGolden     # 跑 golden 套件
lake build Examples    # 示例合约
```

工具链：Lean/Lake **v4.31.0**（`lean-toolchain` 固定）。无外部依赖 ——
`lake-manifest.json` 为空。

## CLI

```text
pf build [--out DIR] [--module MOD] [Contract ...]
pf init <name>
pf --version
```

`pf build` 为每个程序写出 `Name.dpn.json`（规范 DPN 包 JSON）。
裸名字映射到仓库内 `Examples.Psy` fixture；用户项目传 `--module`
或在 `pf.toml` 里列 `[[program]]` 条目。

## psy-dpn-v1 切片边界

已支持：单叶/多叶 `UInt64`/`Bool` 标量状态、checked UInt64 算术
（add/sub/mul/div/mod）、位运算、比较、select、shl/shr、checked bitwise-not、
DPN 上下文读取（`psyUserId` 等）、返回值 select 合并的 if/else 与存储、
固定向量（静态索引）。

Fail-closed（lowering 时拒绝）：动态向量索引、状态循环、typed error
payload、聚合/多值返回、聚合参数、宽（UInt128/256）状态槽。

## 信任边界

- DPN 包 JSON 是**电路描述**，由 psy runtime/证明栈消费。本仓库不证明
  EVM 或 DPN refinement。
- Counter golden 是结构性的：产出的包必须与 V2 手工构建的
  `counterPackageGoldenV1` 保持相等（CI 强制）。
- method id 来自官方 SHA-256 算法；Counter 三个值作为回归 golden 固定。

## 许可证

[MIT](LICENSE)