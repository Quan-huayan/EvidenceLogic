# 背书逻辑 v1.0 —— Lean 4 形式化

「背书逻辑 v1.0 定稿」的 Lean 4 形式化：语言、公理系统（E／S1／S2／F1–F4／R1／P1／P2）、
第九节可导出结果，以及其上的模型论（模型类、可靠性定理、典范模型族、第十节反模型）。

**零依赖**（只用 Lean 4 核心与 `Std`，不需 Mathlib），构建约 10 秒：
零错误、零警告、无 `sorry`、无 `axiom`。工具链见 `lean-toolchain`。

```powershell
lake build
```

## 文档

| 文档 | 内容 |
|---|---|
| [`docs/背书逻辑v1.0-定稿.md`](docs/背书逻辑v1.0-定稿.md) | 定稿原稿（逐字存档） |
| [`docs/设计说明.md`](docs/设计说明.md) | **语法／证明系统／语义三层是什么**，以及各项设计决定的理由 |
| [`docs/主要结果.md`](docs/主要结果.md) | 定理清单、证明思路、与第九／十节的逐条对应 |
| [`docs/讨论与局限.md`](docs/讨论与局限.md) | 完备性未证等：明确区分"已证"与"未证" |

## 模块

| 模块 | 一句话 |
|---|---|
| [`Syntax.lean`](EvidenceLogic/Syntax.lean) | 语言：单排序 `Form`（公式即项）、`⊳`／`⊲`、自由变元、代入、替换上下文 |
| [`Semantics.lean`](EvidenceLogic/Semantics.lean) | **语义**：命题层 `PSet`、经典基语义 `Base`（定义 `⊢`）、背书语义 `Frame`、模型类 `IsModel` |
| [`Derivable.lean`](EvidenceLogic/Derivable.lean) | 公理系统：10 个构造子对应定稿各条规则 |
| [`Canonical.lean`](EvidenceLogic/Canonical.lean) | 典范（自由）模型族 + 存在性定理 |
| [`Soundness.lean`](EvidenceLogic/Soundness.lean) | 可靠性定理（连接证明系统与语义） |
| [`Derived.lean`](EvidenceLogic/Derived.lean) | 定稿第九节：16 项可导出结果 |
| [`Properties.lean`](EvidenceLogic/Properties.lean) | 定稿第八节：右封闭、合取封闭、爆炸、不蕴涵真 |
| [`NonDerivable.lean`](EvidenceLogic/NonDerivable.lean) | 定稿第十节：有限反模型 `M3` 覆盖 10 条 |
| [`Prelude.lean`](EvidenceLogic/Prelude.lean) | 自足格运算记号层（`⊤ ⊥ ⊓ ⊔ ᶜ`） |
| [`EvidenceLogic.lean`](EvidenceLogic.lean) | 汇总模块 |

## 主要结果

* **可靠性**：`Derivable.soundness` —— `⊢ᴱ φ ⇒ M ⊨ φ`（对一切模型）。
* **存在性**：`Canon.isModel` —— 任意非空 `W`、任意 `atomRel` 下，
  `X ⊳ φ ⟺ X ≤ ⟦φ⟧ ∨ X = ⊤ ∨ ⟦φ⟧ = ⊤`（`⊲` 对偶）自动满足定稿全部规则。
* **可导出（第九节）**：`Derived.lean` 共 16 项，含四条"关系的关系"。
* **不可推导（第十节）**：`NonDerivable.lean` 以 `Fin 3` 上的有限反模型
  逐条给出 `_not_valid` 与 `_not_derivable`；其中「拆合取支持者」另给出
  更强的**规则级非可容许性** `and_split_not_admissible`。
* **不蕴涵真**：`not_truth_preserving` 与 `support_does_not_imply_truth`。

未证明的部分（**完备性**、第十节其余条目的规则级非可容许性等）见
[`docs/讨论与局限.md`](docs/讨论与局限.md)。
