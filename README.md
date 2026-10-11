# 背书逻辑 v1.0 —— Lean 4 形式化

> 《背书逻辑 v1.0 定稿》的完整 Lean 4 形式化（**零依赖**，不需 Mathlib），
> 外加一层在其语义上做的**证据语义分析**。全库**无 `sorry`、无自定义 `axiom`、零警告**。

```powershell
lake build     # 32 jobs，零错误零警告
```

## 三十秒

| 问题 | 答案 |
|---|---|
| **定稿被证到什么程度？** | 第十节 12 条"推不出"拿下 **10 条规则级非可容许**（前提全部可推导、结论不可推导）；剩下 **支持传递** 与 **S7** |
| **剩下两条卡在哪？** | 三条**互不包含**的路线：① 禁用／受限 `E`（`EFree`／`RestrictedE`）② 条件化到**一条引理** `TransferLemma`（未证、未被反驳；反驳搜索 16384 组无反例）③ **新**：全量 `Derivable` 在**结论分量关系自由**时**无条件**成立（`NoRelFragment`）⇒ 任何反例的**结论分量**都必须含关系子公式 |
| **语义只有一族吗？** | **不是，至少三族**：典范 `suppP`（`Canonical`）· 严格蕴含（`Strict`，**一个析取项都没有**）· 阈值族（`Threshold`，把 `X = ⊤` 换成任意固定 `U`）。三族都是同一公理系统的模型 ⇒「哪一族才对」是**设计取舍**：定稿选 `suppP` 是为了让支持传递／S7 在语义上失效 |
| **最硬的三个新结果？** | ① `⊲` **不能**由 `⊳` 与 `¬` 定义（"独立原语"在语义上有据）② 证据项的**正向刻画**（原子支持者根 ∈ `{e,s1,s2,f1,f4}`，**紧**）③ 可靠性 = 显式 `Derivable.rec` 折叠（初始代数到模型的唯一同态） |
| **哪里没证？** | 见 [`docs/讨论与局限.md`](docs/讨论与局限.md) 第 7 节：一条前沿 + 六处被机器检查**推翻或修正**的分析 |

## 读什么（按目的选）

| 你的目的 | 去看 |
|---|---|
| 形式化本身：语言、十条规则、语义、模型类 | [`docs/设计说明.md`](docs/设计说明.md) |
| 结论清单（与定稿第八／九／十节逐条对应） | [`docs/主要结果.md`](docs/主要结果.md) |
| 语义为什么长这样、怎么解读、类型论／范畴论对应 | [`docs/证据语义解读.md`](docs/证据语义解读.md) |
| 明确区分"已证／未证"，以及被推翻过的分析 | [`docs/讨论与局限.md`](docs/讨论与局限.md) |
| 定稿原文 | [`docs/背书逻辑v1.0-定稿.md`](docs/背书逻辑v1.0-定稿.md) |

---

# 模块（29 个，**目录即分层**）

```
EvidenceLogic/
├── Core/      语言与基础     Prelude · Syntax
├── Model/     语义与模型论   Semantics · Canonical · Soundness · Strict · Threshold
├── System/    证明系统与定稿 Derivable · Properties · Derived · NonDerivable · NonAdmissible
├── Analysis/  证据语义分析   Structure · Disjuncts · Algebra · Evidence · Initiality
│                            · Inversion · InversionRefut · NormalForm
└── Frontier/  唯一前沿       EFree · RestrictedE · Transfer · Conditional
                             · Probe · Obstruction · SingleLayer · SingleLayerFull
                             · NoRelFragment
```

（**定理名与命名空间不随目录变化**，仍是 `EvidenceLogic.*`——`Canon.isModel`、`Derivable.soundness` 等照旧。）

## `Core/` —— 语言与基础

| 模块 | 一句话 |
|---|---|
| [`Prelude.lean`](EvidenceLogic/Core/Prelude.lean) | 自足格运算记号层（`⊤ ⊥ ⊓ ⊔ ᶜ`），为免 Mathlib 依赖而自建 |
| [`Syntax.lean`](EvidenceLogic/Core/Syntax.lean) | 语言：`Form`（含 `⊳`／`⊲`、量词）、自由变元、代入、替换上下文 `Ctx` |

## `Model/` —— 语义与模型论

| 模块 | 一句话 |
|---|---|
| [`Semantics.lean`](EvidenceLogic/Model/Semantics.lean) | **语义**：命题层 `PSet`、真值索引的经典基 `Base`（定义 `⊢`）、语法索引的背书框架 `Frame`、模型类 `IsModel` |
| [`Canonical.lean`](EvidenceLogic/Model/Canonical.lean) | 典范（自由）模型族与存在性定理：满足全部规则的最一般语义 |
| [`Soundness.lean`](EvidenceLogic/Model/Soundness.lean) | 可靠性：`⊢ᴱ φ ⇒ M ⊨ φ`（对一切模型） |
| [`Strict.lean`](EvidenceLogic/Model/Strict.lean) | **第二模型族**（严格蕴含框架：`X ⊳ Y ⟺ X ≤ Y`）；`strict_isModel` ⇒ **全量 `Derivable` 的**无条件不变量 `strict_supp_le`；`strict_transitivity_rule_valid` 把定稿的设计理由证明成定理 |
| [`Threshold.lean`](EvidenceLogic/Model/Threshold.lean) | **第三模型族**（阈值族：`X ⊳ Y ⟺ X ≤ Y ∨ X = U ∨ Y = ⊤`，`U` 任意）；`th_supp_le` 给出**每阈值一条**的不变量；`thSuppP_not_transitive` 说明破坏传递性的是"阈值**形状**"而非 `⊤` 本身（**零公理**） |

## `System/` —— 证明系统与定稿第八／九／十节

| 模块 | 一句话 |
|---|---|
| [`Derivable.lean`](EvidenceLogic/System/Derivable.lean) | **公理系统**：10 个构造子，一一对应定稿各条规则（E／S1／S2／F1–F4／R1／P1／P2） |
| [`Properties.lean`](EvidenceLogic/System/Properties.lean) | 第八节：右封闭、合取封闭、爆炸、不蕴涵真 |
| [`Derived.lean`](EvidenceLogic/System/Derived.lean) | 第九节：16 项可导出结果（含四条"关系的关系"） |
| [`NonDerivable.lean`](EvidenceLogic/System/NonDerivable.lean) | 第十节：`Fin 3` 上的有限反模型逐条反驳，134 条声明 |
| [`NonAdmissible.lean`](EvidenceLogic/System/NonAdmissible.lean) | **规则级非可容许（N3）**：把"推不出"加强为"前提全可推导而结论不可推导"，10 条 + 见证筛子 + 残余障碍 |

## `Analysis/` —— 证据语义分析

> 判据到底由哪些析取项构成、支持／反驳满足哪些定律、证据项本身是什么、能推到哪一步。

| 模块 | 一句话 |
|---|---|
| [`Structure.lean`](EvidenceLogic/Analysis/Structure.lean) | **结构事实**：退化支持者既支持也反驳一切；支持自反但不传递；关系式真值恒为常值 |
| [`Disjuncts.lean`](EvidenceLogic/Analysis/Disjuncts.lean) | **判据的本质形式**：支持侧本质 **2** 项、反驳侧本质 **3** 项；析取项**必要性**（删去反驳侧 `Y = ⊤` 后框架**不是模型**） |
| [`Algebra.lean`](EvidenceLogic/Analysis/Algebra.lean) | **代数画像**（44 条）：支持"有单位、无乘法"，反驳更贫瘠；**`refutP X Y → suppP X Yᶜ` 为假** ⇒ `⊲` 是独立原语 |

| [`Evidence.lean`](EvidenceLogic/Analysis/Evidence.lean) | 证据项的 **`Type` 值呈现** `Ev`：证据是可计算数据；`Derivable → Ev` 被**内核禁止**（`Prop` 不能大消去到 `Type`） |
| [`Inversion.lean`](EvidenceLogic/Analysis/Inversion.lean) | **原子支持者的正向刻画**：最后一步 ∈ `{e,s1,s2,f1,f4}`（**紧**）；并**证伪**了"`f1/f4` 也被排除"的假设 |
| [`InversionRefut.lean`](EvidenceLogic/Analysis/InversionRefut.lean) | **原子反驳者的正向刻画**：最后一步 ∈ `{e,r1,f1,f4}`（**紧**，四槽位皆有见证） |
| [`NormalForm.lean`](EvidenceLogic/Analysis/NormalForm.lean) | **正规形**：`s2` 链剥净、被支持式沿链单调、端点**唯一**；用"强化消去器"，无需终止性证明 |
| [`Initiality.lean`](EvidenceLogic/Analysis/Initiality.lean) | **初始性**：Lindenbaum 商与解释下降＋唯一性；可靠性 = 显式 `Derivable.rec` 折叠 |

## `Frontier/` —— 唯一前沿：支持传递 / S7

> 两条未拿下规则的可复核障碍链——从"整段禁用 `E`"逐级放宽，最后条件化到**一条引理**。

| 模块 | 一句话 |
|---|---|
| [`EFree.lean`](EvidenceLogic/Frontier/EFree.lean) | **无 `E` 片段**：支持-蕴含不变量 `⟦a⟧ ≤ ⟦b⟧` 成立 ⇒ 两规则结论在一切典范框架中**有效** |
| [`RestrictedE.lean`](EvidenceLogic/Frontier/RestrictedE.lean) | **受限 `E` 片段**（严格扩张）：`E` 源公式不含关系子公式；不变量只在**典范框架**上可陈述（机制见设计说明 §8） |
| [`Transfer.lean`](EvidenceLogic/Frontier/Transfer.lean) | **转移引理**：分量关系自由时已证；一般形式单列为 `Prop`，并给出**边界被占据**的证据 |
| [`Conditional.lean`](EvidenceLogic/Frontier/Conditional.lean) | **条件化前沿定理**：`TransferLemma ⇒` 无片段限制的不变量 ⇒ 支持传递／S7 障碍。**`E` 的"洞在顶层"不在关键路径上** |
| [`Probe.lean`](EvidenceLogic/Frontier/Probe.lean) | 探针工具箱：任意 `suppI := S` 的基结构；单层两条**无条件**分量等式 |
| [`Obstruction.lean`](EvidenceLogic/Frontier/Obstruction.lean) | **反驳搜索**：`PUnit` 上 256 基结构 × 32 关系式 = 16384 组，**0 反例**；朴素候选族整族排除 |
| [`SingleLayer.lean`](EvidenceLogic/Frontier/SingleLayer.lean) | λ-探针 ＋ `probe_pair`（对任意 `S` 的通用等式，零实例归约） |
| [`SingleLayerFull.lean`](EvidenceLogic/Frontier/SingleLayerFull.lean) | **单层情形完整闭合**（`TransferLemma` 的深度 +1 片段） |
| [`NoRelFragment.lean`](EvidenceLogic/Frontier/NoRelFragment.lean) | **关系自由分量（无条件、全量 `Derivable`）**：`supp_le_canon_of_noRel`；两条障碍的收窄 `countermodel_needs_rel`／`s7_countermodel_needs_rel`（反例必须含关系子公式） |

## 汇总

| 模块 | 一句话 |
|---|---|
| [`EvidenceLogic.lean`](EvidenceLogic.lean) | 汇总模块（按 `Core → Model → System → Analysis → Frontier` 顺序导入） |

---

# 主要结果（只列重点，逐条细节见 [`docs/主要结果.md`](docs/主要结果.md)）

1. **第十节 10/12 条"推不出"加强为规则级非可容许** —— 每条给出"前提全可推导、结论不可推导"的实例；
   残余两条（支持传递、S7）的障碍见下。
2. **`⊲` 是独立原语**（`Algebra.lean`）：`refutP X Y → suppP X Yᶜ` **为假** ⇒ 反驳**不能**由
   "支持一个否定"定义——定稿第一节的设计在语义上有据。
3. **判据的本质形式**：支持侧 `X ≤ Y ∨ X = ⊤`，反驳侧 `X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊤`；
   支持侧 `X = ⊤` 是**唯一**破坏传递性的装置（**措辞已在 §7.7 修正**：真正起作用的是
   "支持者恰等于某个固定阈值"这一**形状**，见第 10 条），反驳侧 `Y = ⊤` 是 **P1（`kR = ⊲`）必需**。
4. **证据项的正向刻画**：原子支持者的根 ∈ `{e,s1,s2,f1,f4}`、原子反驳者 ∈ `{e,r1,f1,f4}`（皆紧）；
   `s2` 正规形端点唯一。
5. **可靠性 = 折叠**（`Initiality.lean`）：`Derivable.soundness` 可显式写成 `Derivable.rec` 应用，
   即"初始代数到任意模型代数的唯一同态"。
6. **`Prop` / `Type` 的核层面事实**：`Derivable → Ev` **不可定义**（`Prop` 不能大消去到 `Type`）；
   故"用 `Prop` 还是 `Type`"是实质承诺，也解释了"正向刻画"为何在 `Prop` 呈现下受限。
7. **两条残余规则的障碍链**：无 `E` 片段 → 受限 `E` 片段 → `TransferLemma`（**一条引理**）⇒
   支持传递／S7 的 N3 障碍 ⇒ `TruthPropagation`。条件化链条已机器验证。
8. **第二个模型族**（`Strict.lean`）：把定稿**拒绝**的朴素 `X ≤ Y` 读法做成框架并证明它**也是模型**
   ——于是"否则支持传递将成为有效式"成为定理（`strict_transitivity_rule_valid`）；
   在这个框架上，**全量 `Derivable`**（含任意 `E`）的支持-蕴含不变量**无条件**成立
   （`strict_supp_le`，本工程第一条这样的结果）。
9. **关系自由区的无条件不变量与障碍收窄**（`NoRelFragment.lean`）：由"命题层是常值／`suppI` 无关"
   这座桥把第 8 条搬到**典范框架**，得 `supp_le_canon_of_noRel`（全量 `Derivable`，**不需** `TransferLemma`，
   代价是分量 `NoRel`）；再把 `strict_supp_le` 沿两条前提**串联**（`strict_supp_le_trans`）得
   `transitivity_le_canon_of_noRel`——**中间公式 `b` 可以任意**，于是
   **支持传递／S7 的典范框架反例必须让*结论的分量*含关系子公式**
   （`countermodel_needs_rel`／`s7_countermodel_needs_rel`）——与既有的"反例处 `⟦b⟧ = ⊤`"是**独立**的语法限制。
10. **第三个模型族：阈值族**（`Threshold.lean`）：把 `suppP` 的 `X = ⊤` 一般化为**任意固定阈值** `U`，
    仍是模型（`th_isModel`），并给出**每阈值一条**的参数化不变量 `th_supp_le`；
    `thSuppP_not_transitive`（**零公理**）对任意 `U` 给出非传递见证 ⇒ 破坏传递性的是
    "阈值**形状**"而不是 `⊤` 这个具体集合（`U = ⊤` 时即 `Canon.suppP_not_transitive`）。

# 未证与已修正（诚实清单，详见 [`docs/讨论与局限.md`](docs/讨论与局限.md) 第 7 节）

* **唯一实质前沿**：`TransferLemma`（一般形式）——**未证、未被反驳**。
  它不成立时只意味着现有唯一路线失效，**不**等于推翻"支持传递／S7 是 admissible 但不可导出"的判断
  （该引理是**充分**条件，必要性未知）。第 8–10 条给出的是**绕过它的另一条路线在关系自由区成立**
  以及**语义族的自由度**，都不解决一般情形（`NoRel` 是结论分量上的强语法限制）。
* **未完成/未判定项**：`Algebra` 的个别方向律、`Initiality.completeness_as_injectivity`（只作陈述）等。
* **六处被机器检查推翻或修正的分析**：析取项数（曾写"三项/四项最小装置"）、反演假设（曾写
  "`f1/f4` 也被排除"）、`refutP` 端点支（曾记"数学上成立"）、不变量的适用范围（曾要求任意模型）、
  前沿定位（曾归因于 `E` 的洞）、以及"`X = ⊤` 是唯一破坏传递性的装置"（阈值族给出反例，
  见 §7.7）。**"证不出来"的三种根因**也一并记在那里。
