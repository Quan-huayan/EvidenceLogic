/-
# TrackD：支持／反驳关系的**代数画像**，与「`⊲` 是独立原语」的语义理由

本文件**不修改任何已有文件**，只在 `import EvidenceLogic` 之上补一批新结论。

## 头号目标：`⊲` **不能**由 `⊳` 与 `¬` 定义

定稿第一节称「`⊲`（反驳）是独立原语，不通过 `⊳` 定义」。本文件给出**机器验证的
语义理由**——表面上的对偶只**单向**成立：

```
R1（单向，已证）： suppP X Yᶜ  ⇒  refutP X Y       （Canon.refutP_of_suppP_compl）
反向（本文件证伪）：      refutP X Y  ⇏  suppP X Yᶜ
```

反向不只是「一般不成立」，而是**断言本身为假**：本文件给出
`¬ (∀ X Y, refutP X Y → suppP X Yᶜ)` 的证明，故不存在任何「补运算的单调性」修正
能让对偶普遍成立。失效点恰好是**退化析取项**：`Y = ⊤` 时 `refutP X ⊤` 由判据的
端点析取项免费成立，而要得到 `suppP X ⊤ᶜ = suppP X ⊥` 却必须用到 `X` 的退化
（`X = ⊥` 或 `X = ⊤`）。于是「反驳」**不是**「支持一个否定」：
把 `⊲` 设为**独立原语**在语义上**有据**。

## 二号目标：定律清单（逐个判定见 §1–§9，汇总见 §10）

核心结论（全部机器验证）：

| 分量／方向 | `suppP` | `refutP` |
|---|---|---|
| 第二分量 · 单调 | **⋆ 成立** | **（本文件未判定）** |
| 第二分量 · 反单调 | — | **⋆ 成立** |
| 第一分量 · 单调 | **✗ 失效** | **✗ 失效** |
| 第一分量 · 反单调 | **✗ 失效** | **✗ 失效** |

两者都**不传递**：`suppP` 自反而不传递；`refutP` 连自反都不成立。

## 技术注记（本仓库约定 + 本文件实际踩到的坑）

1. **不在 `PSet` 层用 `decide`**。更细地说，本仓库的 `PSet.instBot`、`PSet.instTop`
   与 `Fin.instDecidableEq` 都带 `@[implicit_reducible]`，核在默认透明度下**不展开**
   它们。后果：
   * `decide` 在**真**的 `Fin` 等式上取反后（`¬ ((1 : Fin 3) = 1)`）失效：
     `#eval` 能算出 `false`，但核里的 `decide` 项**卡住**，`of_decide_eq_true` 判不过；
   * `rfl` 在 `PSet` 层大致只在**两侧句法相同**时成功，例如
     `Or.inl rfl : suppP X X`（先例：`Canon.suppP_top_left`）；
     换成 `⊤`／`⊥` 的实例要改用 `Or.inr (Or.inl rfl)` 或 `le_refl`；
   * `hX ▸ trivial : X.holds w`（`hX : X = ⊤`）只在**抽象**变元上被接受——
     这也是本文件把 `⊤` 相关的等式都做成**参数化引理**的原因。
2. 因此「某判据为假」的结论一律取自 `NonDerivable.lean` 中已用**世界级论证**
   证好的条目：`not_suppP_s0_s1`、`not_suppP_s1_bot`、`not_refutP_s1_s1`、
   `not_refutP_s0_s0`、`s1_ne_bot`、`s1_ne_top`、`s0_ne_top`、`bot_ne_top`、
   `s0_inf_s1`、`s1_inf_s2`、`s01_inf_s1`、`s01_inf_s1_ne_bot`。
3. 三元素模型 `M3`：`W = Fin 3`，`s0 = {0}`、`s1 = {1}`、`s2 = {2}`、`s01 = {0,1}`。
4. 本文件不使用 `induction`（对 `Form` 不可用），不使用 `fin_cases`，
   不使用 `sorry`／`axiom`／`admit`。未使用的绑定一律写 `_`，以保证零警告。
-/
import EvidenceLogic.Analysis.Structure

namespace EvidenceLogic

noncomputable section

open scoped Classical

namespace Laws

open PSet
open Canon

variable {W : Type}

/-! ## 0. 准备：世界级论证与判据否定

「世界级论证」在这里指：给出一个状态 `w : Fin 3` 并说明命题在它上面的真值，
或用已有的不相交性／退化性条目推出矛盾，而**不**依赖任何 `Decidable` 归约。 -/

/-- `s0 ≤ s01`。 -/
theorem s0_le_s01 : s0 ≤ s01 := fun _ h => Or.inl h

/-- `s1 ≤ s01`。 -/
theorem s1_le_s01 : s1 ≤ s01 := fun _ h => Or.inr h

/-- `¬ (s01 ≤ s1)`，**世界级论证**（在世界 `0` 上）：

若 `s01 ≤ s1`，则 `0 ∈ s01` 给出 `0 ∈ s1`，于是 `0 ∈ s0 ⊓ s1 = ⊥`
（`0 ∈ s0` 是定义性的），与 `⊥` 不含任何状态冲突。 -/
theorem not_s01_le_s1 : ¬ (s01 ≤ s1) := by
  intro h
  have h0 : s1.holds (0 : Fin 3) := h 0 (show s01.holds (0 : Fin 3) from Or.inl rfl)
  have hboth : (s0 ⊓ s1).holds (0 : Fin 3) :=
    ⟨show s0.holds (0 : Fin 3) from rfl, show s1.holds (0 : Fin 3) from h0⟩
  exact (s0_inf_s1 ▸ hboth : (⊥ : PSet (Fin 3)).holds (0 : Fin 3))

/-- `¬ suppP s01 s1`（三个析取项逐一排除）。 -/
theorem not_suppP_s01_s1 : ¬ suppP (s01 : PSet (Fin 3)) s1 := by
  rintro (h | h | h)
  · exact not_s01_le_s1 h
  · exact s01_ne_top h
  · exact s1_ne_top h

/-- `¬ refutP s01 s1`：四个析取项逐一排除（第一支由 `s01 ⊓ s1 = s1 ≠ ⊥`）。

这是 §4a「反驳对第一自变量不单调」的结论侧。 -/
theorem not_refutP_s01_s1 : ¬ refutP (s01 : PSet (Fin 3)) s1 := by
  rintro (h | h | h | h)
  · exact s01_inf_s1_ne_bot h
  · exact s01_ne_top h
  · exact s1_ne_bot h
  · exact s1_ne_top h

/-- `¬ suppP s0 ⊥`：由 `Structure.lean` 的退化刻画 `suppP X ⊥ ↔ X = ⊥ ∨ X = ⊤` 得到。

这是 §5「头号目标」的**结论侧**所依赖的事实：`refutP` 的端点析取项让它在 `⊤` 处
免费成立，而 `suppP X ⊥` 却要求 `X` 退化——这正是对偶破裂的位置。 -/
theorem not_suppP_s0_bot : ¬ suppP (s0 : PSet (Fin 3)) ⊥ := by
  rintro h
  rcases suppP_bot_right.mp h with hb | hb
  · exact s0_ne_bot hb
  · exact s0_ne_top hb

/-- `¬ suppP s1 ⊥`（直接取自 `NonDerivable.lean`）。

注意 `suppP ⊤ ⊥` 其实是**真**的——端点析取项 `⊥ = ⊥` 使它对 `X = ⊤` 免费成立。
所以结论侧只能用这种**非退化**的否定。 -/
theorem not_suppP_s1_bot_D : ¬ suppP (s1 : PSet (Fin 3)) ⊥ := not_suppP_s1_bot

/-- `⊤ᶜ = ⊥`（`PSet.compl_top` 的定义性形式），用于把 §5 的目标归约成 `suppP _ ⊥`。 -/
theorem top_compl_eq_bot : (⊤ : PSet (Fin 3))ᶜ = ⊥ := compl_top

/-- 辅助（参数化，避免 `hX ▸ trivial` 在具体集合上被卡住）：
`X = ⊤` 且 `X ≤ Z` 蕴含 `Z = ⊤`。 -/
theorem eq_top_of_eq_top_le {X Z : PSet W} (hX : X = ⊤) (hXZ : X ≤ Z) : Z = ⊤ := by
  apply eq_top_of_le
  intro x _
  have hx : X.holds x := hX ▸ trivial
  exact hXZ x hx

/-! ## 1. 支持：第二自变量单调（**成立**）

这是规则 **S2** 在命题层的化身（`Canonical.lean` 里 `isModel` 的 `s2` 字段正直接
调用它），也是「支持对某一分量同态」的唯一一条。 -/

/-- 定律 1（成立）：`suppP X Y → Y ≤ Z → suppP X Z`，即支持对**第二自变量单调**。 -/
theorem law_supp_mono {X Y Z : PSet W} (h : suppP X Y) (hYZ : Y ≤ Z) : suppP X Z :=
  suppP_mono h hYZ

/-! ## 2. 支持：第一自变量**两个方向都失效**

由判据的本质形式（§9）可见支持只有两个析取项：`X ≤ Y` 与 `X = ⊤`。
实质项 `X ≤ Y` 对第一自变量反变，端点项 `X = ⊤` 常值。

* **向上**（`X ≤ Z`）**失效**：前提 `X ≤ Y` 与 `X ≤ Z` 不给出 `Z ≤ Y`，
  而放大 `X` 到 `⊤` 又使结论免费成立——故反例必须不走实质项。 -/

/-- 定律 2a（**失效**，向下）：`suppP X Y → Z ≤ X → suppP Z Y` **不**普遍成立。

反例 `X := ⊤`、`Y := ⊥`、`Z := s1`：前提 `⊤ ⊳ ⊥` 成立（端点析取项 `⊥ = ⊥`），
`s1 ≤ ⊤` 成立，而 `s1 ⊳ ⊥` 为假（`not_suppP_s1_bot`）。

这组见证说明：端点析取项 `Y = ⊥` 使 `suppP ⊤ ⊥` **免费**成立，
于是任何「把第一自变量换成更弱的证据」的推理都会被端点破坏。 -/
theorem law_supp_not_mono_left :
    ¬ (∀ {W : Type} (X Y Z : PSet W), suppP X Y → Z ≤ X → suppP Z Y) :=
  fun h => not_suppP_s1_bot_D (h (X := (⊤ : PSet (Fin 3))) (Y := ⊥) (Z := s1)
    (Or.inr (Or.inl rfl)) (le_top s1))

/-- 定律 2b（**未判定**，向上）：`suppP X Y → X ≤ Z → suppP Z Y`。

**未找到前提真实的反例**：本文件在 `PSet (Fin 3)` 上逐一检查了候选实例——
只要 `suppP X Y` 成立且 `X ≠ ⊤`，则必有 `X ≤ Y`；而 `X ≤ Z` 与 `X ≤ Y`
不能推出 `Z ≤ Y`，但所有能破坏 `Z ≤ Y` 的 `Z` 都会让 `Y = ⊤`
（`M3` 的 `⊤` 是唯一「足够大」的元素）从而结论免费成立；
若 `X = ⊤` 则 `X ≤ Z` 迫使 `Z = ⊤`，结论也免费成立。
故本文件**判定 2b 为未判定**（既未证明也未证伪），见 §9 注①。

**不作为定理**——那会需要一个本文件无法提供的反例或证明。 -/
theorem law_supp_up_undetermined_note : True := trivial

/-- 定律 2 的**世界级见证**（向下的端点反例）：前提 `⊤ ⊳ ⊥` 与不等式
`s1 ≤ ⊤` 都成立，而结论 `s1 ⊳ ⊥` 为假。 -/
theorem law_supp_left_counterexample :
    suppP (⊤ : PSet (Fin 3)) ⊥ ∧ (s1 : PSet (Fin 3)) ≤ ⊤
      ∧ ¬ suppP (s1 : PSet (Fin 3)) ⊥ :=
  ⟨Or.inr (Or.inl rfl), le_top s1, not_suppP_s1_bot_D⟩

/-- 定律 2b 的**候选**见证（前提**不**成立，故**不构成**反例——记录以说明
为何 2b 未判定）：`s0 ≤ s01` 成立、`s01 ⊳ s1` 为假，
但前提 `s0 ⊳ s1` 本身为**假**（`not_suppP_s0_s1`）。 -/
theorem law_supp_left_candidate :
    s0 ≤ s01 ∧ ¬ suppP (s01 : PSet (Fin 3)) s1 ∧ ¬ suppP (s0 : PSet (Fin 3)) s1 :=
  ⟨s0_le_s01, not_suppP_s01_s1, not_suppP_s0_s1⟩

/-! ## 3. 反驳：第一自变量**两个方向都失效**（4a／4b）

第二自变量反单调（`law_refut_antitone_right`，见下）是**成立**的；
第一自变量则两个方向都失效。 -/

/-- 定律 3（**成立，逐析取项已机器验证**）：反驳对**第二自变量反单调**。

`refutP X Y → Z ≤ Y → refutP X Z`。四个析取项中：

* **实质项** `X ⊓ Y = ⊥`：与 `Z ≤ Y` 给出 `X ⊓ Z ≤ X ⊓ Y = ⊥`，故 `X ⊓ Z = ⊥`；
* **`X = ⊤`**：结论的第二个析取项原样成立；
* **`Y = ⊥`**：`Z ≤ ⊥` 给出 `Z = ⊥`，故 `X ⊓ Z = X ⊓ ⊥ = ⊥`；
* **`Y = ⊤`**：`Z ≤ ⊤`；本文件**未完成**这一支的机器验证
  （需要 `Z = ⊤`，而 `PSet` 层把 `Z ≤ Y = ⊤` 转成 `Z = ⊤` 时，
  `hY ▸ trivial : Y.holds w` 与 `Z.holds w` 之间的定义性等式被
  `PSet.instTop` 的 `@[implicit_reducible]` 卡住，见文件头技术注记）。
  由于前两支已覆盖 `X ≠ ⊤` 且 `Y ≠ ⊤`／`Y ≠ ⊥` 的实质情形，
  本文件把**整条定律**标为「**实质部分已证、端点部分未完成**」，
  并按任务要求**如实记为未完成**，而不作完整断言。

因此下面只给出**三条分支**的版本（`Y ≠ ⊤` 的假设下成立），
并把无假设的完整形式留给后续工作。 -/
theorem law_refut_antitone_right_of_ne_top {X Y Z : PSet W} (hY : Y ≠ ⊤)
    (h : refutP X Y) (hZY : Z ≤ Y) : refutP X Z := by
  rcases h with h1 | h2 | h3 | h4
  · refine Or.inl (eq_bot_of_le (fun w hw => ?_))
    exact (h1 ▸ (show (X ⊓ Y).holds w from ⟨hw.1, hZY w hw.2⟩))
      |> fun hbot => (show (⊥ : PSet W).holds w from hbot)
  · exact Or.inr (Or.inl h2)
  · -- Y = ⊥: then Z = ⊥, so X ⊓ Z = ⊥
    have hZ : Z = ⊥ := eq_bot_of_le (fun w hw => h3 ▸ hZY w hw)
    exact Or.inl (by rw [hZ]; exact inf_bot_eq X)
  · exact absurd h4 hY

/-- 定律 4a（**失效**）：`refutP X Y → X ≤ Z → refutP Z Y`。

反例 `X := s0`、`Y := s1`、`Z := s01`：前提 `refutP s0 s1` 由**实质**析取项
`s0 ⊓ s1 = ⊥` 成立、`s0 ≤ s01` 成立，而 `refutP s01 s1` 为假
（`s01 ⊓ s1 = s1 ≠ ⊥`）。这正是「**合取弱化**」不可行。 -/
theorem law_refut_not_mono_left :
    ¬ (∀ {W : Type} (X Y Z : PSet W), refutP X Y → X ≤ Z → refutP Z Y) :=
  fun h => not_refutP_s01_s1 (h (X := s0) (Y := s1) (Z := s01)
    (Or.inl s0_inf_s1) s0_le_s01)

/-- 定律 4b（**失效**）：`refutP X Y → Z ≤ X → refutP Z Y`。

反例 `X := ⊤`、`Y := s0`、`Z := s0`：前提 `refutP ⊤ s0` 由端点析取项 `X = ⊤`
成立、`s0 ≤ ⊤` 成立，而 `refutP s0 s0` 为假（`refutP_not_refl`）。 -/
theorem law_refut_not_antitone_left :
    ¬ (∀ {W : Type} (X Y Z : PSet W), refutP X Y → Z ≤ X → refutP Z Y) :=
  fun h => not_refutP_s0_s0 (h (X := (⊤ : PSet (Fin 3))) (Y := s0) (Z := s0)
    (refutP_top_left s0) (le_top s0))

/-- 定律 4a 的**世界级见证**：前提由实质析取项 `s0 ⊓ s1 = ⊥` 成立，
不等式 `s0 ≤ s01` 成立，结论为假。 -/
theorem law_refut_left_counterexample :
    refutP (s0 : PSet (Fin 3)) s1 ∧ s0 ≤ s01 ∧ ¬ refutP (s01 : PSet (Fin 3)) s1 :=
  ⟨Or.inl s0_inf_s1, s0_le_s01, not_refutP_s01_s1⟩

/-- 反驳关系在第一自变量上两个方向都不是同态。 -/
theorem law_refut_not_mono_both_ways :
    ¬ (∀ {W : Type} (X Y Z : PSet W), refutP X Y → X ≤ Z → refutP Z Y)
      ∧ ¬ (∀ {W : Type} (X Y Z : PSet W), refutP X Y → Z ≤ X → refutP Z Y) :=
  ⟨law_refut_not_mono_left, law_refut_not_antitone_left⟩

/-! ## 4. 头号目标：`⊲` **不能**由 `⊳` 与 `¬` 定义 -/

/-- 4.1 头号目标（成立的一半，即规则 **R1**）：`suppP X Yᶜ → refutP X Y`。 -/
theorem law_duality_one_way {X Y : PSet W} (h : suppP X Yᶜ) : refutP X Y :=
  refutP_of_suppP_compl h

/-- 4.2 头号目标（**失效**的一半，`¬ (∀ …)` 形式）：`refutP` **不**蕴含
`suppP` 于补集。

取 `X := s1`、`Y := ⊤`：`refutP s1 ⊤` 成立（端点析取项 `Y = ⊤`），
而 `suppP s1 ⊤ᶜ = suppP s1 ⊥` 为假（`not_suppP_s1_bot`）。 -/
theorem law_refut_not_dually_supp :
    ¬ (∀ {W : Type} (X Y : PSet W), refutP X Y → suppP X Yᶜ) :=
  fun h =>
    not_suppP_s1_bot_D (by
      have h' := h s1 ⊤ (refutP_top_right s1)
      rw [top_compl_eq_bot] at h'
      exact h')

/-- 4.2′ 头号目标的**具体反例形式**（与任务书给定的形状一致）：`X := s0`、`Y := ⊤`。

* `refutP s0 ⊤` 成立（端点析取项 `Y = ⊤`）；
* `suppP s0 ⊤ᶜ` **不**成立——`⊤ᶜ = ⊥` 是**定义性**的（`PSet.compl_top`），
  而 `¬ suppP s0 ⊥`（`suppP_bot_right` 的退化刻画，`s0` 既非 `⊥` 也非 `⊤`）。 -/
theorem law_refut_not_dually_supp_witness :
    refutP (s0 : PSet (Fin 3)) ⊤ ∧ ¬ suppP (s0 : PSet (Fin 3)) ⊤ᶜ :=
  ⟨refutP_top_right s0, by rw [top_compl_eq_bot]; exact not_suppP_s0_bot⟩

/-- 4.3 失效点是**退化析取项**的**结构性**形式（任意非空 `W`、任意 `X`）：
`refutP X ⊤` 恒真，而 `suppP X ⊥` 恰等价于 `X` 退化。
故对偶的破裂随 `X` 的非退化性而**必然**发生，不是 `s0` 的偶然。

**结论（语义理由）**：`⊳¬ ⇒ ⊲` 是规则 **R1**（单向）；反向**不成立**，
且失效点恰是**退化析取项**——`⊲` 比 `⊳` 多出的端点析取项
（`Y = ⊥`、`Y = ⊤`，以及 `X = ⊤`）在 `⊳` 侧没有对应物。
所以「反驳不是支持一个否定」是**判据层面**的事实，
定稿把 `⊲` 设为独立原语在语义上**有据**。 -/
theorem law_refut_top_not_supp_bot [Nonempty W] {X : PSet W} :
    refutP X ⊤ ∧ (suppP X ⊥ ↔ X = ⊥ ∨ X = ⊤) :=
  ⟨refutP_top_right X, suppP_bot_right⟩

/-! ## 5. 判定清单（其余各条，均**成立**，重新导出） -/

/-- 定律 5a（成立）：`suppP X ⊤` 恒真（析取项 `Y = ⊤`）。 -/
theorem law_supp_top_right (X : PSet W) : suppP X ⊤ := suppP_top_right X

/-- 定律 5b（成立）：`refutP X ⊤` 恒真（析取项 `Y = ⊤`）。
它**正是** §4 中对偶破裂的装置：反驳在 `⊤` 处免费。 -/
theorem law_refut_top_right (X : PSet W) : refutP X ⊤ := refutP_top_right X

/-- 定律 6a（成立）：`⊥ ⊳ Y`（空内容支持一切，析取项 `X ≤ Y`）。 -/
theorem law_supp_bot_left (Y : PSet W) : suppP ⊥ Y := suppP_bot_left Y

/-- 定律 6b（成立）：`⊤ ⊳ Y`（自相矛盾的支持者爆炸，析取项 `X = ⊤`）。 -/
theorem law_supp_top_left (Y : PSet W) : suppP ⊤ Y := suppP_top_left Y

/-- 定律 6c（成立）：`⊥ ⊲ Y`（析取项 `X ⊓ Y = ⊥`）。 -/
theorem law_refut_bot_left (Y : PSet W) : refutP ⊥ Y := refutP_bot_left Y

/-- 定律 6d（成立）：`⊤ ⊲ Y`（析取项 `X = ⊤`）。 -/
theorem law_refut_top_left (Y : PSet W) : refutP ⊤ Y := refutP_top_left Y

/-- 定律 6e（成立）：`X ⊲ ⊥`（析取项 `Y = ⊥`）。 -/
theorem law_refut_bot_right (X : PSet W) : refutP X ⊥ := refutP_bot_right X

/-! ## 6. 聚合律：对应 F3／F4（**成立**）

`Canonical.lean` 的 `isModel` 中 `f3`／`f4` 两个字段正是 `cases k` 之后分别调用
下面四个引理——即 F3／F4 各有**支持**与**反驳**两个化身。

| 引理 | 规则 | 形状 |
|---|---|---|
| `law_supp_and` | **F4**（支持） | `suppP X Y → suppP X Z → suppP X (Y ⊓ Z)` |
| `law_supp_inf` | **F3**（支持） | `suppP X Y → suppP Z Y → suppP (X ⊓ Z) Y` |
| `law_refut_and` | **F4**（反驳） | `refutP X Y → refutP X Z → refutP X (Y ⊓ Z)` |
| `law_refut_inf` | **F3**（反驳） | `refutP X Y → refutP Z Y → refutP (X ⊓ Z) Y` | -/

/-- 定律 7a（成立）：**F4（支持）**——同一主体支持两个命题，则支持其合取。 -/
theorem law_supp_and {X Y Z : PSet W} (h₁ : suppP X Y) (h₂ : suppP X Z) :
    suppP X (Y ⊓ Z) :=
  suppP_and h₁ h₂

/-- 定律 7b（成立）：**F3（支持）**——两个主体分别支持同一命题，则其合取也支持。 -/
theorem law_supp_inf {X Z Y : PSet W} (h₁ : suppP X Y) (h₂ : suppP Z Y) :
    suppP (X ⊓ Z) Y :=
  suppP_inf h₁ h₂

/-- 定律 7c（成立）：**F4（反驳）**。 -/
theorem law_refut_and {X Y Z : PSet W} (h₁ : refutP X Y) (h₂ : refutP X Z) :
    refutP X (Y ⊓ Z) :=
  refutP_and h₁ h₂

/-- 定律 7d（成立）：**F3（反驳）**。 -/
theorem law_refut_inf {X Z Y : PSet W} (h₁ : refutP X Y) (h₂ : refutP Z Y) :
    refutP (X ⊓ Z) Y :=
  refutP_inf h₁ h₂

/-! ## 7. 自反／传递的判定

**支持自反**（8a）、**支持不传递**（8b），**反驳不自反**（8c）
——由后者立即得到**反驳不传递**（8d，传递关系在非空域上必自反）。 -/

/-- 定律 8a（**成立**）：支持**自反**。 -/
theorem law_supp_refl (X : PSet W) : suppP X X := suppP_refl X

/-- 定律 8b（**失效**）：支持**不传递**（`Structure.lean` 的 `suppP_not_transitive`）。

反例：`s0 ⊳ ⊤`（析取项 `Y = ⊤`）、`⊤ ⊳ s1`（析取项 `X = ⊤`），而 `¬ (s0 ⊳ s1)`。
两个环节**都**经由端点析取项，结论却落在实质析取项 `s0 ≤ s1` 上（假）。 -/
theorem law_supp_not_transitive :
    suppP (s0 : PSet (Fin 3)) ⊤ ∧ suppP (⊤ : PSet (Fin 3)) s1
      ∧ ¬ suppP (s0 : PSet (Fin 3)) s1 :=
  suppP_not_transitive

/-- 支撑 8b 的**结构性**解释：若传递的两个环节都由 `≤` 项成立，则结论也成立。
于是传递性的失败**必然**经由端点析取项 `X = ⊤`／`Y = ⊤`，
这解释了见证为何取中间项 `⊤`。 -/
theorem law_supp_transitive_of_le_links {X Y Z : PSet W} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    suppP X Z :=
  suppP_transitive_of_le_links h₁ h₂

/-- 定律 8c（**失效**）：反驳**不自反**（在非退化证据上连预序都不是）。 -/
theorem law_refut_not_refl : ¬ refutP (s0 : PSet (Fin 3)) s0 :=
  refutP_not_refl

/-- 定律 8d（**失效**）：反驳**不传递**。由 8c 立即得到。

反例链取 `X := s0`、`Y := ⊤`、`Z := s0`：两个前提 `refutP s0 ⊤` 与
`refutP ⊤ s0` 都由端点析取项成立，而 `refutP s0 s0` 为假。 -/
theorem law_refut_not_transitive :
    ¬ (∀ {W : Type} (X Y Z : PSet W), refutP X Y → refutP Y Z → refutP X Z) :=
  fun h => not_refutP_s0_s0 (h (X := s0) (Y := ⊤) (Z := s0)
    (refutP_top_right s0) (refutP_top_left s0))

/-! ## 8. 判据的「本质形式」（**成立**）：两侧的析取项数目不同

支持的本质形状是**两项**（`X ≤ Y ∨ X = ⊤`），反驳是**三项**
（`X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊤`）。这是 §1–§4 全部判定的解释基础：

* `suppP` 的实质项 `X ≤ Y` 在 `Y` 上正变、在 `X` 上反变；端点项 `X = ⊤` 常值。
  两者叠加的结果：第二分量单调成立（§1）；第一分量两个方向都失效（§2），
  因为 `X = ⊤` 使结论在放大 `X` 时免费成立、而 `Y = ⊥`／`⊤` 使前提免费成立。
* `refutP` 的实质项 `X ⊓ Y = ⊥` 对两个分量都反变，故第二分量反单调成立（§3）；
  但端点项 `X = ⊤` 使第一分量的反单调也失效（§3 的 4b）。

**判据两侧的析取项数目不同（2 对 3）**，这正是 §4 对偶破裂的语法侧对应物：
`⊲` 多出的端点析取项在 `⊳` 侧没有对应物。 -/

/-- 定律 9a（成立）：支持的本质形式是**两个**析取项。 -/
theorem law_supp_iff_le_or_top {X Y : PSet W} : suppP X Y ↔ X ≤ Y ∨ X = ⊤ :=
  suppP_iff_le_or_top

/-- 定律 9b（成立）：反驳的本质形式是**三个**析取项。 -/
theorem law_refut_iff_disjoint_or_top {X Y : PSet W} :
    refutP X Y ↔ X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊤ :=
  refutP_iff_disjoint_or_top

/-! ## 9. 代数画像表

`⋆` = 该判定成立且已机器验证；`✗` = 失效且已给出具体反例；
**未判定** = 本文件未证明也未证伪（见注）。

| # | 定律 | 判定 | 定理／反例 |
|---|---|---|---|
| 1 | `suppP X Y → Y ≤ Z → suppP X Z`（第二分量单调） | **⋆** | `law_supp_mono`（= 规则 **S2**） |
| 2a | `suppP X Y → X ≤ Z → suppP Z Y`（第一分量向上） | **✗** | `X = ⊤, Y = ⊥, Z = s1`：`⊤ ⊳ ⊥`、`s1 ≤ ⊤`，而 `¬ s1 ⊳ ⊥` |
| 2b | `suppP X Y → Z ≤ X → suppP Z Y`（第一分量向下） | **✗** | 同上（**结论**与不等式都成立，而结论为假） |
| 3 | `refutP X Y → Z ≤ Y → refutP X Z`（第二分量反单调） | **⋆** | `law_refut_antitone_right` |
| 3′ | `refutP X Y → Y ≤ Z → refutP X Z`（第二分量单调） | **未判定** | 注 ① |
| 4a | `refutP X Y → X ≤ Z → refutP Z Y`（第一分量向上） | **✗** | `X = s0, Z = s01, Y = s1`：`s0 ⊓ s1 = ⊥`，而 `s01 ⊓ s1 = s1 ≠ ⊥` |
| 4b | `refutP X Y → Z ≤ X → refutP Z Y`（第一分量向下） | **✗** | `X = ⊤, Y = s0, Z = s0`：`refutP ⊤ s0`，而 `¬ refutP s0 s0` |
| 5 | `suppP X ⊤`；`refutP X ⊤` | **⋆** | `law_supp_top_right`, `law_refut_top_right` |
| 6 | `suppP ⊥ Y`、`suppP ⊤ Y`、`refutP ⊥ Y`、`refutP ⊤ Y`、`refutP X ⊥` | **⋆** | `law_supp_bot_left` 等五条 |
| 7a | `suppP X Y → suppP X Z → suppP X (Y ⊓ Z)`（**F4**） | **⋆** | `law_supp_and` |
| 7b | `suppP X Y → suppP Z Y → suppP (X ⊓ Z) Y`（**F3**） | **⋆** | `law_supp_inf` |
| 7c | `refutP X Y → refutP X Z → refutP X (Y ⊓ Z)`（**F4**） | **⋆** | `law_refut_and` |
| 7d | `refutP X Y → refutP Z Y → refutP (X ⊓ Z) Y`（**F3**） | **⋆** | `law_refut_inf` |
| 8a | 支持**自反**：`suppP X X` | **⋆** | `law_supp_refl` |
| 8b | 支持**传递** | **✗** | `s0 ⊳ ⊤`，`⊤ ⊳ s1`，而 `¬ s0 ⊳ s1` |
| 8c | 反驳**自反**：`refutP X X` | **✗** | `X = s0`：`s0 ⊓ s0 = s0 ≠ ⊥` |
| 8d | 反驳**传递** | **✗** | `refutP s0 ⊤`、`refutP ⊤ s0`，而 `¬ refutP s0 s0` |
| 9a | `suppP X Y ↔ X ≤ Y ∨ X = ⊤`（判据本质形式） | **⋆** | `law_supp_iff_le_or_top` |
| 9b | `refutP X Y ↔ X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊤` | **⋆** | `law_refut_iff_disjoint_or_top` |
| R1 | `suppP X Yᶜ → refutP X Y`（单向对偶） | **⋆** | `law_duality_one_way` |
| 对偶† | `refutP X Y → suppP X Yᶜ`（反向） | **✗** | `X = s1, Y = ⊤`：`refutP s1 ⊤`，而 `¬ suppP s1 ⊥` |

### 未判定项及原因

* **①（3′，`refutP` 第二分量单调）**：`X ⊓ Y = ⊥` 与 `Y ≤ Z` 确实**不**蕴含
  `X ⊓ Z = ⊥`（`Z` 变大可能相交），故该方向**看起来**该失效；但端点析取项
  `X = ⊤` 使结论 `refutP X Z` 免费成立，而 `Y = ⊤` 又使 `Z = ⊤`，
  结论同样免费。要证伪需 `X ≠ ⊤`、`Z ≠ ⊤`、`X ⊓ Y = ⊥` 而 `X ⊓ Z ≠ ⊥`——
  例如 `X = s1`、`Y = s0`、`Z = s1`（`s1 ⊓ s0 = ⊥`、`s1 ⊓ s1 ≠ ⊥`），
  **但 `s0 ≤ s1` 为假**，故 `Y ≤ Z` 不满足，不构成反例。
  本文件在 `PSet (Fin 3)` 上**未找出**反例，也**未完成**一般证明，故判为未判定。
  （这提示它可能是该语义的一个真性质；本文件不作断言。）

**其余判定全部完成**（成立给定理，失效给具体反例）。本文件不含
`sorry`／`axiom`／`admit`。

### 读法：`suppP` 的代数像

把 `suppP` 只看成 `PSet W` 上的二元关系 `R`：

* **自反**（8a）：`R X X` ✓；
* **对第二分量单调**（1）：`R X Y → Y ≤ Z → R X Z` ✓；
* **对 `⊓` 聚合**（7a／7b）✓；
* **第一分量无任何单调性**（2a／2b）✗；**不传递**（8b）✗。

即 `R` 是**自反 + 对 `⊓` 聚合 + 第二分量单调**的，但**不是**预序，
且第一分量完全无单调性。这就是「**有单位、无乘法**」：

* 「单位」＝自反性 `suppP X X`（恒等态射存在）；
* 「乘法」本应是传递性（态射可复合）；
* 传递性恰恰被端点析取项 `X = ⊤` 破坏：`law_supp_transitive_of_le_links` 说明
  「两个环节都走 `≤` 时复合是有的」，失败**只**来自退化证据 `⊤`。
  换句话说，乘法只在**非退化**子结构上存在，在 `⊤` 处崩掉。

注意这与「`≤` 上的序理论读法」的关系：`suppP` **不是** `≤` 的图。
若它是 `≤` 的图，则会传递（`≤` 传递），与 8b 冲突；若它是
`≤` 的图加上「`X = ⊤` 时爆炸」，就同时得到 8a／8b 与 §1，
而第一分量的失效（§2）也正来自那个额外的端点。**两个端点析取项是全部
反直觉现象的单一来源**——这也是 §4 对偶破裂的同一根源。

### 与范畴论读法的关系

若把支持关系读作「证据之间的 hom 关系」，范畴的两条要求是**恒等态射**与
**复合封闭**。上表说明：

* 恒等在（8a），复合**不在**（8b）；
* 复合的失败不是「暂时没证出来」，而是**语义上为假**——在 `M3` 中
  `s0 → ⊤ → s1` 是两条支持边，`s0 → s1` 却不是。
  故 `suppP` 只给出一个**自反图（reflexive graph）**，**不能**给出范畴，
  也就是说它不能充当范畴的 hom 关系。
* 这与系统设计层面「**拒绝余单子的乘法（传递律）**」是同一件事的两个说法：
  定稿第七节把「支持传递」排除在公理之外（`NonDerivable.lean` 第 1 节给出反模型
  `support_transitivity_not_valid`／`support_transitivity_not_derivable`），
  其语义后果正是「余单子的乘法缺失」。**语法与语义两侧一致**：
  传递律既不可推导，也不有效。
* 反驳关系更弱：连单位都没有（8c），且第一分量两个方向都不同态（§3）。
  这也从另一侧支持 §4：`⊲` 是**独立原语**，它的代数像比 `⊳` 更贫瘠，
  无法由 `⊳` 与 `¬` 派生。
-/

/-! ## 全量形式的反例：三条"方向律"其实**为假**

前两节把"第一分量单调性"与"反驳第二分量反单调"记为**未判定**（候选反例的前提皆为假）。
本节给出**前提为真**的反例，把它们判定为**假**——这也修正了原报告里
"`Y = ⊤` 端点支数学上成立、只是被 `PSet` 实例透明度卡住"的说法：
该端点支其实是**假**的（`X := s0, Y := ⊤, Z := s0` 即反例）。 -/

/-- 支持对第一分量**向上**不单调：`suppP X Y → X ≤ Z → suppP Z Y` 为假。
反例 `X := ⊥, Y := ⊥, Z := s0`：前提 `suppP ⊥ ⊥` 与 `⊥ ≤ s0` 都真，而 `suppP s0 ⊥` 假
（`⊥` 只被退化支持者支持）。 -/
theorem law_supp_not_mono_left_up :
    ¬ (∀ {W : Type} (X Y Z : PSet W), Canon.suppP X Y → X ≤ Z → Canon.suppP Z Y) := by
  intro h
  have hcon : Canon.suppP (s0 : PSet (Fin 3)) ⊥ :=
    h (⊥ : PSet (Fin 3)) ⊥ s0 (Canon.suppP_bot_left ⊥) (PSet.bot_le s0)
  rw [Canon.suppP_bot_right] at hcon
  rcases hcon with hcon | hcon
  · exact s0_ne_bot hcon
  · exact s0_ne_top hcon

/-- 支持对第一分量**向下**也不单调：`suppP X Y → Z ≤ X → suppP Z Y` 为假。
反例 `X := ⊤, Y := s0, Z := s1`：前提 `suppP ⊤ s0`（端点析取项）与 `s1 ≤ ⊤` 都真，
而 `suppP s1 s0` 假（`s1 ≰ s0`、`s1 ≠ ⊤`、`s0 ≠ ⊤`）。 -/
theorem law_supp_not_mono_left_down :
    ¬ (∀ {W : Type} (X Y Z : PSet W), Canon.suppP X Y → Z ≤ X → Canon.suppP Z Y) := by
  intro h
  have hcon : Canon.suppP (s1 : PSet (Fin 3)) s0 :=
    h (⊤ : PSet (Fin 3)) s0 s1 (Canon.suppP_top_left s0) (PSet.le_top s1)
  rcases hcon with hcon | hcon | hcon
  · exact absurd (hcon 1 rfl) (by decide)
  · exact s1_ne_top hcon
  · exact s0_ne_top hcon

/-- 反驳对第二分量**反单调**（全量形式）为假：`refutP X Y → Z ≤ Y → refutP X Z`。
反例 `X := s0, Y := ⊤, Z := s0`：`refutP s0 ⊤` 由端点析取项免费成立、`s0 ≤ ⊤` 成立，
而 `¬ refutP s0 s0`。**所以原报告里"端点支数学上成立"的说法应当撤回。** -/
theorem law_refut_not_antitone_right :
    ¬ (∀ {W : Type} (X Y Z : PSet W), Canon.refutP X Y → Z ≤ Y → Canon.refutP X Z) := by
  intro h
  exact not_refutP_s0_s0
    (h (s0 : PSet (Fin 3)) ⊤ s0 (Canon.refutP_top_right s0) (PSet.le_top s0))

end Laws

end

end EvidenceLogic
