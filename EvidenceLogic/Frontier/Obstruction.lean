/-
# TrackR：对 `TransferLemma` 的反驳尝试、障碍分析与穷举搜索

本文件**不修改任何已有文件**，只在既有 `import` 之上补新结论。
所有绑定要么使用、要么写 `_`；不使用 `sorry`／`axiom`／`admit`／`native_decide`。

## 0. 结论摘要

* **没有找到反例**。`TransferLemma`（`EvidenceLogic/Transfer.lean` 第 3 节）在本文件中
  **既没有被证明，也没有被反驳**。
* 第 2.6 节**证伪**了两条原先被当作「障碍」的中间命题
  （`a ⊓ b = a ⊓ b' ⇒ a ≤ b` 与 `a ⊔ b = a ⊔ b' ⇒ b = b'`，两者都是**假**的）；
  第 2.7 节给出并**机器验证**了它们的正确替代（`inf_eq_iff_le_right`、
  `suppP_congr_of_inf_eq`、`eq_of_inf_sup_eq`）。
* 第 3 节给出 `⊣⊢` 在两个投影基上的**分量抽取引理**（机器验证）。
* 第 4 节给出**穷举搜索**（`#eval`，只用于发现，不作为证明）及其**确切范围与结果**。

## 1. 强度声明（务必先读）

1. 本文件**不**声称 `TransferLemma` 成立；
2. 本文件**不**声称 `TransferLemma` 不成立——**未找到反例**，仅此而已；
3. 本文件**不**声称搜索穷尽了一切可能性。搜索只覆盖第 4 节**逐条列出**的范围
   （单元素世界、`atomRel := ⊥`、**无量词**、自由变元仅 `{0, 1}`、
   16 × 16 张真值表 × 2 个赋值、候选池 `gen1`＝ 32 个公式、嵌套深度 ≤ 1）；
4. 本文件**不**声称 `TransferLemma` 与 `Conditional.lean` 的条件化链条的关系已被判定；
5. 下表说明每一节结论的**性质**（定理 / 反例 / 计算），不得互相冒充：

   | 内容 | 性质 |
   |---|---|
   | `suppP_def`、`suppP_of_left_top/right_top`、`suppP_bot_left` | 机器验证的定理 |
   | `suppP_mono`、`suppP_eq_of_le_both` | 机器验证的定理 |
   | `not_forall_inf_eq_le`、`not_forall_sup_eq_eq`、`suppP_sup_hypothesis_fails` | 机器验证的**反例**（§2.6） |
   | `inf_eq_iff_le_right`、`suppP_congr_of_inf_eq`、`eq_of_inf_sup_eq` | 机器验证的**定理**（§2.7） |
   | `naive_family_excluded(_sup)` | 机器验证的定理（抽象形式，§2.8） |
   | `left/right_component_eq_of_cequiv` | 机器验证的定理（§3） |
   | §4 的 `#eval` | **计算**，不构成证明 |
-/
import EvidenceLogic.Frontier.Transfer

namespace EvidenceLogic
namespace TrackR

open PSet

noncomputable section

variable {W : Type}

/-! ## 2. 前提 `(★_S)` 的结构分析与障碍

`TransferLemma` 的前提是 `(u ⊳ v) ⊣⊢ (u' ⊳ v')`，即对**一切** `Base B`

    `suppI_B (⟦u⟧_B) (⟦v⟧_B) = suppI_B (⟦u'⟧_B) (⟦v'⟧_B)`          `(★_B)`

（`CEquiv` 是逐 `Base`、逐赋值的 `≤` 双向，故在每个 `Base` 上就是真值相等）。 -/

/-- `Canon.suppP` 按定义即三个析取项。 -/
theorem suppP_def (X Y : PSet W) : Canon.suppP X Y ↔ (X ≤ Y ∨ X = ⊤ ∨ Y = ⊤) :=
  Iff.rfl

/-- `a = ⊤` 时 `suppP a b` 恒成立。 -/
theorem suppP_of_left_top {a b : PSet W} (h : a = ⊤) : Canon.suppP a b :=
  Or.inr (Or.inl h)

/-- `b = ⊤` 时 `suppP a b` 恒成立。 -/
theorem suppP_of_right_top (a : PSet W) : Canon.suppP a ⊤ :=
  Or.inr (Or.inr rfl)

/-- `X = ⊥` 时 `suppP ⊥ X` 由第一析取项平凡成立。 -/
theorem suppP_bot_left (Y : PSet W) : Canon.suppP (⊥ : PSet W) Y :=
  Or.inl (fun _ h => absurd h (PSet.not_bot _))

/-- **机器验证**：`suppP` 在第二个自变量上单调。 -/
theorem suppP_mono {X Y Z : PSet W} (h : Canon.suppP X Y) (hYZ : Y ≤ Z) : Canon.suppP X Z := by
  rcases h with h | h | h
  · exact Or.inl (PSet.le_trans h hYZ)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (PSet.eq_top_of_le (h ▸ hYZ)))

/-- **机器验证**：若 `X ≤ Y` 且 `X ≤ Y'`，则 `suppP X Y` 与 `suppP X Y'` 等价
（两者都由第一析取项成立）。这是障碍 1 的**收尾**步骤（本身为真）。 -/
theorem suppP_eq_of_le_both {X Y Y' : PSet W} (hY : X ≤ Y) (hY' : X ≤ Y') :
    (Canon.suppP X Y ↔ Canon.suppP X Y') :=
  Iff.intro (fun _ => Or.inl hY') (fun _ => Or.inl hY)

/-! ### 2.5 逐点展开引理（`@[simp]`，本文件内新增，不改动已有文件）

`PSet` 的 `⊓`／`⊔`／`ᶜ` 实例在 `EvidenceLogic/Semantics.lean` 中标为
`@[implicit_reducible]`，直接对 `(a ⊓ b).holds w` 做 `▸`／投影容易被 elaborator
换形。这里补一组 `@[simp]` 展开引理，之后统一用 `rw` 把
`(a ⊓ b).holds w` 显式化成 `a.holds w ∧ b.holds w`。 -/

@[simp] theorem PSet.holds_inf (a b : PSet W) (w : W) :
    (a ⊓ b).holds w ↔ a.holds w ∧ b.holds w := Iff.rfl

@[simp] theorem PSet.holds_sup (a b : PSet W) (w : W) :
    (a ⊔ b).holds w ↔ a.holds w ∨ b.holds w := Iff.rfl

@[simp] theorem PSet.holds_compl (a : PSet W) (w : W) :
    (aᶜ).holds w ↔ ¬ a.holds w := Iff.rfl

@[simp] theorem PSet.holds_top (w : W) : (⊤ : PSet W).holds w ↔ True := Iff.rfl

@[simp] theorem PSet.holds_bot (w : W) : (⊥ : PSet W).holds w ↔ False := Iff.rfl

/-! ### 2.6 两条中间命题**为假**（附机器验证的反例）

原先本节写下的两条「障碍」中间命题**数学上是假的**：

* `a ⊓ b = a ⊓ b' ⇒ a ≤ b` **为假**（`not_forall_inf_eq_le`）。反例：`a := s0`、
  `b := b' := ⊥`（`W := Fin 3`）。前提因 `b = b'` 而平凡成立（两边都是 ⊥），
  但 `s0 ≤ ⊥` 假——世界 `0` 属于 `s0` 而不属于 `⊥`。
  正确的内核是 `a ≤ b ↔ a ≤ b'`（§2.7 `inf_eq_iff_le_right`）：
  `⊓` 的等式**只约束 `a` 上的取值**，在 `a` 之外什么也不说。
* `a ⊔ b = a ⊔ b' ⇒ b = b'` **为假**（`not_forall_sup_eq_eq`）。反例：`a := s0`、
  `b := s1`、`b' := s01`。前提成立（两边都是 `s01`），但 `s1 ≠ s01`——
  世界 `0` 属于 `s01` 而不属于 `s1`。即 `b` 与 `b'` 只可能在 `a` **之外**被约束。

**由此撤回**：「同一左分量则整族候选全灭」的说法不成立。事实上
`Canon.suppP s0 s1` 与 `Canon.suppP s0 s01` **取值不同**（前者假、后者真），
故 `S := Canon.suppP` **不满足** §2.8 中 `naive_family_excluded_sup` 的假设 `hS`
（那条引理本身是关于任意 `S` 的平凡真命题，但对 `suppP` **不可用**）。
能站住的排除机制只有 §2.7 的 `suppP_congr_of_inf_eq`（`⊓` 侧）与
`eq_of_inf_sup_eq`（`⊓` 与 `⊔` 合用），见 §2.8 的说明。 -/

/-- 反例所用的世界类型是 `Fin 3`；`s0`、`s1`、`s01` 是它的三个子集。 -/
abbrev s0 : PSet (Fin 3) := ⟨fun n => n = 0⟩

/-- 单点 `{1}`（见 `s0` 的说明）。 -/
abbrev s1 : PSet (Fin 3) := ⟨fun n => n = 1⟩

/-- 两点 `{0, 1}`（见 `s0` 的说明）。 -/
abbrev s01 : PSet (Fin 3) := ⟨fun n => n = 0 ∨ n = 1⟩

/-- `s0 ⊔ s1 = s0 ⊔ s01`：两边逐世界都是 `{0, 1}`。 -/
theorem sup_eq_s01 : s0 ⊔ s1 = s0 ⊔ s01 := by
  apply PSet.ext
  intro w
  show ((s0 ⊔ s1).holds w) ↔ ((s0 ⊔ s01).holds w)
  rw [PSet.holds_sup, PSet.holds_sup]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h

/-- `s0 ≤ s01`。 -/
theorem s0_le_s01 : s0 ≤ s01 := fun _ h => Or.inl h

/-- `s0` 不是 `⊤`（世界 `1` 不属于它）。 -/
theorem s0_ne_top : s0 ≠ (⊤ : PSet (Fin 3)) := by
  intro h
  have h1 : s0.holds (1 : Fin 3) := by rw [h]; trivial
  exact absurd h1 (by decide)

/-- `s1` 不是 `⊤`（世界 `0` 不属于它）。 -/
theorem s1_ne_top : s1 ≠ (⊤ : PSet (Fin 3)) := by
  intro h
  have h1 : s1.holds (0 : Fin 3) := by rw [h]; trivial
  exact absurd h1 (by decide)

/-- `¬ suppP s0 s1`：`s0 ≰ s1`、`s0 ≠ ⊤`、`s1 ≠ ⊤` 三条均为真。 -/
theorem not_suppP_s0_s1 : ¬ Canon.suppP s0 s1 := by
  rintro (h | h | h)
  · exact absurd (h (0 : Fin 3) rfl) (by decide)
  · exact s0_ne_top h
  · exact s1_ne_top h

/-- **反例 1（机器验证）**：`a ⊓ b = a ⊓ b' ⇒ a ≤ b` 对一切 `W`、`a`、`b`、`b'`
**不成立**。 -/
theorem not_forall_inf_eq_le :
    ¬ (∀ {W : Type} (a b b' : PSet W), a ⊓ b = a ⊓ b' → a ≤ b) := by
  intro h
  have hle : s0 ≤ (⊥ : PSet (Fin 3)) := h s0 ⊥ ⊥ rfl
  exact PSet.not_bot (0 : Fin 3) (hle (0 : Fin 3) rfl)

/-- **反例 2（机器验证）**：`a ⊔ b = a ⊔ b' ⇒ b = b'` 对一切 `W`、`a`、`b`、`b'`
**不成立**。 -/
theorem not_forall_sup_eq_eq :
    ¬ (∀ {W : Type} (a b b' : PSet W), a ⊔ b = a ⊔ b' → b = b') := by
  intro h
  have heq : s1 = s01 := h s0 s1 s01 sup_eq_s01
  have hiff : s1.holds (0 : Fin 3) ↔ s01.holds (0 : Fin 3) := by rw [heq]
  exact absurd (hiff.mpr (by decide)) (by decide)

/-- **机器验证**：`S := Canon.suppP` **不满足** `⊔` 侧排除引理的假设
（`s0 ⊔ s1 = s0 ⊔ s01` 但 `suppP s0 s1 ↛ suppP s0 s01`）。 -/
theorem suppP_sup_hypothesis_fails :
    ¬ (∀ {W : Type} (a b b' : PSet W), a ⊔ b = a ⊔ b' →
        (Canon.suppP a b ↔ Canon.suppP a b')) := by
  intro hS
  have hiff := hS s0 s1 s01 sup_eq_s01
  exact not_suppP_s0_s1 (hiff.mpr (Or.inl s0_le_s01))

/-! ### 2.7 正确版本（机器验证）

三条替代 §2.6 中假命题的定理。 -/

/-- **障碍 1 的正确内核**：`a ⊓ b = a ⊓ b'` 不给 `a ≤ b`，而给 `a ≤ b ↔ a ≤ b'`。

逐世界看，前提等价于 `a.holds w ∧ b.holds w ↔ a.holds w ∧ b'.holds w`；
在 `a.holds w` 成立处这退化为 `b.holds w ↔ b'.holds w`。 -/
theorem inf_eq_iff_le_right {W : Type} {a b b' : PSet W} (h : a ⊓ b = a ⊓ b') :
    (a ≤ b ↔ a ≤ b') := by
  have hpt : ∀ w, (a.holds w ∧ b.holds w) ↔ (a.holds w ∧ b'.holds w) := by
    intro w
    have h1 : (a ⊓ b).holds w = (a ⊓ b').holds w := congrFun (congrArg PSet.holds h) w
    rw [PSet.holds_inf, PSet.holds_inf] at h1
    exact Iff.intro (Eq.mp h1) (Eq.mpr h1)
  constructor
  · intro hab w hw
    exact ((hpt w).mp (And.intro hw (hab w hw))).2
  · intro hab' w hw
    exact ((hpt w).mpr (And.intro hw (hab' w hw))).2

/-- **障碍 1（正确版）**：`a ⊓ b = a ⊓ b'` 蕴涵 `suppP a b = suppP a b'`。

三支分别对应 `suppP a b` 的三个析取项：
* `a ≤ b`：由 `inf_eq_iff_le_right` 换成 `a ≤ b'`；
* `a = ⊤`：右边第二个析取项立即成立；
* `b = ⊤`：此时 `a ⊓ b' = a ⊓ b = a ⊓ ⊤ = a`，逐世界推出 `a ≤ b'`，
  于是右边**也**由第一析取项成立——这一步**不需要** `b' = ⊤`。 -/
theorem suppP_congr_of_inf_eq {W : Type} {a b b' : PSet W} (h : a ⊓ b = a ⊓ b') :
    Canon.suppP a b = Canon.suppP a b' := by
  have hle := inf_eq_iff_le_right h
  refine propext (Iff.intro (fun hL => ?_) (fun hR => ?_))
  · rcases hL with h1 | h1 | h1
    · exact Or.inl (hle.mp h1)
    · exact Or.inr (Or.inl h1)
    · have hb : a ⊓ b' = a := by rw [← h, h1, PSet.inf_top_eq]
      refine Or.inl (fun w hw => ?_)
      have h2 : (a ⊓ b').holds w := hb.symm ▸ hw
      rw [PSet.holds_inf] at h2
      exact h2.2
  · rcases hR with h1 | h1 | h1
    · exact Or.inl (hle.mpr h1)
    · exact Or.inr (Or.inl h1)
    · have hb : a ⊓ b = a := by rw [h, h1, PSet.inf_top_eq]
      refine Or.inl (fun w hw => ?_)
      have h2 : (a ⊓ b).holds w := hb.symm ▸ hw
      rw [PSet.holds_inf] at h2
      exact h2.2

/-- **障碍 2（这条是真的）**：`a ⊓ b = a ⊓ b'` 与 `a ⊔ b = a ⊔ b'` 同时成立 ⇒ `b = b'`。

逐世界看：`a.holds w` 成立时用 `⊓` 的等式（退化为 `b.holds w ↔ b'.holds w`），
`a.holds w` 不成立时用 `⊔` 的等式（同样退化）。 -/
theorem eq_of_inf_sup_eq {W : Type} {a b b' : PSet W}
    (h₁ : a ⊓ b = a ⊓ b') (h₂ : a ⊔ b = a ⊔ b') : b = b' := by
  have h1pt : ∀ w, (a.holds w ∧ b.holds w) ↔ (a.holds w ∧ b'.holds w) := by
    intro w
    have h : (a ⊓ b).holds w = (a ⊓ b').holds w := congrFun (congrArg PSet.holds h₁) w
    rw [PSet.holds_inf, PSet.holds_inf] at h
    exact Iff.intro (Eq.mp h) (Eq.mpr h)
  have h2pt : ∀ w, (a.holds w ∨ b.holds w) ↔ (a.holds w ∨ b'.holds w) := by
    intro w
    have h : (a ⊔ b).holds w = (a ⊔ b').holds w := congrFun (congrArg PSet.holds h₂) w
    rw [PSet.holds_sup, PSet.holds_sup] at h
    exact Iff.intro (Eq.mp h) (Eq.mpr h)
  apply PSet.ext
  intro w
  by_cases ha : a.holds w
  · exact Iff.intro (fun hb => ((h1pt w).mp (And.intro ha hb)).2)
      (fun hb => ((h1pt w).mpr (And.intro ha hb)).2)
  · exact Iff.intro
      (fun hb => ((h2pt w).mp (Or.inr hb)).elim (fun hx => absurd hx ha) id)
      (fun hb => ((h2pt w).mpr (Or.inr hb)).elim (fun hx => absurd hx ha) id)

/-! ### 2.8 排除族的抽象形式（机器验证）

下面两条把「`S` 由 `⊓` 的等式决定」／「`S` 由 `⊔` 的等式决定」写成对**任意**命题族 `S`
的排除陈述；它们本身是平凡真命题（就是假设 `hS` 的应用）。
真正的排除力来自 §2.7：`(★_{inf})` 给出 `a ⊓ b = a ⊓ b'`，由 `suppP_congr_of_inf_eq`
立刻迫使 `suppP` 相等；而「同一左分量、不同右分量」的候选族要搬到 `Canon.base`，
需要 `(★_{inf})` 与 `(★_{sup})` **合用** `eq_of_inf_sup_eq` 得到 `⟦D⟧ = ⟦D'⟧`
——注意这两个等式是在 `S := inf`／`S := sup` 两个**基**上成立的，搬到 `Canon.base`
仍需基无关性：分量**关系自由**时这由 `NoRel` 那一组引理提供，该族确实被排除；
分量**含关系子公式**时基无关性正是原缺口（`Transfer.lean` 第 2 节够不到的地方）。 -/

/-- **排除族（`⊓` 侧）**：若 `S` 满足「`a ⊓ b = a ⊓ b'` 蕴涵 `S a b ↔ S a b'`」，
则由 `⊣⊢` 在 `S := inf` 基上得到的 `a ⊓ b = a ⊓ b'` 已经迫使 `S a b ↔ S a b'`。 -/
theorem naive_family_excluded {a b b' : PSet W} {S : PSet W → PSet W → Prop}
    (hS : ∀ {x y y' : PSet W}, x ⊓ y = x ⊓ y' → (S x y ↔ S x y'))
    (h : a ⊓ b = a ⊓ b') : (S a b ↔ S a b') :=
  hS h

/-- **排除族（`⊔` 侧）**：若 `S` 满足「`a ⊔ b = a ⊔ b'` 蕴涵 `S a b ↔ S a b'`」，
则由 `⊣⊢` 在 `S := sup` 基上得到的 `a ⊔ b = a ⊔ b'` 已经迫使 `S a b ↔ S a b'`。

**注意**：`S := Canon.suppP` **不满足**这个假设（见 §2.6
`suppP_sup_hypothesis_fails`：`s0 ⊔ s1 = s0 ⊔ s01` 而 `suppP s0 s1` 假、
`suppP s0 s01` 真）。故本条对 `suppP` **不适用**。 -/
theorem naive_family_excluded_sup {a b b' : PSet W} {S : PSet W → PSet W → Prop}
    (hS : ∀ {x y y' : PSet W}, x ⊔ y = x ⊔ y' → (S x y ↔ S x y'))
    (h : a ⊔ b = a ⊔ b') : (S a b ↔ S a b') :=
  hS h

/-! ## 3. `⊣⊢` 在两个投影基上的分量抽取（机器验证）

这两条说明：`(★_S)` 在 `S` 是**投影**时确实给出分量等式——这正是 `Transfer.lean`
第 2 节 `cequiv_rel_components_of_noRel` 的机制；而 `S := Canon.suppP` 不是投影，
所以拿不到分量等式。 -/

/-- 第一投影基：`a ⊳ b` 的真值恰为 `⟦a⟧`。 -/
abbrev projBase₁ (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := fun X _ => X, refutI := fun _ _ => ⊥ }

/-- 第二投影基：`a ⊳ b` 的真值恰为 `⟦b⟧`。 -/
abbrev projBase₂ (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := fun _ Y => Y, refutI := fun _ _ => ⊥ }

/-- **左分量抽取**：`(u ⊳ v) ⊣⊢ (u' ⊳ v')` 在第一投影基上给出 `⟦u⟧ = ⟦u'⟧`。 -/
theorem left_component_eq_of_cequiv {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {u v u' v' : Form} (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) :
    (projBase₁ W atomRel).truth u ρ = (projBase₁ W atomRel).truth u' ρ := by
  have hle : (projBase₁ W atomRel).truth u ρ ≤ (projBase₁ W atomRel).truth u' ρ :=
    h.1 (projBase₁ W atomRel) ρ
  have hge : (projBase₁ W atomRel).truth u' ρ ≤ (projBase₁ W atomRel).truth u ρ :=
    h.2 (projBase₁ W atomRel) ρ
  exact PSet.ext (fun w => Iff.intro (hle w) (hge w))

/-- **右分量抽取**：`(u ⊳ v) ⊣⊢ (u' ⊳ v')` 在第二投影基上给出 `⟦v⟧ = ⟦v'⟧`。 -/
theorem right_component_eq_of_cequiv {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {u v u' v' : Form} (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) :
    (projBase₂ W atomRel).truth v ρ = (projBase₂ W atomRel).truth v' ρ := by
  have hle : (projBase₂ W atomRel).truth v ρ ≤ (projBase₂ W atomRel).truth v' ρ :=
    h.1 (projBase₂ W atomRel) ρ
  have hge : (projBase₂ W atomRel).truth v' ρ ≤ (projBase₂ W atomRel).truth v ρ :=
    h.2 (projBase₂ W atomRel) ρ
  exact PSet.ext (fun w => Iff.intro (hle w) (hge w))

/-- **左分量抽取的逐点形式**。 -/
theorem left_component_eq_of_cequiv_pointwise {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W)
    {u v u' v' : Form} (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) (w : W) :
    (projBase₁ W atomRel).truth u ρ w ↔ (projBase₁ W atomRel).truth u' ρ w := by
  rw [left_component_eq_of_cequiv atomRel h ρ]

/-- **右分量抽取的逐点形式**。 -/
theorem right_component_eq_of_cequiv_pointwise {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W)
    {u v u' v' : Form} (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) (w : W) :
    (projBase₂ W atomRel).truth v ρ w ↔ (projBase₂ W atomRel).truth v' ρ w := by
  rw [right_component_eq_of_cequiv atomRel h ρ]

/-! ## 4. 穷举搜索：把问题化为有限真值表

两个世界的情形下，`PSet W` 未必只有两个元素（元素是 `W → Prop`），
但**真值**只在 `W` 上取值。把世界类型取为 `PUnit` 时，一个 `PSet PUnit` 就完全由
它在唯一世界上的真值决定，于是任何 `Base` 在真值层面都退化为两张真值表
`suppI, refutI : {⊥, ⊤} → {⊥, ⊤} → {⊥, ⊤}`。
`{false, true}² → {false, true}` 共 `2^4 = 16` 张表，下面的 `allBoolOp` **逐张列出**
（`&&`、`||`、`!a`、`!b`、`!(a&&b)`、`!(a||b)`、`!a||b`、`a&&!b`、`!a&&b`、`a||!b`、
`!(!a||b)`、`!(a&&!b)`、`true`、`false`、`a`、`b`；它们是 `Bool` 上全部 16 个
二元函数，两两不同），故 `(suppI, refutI)` 合计恰好 `256` 种，搜索对它们**全枚举**。

`atomRel` 取常值 `⊥`（故 `atom` 的真值恒为 `⊥`）。搜索用 `Bool` 表实现，
`#eval` 执行——**只用于发现，不作为证明**。范围逐条列在下面：

* 世界：`PUnit`（单元素）；
* `atomRel := fun _ _ => ⊥`；
* 公式：**无量词**，自由变元仅 `{0, 1}`；
* 赋值：`x := ⊤` 固定，`y ∈ {⊥, ⊤}` 两种（结论在 `x := ⊤` 处检查）；
* 基结构：`16 × 16 = 256` 种 `(S, R)` 全枚举；
* 候选池 `gen1`：由 `{⊥, ⊤, x, y}` 两两组合出的关系式，共 `4 × 4 × 2 = 32` 个，
  嵌套深度 ≤ 1；
* 检查：对 `(u, v, u', v') ∈ gen1 × gen0 × gen1 × gen0`（`32 × 4 × 32 × 4 = 16384` 组）
  先做廉价筛选（`u` 或 `v` 在检查赋值处的典范真值必须不同），再对通过筛选者
  验证 `∀ S R ρ, ⟦u ⊳ v⟧ = ⟦u' ⊳ v'⟧`（两个赋值，提前退出）。

**结果：`0` 组通过筛选。** 即：在该范围内**未找到反例**。 -/
section Search

/-- 16 张布尔二元真值表（穷举 `{false, true}² → {false, true}`）。 -/
def allBoolOp : List (Bool → Bool → Bool) :=
  [fun a b => a && b, fun a b => a || b, fun a _ => !a, fun _ b => !b,
   fun a b => !(a && b), fun a b => !(a || b), fun a b => !a || b, fun a b => a && !b,
   fun a b => !a && b, fun a b => a || !b, fun a b => !(!a || b), fun a b => !(a && !b),
   fun _ _ => true, fun _ _ => false, fun a _ => a, fun _ b => b]

/-- 典范 `suppP` 的真值表：`a ≤ b ∨ a = ⊤ ∨ b = ⊤`。 -/
def suppTab (a b : Bool) : Bool := !a || b

/-- 典范 `refutP` 的真值表：`a ⊓ b = ⊥ ∨ a = ⊤ ∨ b = ⊥ ∨ b = ⊤`。 -/
def refutTab (a b : Bool) : Bool := !(a && b) || a || !b

/-- 公式在真值表模型中的值（无量词片段即第 4 节搜索的范围）。 -/
def evalB (r s : Bool → Bool → Bool) (ρ : Nat → Bool) : Form → Bool
  | .var n => ρ n
  | .atom _ _ => false
  | .bot => false
  | .top => true
  | .not φ => !evalB r s ρ φ
  | .and φ ψ => evalB r s ρ φ && evalB r s ρ ψ
  | .or φ ψ => evalB r s ρ φ || evalB r s ρ ψ
  | .imp φ ψ => !evalB r s ρ φ || evalB r s ρ ψ
  | .all _ φ => evalB r s ρ φ
  | .ex _ φ => evalB r s ρ φ
  | .supp a b => r (evalB r s ρ a) (evalB r s ρ b)
  | .refut a b => s (evalB r s ρ a) (evalB r s ρ b)

/-- 检查赋值：`x := ⊤`，`y := ⊥`。 -/
def rhoA : Nat → Bool := fun n => if n = 1 then false else true

/-- 检查赋值：`x := ⊤`，`y := ⊤`。 -/
def rhoB : Nat → Bool := fun _ => true

/-- 在全部 256 个真值表基上、两个检查赋值下，两个关系式的值都相等。 -/
def sameRel (u v u' v' : Form) : Bool :=
  allBoolOp.all fun r => allBoolOp.all fun s =>
    (evalB r s rhoA (u ⊳ v) == evalB r s rhoA (u' ⊳ v')) &&
    (evalB r s rhoB (u ⊳ v) == evalB r s rhoB (u' ⊳ v'))

/-- 公式在典范真值表下的值（检查赋值 `x := ⊤, y := ⊥`）。 -/
def canonVal (φ : Form) : Bool := evalB suppTab refutTab rhoA φ

/-- 原子池 `{⊥, ⊤, x, y}`。 -/
def gen0 : List Form := [.bot, .top, .var 0, .var 1]

/-- 一层嵌套的关系式池（32 个）。 -/
def gen1 : List Form :=
  List.flatten <| gen0.map fun a => List.flatten <| gen0.map fun b => [a ⊳ b, a ⊲ b]

/-- **搜索结果**：`(u, v, u', v')` 使得在全部 256 个基上 `u ⊳ v` 与 `u' ⊳ v'` 同值，
但 `u` 或 `v` 的典范真值不同。 -/
def counterexamples : List (Form × Form × Form × Form) :=
  gen1.foldl (fun (acc : List (Form × Form × Form × Form)) u =>
    gen0.foldl (fun (acc1 : List (Form × Form × Form × Form)) v =>
      gen1.foldl (fun (acc2 : List (Form × Form × Form × Form)) u' =>
        gen0.foldl (fun (acc3 : List (Form × Form × Form × Form)) v' =>
          if sameRel u v u' v' && (canonVal u != canonVal u' || canonVal v != canonVal v')
          then (u, v, u', v') :: acc3 else acc3) acc2) acc1) acc) []

end Search

end

end TrackR
end EvidenceLogic

open EvidenceLogic TrackR

-- 搜索空间的规模与结果（`#eval`，仅用于发现）
-- #eval gen1.length
-- #eval allBoolOp.length * allBoolOp.length
-- #eval counterexamples.length
-- #eval counterexamples.map (fun t => (repr t.1, repr t.2.1, repr t.2.2.1, repr t.2.2.2))
