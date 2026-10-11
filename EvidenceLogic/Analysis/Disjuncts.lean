/-
# 析取项的必要性（Disjuncts）
把「两个写出来的析取项是冗余的、其余各司其职」变成机器验证

本文件**不修改任何已有文件**，只在 `EvidenceLogic` 之上把「析取项分工」的分析
变成可编译的定理。判据（`EvidenceLogic/Canonical.lean`）：

```
X ⊳ Y  ⟺  X ≤ Y  ∨  X = ⊤  ∨  Y = ⊤                       （Canon.suppP）
X ⊲ Y  ⟺  X ⊓ Y = ⊥  ∨  X = ⊤  ∨  Y = ⊥  ∨  Y = ⊤          （Canon.refutP）
```

`Structure.lean` 已证：支持侧写出来的 `Y = ⊤` 与反驳侧写出来的 `Y = ⊥` 是**冗余**的
（`Canon.suppP_iff_le_or_top`、`Canon.refutP_iff_disjoint_or_top`）。本文件证明余下三组事实：

1. **支持侧**：`X = ⊤` 是**唯一**破坏传递性的装置。传递的两个环节若都走 `≤` 项，
   结论也由 `≤` 项成立（`Canon.suppP_transitive_of_le_links`）；于是任何传递失败的
   见证里，第二个环节**不可能**是 `≤` 项，只能走 `X = ⊤` 项（此处的 `X` 即中间项）。
2. **反驳侧**：`Y = ⊤` **不**冗余——它是 P1／P2 在 `kR = ⊲` 时所需要的。删去它得到
   缩减判据 `disj_refutP₀`；该判据在「非退化支持者 + 被反驳式真值为 `⊤`」处失效
   （`disj_refutP₀_fails_on_top_right`），并且**缩减判据下的典范框架不是模型**
   （`disj_reduced_frame_not_model`：P1 在 `kR = ⊲` 的一个具体实例上失败）。
3. **朴素读法**：把 `X ⊳ Y` 读成 `X ≤ Y` 时，支持侧规则 `S1`／`F3`／`F4` 的命题层
   形状**全部成立**，但**支持传递也成立**——这正是定稿第七节拒绝朴素读法的理由。

技术注记：本文件**不**在 `PSet` 层用 `decide`（那会卡在 `Classical.choice`），
只在 `Fin 3` 的具体等式上用 `by decide`。
-/
import EvidenceLogic.Analysis.Structure
import EvidenceLogic.System.NonAdmissible

namespace EvidenceLogic

variable {W : Type}

/-! ## 一、支持侧：传递失败**只能**经由 `X = ⊤` 项 -/

/-- **见证 `suppP_not_transitive` 的第二个环节不是 `≤` 项**：世界 `0` 属于 `⊤` 但不属于 `s1`。

`suppP_not_transitive` 取 `s0 ⊳ ⊤ ⊳ s1`。第一个环节 `s0 ⊳ ⊤` 用 `≤` 项（`s0 ≤ ⊤`）；
第二个环节 `⊤ ⊳ s1` 若要成立，只能用 `suppP` 的 `X = ⊤` 项——因为 `⊤ ≤ s1` 为假
（本定理），而第三项 `s1 = ⊤` 也为假（`s1_ne_top`）。 -/
theorem disj_second_link_not_le : ¬ ((⊤ : PSet (Fin 3)) ≤ s1) :=
  fun h => absurd (h 0 trivial) (by decide)

/-- `Canon.suppP_transitive_of_le_links`（两个环节都走 `≤` 项则传递成立）的**逆否式**：
既然 `≤` 项的两个环节足以给出传递，那么传递失败的见证里，两个环节**不可能**都走 `≤` 项。 -/
theorem disj_failure_needs_non_le_link {X Y Z : PSet W}
    (h₃ : ¬ Canon.suppP X Z) : ¬ (X ≤ Y ∧ Y ≤ Z) :=
  fun ⟨hXY, hYZ⟩ => h₃ (Canon.suppP_transitive_of_le_links hXY hYZ)

/-- **支持侧的一般形式**：若 `X ⊳ Y`、`Y ⊳ Z` 而 `X ⋫ Z`，则第二个环节不是 `≤` 项，
且中间项必为 `⊤`。

也就是说：传递失败的见证里，第二个环节 `Y ⊳ Z` 唯一可用的析取项是 **`Y = ⊤`**
（第一项 `Y ≤ Z` 由本定理否定，第三项 `Z = ⊤` 由 `¬ suppP X Z` 否定，
第二项 `Y = ⊤` 由 `suppP_middle_eq_top` 强制）。于是「传递失败只能经由 `X = ⊤` 项」。 -/
theorem disj_transitivity_failure_via_top_left {X Y Z : PSet W}
    (h₁ : Canon.suppP X Y) (h₂ : Canon.suppP Y Z) (h₃ : ¬ Canon.suppP X Z) :
    ¬ (Y ≤ Z) ∧ Y = ⊤ := by
  have hX : X ≠ ⊤ := fun h => h₃ (Or.inr (Or.inl h))
  have hZ : Z ≠ ⊤ := fun h => h₃ (Or.inr (Or.inr h))
  have hYZ : ¬ (Y ≤ Z) := by
    intro hle
    rcases h₁ with hXY | hXt | hY
    · exact h₃ (Or.inl (PSet.le_trans hXY hle))
    · exact hX hXt
    · exact hZ (PSet.eq_top_of_le (hY ▸ hle))
  exact ⟨hYZ, suppP_middle_eq_top h₁ h₂ h₃⟩

/-- 把 `disj_transitivity_failure_via_top_left` 用在 `suppP_not_transitive` 的见证上：
`s0 ⊳ ⊤` 走 `≤` 项，`⊤ ⊳ s1` 走 `X = ⊤` 项，而 `s0 ⋫ s1`。 -/
theorem disj_not_transitive_witness_analysis :
    ¬ ((⊤ : PSet (Fin 3)) ≤ s1) ∧ (⊤ : PSet (Fin 3)) = ⊤ :=
  disj_transitivity_failure_via_top_left
    (X := s0) (Y := (⊤ : PSet (Fin 3))) (Z := s1)
    (Or.inl (PSet.le_top s0)) (Or.inr (Or.inl rfl)) not_suppP_s0_s1

/-- 三条事实合起来描述见证的第二个环节：`⊤ ⊳ s1` 成立，但它**不是** `≤` 项，
也**不是** `s1 = ⊤` 项，因此只能是 `X = ⊤` 项。 -/
theorem disj_second_link_only_via_top_left :
    Canon.suppP (⊤ : PSet (Fin 3)) s1
      ∧ ¬ ((⊤ : PSet (Fin 3)) ≤ s1) ∧ ¬ (s1 = ⊤) :=
  ⟨Or.inr (Or.inl rfl), disj_second_link_not_le, s1_ne_top⟩

/-! ## 二、反驳侧：`Y = ⊤` 不可删——它是 P1（`kR = ⊲`）所需的判据 -/

/-- 去掉 `Y = ⊤` 后的「缩减反驳判据」。 -/
def disj_refutP₀ {W : Type} (X Y : PSet W) : Prop := X ⊓ Y = ⊥ ∨ X = ⊤

/-- `s0` 非退化：既不是 `⊥` 也不是 `⊤`。

P1／P2 在 `kR = ⊲` 时结论是 `X ⊲ (内层关系式)`；只要 `X` 非退化而内层关系式真值为 `⊤`，
缩减判据就必须失效（下条定理）——这正是 `Y = ⊤` 项不可删的原因。 -/
theorem disj_s0_nondegenerate : (s0 : PSet (Fin 3)) ≠ ⊥ ∧ (s0 : PSet (Fin 3)) ≠ ⊤ :=
  ⟨s0_ne_bot, s0_ne_top⟩

/-- 缩减判据在 `Y = ⊤` 处**退化为「支持者本身退化」**。 -/
theorem disj_refutP₀_top_right_iff {X : PSet W} :
    disj_refutP₀ X ⊤ ↔ X = ⊥ ∨ X = ⊤ := by
  constructor
  · rintro (h | h)
    · exact Or.inl (by simpa using h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (by rw [h, PSet.bot_inf_eq])
    · exact Or.inr h

/-- **缩减判据在「非退化支持者 + 被反驳式真值为 `⊤`」上失效**（一般形式）。 -/
theorem disj_refutP₀_fails_of_top_right {X : PSet W} (hbot : X ≠ ⊥) (htop : X ≠ ⊤) :
    ¬ disj_refutP₀ X ⊤ :=
  fun h => (disj_refutP₀_top_right_iff.mp h).elim hbot htop

/-- **缩减判据在「非退化支持者 + 真值为 `⊤` 的被反驳式」上失效**（`s0` 的具体实例）。 -/
theorem disj_refutP₀_fails_on_top_right : ¬ disj_refutP₀ (s0 : PSet (Fin 3)) ⊤ :=
  disj_refutP₀_fails_of_top_right s0_ne_bot s0_ne_top

/-- 全判据与缩减判据在 `Y = ⊤`、`X = s0` 处**分道扬镳**：
`Canon.refutP s0 ⊤` 由 `Y = ⊤` 项成立，而缩减判据 `disj_refutP₀ s0 ⊤` 不成立。 -/
theorem disj_top_right_separates_refutP :
    Canon.refutP (s0 : PSet (Fin 3)) ⊤ ∧ ¬ disj_refutP₀ (s0 : PSet (Fin 3)) ⊤ :=
  ⟨Canon.refutP_top_right _, disj_refutP₀_fails_on_top_right⟩

/-! ### P1 链条的每一环

P1（`kR = ⊲`）的结论是 `(⟦a⟧ ⊓ ⟦b⟧) ⊲ (内层关系式)`，其中内层关系式
`Kind.form kS (.and c d) f` 恰是 P1 **第三个前提**：

* 该前提在被用于 P1 之前先作为**关系式**被（在见证中）推导出来；
* 由 `derivable_rel_truth_eq_top`，**任何可推导的关系式在任意模型、任意赋值下真值为 `⊤`**；
* 于是 P1 的结论在该赋值处正是 `(⟦a⟧ ⊓ ⟦b⟧) ⊲ ⊤`——它**只能**由反驳判据的 `Y = ⊤` 项成立；
* 取 `⟦a⟧ ⊓ ⟦b⟧ = s0`（非退化）即可看到缩减判据失效。

下面把每一环都写成一个定理。 -/

/-- **第一环**：P1 第三个前提（内层关系式）可推导 ⇒ 它在任意模型、任意赋值下真值为 `⊤`
（`derivable_rel_truth_eq_top` 在 P1 前提形状上的特化）。 -/
theorem disj_inner_rel_truth_eq_top {M : Frame} (hM : IsModel M) {kS : Kind} {c d f : Form}
    (hd : Derivable (Kind.form kS (.and c d) f)) (ρ : Nat → PSet M.W) :
    M.truth (Kind.form kS (.and c d) f) ρ = ⊤ :=
  derivable_rel_truth_eq_top hM hd ρ

/-- **第二环**：在典范框架里，反驳关系式的真值恰是 `refutP` 作用在两个真值上；
当被反驳式真值为 `⊤` 时，`Y = ⊤` 项使反驳成立。 -/
theorem disj_canon_refut_of_inner_top (W : Type)
    (atomRel : Nat → List (PSet W) → PSet W) (X : PSet W) (a : Form)
    (ρ : Nat → PSet W)
    (h : (Canon.base W atomRel).truth a ρ = ⊤) :
    Canon.refutP X ((Canon.base W atomRel).truth a ρ) := by
  rw [h]
  exact Canon.refutP_top_right X

/-- **第三环**：缩减判据蕴含全判据。 -/
theorem disj_refutP₀_imp_refutP {X Y : PSet W} (h : disj_refutP₀ X Y) :
    Canon.refutP X Y := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- **全判据严格强于缩减判据**：蕴含成立，且在 `Y = ⊤` 处取到反例（`X = s0` 非退化）。 -/
theorem disj_refutP_strictly_stronger :
    (∀ {W' : Type} {X Y : PSet W'}, disj_refutP₀ X Y → Canon.refutP X Y) ∧
      (Canon.refutP (s0 : PSet (Fin 3)) ⊤ ∧ ¬ disj_refutP₀ (s0 : PSet (Fin 3)) ⊤) :=
  ⟨fun h => disj_refutP₀_imp_refutP h, disj_top_right_separates_refutP⟩

/-! ### 删去 `Y = ⊤` 会破坏 P1：缩减判据下的典范框架**不是模型**

把 `Canon.frame` 的反驳判据换成 `disj_refutP₀`，得到 `disj_frame₀`。
在 `disj_frame₀` 中取 P1 的实例

```
kR = ⊲, kS = ⊳, a = F1, b = F4, c = F2, d = F3, f = ⊤, ρ = rho0
```

三个前提都成立：

* `⟦F1⟧ ⊓ ⟦F2⟧ = s0 ⊓ s1 = ⊥`（`refutP₀` 第一项）；
* `⟦F4⟧ ⊓ ⟦F3⟧ = s01 ⊓ s2 = ⊥`（同上）；
* `⊳` 前提用 `Canon.suppP`，由 `f = ⊤`（即 `suppP` 的 `Y = ⊤` 项）成立。

而结论是 `(s0 ⊓ s01) ⊲ (F2 ∧ F3 ⊳ ⊤)`：被反驳式的真值为 `⊤`，支持者为 `s0 ⊓ s01 = s0`
（非退化），于是 `disj_refutP₀ s0 ⊤` 为假。故 `IsModel.p1` 在 `disj_frame₀` 上失败。 -/

/-- `s0 ⊓ s01 = s0`。 -/
theorem disj_s0_inf_s01 : (s0 : PSet (Fin 3)) ⊓ s01 = s0 := by
  apply PSet.ext
  intro w
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩

/-- 基结构中，`.supp` 关系式在 `f = Form.top` 时真值为 `⊤`（`suppP` 的 `Y = ⊤` 项）。 -/
theorem disj_base_relForm_supp_top_right (W : Type)
    (atomRel : Nat → List (PSet W) → PSet W) (c d : Form) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth (Kind.form Kind.supp (.and c d) Form.top) ρ = ⊤ := by
  apply PSet.eq_top_of_le
  intro w _
  show Canon.suppP ((Canon.base W atomRel).truth (.and c d) ρ)
    ((Canon.base W atomRel).truth Form.top ρ)
  exact Or.inr (Or.inr rfl)

/-- 把典范框架的反驳判据换成**缩减判据** `disj_refutP₀`（即删去 `Y = ⊤` 项）的框架。 -/
noncomputable def disj_frame₀ : Frame :=
  { W := Fin 3
    atomRel := atomRel3
    supp := fun X φ ρ => Canon.suppP X ((Canon.base (Fin 3) atomRel3).truth φ ρ)
    refut := fun X φ ρ => disj_refutP₀ X ((Canon.base (Fin 3) atomRel3).truth φ ρ) }

/-- `disj_frame₀` 中 `F1` 的真值与 `M3` 相同。 -/
theorem disj_frame₀_truth_F1 (ρ : Nat → PSet (Fin 3)) : disj_frame₀.truth F1 ρ = s0 := rfl

/-- `disj_frame₀` 中 `F4` 的真值与 `M3` 相同。 -/
theorem disj_frame₀_truth_F4 (ρ : Nat → PSet (Fin 3)) : disj_frame₀.truth F4 ρ = s01 := rfl

/-- `disj_frame₀` 中 `F2` 的真值与 `M3` 相同。 -/
theorem disj_frame₀_truth_F2 (ρ : Nat → PSet (Fin 3)) : disj_frame₀.truth F2 ρ = s1 := rfl

/-- `disj_frame₀` 中 `F3` 的真值与 `M3` 相同。 -/
theorem disj_frame₀_truth_F3 (ρ : Nat → PSet (Fin 3)) : disj_frame₀.truth F3 ρ = s2 := rfl

/-- **缩减判据下的典范框架不是模型**：`IsModel.p1` 在 `kR = ⊲` 的实例上失败。

这就是「去掉 `Y = ⊤` 会让 P1 所需的判据失效」的机器验证：`Y = ⊤` 项不是冗余项，
而是 `kR = ⊲` 时 P1 结论唯一可用的出口。 -/
theorem disj_reduced_frame_not_model : ¬ IsModel disj_frame₀ := by
  intro hM
  have h1 : disj_frame₀.refut (disj_frame₀.truth F1 rho0) F2 rho0 := by
    rw [disj_frame₀_truth_F1]
    show disj_refutP₀ (s0 : PSet (Fin 3)) s1
    exact Or.inl s0_inf_s1
  have h2 : disj_frame₀.refut (disj_frame₀.truth F4 rho0) F3 rho0 := by
    rw [disj_frame₀_truth_F4]
    show disj_refutP₀ (s01 : PSet (Fin 3)) s2
    exact Or.inl s01_inf_s2
  have h3 : disj_frame₀.supp (disj_frame₀.truth F2 rho0 ⊓ disj_frame₀.truth F3 rho0)
      Form.top rho0 := by
    rw [disj_frame₀_truth_F2, disj_frame₀_truth_F3]
    show Canon.suppP ((s1 : PSet (Fin 3)) ⊓ s2) ⊤
    exact Or.inr (Or.inr rfl)
  have hconcl := hM.p1 Kind.refut Kind.supp F1 F4 F2 F3 Form.top rho0 h1 h2 h3
  have hconcl' : disj_refutP₀ ((s0 : PSet (Fin 3)) ⊓ s01)
      ((Canon.base (Fin 3) atomRel3).truth (Kind.form Kind.supp (.and F2 F3) Form.top) rho0) :=
    hconcl
  rw [disj_base_relForm_supp_top_right (Fin 3) atomRel3 F2 F3 rho0] at hconcl'
  have hbad : ¬ disj_refutP₀ ((s0 : PSet (Fin 3)) ⊓ s01) ⊤ := by
    intro hh
    rw [disj_s0_inf_s01] at hh
    exact disj_refutP₀_fails_of_top_right s0_ne_bot s0_ne_top hh
  exact hbad hconcl'

/-! ## 三、朴素读法的 `PSet` 层事实：支持侧规则全成立、但传递也成立

把 `X ⊳ Y` 朴素地读成 `X ≤ Y`，则 `S1`（自反蕴含）、`F3`（合取主体）、`F4`（合取结论）
的**命题层形状**都成立。这不是"朴素读法破坏规则"——它完整地满足支持侧规则；
它**唯一**的问题是把支持传递也变成了有效式（`disj_naive_transitive`），
而支持传递正是定稿第七节明确排除的规则（并在 `NonDerivable` 中以 `M3` 反模型否证）。
这就是定稿第七节拒绝朴素读法的理由。 -/

/-- 朴素读法下 `S1` 的形状：`X ≤ Y ⇒ X ⊳ Y`（此处即前提本身）。 -/
theorem disj_naive_s1 {X Y : PSet W} (h : X ≤ Y) : X ≤ Y := h

/-- 朴素读法下 `F3` 的形状：`X ⊳ Y` 与 `Z ⊳ Y` 给出 `(X ⊓ Z) ⊳ Y`。

（`h₂` 在该读法下是**多余的**前提——`X ⊓ Z ≤ X ≤ Y` 已足够，故按工程约定写 `_h₂`；
这本身也说明朴素读法对支持侧规则只有增强、没有削弱。） -/
theorem disj_naive_f3 {X Z Y : PSet W} (h₁ : X ≤ Y) (_h₂ : Z ≤ Y) : X ⊓ Z ≤ Y :=
  fun _ hw => h₁ _ hw.1

/-- 朴素读法下 `F4` 的形状：`X ⊳ Y` 与 `X ⊳ Z` 给出 `X ⊳ (Y ⊓ Z)`。 -/
theorem disj_naive_f4 {X Y Z : PSet W} (h₁ : X ≤ Y) (h₂ : X ≤ Z) : X ≤ Y ⊓ Z :=
  PSet.le_inf h₁ h₂

/-- 朴素读法下**支持传递成立**：`X ⊳ Y` 与 `Y ⊳ Z` 给出 `X ⊳ Z`。

这正是定稿第七节拒绝朴素读法的唯一理由：它不是"不满足支持侧规则"，
而是把被明确排除的传递规则变成了有效式。 -/
theorem disj_naive_transitive {X Y Z : PSet W} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) : X ≤ Z :=
  PSet.le_trans h₁ h₂

end EvidenceLogic
