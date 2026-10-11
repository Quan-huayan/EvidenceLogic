/-
# 背书逻辑 v1.0：规则级非可容许性（NonAdmissible）

本文件形式化定稿第十节结论的**强读法**：相应**规则**不可导出，即存在
「前提全部可推导、结论不可推导」的实例。

## 与 `NonDerivable` 的区别

`NonDerivable` 证明的是：定稿第七节各条规则对应的**蕴含式**在模型类中不有效，
因而（由可靠性）作为公式不可推导。那是关于**公式**的结论，弱于本文件。

本文件证明的是**规则级**结论 `and_split_not_admissible` 那样的形式：

```lean
¬ (∀ <参数>, Derivable <前提₁> → Derivable <前提₂> → Derivable <结论>)
```

即：该规则**不是**可容许规则。证明方法固定为两步——

1. **前提可推导**：给出具体的见证实例，并显式构造 `Derivable` 的推导
   （最常用 `Derivable.s1`／`Derivable.s2`／`Derivable.r1`／`support_refl`
   与 `P1`／`P2` 的组合）；
2. **结论不可推导**：在某个 `Canon.frame`（有限模型）中算出结论不有效，
   再由 `not_derivable_of_countermodel`（可靠性的逆否命题）得到不可推导。

## 方法与边界（务必连同结论一起读）

* 反模型只能来自 `Canon.frame W atomRel` 这一族。任意 Canon 框架中关系式的
  真值都是**常值命题**（`⊤` 或 `⊥`），且
  `Canon.suppP X Y = (X ≤ Y ∨ X = ⊤ ∨ Y = ⊤)`、
  `Canon.refutP X Y = (X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊥ ∨ Y = ⊤)`。
  这些析取项会让许多见证**必然无效应**（例如取 `a := c ⊲ d` 配 `support_refl`
  去否证「拆嵌套关系」）。
* `Entails a c` 自动给出 `Derivable (a ⊳ c)`（S1），`Entails a (.not c)` 自动给出
  `Derivable (a ⊲ c)`（S1＋R1）。因此**结论不能被其支持者蕴含**。
* 传递型规则有一个系统性障碍：若前提是 `Derivable.s1` 的实例（即来自 `Entails`），
  则 **S2 立刻给出结论**——这类实例一律可容许。故传递型的见证必须让某个前提
  来自 F1–F4／P1／P2／R1 这类**非 S1** 的构造。见本文件末尾的说明。
-/
import EvidenceLogic.System.Derived
import EvidenceLogic.System.NonDerivable

namespace EvidenceLogic

noncomputable section

open scoped Classical

/-! ## 〇、一条通用筛子：可推导的关系式真值恒为 `⊤`

关系式的真值在任意框架中都是**常值命题**（`⟨fun _ => M.supp …⟩`），故
「有效」等于「该常值命题为真」，即真值为 `⊤`。由可靠性立即得到：
**任何可推导的关系式在任意模型、任意赋值下真值都是 `⊤`。**

这是寻找 N3 见证时最有用的筛子。例如「拆嵌套关系」若取 `a := c ⊲ d` 配
`support_refl`，则该前提的真值是 `⊤`，`suppP` 的 `Y = ⊤` 析取项会把前提
免费满足；更糟的是结论 `a ⊳ c` 的真值成了 `suppP ⊤ (truth c)`，也恒为 `⊤`，
于是**见证必然无效应**。同理，凡前提是推出关系式者，它在反模型中不可能取
`⊥` 或中间真值，一切"靠反模型把前提做假"的思路都不成立——前提必须靠**推导**
证明，结论才靠反模型否证。 -/

/-- **可推导的关系式在任意模型、任意赋值下真值为 `⊤`**。 -/
theorem derivable_rel_truth_eq_top {k : Kind} {a b : Form} {M : Frame} (hM : IsModel M)
    (h : Derivable (Kind.form k a b)) (ρ : Nat → PSet M.W) :
    M.truth (Kind.form k a b) ρ = ⊤ :=
  Derivable.soundness M hM h ρ

/-! ## 三、筛子：常值支持者使关系陈述必然有效

**这是本文件最重要的方法论结果。** 它把「某类见证注定失败」变成可机器复核的定理，
从而把"还没写出来"与"原理上不可能"区分开。

定义：公式 `φ` 在框架 `M` 中**真值恒为常值命题**（`ConstTruth`），当且仅当对每个赋值，
`M.truth φ ρ` 作为集合不随世界变化。关系式（`a ⊳ b`、`a ⊲ b`）、`⊤`、`⊥` 都满足，
且对 `¬`／`∧`／`∨`／`→` 封闭（这正是"支持关系的真值是恒常命题"这一设计事实）。

**筛子**：在任意典范框架中，若结论的**支持者**满足 `ConstTruth`，则该结论**有效**。
理由是一行集合论：常值支持者 `⟨fun _ => P⟩` 在 `suppP` 下恒真（`P` 真则支持者为 `⊤`，
`P` 假则支持者为 `⊥ ≤` 一切），`refutP` 同理。

**推论（为什么某些见证不可能成功）**：

* 「拆嵌套关系」若用 `support_refl` 取 `a := c ⊲ d`，则结论 `(c ⊲ d) ⊳ c` 在**所有**
  典范框架中都有效 —— 无法否证；
* 「拆反驳支持关系」最便宜的见证取 `a := ¬(c ⊳ d)`（`R1 ∘ S1`），则结论
  `(¬(c ⊳ d)) ⊲ c` 同样在**所有**典范框架中有效 —— 无法否证。

换言之：**结论的支持者里只要不出现原子（真值可自由变化的成分），结论就无从否证。** -/

/-- 在框架 `M` 中「真值恒为常值命题」。 -/
def ConstTruth (M : Frame) (φ : Form) : Prop :=
  ∀ ρ : Nat → PSet M.W, ∃ P : Prop, M.truth φ ρ = (⟨fun _ => P⟩ : PSet M.W)

namespace ConstTruth

variable {M : Frame}

theorem top : ConstTruth M Form.top := fun _ => ⟨True, rfl⟩

theorem bot : ConstTruth M Form.bot := fun _ => ⟨False, rfl⟩

theorem supp (a b : Form) : ConstTruth M (a ⊳ b) := fun _ => ⟨_, rfl⟩

theorem refut (a b : Form) : ConstTruth M (a ⊲ b) := fun _ => ⟨_, rfl⟩

theorem not {φ : Form} (h : ConstTruth M φ) : ConstTruth M (.not φ) := by
  intro ρ
  obtain ⟨P, hP⟩ := h ρ
  exact ⟨¬P, by
    show (M.truth φ ρ)ᶜ = (⟨fun _ => ¬P⟩ : PSet M.W)
    rw [hP]
    rfl⟩

theorem and {φ ψ : Form} (h₁ : ConstTruth M φ) (h₂ : ConstTruth M ψ) :
    ConstTruth M (.and φ ψ) := by
  intro ρ
  obtain ⟨P, hP⟩ := h₁ ρ
  obtain ⟨Q, hQ⟩ := h₂ ρ
  exact ⟨P ∧ Q, by
    show M.truth φ ρ ⊓ M.truth ψ ρ = (⟨fun _ => P ∧ Q⟩ : PSet M.W)
    rw [hP, hQ]
    rfl⟩

theorem or {φ ψ : Form} (h₁ : ConstTruth M φ) (h₂ : ConstTruth M ψ) :
    ConstTruth M (.or φ ψ) := by
  intro ρ
  obtain ⟨P, hP⟩ := h₁ ρ
  obtain ⟨Q, hQ⟩ := h₂ ρ
  exact ⟨P ∨ Q, by
    show M.truth φ ρ ⊔ M.truth ψ ρ = (⟨fun _ => P ∨ Q⟩ : PSet M.W)
    rw [hP, hQ]
    rfl⟩

theorem imp {φ ψ : Form} (h₁ : ConstTruth M φ) (h₂ : ConstTruth M ψ) :
    ConstTruth M (.imp φ ψ) := by
  intro ρ
  obtain ⟨P, hP⟩ := h₁ ρ
  obtain ⟨Q, hQ⟩ := h₂ ρ
  exact ⟨¬P ∨ Q, by
    show (M.truth φ ρ)ᶜ ⊔ M.truth ψ ρ = (⟨fun _ => ¬P ∨ Q⟩ : PSet M.W)
    rw [hP, hQ]
    rfl⟩

end ConstTruth

/-- 常值左参数使 `suppP` 恒真。 -/
theorem canon_suppP_const_left {W : Type} {P : Prop} (Y : PSet W) :
    Canon.suppP (⟨fun _ => P⟩ : PSet W) Y := by
  by_cases h : P
  · exact Or.inr (Or.inl (PSet.ext (fun _ => ⟨fun _ => trivial, fun _ => h⟩)))
  · exact Or.inl (fun _ hp => absurd hp h)

/-- 常值左参数使 `refutP` 恒真。 -/
theorem canon_refutP_const_left {W : Type} {P : Prop} (Y : PSet W) :
    Canon.refutP (⟨fun _ => P⟩ : PSet W) Y := by
  by_cases h : P
  · exact Or.inr (Or.inl (PSet.ext (fun _ => ⟨fun _ => trivial, fun _ => h⟩)))
  · exact Or.inl (PSet.eq_bot_of_le (fun _ hw => absurd hw.1 h))

/-- **筛子（支持）**：典范框架中，`ConstTruth` 的支持者使支持陈述有效。 -/
theorem canon_valid_supp_of_const_left {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {a φ : Form} (ha : ConstTruth (Canon.frame W atomRel) a) :
    (Canon.frame W atomRel).Valid (a ⊳ φ) := by
  intro ρ
  obtain ⟨P, hP⟩ := ha ρ
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth a ρ)
    ((Canon.base W atomRel).truth φ ρ)⟩ : PSet W) = ⊤
  rw [hP]
  exact PSet.ext (fun _ => ⟨fun _ => trivial, fun _ => canon_suppP_const_left _⟩)

/-- **筛子（反驳）**：典范框架中，`ConstTruth` 的支持者使反驳陈述有效。 -/
theorem canon_valid_refut_of_const_left {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {a φ : Form} (ha : ConstTruth (Canon.frame W atomRel) a) :
    (Canon.frame W atomRel).Valid (a ⊲ φ) := by
  intro ρ
  obtain ⟨P, hP⟩ := ha ρ
  show (⟨fun _ => Canon.refutP ((Canon.frame W atomRel).truth a ρ)
    ((Canon.base W atomRel).truth φ ρ)⟩ : PSet W) = ⊤
  rw [hP]
  exact PSet.ext (fun _ => ⟨fun _ => trivial, fun _ => canon_refutP_const_left _⟩)

/-- **「拆嵌套关系」用 `support_refl`（`a := c ⊲ d`）的见证注定失败**：
结论 `(c ⊲ d) ⊳ c` 在任意典范框架下有效。 -/
theorem canon_valid_supp_of_refut_supporter {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W) (c d φ : Form) :
    (Canon.frame W atomRel).Valid ((c ⊲ d) ⊳ φ) :=
  canon_valid_supp_of_const_left atomRel (ConstTruth.refut c d)

/-- **「拆嵌套关系」用 `a := c ⊳ d` 的见证同样失败**。 -/
theorem canon_valid_supp_of_supp_supporter {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W) (c d φ : Form) :
    (Canon.frame W atomRel).Valid ((c ⊳ d) ⊳ φ) :=
  canon_valid_supp_of_const_left atomRel (ConstTruth.supp c d)

/-- **「拆反驳支持关系」最便宜的见证（`a := ¬(c ⊳ d)`，`R1 ∘ S1`）注定失败**：
结论 `(¬(c ⊳ d)) ⊲ c` 在任意典范框架下有效。 -/
theorem canon_valid_refut_of_not_supp_supporter {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W) (c d φ : Form) :
    (Canon.frame W atomRel).Valid ((Form.not (c ⊳ d)) ⊲ φ) :=
  canon_valid_refut_of_const_left atomRel (ConstTruth.not (ConstTruth.supp c d))

/-! ## 一、拆全称支持者：`(∀x p(x)) ⊳ φ ⇏ p(a) ⊳ φ`

见证：`p := F5`、`x := 0`、`a := ⊥`、`φ := ∀x F5`。
* 前提 `(∀x F5) ⊳ (∀x F5)` 由 `support_refl` 可推导；
* 结论 `(atom 5 [⊥]) ⊳ (∀x F5)` 在 `M3` 中不有效：其支持者真值为 `s0`、
  被支持公式真值为 `⊥`，而 `suppP s0 ⊥` 三项皆假。 -/

/-- 见证结论在 `M3` 中不有效。（注意与 `NonDerivable.all_split_not_valid` 区分：
后者否证的是**蕴含式**，本定理否证的是本文件见证的**结论公式**。） -/
theorem all_split_conclusion_not_valid :
    ¬ M3.Valid (inst 0 Form.bot F5 ⊳ Form.all 0 F5) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  rw [M3_truth_supp,
    (show M3.truth (inst 0 Form.bot F5) rho0 = s0 from by
      show (if (⊥ : PSet (Fin 3)) = s0 then s2 else s0) = s0
      exact if_neg bot_ne_s0),
    (show B3.truth (Form.all 0 F5) rho0 = ⊥ from B3_truth_all_F5 rho0)]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h | h
  · exact not_s0_le_bot h
  · exact s0_ne_top h
  · exact bot_ne_top h

/-- **拆全称支持者不是可容许规则**。 -/
theorem all_split_not_admissible :
    ¬ (∀ (p φ a : Form) (x : Nat),
      Derivable (Form.all x p ⊳ φ) → Derivable (inst x a p ⊳ φ)) :=
  fun h => not_derivable_of_countermodel M3_isModel all_split_conclusion_not_valid
    (h F5 (Form.all 0 F5) Form.bot 0 (support_refl (Form.all 0 F5)))

/-! ## 二、非命题性反驳逆后承：`t ⊲ ψ`、`φ ⊢ ψ` ⇏ `t ⊲ φ`

见证（规则带语义副作用条件 `φ ⊢ ψ`）：
* `t := (¬F1) ∧ (¬F2)`、`ψ := (F1 ∧ F2) ⊳ F1`、`φ := ψ ∧ F3`；
* 前提 `t ⊲ ψ` 由 `P1`（`R = ⊲`、`S = ⊳`）拼出：三个子前提
  `(¬F1) ⊲ F1`、`(¬F2) ⊲ F2`（`R1 ∘ S1`）与 `(F1 ∧ F2) ⊳ F1`（`S1`）都可推导；
* 副作用条件 `φ ⊢ ψ` 由合取消去给出；
* 结论 `t ⊲ φ` 在 `M3` 中不有效：`t` 的真值为 `s0ᶜ ⊓ s1ᶜ`、`φ` 的真值为 `s2`，
  而 `refutP` 四项皆假。 -/

/-- 见证前提 `t ⊲ ψ` 可推导。 -/
theorem refute_converse_premise_derivable :
    Derivable (Form.and (Form.not F1) (Form.not F2) ⊲
      Kind.form .supp (Form.and F1 F2) F1) :=
  Derivable.p1 (kR := .refut) (kS := .supp)
    (a := Form.not F1) (b := Form.not F2) (c := F1) (d := F2) (f := F1)
    (Derivable.r1 (Derivable.s1 (entails_refl (Form.not F1))))
    (Derivable.r1 (Derivable.s1 (entails_refl (Form.not F2))))
    (Derivable.s1 (entails_and_left F1 F2))

/-- 见证结论在 `M3` 中不有效。 -/
theorem refute_converse_not_valid : ¬ M3.Valid
    (Form.and (Form.not F1) (Form.not F2) ⊲ Form.and (Form.and F1 F2 ⊳ F1) F3) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  rw [M3_truth_refut,
    (show M3.truth (Form.and (Form.not F1) (Form.not F2)) rho0 = s0ᶜ ⊓ s1ᶜ from by
      rw [M3_truth_and, (show M3.truth (Form.not F1) rho0 = s0ᶜ from rfl),
        (show M3.truth (Form.not F2) rho0 = s1ᶜ from rfl)]),
    (show B3.truth (Form.and (Form.and F1 F2 ⊳ F1) F3) rho0 = s2 from by
      rw [B3_truth_and, B3_truth_F3, B3_truth_supp, B3_truth_and, B3_truth_F1, B3_truth_F2,
        s0_inf_s1]
      rw [show cst (Canon.suppP (⊥ : PSet (Fin 3)) s0) = ⊤ from
        cst_eq_top_of _ (Or.inl (PSet.bot_le s0)), PSet.top_inf_eq])]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h | h | h
  · exact pset_ne_of_world 2
      (show ((s0ᶜ ⊓ s1ᶜ : PSet (Fin 3)) ⊓ s2) 2 from
        ⟨⟨show ¬ ((2 : Fin 3) = 0) from by decide,
          show ¬ ((2 : Fin 3) = 1) from by decide⟩,
          show (s2 : PSet (Fin 3)) 2 from by decide⟩)
      (fun h => h) h
  · exact pset_ne_of_world' 0 (show (⊤ : PSet (Fin 3)) 0 from trivial)
      (show ¬ (s0ᶜ ⊓ s1ᶜ : PSet (Fin 3)) 0 from fun hh => hh.1 rfl) h
  · exact pset_ne_of_world 2 (show (s2 : PSet (Fin 3)) 2 from by decide) (fun h => h) h
  · exact pset_ne_of_world' 0 (show (⊤ : PSet (Fin 3)) 0 from trivial)
      (show ¬ (s2 : PSet (Fin 3)) 0 from by decide) h

/-- **非命题性反驳逆后承不是可容许规则**（定稿第七节末条）。 -/
theorem refute_converse_not_admissible :
    ¬ (∀ t φ ψ : Form, Derivable (t ⊲ ψ) → Entails φ ψ → Derivable (t ⊲ φ)) :=
  fun h => not_derivable_of_countermodel M3_isModel refute_converse_not_valid
    (h (Form.and (Form.not F1) (Form.not F2))
      (Form.and (Kind.form .supp (Form.and F1 F2) F1) F3)
      (Kind.form .supp (Form.and F1 F2) F1)
      refute_converse_premise_derivable
      (entails_and_left (Kind.form .supp (Form.and F1 F2) F1) F3))

/-! ## 四、反驳传递：`(a ⊲ b) ∧ (b ⊲ c) ⇏ a ⊲ c`

见证 `a := F1`、`b := ⊥`、`c := F1`。要诀是 `⊥` 与 `¬⊥` 的极端地位：

* `F1 ⊲ ⊥` 可推导：`¬⊥` 是有效式，故 `Entails F1 (¬⊥)`，`S1` 给出 `F1 ⊳ ¬⊥`，
  `R1` 给出结论；
* `⊥ ⊲ F1` 可推导：`Entails ⊥ (¬F1)`，同上；
* 结论 `F1 ⊲ F1` 在 `M3` 中不有效（`refutP s0 s0` 四项皆假），故不可推导。

这与「支持传递」形成鲜明对照：对支持传递而言，两个前提的**可推导性**会迫使结论
在所有模型中**有效**，因此反模型方法对它无效（论证见本文件末尾的说明）。 -/

/-- 见证前提 `F1 ⊲ ⊥` 可推导。 -/
theorem refut_transitivity_premise_left : Derivable (F1 ⊲ Form.bot) :=
  Derivable.r1 (Derivable.s1 (fun _ _ w _ => PSet.not_bot w))

/-- 见证前提 `⊥ ⊲ F1` 可推导。 -/
theorem refut_transitivity_premise_right : Derivable (Form.bot ⊲ F1) :=
  Derivable.r1 (Derivable.s1 (fun _ _ w h => absurd h (PSet.not_bot w)))

/-- 见证结论 `F1 ⊲ F1` 在 `M3` 中不有效。 -/
theorem refut_self_not_valid : ¬ M3.Valid (F1 ⊲ F1) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  rw [M3_truth_refut, M3_truth_F1, B3_truth_F1]
  exact cst_ne_top_of_not not_refutP_s0_s0

/-- **反驳传递不是可容许规则**。 -/
theorem refute_transitivity_not_admissible :
    ¬ (∀ a b c : Form, Derivable (a ⊲ b) → Derivable (b ⊲ c) → Derivable (a ⊲ c)) :=
  fun h => not_derivable_of_countermodel M3_isModel refut_self_not_valid
    (h F1 Form.bot F1 refut_transitivity_premise_left refut_transitivity_premise_right)

/-! ## 五、拆嵌套关系（第二半）：`a ⊳ (c ⊲ d) ⇏ c ⊲ d`

见证 `a := F1 ⊲ F1`、`c := d := F1`：前提 `(F1 ⊲ F1) ⊳ (F1 ⊲ F1)` 由 `support_refl`
可推导，结论 `F1 ⊲ F1` 不可推导（`refut_self_not_valid`）。 -/

/-- **「从 `a ⊳ (c ⊲ d)` 拆出 `c ⊲ d`」不是可容许规则**。 -/
theorem nested_refut_not_admissible :
    ¬ (∀ a c d : Form, Derivable (a ⊳ (c ⊲ d)) → Derivable (c ⊲ d)) :=
  fun h => not_derivable_of_countermodel M3_isModel refut_self_not_valid
    (h (F1 ⊲ F1) F1 F1 (support_refl (F1 ⊲ F1)))

/-! ## 六、反驳合取拆项：`t ⊲ (φ ∧ ψ) ⇏ t ⊲ φ`

见证 `t := ¬(F4 ∧ F1)`、`φ := F4`、`ψ := F1`。前提 `t ⊲ (φ ∧ ψ)` 由 `R1 ∘ S1`
给出（`t` 本身就是 `¬(φ ∧ ψ)`，故 `S1` 用自反蕴含即可）。

**为什么不能取更简单的见证**：若用 `F4`（kR = refut）推前提，则结论 `t ⊲ φ`
恰好是前提之一，规则平凡可容许；若前提来自 `R1 ∘ S1` 且取 `φ = F1, ψ = F2`，
则 `t = ¬(F1 ∧ F2)` 的真值为 `⊤`（M3 中 `s0 ⊓ s1 = ⊥`），`refutP ⊤ _` 恒真，
结论反而**有效**。取 `F4 ∧ F1` 使 `t` 的真值为 `s0ᶜ`（既非 `⊤` 也非 `⊥`），
才使 `refutP` 的四个析取项全部落空。 -/

/-- 见证结论 `¬(F4 ∧ F1) ⊲ F4` 在 `M3` 中不有效。 -/
theorem refut_and_conclusion_not_valid :
    ¬ M3.Valid (Form.not (Form.and F4 F1) ⊲ F4) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  rw [M3_truth_refut,
    (show M3.truth (Form.not (Form.and F4 F1)) rho0 = ((s01 ⊓ s0)ᶜ : PSet (Fin 3)) from by
      show (M3.truth (Form.and F4 F1) rho0)ᶜ = ((s01 ⊓ s0)ᶜ : PSet (Fin 3))
      rw [M3_truth_and, M3_truth_F4, M3_truth_F1]),
    (show B3.truth F4 rho0 = s01 from B3_truth_F4 rho0)]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h | h | h
  · exact pset_ne_of_world 1
      (show (((s01 ⊓ s0)ᶜ : PSet (Fin 3)) ⊓ s01) 1 from
        ⟨show ¬ ((s01 ⊓ s0 : PSet (Fin 3)) 1) from fun hh => absurd hh.2 (by decide),
          show (s01 : PSet (Fin 3)) 1 from Or.inr rfl⟩)
      (fun h => h) h
  · exact pset_ne_of_world' 0 (show (⊤ : PSet (Fin 3)) 0 from trivial)
      (show ¬ (((s01 ⊓ s0)ᶜ : PSet (Fin 3))) 0 from
        fun hh => hh ⟨Or.inl rfl, rfl⟩) h
  · exact pset_ne_of_world 0 (show (s01 : PSet (Fin 3)) 0 from Or.inl rfl) (fun h => h) h
  · exact pset_ne_of_world' 2 (show (⊤ : PSet (Fin 3)) 2 from trivial)
      (show ¬ (s01 : PSet (Fin 3)) 2 from
        fun hh => by rcases hh with h | h <;> exact absurd h (by decide)) h

/-- **反驳合取拆项不是可容许规则**。 -/
theorem refut_and_not_admissible :
    ¬ (∀ t φ ψ : Form, Derivable (t ⊲ (Form.and φ ψ)) → Derivable (t ⊲ φ)) :=
  fun h => not_derivable_of_countermodel M3_isModel refut_and_conclusion_not_valid
    (h (Form.not (Form.and F4 F1)) F4 F1
      (Derivable.r1 (Derivable.s1 (entails_refl (Form.not (Form.and F4 F1))))))

/-! ## 七、反驳全称拆实例：`t ⊲ ∀x φ ⇏ t ⊲ φ[x := a]`

见证 `t := ¬(∀x F5)`、`x := 0`、`φ := F5`、`a := ⊥`。前提 `t ⊲ ∀x F5` 由 `R1 ∘ S1`
给出（`t` 本身就是 `¬(∀x F5)`）。

**为什么必须自建 `M4`**：在 `M3` 中 `⟦∀x F5⟧ = ⊥`，于是 `⟦t⟧ = ⊤`，而 `refutP ⊤ _`
恒真（`X = ⊤` 析取项），反模型走不通。故把一元原子 `5` 的解释改为
「参数 `≤ s0` 时取 `s01`，否则取 `s0`」：

* `⟦∀x F5⟧ = s0`（对**全部** `X : PSet (Fin 3)` 求交：`X := s1` 一项给出 `s0`）；
* `⟦F5[0 := ⊥]⟧ = s01`（因为 `⊥ ≤ s0`）；
* 于是 `⟦t⟧ = s0ᶜ`，而 `refutP s0ᶜ s01` 四项皆假：`1 ∈ s0ᶜ ⊓ s01`、`0 ∉ s0ᶜ`、
  `0 ∈ s01`、`2 ∉ s01`。 -/

/-- 一元原子 `5` 的新解释：参数 `≤ s0` 时取 `s01`，否则取 `s0`（其余原子同 `atomRel3`）。 -/
def atomRel4 : Nat → List (PSet (Fin 3)) → PSet (Fin 3)
  | 0, _ => ⊤
  | 1, _ => s0
  | 2, _ => s1
  | 3, _ => s2
  | 4, _ => s01
  | 5, args => match args with
      | X :: _ => if X ≤ s0 then s01 else s0
      | [] => ⊥
  | _, _ => ⊥

/-- 相应的经典基结构。 -/
abbrev B4 : Base := Canon.base (Fin 3) atomRel4

/-- 自建反模型 `M4`。 -/
abbrev M4 : Frame := Canon.frame (Fin 3) atomRel4

/-- `M4` 是模型（由存在性定理）。 -/
theorem M4_isModel : IsModel M4 := Canon.isModel (Fin 3) atomRel4

/-- `s1 ≰ s0`。 -/
theorem not_s1_le_s0 : ¬ ((s1 : PSet (Fin 3)) ≤ s0) :=
  fun h => absurd (h 1 rfl) (by decide)

theorem B4_truth_all (x : Nat) (φ : Form) (ρ : Nat → PSet (Fin 3)) :
    B4.truth (Form.all x φ) ρ = PSet.iInter (fun X => B4.truth φ (upd ρ x X)) := rfl

theorem B4_truth_not (φ : Form) (ρ : Nat → PSet (Fin 3)) :
    B4.truth (Form.not φ) ρ = (B4.truth φ ρ)ᶜ := rfl

theorem B4_truth_refut (a b : Form) (ρ : Nat → PSet (Fin 3)) :
    B4.truth (a ⊲ b) ρ = cst (Canon.refutP (B4.truth a ρ) (B4.truth b ρ)) := rfl

/-- `M4` 的框架真值与基真值一致。 -/
theorem M4_truth_eq_base (φ : Form) (ρ : Nat → PSet (Fin 3)) :
    M4.truth φ ρ = B4.truth φ ρ := Canon.frame_truth (Fin 3) atomRel4 φ ρ

/-- `≤` 双向给出相等。 -/
theorem pset_le_antisymm {W : Type} {X Y : PSet W} (h₁ : X ≤ Y) (h₂ : Y ≤ X) : X = Y := by
  apply PSet.ext
  intro w
  exact ⟨fun hx => h₁ w hx, fun hy => h₂ w hy⟩

/-- **`M4` 中 `⟦∀x F5⟧ = s0`**。

注意每一步都要用 `show` 把 `PSet.iInter` 的投影显式归约成 `if` 表达式；
否则 `rw [if_pos …]` 因 `iInter` 未归约而找不到模式。 -/
theorem M4_truth_all_F5 : B4.truth (Form.all 0 F5) rho0 = s0 := by
  rw [B4_truth_all]
  show PSet.iInter (fun X : PSet (Fin 3) => if X ≤ s0 then s01 else s0) = s0
  apply pset_le_antisymm
  · intro w hw
    have hb : (if (s1 : PSet (Fin 3)) ≤ s0 then s01 else s0) w := hw s1
    show s0 w
    rw [if_neg not_s1_le_s0] at hb
    exact hb
  · intro w hw X
    show (if X ≤ s0 then s01 else s0) w
    by_cases hX : X ≤ s0
    · rw [if_pos hX]
      exact Or.inl hw
    · rw [if_neg hX]
      exact hw

/-- **`M4` 中 `⟦¬∀x F5⟧ = s0ᶜ`**。 -/
theorem M4_truth_not_all_F5 : B4.truth (Form.not (Form.all 0 F5)) rho0 = s0ᶜ := by
  rw [B4_truth_not, M4_truth_all_F5]

/-- **`M4` 中 `⟦F5[0 := ⊥]⟧ = s01`**（因为 `⊥ ≤ s0`）。 -/
theorem M4_truth_inst_bot_F5 : B4.truth (inst 0 Form.bot F5) rho0 = s01 := by
  show (if (⊥ : PSet (Fin 3)) ≤ s0 then s01 else s0) = s01
  exact if_pos (PSet.bot_le s0)

/-- 见证结论 `¬∀x F5 ⊲ F5[0 := ⊥]` 在 `M4` 中不有效。 -/
theorem refut_all_inst_conclusion_not_valid :
    ¬ M4.Valid (Form.not (Form.all 0 F5) ⊲ inst 0 Form.bot F5) := by
  have hne : B4.truth (Form.not (Form.all 0 F5) ⊲ inst 0 Form.bot F5) rho0 ≠ ⊤ := by
    rw [B4_truth_refut, M4_truth_not_all_F5, M4_truth_inst_bot_F5]
    apply cst_ne_top_of_not
    intro h
    rcases h with h | h | h | h
    · exact pset_ne_of_world 1
        (show ((s0ᶜ ⊓ s01 : PSet (Fin 3))) 1 from
          ⟨show ¬ ((1 : Fin 3) = 0) from by decide,
            show (s01 : PSet (Fin 3)) 1 from Or.inr rfl⟩)
        (fun h => h) h
    · exact pset_ne_of_world' 0 (show (⊤ : PSet (Fin 3)) 0 from trivial)
        (show ¬ (s0ᶜ : PSet (Fin 3)) 0 from fun hh => hh rfl) h
    · exact pset_ne_of_world 0 (show (s01 : PSet (Fin 3)) 0 from Or.inl rfl) (fun h => h) h
    · exact pset_ne_of_world' 2 (show (⊤ : PSet (Fin 3)) 2 from trivial)
        (show ¬ (s01 : PSet (Fin 3)) 2 from
          fun hh => by rcases hh with h | h <;> exact absurd h (by decide)) h
  intro hv
  exact hne (M4_truth_eq_base (Form.not (Form.all 0 F5) ⊲ inst 0 Form.bot F5) rho0 ▸ hv rho0)

/-- **反驳全称拆实例不是可容许规则**。 -/
theorem refut_all_not_admissible :
    ¬ (∀ (t : Form) (x : Nat) (φ a : Form),
        Derivable (t ⊲ (Form.all x φ)) → Derivable (t ⊲ (inst x a φ))) :=
  fun h => not_derivable_of_countermodel M4_isModel refut_all_inst_conclusion_not_valid
    (h (Form.not (Form.all 0 F5)) 0 F5 Form.bot
      (Derivable.r1 (Derivable.s1 (entails_refl (Form.not (Form.all 0 F5))))))

/-! ## 九、拆嵌套支持（第一半）：`a ⊳ (c ⊲ d) ⇏ a ⊳ c`

见证 `a := (F2 ⊲ F3) ∧ F1`、`c := F2`、`d := F3`。

**这条之所以能成功，正是因为它绕开了第三节的筛子**：支持者不是关系式本身，
而是「关系式 ∧ 原子」，其真值为 `⊤ ⊓ s0 = s0` —— **非常值命题**，于是
`suppP s0 s1` 三项皆假。前提 `a ⊳ (c ⊲ d)` 由 `S1` 加合取消去可推导
（`Entails ((c ⊲ d) ∧ x) (c ⊲ d)`）。 -/

/-- 见证结论 `((F2 ⊲ F3) ∧ F1) ⊳ F2` 在 `M3` 中不有效。 -/
theorem nested_supp_conclusion_not_valid :
    ¬ M3.Valid (Form.and (F2 ⊲ F3) F1 ⊳ F2) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  rw [M3_truth_supp]
  have hX : M3.truth (Form.and (F2 ⊲ F3) F1) rho0 = s0 := by
    show (M3.truth (F2 ⊲ F3) rho0 ⊓ M3.truth F1 rho0) = s0
    rw [M3_truth_refut, M3_truth_F1]
    show (cst (Canon.refutP (M3.truth F2 rho0) (B3.truth F3 rho0)) ⊓ s0) = s0
    rw [show M3.truth F2 rho0 = s1 from rfl, show B3.truth F3 rho0 = s2 from rfl,
      cst_eq_top_of (Canon.refutP s1 s2) (Or.inl s1_inf_s2), PSet.top_inf_eq]
  rw [hX, show B3.truth F2 rho0 = s1 from rfl]
  apply cst_ne_top_of_not
  exact not_suppP_s0_s1

/-- **「拆嵌套支持（第一半）」不是可容许规则**。 -/
theorem nested_supp_not_admissible :
    ¬ (∀ a c d : Form, Derivable (a ⊳ (c ⊲ d)) → Derivable (a ⊳ c)) :=
  fun h =>
    not_derivable_of_countermodel M3_isModel nested_supp_conclusion_not_valid
      (h (Form.and (F2 ⊲ F3) F1) F2 F3
        (Derivable.s1 (entails_and_left (F2 ⊲ F3) F1)))

/-! ## 十、拆反驳支持关系：`a ⊲ (c ⊳ d) ⇏ a ⊲ c` 且 `⇏ a ⊲ d`

见证同上思路：支持者取「`¬(c ⊳ d)` ∧ 原子」，前提由 `R1 ∘ S1` 得到
（`S1` 用合取消去给出 `a ⊳ ¬(c ⊳ d)`，`R1` 给出 `a ⊲ (c ⊳ d)`）。 -/

/-- 见证结论 `((¬(F3 ⊳ F2)) ∧ F3) ⊲ F3` 在 `M3` 中不有效。 -/
theorem refute_supp_conclusion_not_valid :
    ¬ M3.Valid (Form.and (Form.not (F3 ⊳ F2)) F3 ⊲ F3) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  rw [M3_truth_refut]
  have hX : M3.truth (Form.and (Form.not (F3 ⊳ F2)) F3) rho0 = s2 := by
    show (M3.truth (Form.not (F3 ⊳ F2)) rho0 ⊓ M3.truth F3 rho0) = s2
    rw [M3_truth_F3]
    show ((M3.truth (F3 ⊳ F2) rho0)ᶜ ⊓ s2) = s2
    rw [M3_truth_supp]
    rw [show M3.truth F3 rho0 = s2 from rfl, show B3.truth F2 rho0 = s1 from rfl,
      cst_eq_bot_of_not not_suppP_s2_s1, PSet.compl_bot, PSet.top_inf_eq]
  rw [hX, show B3.truth F3 rho0 = s2 from rfl]
  apply cst_ne_top_of_not
  exact not_refutP_s2_s2

/-- **「拆反驳支持关系」（推出 `a ⊲ c`）不是可容许规则**。 -/
theorem refute_supp_not_admissible :
    ¬ (∀ a c d : Form, Derivable (a ⊲ (c ⊳ d)) → Derivable (a ⊲ c)) :=
  fun h =>
    not_derivable_of_countermodel M3_isModel refute_supp_conclusion_not_valid
      (h (Form.and (Form.not (F3 ⊳ F2)) F3) F3 F2
        (Derivable.r1 (Derivable.s1 (entails_and_left (Form.not (F3 ⊳ F2)) F3))))

/-- 见证结论 `((¬(F3 ⊳ F2)) ∧ F2) ⊲ F2` 在 `M3` 中不有效。 -/
theorem refute_supp_conclusion_not_valid_d :
    ¬ M3.Valid (Form.and (Form.not (F3 ⊳ F2)) F2 ⊲ F2) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  rw [M3_truth_refut]
  have hX : M3.truth (Form.and (Form.not (F3 ⊳ F2)) F2) rho0 = s1 := by
    show (M3.truth (Form.not (F3 ⊳ F2)) rho0 ⊓ M3.truth F2 rho0) = s1
    rw [M3_truth_F2]
    show ((M3.truth (F3 ⊳ F2) rho0)ᶜ ⊓ s1) = s1
    rw [M3_truth_supp]
    rw [show M3.truth F3 rho0 = s2 from rfl, show B3.truth F2 rho0 = s1 from rfl,
      cst_eq_bot_of_not not_suppP_s2_s1, PSet.compl_bot, PSet.top_inf_eq]
  rw [hX, show B3.truth F2 rho0 = s1 from rfl]
  apply cst_ne_top_of_not
  exact not_refutP_s1_s1

/-- **「拆反驳支持关系」（推出 `a ⊲ d`）不是可容许规则**。 -/
theorem refute_supp_not_admissible' :
    ¬ (∀ a c d : Form, Derivable (a ⊲ (c ⊳ d)) → Derivable (a ⊲ d)) :=
  fun h =>
    not_derivable_of_countermodel M3_isModel refute_supp_conclusion_not_valid_d
      (h (Form.and (Form.not (F3 ⊳ F2)) F2) F3 F2
        (Derivable.r1 (Derivable.s1 (entails_and_left (Form.not (F3 ⊳ F2)) F2))))

/-! ## 十一、定稿第十节的完整战果，与尚未攻下者的可复核障碍

### 11.1 战果总表（十二个子命题中已拿下十个）

| 定稿第十节条目 | N3 定理 | 位置 |
|---|---|---|
| 支持传递 | **未拿下**（见 11.3） | — |
| 反驳传递 | `refute_transitivity_not_admissible` | 本文件第四节 |
| 拆合取支持者 | `and_split_not_admissible` | `NonDerivable` |
| 拆全称支持者 | `all_split_not_admissible` | 本文件第一节 |
| 拆嵌套关系 → `a ⊳ c` | `nested_supp_not_admissible` | 本文件第九节 |
| 拆嵌套关系 → `c ⊲ d` | `nested_refut_not_admissible` | 本文件第五节 |
| 拆反驳支持关系 → `a ⊲ c` | `refute_supp_not_admissible` | 本文件第十节 |
| 拆反驳支持关系 → `a ⊲ d` | `refute_supp_not_admissible'` | 本文件第十节 |
| S7 不同主体合取 | **未拿下**（见 11.3） | — |
| 反驳合取拆项 | `refut_and_not_admissible` | 本文件第六节 |
| 反驳全称拆实例 | `refut_all_not_admissible` | 本文件第七节 |
| 非命题性反驳逆后承 | `refute_converse_not_admissible` | 本文件第二节 |

### 11.2 已被机器复核的筛子（第三节）

* `derivable_rel_truth_eq_top`：任何可推导的关系式在任意模型、任意赋值下真值为 `⊤`。
* `canon_valid_supp_of_const_left` / `canon_valid_refut_of_const_left`：
  结论的支持者若真值恒为常值命题，则该结论在任意典范框架中有效。
* 由此排除的见证形状：`a := c ⊲ d`、`a := c ⊳ d`（`canon_valid_supp_of_*_supporter`）、
  `a := ¬(c ⊳ d)`（`canon_valid_refut_of_not_supp_supporter`），
  以及一切「支持者只由关系式与 `⊤`／`⊥` 经 `¬ ∧ ∨ →` 构成」的见证。

**但筛子不是全部真相**：第九、十节的成功见证恰恰**绕开了**它——
支持者取「关系式 ∧ 原子」（如 `(F2 ⊲ F3) ∧ F1`），其真值 `⊤ ⊓ s0 = s0` 不再常值，
于是结论可以被否证。这说明"支持者里出现原子"是绕过筛子的**关键**，
也说明 11.3 的两条不能仅凭筛子断言。

### 11.3 支持传递与 S7：为何反模型方法被堵死

**（a）已机器复核的部分**（见第十二节）：

* `suppP_middle_eq_top`：`suppP X Y ∧ suppP Y Z ∧ ¬ suppP X Z ⟹ Y = ⊤`。
* `support_transitivity_middle_truth_top`：任何典范框架里的反例都**被迫**让中间公式 `b`
  在该赋值处真值为 `⊤`。
* `TruthPropagation`（单列为 `Prop`，本文件**未证**）＋
  `support_transitivity_conclusion_valid_of_propagation`：**若**传播引理成立，
  **则**支持传递的结论在一切典范框架、一切赋值下有效，`not_derivable_of_countermodel` 失效。

**（b）两条独立分析都指向同一缺口。** 对 `Derivable (t ⊳ c)` 归纳验证传播引理，
`s1`／`s2`／`f1`–`f4`／`p1`／`p2` 各支都是几行 `PSet` 引理即可闭合；
**唯一未闭合的是 `E` 的「洞在顶层」情形**：此时只有 `Derivable γ` 与
`γ ⊣⊢ (t ⊳ c)`。基语义下取 `suppI` 为投影（`fun X _ => X` 或 `fun _ Y => Y`）
只能得到该基结构内的真值相等，而典范框架用的 `suppI` 是 `suppP`——两者一般不同。
补齐这一步等价于要求**「公式模 `⊣⊢` 的 Lindenbaum 代数」与典范框架真值相合**，
正是 [`docs/讨论与局限.md`](../../docs/讨论与局限.md) 第 2 节点明的**完备性/相合性公开问题**。

**（c）S7 的同类结论**（对 `Fin 3` 的 8 个命题穷举全部 `(⟦a⟧,⟦φ⟧,⟦b⟧,⟦ψ⟧)` 共 4096 组）：
结论失效要求 `⟦a⟧⊓⟦b⟧ ≰ ⟦φ⟧⊓⟦ψ⟧ ∧ ⟦a⟧⊓⟦b⟧ ≠ ⊤ ∧ ⟦φ⟧⊓⟦ψ⟧ ≠ ⊤`；
两个前提可推导使 `suppP` 各取一个析取项，九种组合中八种与上式直接矛盾，
剩下一种恰好要求「存在可推导的 `b ⊳ ψ` 使 `⟦b⟧ = ⊤` 而 `⟦ψ⟧ ≠ ⊤`」——
即传播引理的**否定**。在传播引理约束下，满足反例条件的组合数 **= 0**（不加约束为 168 组）。

**结论**：本文对这两条**只有** `NonDerivable` 的「蕴含式非有效 + 不可推导」，
**不能**说它们"每个实例都推不出"；现有证据倾向它们**作为规则可容许**、
只是不可作为公理导出（admissible but not derivable）。而"它们不可能被反模型否证"这一
障碍说明**尚未完全定理化**：它精确地归约到本工程公开的完备性/相合性问题。 -/

/-! ## 十二、支持传递的机器复核障碍（把 11.3 的分析尽量定理化）

11.3 的分析可以部分形式化。以下两条**已证**：

* 任何典范框架中的反例都**被迫**让中间公式的真值为 `⊤`（`suppP` 层面的推理）；
* 若把「真值传播引理」作为假设（`TruthPropagation`），则支持传递的结论在**一切**
  典范框架、**一切**赋值下都有效——于是 `not_derivable_of_countermodel` 这条路
  **根本走不通**。

传播引理本身尚未证明：它唯一未闭合的是 `E` 的「洞在顶层」情形，那一步等价于
要求「公式模 `⊣⊢` 的 Lindenbaum 代数」与典范框架真值相合，即
[`docs/讨论与局限.md`](../../docs/讨论与局限.md) 第 2 节点明的公开问题。

**把障碍压到最紧的形式**（两条**无缺口**的必要条件，见下）：

* `support_transitivity_middle_truth_top`：反例处必有 `⟦b⟧ = ⊤`；
* `countermodel_formula_truth_ne_top`：反例处必有 `⟦c⟧ ≠ ⊤`。

合起来：**支持传递的见证必须给出一个「可推导的」支持式 `b ⊳ c`，使主体真值为 `⊤`
而被支持公式真值不为 `⊤`**——这正是传播引理的否定。同理，S7 的九种析取组合中
唯一不被直接矛盾排除的那一种也恰好要求这样的 `b ⊳ ψ`。

因此这两条的"非可容许性"在本形式化中**既没有证成、也没有被否证**：
所有已知技巧都被上述必要条件与第三节的筛子排除，而唯一出路（传播引理／转移引理）
归约到本工程公开的相合性问题。 -/

/-- **命题层障碍**：`suppP X Y`、`suppP Y Z`、`¬ suppP X Z` 三者不相容，除非 `Y = ⊤`。

即：支持传递的反例若存在，中间项真值必为 `⊤`。 -/
theorem suppP_middle_eq_top {W : Type} {X Y Z : PSet W}
    (h₁ : Canon.suppP X Y) (h₂ : Canon.suppP Y Z) (h₃ : ¬ Canon.suppP X Z) :
    Y = ⊤ := by
  by_cases hY : Y = ⊤
  · exact hY
  · exfalso
    have hX : X ≠ ⊤ := fun h => h₃ (Or.inr (Or.inl h))
    have hZ : Z ≠ ⊤ := fun h => h₃ (Or.inr (Or.inr h))
    have hYZ : Y ≤ Z := by
      rcases h₂ with h | h | h
      · exact h
      · exact absurd h hY
      · exact absurd h hZ
    have hXY : X ≤ Y := by
      rcases h₁ with h | h | h
      · exact h
      · exact absurd h hX
      · exact absurd h hY
    exact h₃ (Or.inl (PSet.le_trans hXY hYZ))

/-- **典范框架中的障碍**：若 `a ⊳ b` 与 `b ⊳ c` 都可推导，而结论 `a ⊳ c` 在
典范框架的赋值 `ρ` 处不为 `⊤`，则 `b` 在该处的真值必为 `⊤`。 -/
theorem support_transitivity_middle_truth_top
    (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    (a b c : Form) (ρ : Nat → PSet W)
    (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c))
    (h₃ : ¬ (Canon.frame W atomRel).truth (a ⊳ c) ρ = ⊤) :
    (Canon.frame W atomRel).truth b ρ = ⊤ := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  have hM : IsModel (Canon.frame W atomRel) := Canon.isModel W atomRel
  have hv₁ : (Canon.frame W atomRel).truth (a ⊳ b) ρ = ⊤ :=
    Derivable.soundness (Canon.frame W atomRel) hM h₁ ρ
  have hv₂ : (Canon.frame W atomRel).truth (b ⊳ c) ρ = ⊤ :=
    Derivable.soundness (Canon.frame W atomRel) hM h₂ ρ
  have hs₁ : Canon.suppP ((Canon.frame W atomRel).truth a ρ)
      ((Canon.base W atomRel).truth b ρ) :=
    (PSet.const_eq_top_iff w₀).mp hv₁
  have hb : (Canon.frame W atomRel).truth b ρ = (Canon.base W atomRel).truth b ρ :=
    Canon.frame_truth W atomRel b ρ
  have hs₂ : Canon.suppP ((Canon.base W atomRel).truth b ρ)
      ((Canon.base W atomRel).truth c ρ) := by
    rw [← hb]
    exact (PSet.const_eq_top_iff w₀).mp hv₂
  have hs₃ : ¬ Canon.suppP ((Canon.frame W atomRel).truth a ρ)
      ((Canon.base W atomRel).truth c ρ) :=
    fun hcon => h₃ ((PSet.const_eq_top_iff w₀).mpr hcon)
  have hmid : (Canon.base W atomRel).truth b ρ = ⊤ :=
    suppP_middle_eq_top hs₁ hs₂ hs₃
  rw [hb]
  exact hmid

/-- **任何模型中的必要条件（无缺口）**：真值为 `⊤` 的公式被任何真值所支持
（`S1` ＋ `IsModel.classical`）。 -/
theorem supp_of_truth_top {M : Frame} (hM : IsModel M) (a c : Form)
    (ρ : Nat → PSet M.W) (hc : M.truth c ρ = ⊤) : M.supp (M.truth a ρ) c ρ :=
  hM.s1 a c ρ (by rw [hc]; exact PSet.le_top (M.truth a ρ))

/-- **任何模型中的必要条件（无缺口）**：若结论 `a ⊳ c` 在某模型、某赋值处不成立，
则 `c` 在该处的真值必不为 `⊤`。 -/
theorem countermodel_formula_truth_ne_top {M : Frame} (hM : IsModel M)
    {a c : Form} {ρ : Nat → PSet M.W} (h : ¬ M.truth (a ⊳ c) ρ = ⊤) :
    M.truth c ρ ≠ ⊤ :=
  fun hc => h (Derivable.valid_supp M hM (supp_of_truth_top hM a c ρ hc))

/-- **真值传播引理（本文件未证，单列为 `Prop`）**：任一可推导的支持式 `t ⊳ c`，
在其主体真值为 `⊤` 的赋值处，被支持公式的真值也被迫为 `⊤`。 -/
def TruthPropagation : Prop :=
  ∀ {t c : Form}, Derivable (t ⊳ c) →
    ∀ (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
      (ρ : Nat → PSet W),
      (Canon.frame W atomRel).truth t ρ = ⊤ → (Canon.frame W atomRel).truth c ρ = ⊤

/-- **归约**：若真值传播引理成立，则支持传递的结论在一切典范框架、一切赋值下有效——
于是典范框架反模型法失效。 -/
theorem support_transitivity_conclusion_valid_of_propagation
    (hprop : TruthPropagation)
    (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    (a b c : Form) (ρ : Nat → PSet W)
    (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c)) :
    (Canon.frame W atomRel).truth (a ⊳ c) ρ = ⊤ := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  by_cases hne : (Canon.frame W atomRel).truth (a ⊳ c) ρ = ⊤
  · exact hne
  · have hmid : (Canon.frame W atomRel).truth b ρ = ⊤ :=
      support_transitivity_middle_truth_top W atomRel a b c ρ h₁ h₂ hne
    have hc : (Canon.frame W atomRel).truth c ρ = ⊤ := hprop h₂ W atomRel ρ hmid
    have hbc : (Canon.base W atomRel).truth c ρ = ⊤ := by
      rw [← Canon.frame_truth W atomRel c ρ]
      exact hc
    exact absurd ((PSet.const_eq_top_iff w₀).mpr (Or.inr (Or.inr hbc))) hne

end

end EvidenceLogic
