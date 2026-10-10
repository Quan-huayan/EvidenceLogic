/-
# 背书逻辑 v1.0：可导出结果（Derived）

本文件形式化「背书逻辑 v1.0 定稿」第九节「可导出结果」所列诸条：

* **支持方面（1–5）**：支持自反、合取消除、全称实例化、支持弱化、肯定前件；
* **反驳方面（6–10）**：支持否定即反驳、支持即反驳否定、命题性反驳逆后承、
  反驳析取、反驳存在；
* **关系的关系（11–14）**：`R, S ∈ {⊳, ⊲}` 四种组合下的嵌套导出；
* **合取与全称推广（15–16）**：公理 `P1`／`P2` 的重述。

为保证自足，本文件只依赖 `EvidenceLogic.Derivable`（它已重导出语义层），
不使用 `sorry`／`axiom`，也不引入 Mathlib。
-/
import EvidenceLogic.Derivable

namespace EvidenceLogic

/-! ## 一、后承与等价的基本事实

`Entails p q` 是「逐基结构（`Base`）、逐赋值的真值不等式」。以下引理把它
化归为 `PSet` 层面的初等推理，供 `S1`／`S2`／`E` 使用。 -/

/-- 后承自反：`φ ⊢ φ`。 -/
theorem entails_refl (φ : Form) : Entails φ φ := by
  intro B ρ
  exact PSet.le_refl _

/-- 合取消除（左）：`φ ∧ ψ ⊢ φ`。 -/
theorem entails_and_left (φ ψ : Form) : Entails (.and φ ψ) φ := by
  intro B ρ w h
  exact h.1

/-- 合取消除（右）：`φ ∧ ψ ⊢ ψ`。 -/
theorem entails_and_right (φ ψ : Form) : Entails (.and φ ψ) ψ := by
  intro B ρ w h
  exact h.2

/-- 合取引入（幂等方向）：`φ ⊢ φ ∧ φ`。 -/
theorem entails_and_self (φ : Form) : Entails φ (.and φ φ) := by
  intro B ρ w h
  exact ⟨h, h⟩

/-- 析取引入（左）：`φ ⊢ φ ∨ ψ`。 -/
theorem entails_or_left (φ ψ : Form) : Entails φ (.or φ ψ) := by
  intro B ρ w h
  exact Or.inl h

/-- 析取引入（右）：`ψ ⊢ φ ∨ ψ`。 -/
theorem entails_or_right (φ ψ : Form) : Entails ψ (.or φ ψ) := by
  intro B ρ w h
  exact Or.inr h

/-- 全称实例化：`∀x φ ⊢ φ[x := a]`，其中 `a` 对 `x` 在 `φ` 中可代入。 -/
theorem entails_all_inst {x : Nat} {φ a : Form} (hf : FreeFor a x φ) :
    Entails (.all x φ) (inst x a φ) := by
  intro B ρ w h
  rw [Base.truth_inst B hf ρ]
  exact PSet.iInter_le (fun X : PSet B.W => B.truth φ (upd ρ x X)) (B.truth a ρ) w h

/-- 肯定前件（语义层）：`(φ → ψ) ∧ φ ⊢ ψ`。 -/
theorem entails_mp (φ ψ : Form) : Entails (.and (.imp φ ψ) φ) ψ := by
  intro B ρ w h
  rcases h.1 with hx | hy
  · exact absurd h.2 hx
  · exact hy

/-- 双重否定引入：`φ ⊢ ¬¬φ`。 -/
theorem entails_dni (φ : Form) : Entails φ (.not (.not φ)) := by
  intro B ρ w h hx
  exact hx h

/-- 逆否：由 `φ ⊢ ψ` 得 `¬ψ ⊢ ¬φ`。 -/
theorem entails_not_of_entails {φ ψ : Form} (h : Entails φ ψ) :
    Entails (.not ψ) (.not φ) := by
  intro B ρ w hw hf
  exact hw (h B ρ w hf)

/-- `¬(φ ∨ ψ) ⊢ ¬φ`。 -/
theorem entails_not_or_left (φ ψ : Form) : Entails (.not (.or φ ψ)) (.not φ) := by
  intro B ρ w h hf
  exact h (Or.inl hf)

/-- `¬(φ ∨ ψ) ⊢ ¬ψ`。 -/
theorem entails_not_or_right (φ ψ : Form) : Entails (.not (.or φ ψ)) (.not ψ) := by
  intro B ρ w h hf
  exact h (Or.inr hf)

/-- `¬∃x φ ⊢ ¬φ[x := a]`，其中 `a` 对 `x` 在 `φ` 中可代入。 -/
theorem entails_not_ex_inst {x : Nat} {φ a : Form} (hf : FreeFor a x φ) :
    Entails (.not (.ex x φ)) (.not (inst x a φ)) := by
  intro B ρ w h hc
  rw [Base.truth_inst B hf ρ] at hc
  exact h ⟨B.truth a ρ, hc⟩

/-- 合取幂等（等价）：`φ ∧ φ ⊣⊢ φ`。 -/
theorem cequiv_and_self (φ : Form) : (.and φ φ) ⊣⊢ φ :=
  ⟨entails_and_left φ φ, entails_and_self φ⟩

/-- 合取幂等（反向等价）：`φ ⊣⊢ φ ∧ φ`。 -/
theorem cequiv_self_and (φ : Form) : φ ⊣⊢ (.and φ φ) :=
  ⟨entails_and_self φ, entails_and_left φ φ⟩

/-! ## 二、支持方面（1–5） -/

/-- **1. 支持自反**。`p` 支持自身：`p ⊳ p`。 -/
theorem support_refl (p : Form) : Derivable (p ⊳ p) :=
  Derivable.s1 (entails_refl p)

/-- **2. 合取消除（左）**。由 `t ⊳ (φ ∧ ψ)` 得 `t ⊳ φ`。 -/
theorem support_and_left {t φ ψ : Form} (h : Derivable (t ⊳ (.and φ ψ))) :
    Derivable (t ⊳ φ) :=
  Derivable.s2 h (entails_and_left φ ψ)

/-- **2. 合取消除（右）**。由 `t ⊳ (φ ∧ ψ)` 得 `t ⊳ ψ`。 -/
theorem support_and_right {t φ ψ : Form} (h : Derivable (t ⊳ (.and φ ψ))) :
    Derivable (t ⊳ ψ) :=
  Derivable.s2 h (entails_and_right φ ψ)

/-- **3. 全称实例化**。由 `t ⊳ ∀x φ` 得 `t ⊳ φ[x := a]`（`a` 对 `x` 可代入）。 -/
theorem support_all_inst {t : Form} {x : Nat} {φ a : Form}
    (h : Derivable (t ⊳ (.all x φ))) (hf : FreeFor a x φ) :
    Derivable (t ⊳ inst x a φ) :=
  Derivable.s2 h (entails_all_inst hf)

/-- **4. 支持弱化（左）**。由 `t ⊳ φ` 得 `t ⊳ (φ ∨ ψ)`。 -/
theorem support_weaken_left {t φ ψ : Form} (h : Derivable (t ⊳ φ)) :
    Derivable (t ⊳ (.or φ ψ)) :=
  Derivable.s2 h (entails_or_left φ ψ)

/-- **4. 支持弱化（右）**。由 `t ⊳ φ` 得 `t ⊳ (ψ ∨ φ)`。 -/
theorem support_weaken_right {t φ ψ : Form} (h : Derivable (t ⊳ φ)) :
    Derivable (t ⊳ (.or ψ φ)) :=
  Derivable.s2 h (entails_or_right ψ φ)

/-- **5. 肯定前件**。由 `t ⊳ (φ → ψ)` 与 `t ⊳ φ` 得 `t ⊳ ψ`。 -/
theorem support_mp {t φ ψ : Form} (h₁ : Derivable (t ⊳ (.imp φ ψ)))
    (h₂ : Derivable (t ⊳ φ)) : Derivable (t ⊳ ψ) :=
  Derivable.s2 (Derivable.f4 (k := .supp) h₁ h₂) (entails_mp φ ψ)

/-! ## 三、反驳方面（6–10） -/

/-- **6. 支持否定即反驳**（即规则 `R1`）。由 `t ⊳ ¬φ` 得 `t ⊲ φ`。 -/
theorem refute_of_support_not {t φ : Form} (h : Derivable (t ⊳ (.not φ))) :
    Derivable (t ⊲ φ) :=
  Derivable.r1 h

/-- **7. 支持即反驳否定**。由 `t ⊳ φ` 得 `t ⊲ ¬φ`。 -/
theorem refute_not_of_support {t φ : Form} (h : Derivable (t ⊳ φ)) :
    Derivable (t ⊲ (.not φ)) :=
  Derivable.r1 (Derivable.s2 h (entails_dni φ))

/-- **8. 命题性反驳逆后承**。由 `φ ⊢ ψ` 与 `t ⊳ ¬ψ` 得 `t ⊲ φ`。 -/
theorem refute_of_entails_not {t φ ψ : Form} (h : Entails φ ψ)
    (hψ : Derivable (t ⊳ (.not ψ))) : Derivable (t ⊲ φ) :=
  Derivable.r1 (Derivable.s2 hψ (entails_not_of_entails h))

/-- **9. 反驳析取（左）**。由 `t ⊳ ¬(φ ∨ ψ)` 得 `t ⊲ φ`。 -/
theorem refute_or_left {t φ ψ : Form} (h : Derivable (t ⊳ (.not (.or φ ψ)))) :
    Derivable (t ⊲ φ) :=
  Derivable.r1 (Derivable.s2 h (entails_not_or_left φ ψ))

/-- **9. 反驳析取（右）**。由 `t ⊳ ¬(φ ∨ ψ)` 得 `t ⊲ ψ`。 -/
theorem refute_or_right {t φ ψ : Form} (h : Derivable (t ⊳ (.not (.or φ ψ)))) :
    Derivable (t ⊲ ψ) :=
  Derivable.r1 (Derivable.s2 h (entails_not_or_right φ ψ))

/-- **10. 反驳存在**。由 `t ⊳ ¬∃x φ` 得 `t ⊲ φ[x := a]`（`a` 对 `x` 可代入）。 -/
theorem refute_ex_inst {t : Form} {x : Nat} {φ a : Form}
    (h : Derivable (t ⊳ (.not (.ex x φ)))) (hf : FreeFor a x φ) :
    Derivable (t ⊲ inst x a φ) :=
  Derivable.r1 (Derivable.s2 h (entails_not_ex_inst hf))

/-! ## 四、关系的关系（11–14）

由 `P1` 出发：把两个前提中的 `c` 换成 `c ∧ c`，用 `P1` 合成嵌套关系，
再用元规则 `E`（合取幂等 `x ∧ x ⊣⊢ x`）把两处 `x ∧ x` 消去。
由于 `⊳`／`⊲` 的语义是任意的真值函数，这一步**必须**在语法层通过
`Replace`（单项上下文）完成，而不能用整体等价。 -/

/-- 关系的关系（一般形式）：`R, S ∈ {⊳, ⊲}` 任意组合。

由 `a R c` 与 `c S d` 得 `a R (c S d)`。 -/
theorem derivable_rel_rel {kR kS : Kind} {a c d : Form}
    (h₁ : Derivable (Kind.form kR a c)) (h₂ : Derivable (Kind.form kS c d)) :
    Derivable (Kind.form kR a (Kind.form kS c d)) := by
  -- 第一步：把前提 `c S d` 中的 `c` 换成 `c ∧ c`（合取幂等的反向）。
  have hcc : Derivable (Kind.form kS (.and c c) d) := by
    cases kS
    · exact Derivable.e (φ := c) (ψ := .and c c)
        ⟨Ctx.suppL Ctx.hole d, rfl, rfl⟩ (cequiv_self_and c) h₂
    · exact Derivable.e (φ := c) (ψ := .and c c)
        ⟨Ctx.refutL Ctx.hole d, rfl, rfl⟩ (cequiv_self_and c) h₂
  -- 第二步：以 `b := a`、`d := c` 实例化 `P1`。
  have hp1 : Derivable (Kind.form kR (.and a a) (Kind.form kS (.and c c) d)) :=
    Derivable.p1 (kR := kR) (kS := kS) (a := a) (b := a) (c := c) (d := c) (f := d)
      h₁ h₁ hcc
  -- 第三步：消去内层的 `c ∧ c`。
  have hstep : Derivable (Kind.form kR (.and a a) (Kind.form kS c d)) := by
    cases kR <;> cases kS
    · exact Derivable.e (φ := .and c c) (ψ := c)
        ⟨Ctx.suppR (.and a a) (Ctx.suppL Ctx.hole d), rfl, rfl⟩ (cequiv_and_self c) hp1
    · exact Derivable.e (φ := .and c c) (ψ := c)
        ⟨Ctx.suppR (.and a a) (Ctx.refutL Ctx.hole d), rfl, rfl⟩ (cequiv_and_self c) hp1
    · exact Derivable.e (φ := .and c c) (ψ := c)
        ⟨Ctx.refutR (.and a a) (Ctx.suppL Ctx.hole d), rfl, rfl⟩ (cequiv_and_self c) hp1
    · exact Derivable.e (φ := .and c c) (ψ := c)
        ⟨Ctx.refutR (.and a a) (Ctx.refutL Ctx.hole d), rfl, rfl⟩ (cequiv_and_self c) hp1
  -- 第四步：消去外层的 `a ∧ a`。
  cases kR
  · exact Derivable.e (φ := .and a a) (ψ := a)
      ⟨Ctx.suppL Ctx.hole (Kind.form kS c d), rfl, rfl⟩ (cequiv_and_self a) hstep
  · exact Derivable.e (φ := .and a a) (ψ := a)
      ⟨Ctx.refutL Ctx.hole (Kind.form kS c d), rfl, rfl⟩ (cequiv_and_self a) hstep

/-- **11. 支持—支持**。由 `a ⊳ c` 与 `c ⊳ d` 得 `a ⊳ (c ⊳ d)`。 -/
theorem support_support {a c d : Form} (h₁ : Derivable (a ⊳ c))
    (h₂ : Derivable (c ⊳ d)) : Derivable (a ⊳ (c ⊳ d)) :=
  derivable_rel_rel (kR := .supp) (kS := .supp) h₁ h₂

/-- **12. 支持—反驳**。由 `a ⊳ c` 与 `c ⊲ d` 得 `a ⊳ (c ⊲ d)`。 -/
theorem support_refute {a c d : Form} (h₁ : Derivable (a ⊳ c))
    (h₂ : Derivable (c ⊲ d)) : Derivable (a ⊳ (c ⊲ d)) :=
  derivable_rel_rel (kR := .supp) (kS := .refut) h₁ h₂

/-- **13. 反驳—支持**。由 `a ⊲ c` 与 `c ⊳ d` 得 `a ⊲ (c ⊳ d)`。 -/
theorem refute_support {a c d : Form} (h₁ : Derivable (a ⊲ c))
    (h₂ : Derivable (c ⊳ d)) : Derivable (a ⊲ (c ⊳ d)) :=
  derivable_rel_rel (kR := .refut) (kS := .supp) h₁ h₂

/-- **14. 反驳—反驳**。由 `a ⊲ c` 与 `c ⊲ d` 得 `a ⊲ (c ⊲ d)`。 -/
theorem refute_refute {a c d : Form} (h₁ : Derivable (a ⊲ c))
    (h₂ : Derivable (c ⊲ d)) : Derivable (a ⊲ (c ⊲ d)) :=
  derivable_rel_rel (kR := .refut) (kS := .refut) h₁ h₂

/-! ## 五、合取与全称推广（15–16）

这两条正是公理 `P1`／`P2` 的重述，直接由归纳定义给出。 -/

/-- **15. 二元合取推广**（公理 `P1` 的重述）。

由 `a R c`、`b R d` 与 `(c ∧ d) S f` 得 `(a ∧ b) R ((c ∧ d) S f)`。 -/
theorem conj_promotion {kR kS : Kind} {a b c d f : Form}
    (h₁ : Derivable (Kind.form kR a c)) (h₂ : Derivable (Kind.form kR b d))
    (h₃ : Derivable (Kind.form kS (.and c d) f)) :
    Derivable (Kind.form kR (.and a b) (Kind.form kS (.and c d) f)) :=
  Derivable.p1 (kR := kR) (kS := kS) (a := a) (b := b) (c := c) (d := d) (f := f)
    h₁ h₂ h₃

/-- **16. 全称推广**（公理 `P2` 的重述）。

由 `a R c`、`(∀x c) S f` 与 `x ∉ FV(f)` 得 `(∀x a) R ((∀x c) S f)`。 -/
theorem all_promotion {kR kS : Kind} {a c f : Form} {x : Nat}
    (h₁ : Derivable (Kind.form kR a c)) (h₂ : Derivable (Kind.form kS (.all x c) f))
    (hx : ¬ FreeIn x f) :
    Derivable (Kind.form kR (.all x a) (Kind.form kS (.all x c) f)) :=
  Derivable.p2 (kR := kR) (kS := kS) (a := a) (c := c) (f := f) (x := x) h₁ h₂ hx

end EvidenceLogic
