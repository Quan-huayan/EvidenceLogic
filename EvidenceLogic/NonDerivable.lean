/-
# 背书逻辑 v1.0：不可推导的典型命题（NonDerivable）

本文件形式化定稿第十节「不能推出的典型命题」：为定稿第七节明确**排除**的每一条规则
给出一个**有限反模型**，并由此（借助 `Derivable.soundness`）证明相应命题**不可推导**。

## 方法

1. **一般原则** `not_derivable_of_countermodel`：若 `φ` 在某个模型中不有效，
   则 `φ` 不可推导（可靠性的逆否命题）。
2. **三元素反模型** `M3`：取 `W := Fin 3`，四个基本命题
   `s0 = {0}`、`s1 = {1}`、`s2 = {2}`、`s01 = {0,1}`，原子解释 `atomRel3`，
   框架 `M3 := Canon.frame (Fin 3) atomRel3`；它是模型（`M3_isModel`，
   由存在性定理 `Canon.isModel` 得到）。
3. 对每条被排除的规则取具体实例与赋值（多数取 `rho0 := fun _ => ⊥`，
   涉及一元原子 `F5` 时取 `rho1 := upd rho0 0 s0`），算出**前件真、后件假**。

## 记号

* `F0`、`F1`、`F2`、`F3`、`F4` 是五个零元原子，其解释分别为 `⊤`、`s0`、`s1`、`s2`、`s01`；
* `F5 = P₅(x)` 是一元原子，解释为「参数为 `s0` 时取 `s2`，否则取 `s0`」；
* `rho0` 为恒取 `⊥` 的赋值，`rho1` 为在 `rho0` 上把变元 `0` 取为 `s0` 的赋值。

`F5` 的设计使 `∀x F5` 的真值为 `⊥`
（因为 `atomRel3 5 [s0] ⊓ atomRel3 5 [s1] = s2 ⊓ s0 = ⊥`），
而在 `rho1` 下 `F5` 的真值为 `s2`——这正是「拆全称支持者」与「反驳全称拆实例」失效的原因。

## 关于「反驳逆后承」的说明

定稿中的非命题性反驳逆后承带有语义副作用条件 `φ ⊢ ψ`。由于本工程的 `Entails`
是对**所有**基结构量化（即经典后承），对具体原子 `F0`、`F1` 而言 `Entails F1 F0`
并**不**成立（`Entails` 需要 `B.atomRel 1 [] ≤ B.atomRel 0 []` 对任意 `B` 成立）。
因此本文件用 `ψ := Form.top`（`Entails F1 Form.top` 确实成立）给出规则形状的真实例，
另外也给出定稿所要求的 `ψ := F0` 的具体不可推导性结论。

## 关于「系统不蕴涵真」的说明

定稿第八节称「`t ⊳ φ` 不蕴涵 `φ`」。本文件给出两个结论：
`not_truth_preserving`（用 `⊥ ⊳ ⊥` 可推导而 `⊥` 不有效）与
`M3_support_does_not_imply_truth`（在 `M3` 中 `F1 ⊳ F2` 既不有效也不可推导）。
-/
import EvidenceLogic.Canonical
import EvidenceLogic.Soundness

namespace EvidenceLogic

noncomputable section

open scoped Classical

/-! ## 一、一般原则：反模型蕴含不可推导 -/

/-- **反模型原则**：若 `φ` 在模型 `M` 中不有效，则 `φ` 不可推导。 -/
theorem not_derivable_of_countermodel {φ : Form} {M : Frame} (hM : IsModel M)
    (h : ¬ M.Valid φ) : ¬ Derivable φ :=
  fun hd => h (Derivable.soundness M hM hd)

/-! ## 二、三元素反模型 `M3` -/

/-- 命题「处于状态 `0`」。 -/
abbrev s0 : PSet (Fin 3) := ⟨fun w => w = 0⟩

/-- 命题「处于状态 `1`」。 -/
abbrev s1 : PSet (Fin 3) := ⟨fun w => w = 1⟩

/-- 命题「处于状态 `2`」。 -/
abbrev s2 : PSet (Fin 3) := ⟨fun w => w = 2⟩

/-- 命题「处于状态 `0` 或 `1`」。 -/
abbrev s01 : PSet (Fin 3) := ⟨fun w => w = 0 ∨ w = 1⟩

/-- 原子解释：`0` 取 `⊤`，`1`–`4` 取 `s0`、`s1`、`s2`、`s01`，
`5` 取一元原子「参数是 `s0` 则为 `s2`，否则为 `s0`」，其余取 `⊥`。 -/
def atomRel3 : Nat → List (PSet (Fin 3)) → PSet (Fin 3)
  | 0, _ => ⊤
  | 1, _ => s0
  | 2, _ => s1
  | 3, _ => s2
  | 4, _ => s01
  | 5, args => match args with
      | X :: _ => if X = s0 then s2 else s0
      | [] => ⊥
  | _, _ => ⊥

/-- 零元原子 `P₀`（真）。 -/
def F0 : Form := Form.atom 0 []

/-- 零元原子 `P₁`（解释为 `s0`）。 -/
def F1 : Form := Form.atom 1 []

/-- 零元原子 `P₂`（解释为 `s1`）。 -/
def F2 : Form := Form.atom 2 []

/-- 零元原子 `P₃`（解释为 `s2`）。 -/
def F3 : Form := Form.atom 3 []

/-- 零元原子 `P₄`（解释为 `s01`）。 -/
def F4 : Form := Form.atom 4 []

/-- 一元原子 `P₅(x)`（`s0` 取 `s2`，否则取 `s0`）。 -/
def F5 : Form := Form.atom 5 [Form.var 0]

/-- 相应的经典基结构。 -/
abbrev B3 : Base := Canon.base (Fin 3) atomRel3

/-- **三元素反模型**。 -/
abbrev M3 : Frame := Canon.frame (Fin 3) atomRel3

/-- `M3` 是模型：由典范框架的存在性定理得到。 -/
theorem M3_isModel : IsModel M3 := Canon.isModel (Fin 3) atomRel3

/-- 恒取 `⊥` 的赋值。 -/
abbrev rho0 : Nat → PSet (Fin 3) := fun _ => ⊥

/-- 在 `rho0` 上把变元 `0` 取为 `s0` 的赋值。 -/
abbrev rho1 : Nat → PSet (Fin 3) := upd rho0 0 s0

/-! ## 三、基本工具

`cst P` 表示恒常命题；`M3` 中关系子公式的真值恰为恒常命题。 -/

/-- 恒常命题 `⟨fun _ => P⟩`。 -/
abbrev cst (P : Prop) : PSet (Fin 3) := ⟨fun _ => P⟩

@[simp] theorem cst_compl (P : Prop) : (cst P)ᶜ = cst (¬ P) := rfl

@[simp] theorem cst_sup (P Q : Prop) : cst P ⊔ cst Q = cst (P ∨ Q) := rfl

@[simp] theorem cst_inf (P Q : Prop) : cst P ⊓ cst Q = cst (P ∧ Q) := rfl

/-- 恒常命题等于 `⊤` 当且仅当该命题成立。 -/
theorem cst_eq_top_iff (P : Prop) : cst P = ⊤ ↔ P := PSet.const_eq_top_iff (0 : Fin 3)

/-- 命题成立则相应的恒常命题等于 `⊤`。 -/
theorem cst_eq_top_of (P : Prop) (h : P) : cst P = ⊤ := (cst_eq_top_iff P).mpr h

/-- 命题不成立则相应的恒常命题不等于 `⊤`。 -/
theorem cst_ne_top_of_not {P : Prop} (h : ¬ P) : cst P ≠ ⊤ :=
  fun ht => h ((cst_eq_top_iff P).mp ht)

/-- 命题不成立则相应的恒常命题等于 `⊥`。 -/
theorem cst_eq_bot_of_not {P : Prop} (h : ¬ P) : cst P = ⊥ := by
  apply PSet.eq_bot_of_le
  intro w hw
  exact h hw

/-- 在某个状态上真值不同的两个命题不相等（前者真、后者假）。 -/
theorem pset_ne_of_world {X Y : PSet (Fin 3)} (w : Fin 3) (hx : X w) (hy : ¬ Y w) :
    X ≠ Y :=
  fun h => hy (h ▸ hx)

/-- 在某个状态上真值不同的两个命题不相等（前者假、后者真）。 -/
theorem pset_ne_of_world' {X Y : PSet (Fin 3)} (w : Fin 3) (hy : Y w) (hx : ¬ X w) :
    X ≠ Y :=
  fun h => hx (h.symm ▸ hy)

/-! ### 基本命题的不相等与不交 -/

theorem s0_ne_top : s0 ≠ ⊤ := pset_ne_of_world' (1 : Fin 3) trivial (by decide)

theorem s1_ne_top : s1 ≠ ⊤ := pset_ne_of_world' (0 : Fin 3) trivial (by decide)

theorem s2_ne_top : s2 ≠ ⊤ := pset_ne_of_world' (0 : Fin 3) trivial (by decide)

theorem s01_ne_top : s01 ≠ ⊤ := pset_ne_of_world' (2 : Fin 3) trivial (by decide)

theorem bot_ne_top : (⊥ : PSet (Fin 3)) ≠ ⊤ :=
  pset_ne_of_world' (0 : Fin 3) trivial (fun h => h)

theorem s0_ne_bot : s0 ≠ ⊥ := pset_ne_of_world (0 : Fin 3) rfl (fun h => h)

theorem s1_ne_bot : s1 ≠ ⊥ := pset_ne_of_world (1 : Fin 3) rfl (fun h => h)

theorem s2_ne_bot : s2 ≠ ⊥ := pset_ne_of_world (2 : Fin 3) rfl (fun h => h)

theorem bot_ne_s0 : (⊥ : PSet (Fin 3)) ≠ s0 := fun h => s0_ne_bot h.symm

theorem s1_ne_s0 : s1 ≠ s0 := pset_ne_of_world (1 : Fin 3) rfl (by decide)

theorem s0_inf_s1 : s0 ⊓ s1 = ⊥ := by
  apply PSet.eq_bot_of_le
  intro w hw
  exact absurd (hw.1.symm.trans hw.2) (by decide)

theorem s1_inf_s2 : s1 ⊓ s2 = ⊥ := by
  apply PSet.eq_bot_of_le
  intro w hw
  exact absurd (hw.1.symm.trans hw.2) (by decide)

theorem s0_inf_s2 : s0 ⊓ s2 = ⊥ := by
  apply PSet.eq_bot_of_le
  intro w hw
  exact absurd (hw.1.symm.trans hw.2) (by decide)

theorem s1_inf_s0 : s1 ⊓ s0 = ⊥ := by rw [PSet.inf_comm]; exact s0_inf_s1

theorem s2_inf_s1 : s2 ⊓ s1 = ⊥ := by rw [PSet.inf_comm]; exact s1_inf_s2

theorem s2_inf_s0 : s2 ⊓ s0 = ⊥ := by rw [PSet.inf_comm]; exact s0_inf_s2

theorem s01_inf_s2 : s01 ⊓ s2 = ⊥ := by
  apply PSet.eq_bot_of_le
  intro w hw
  rcases hw.1 with h | h
  · exact absurd (h.symm.trans hw.2) (by decide)
  · exact absurd (h.symm.trans hw.2) (by decide)

theorem s0_inf_s0 : s0 ⊓ s0 = s0 := by
  apply PSet.ext
  intro w
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem s1_inf_s1 : s1 ⊓ s1 = s1 := by
  apply PSet.ext
  intro w
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem s2_inf_s2 : s2 ⊓ s2 = s2 := by
  apply PSet.ext
  intro w
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem s01_inf_s1 : s01 ⊓ s1 = s1 := by
  apply PSet.ext
  intro w
  exact ⟨fun h => h.2, fun h => ⟨Or.inr h, h⟩⟩

theorem s0_inf_s0_ne_bot : s0 ⊓ s0 ≠ ⊥ := by rw [s0_inf_s0]; exact s0_ne_bot

theorem s1_inf_s1_ne_bot : s1 ⊓ s1 ≠ ⊥ := by rw [s1_inf_s1]; exact s1_ne_bot

theorem s2_inf_s2_ne_bot : s2 ⊓ s2 ≠ ⊥ := by rw [s2_inf_s2]; exact s2_ne_bot

theorem s01_inf_s1_ne_bot : s01 ⊓ s1 ≠ ⊥ := by rw [s01_inf_s1]; exact s1_ne_bot

theorem not_s0_le_s1 : ¬ (s0 ≤ s1) := fun h => absurd (h 0 rfl) (by decide)

theorem not_s2_le_s1 : ¬ (s2 ≤ s1) := fun h => absurd (h 2 rfl) (by decide)

theorem not_s0_le_bot : ¬ (s0 ≤ ⊥) := fun h => h 0 rfl

theorem not_s1_le_bot : ¬ (s1 ≤ ⊥) := fun h => h 1 rfl

theorem not_s2_le_bot : ¬ (s2 ≤ ⊥) := fun h => h 2 rfl

/-! ### 具体判据的假值 -/

theorem not_suppP_s0_s1 : ¬ Canon.suppP s0 s1 := by
  intro h
  rcases h with h | h | h
  · exact not_s0_le_s1 h
  · exact s0_ne_top h
  · exact s1_ne_top h

theorem not_suppP_s2_s1 : ¬ Canon.suppP s2 s1 := by
  intro h
  rcases h with h | h | h
  · exact not_s2_le_s1 h
  · exact s2_ne_top h
  · exact s1_ne_top h

theorem not_suppP_s1_bot : ¬ Canon.suppP s1 ⊥ := by
  intro h
  rcases h with h | h | h
  · exact not_s1_le_bot h
  · exact s1_ne_top h
  · exact bot_ne_top h

theorem not_refutP_s01_s1 : ¬ Canon.refutP s01 s1 := by
  intro h
  rcases h with h | h | h | h
  · exact s01_inf_s1_ne_bot h
  · exact s01_ne_top h
  · exact s1_ne_bot h
  · exact s1_ne_top h

theorem not_refutP_s0_s0 : ¬ Canon.refutP s0 s0 := by
  intro h
  rcases h with h | h | h | h
  · exact s0_inf_s0_ne_bot h
  · exact s0_ne_top h
  · exact s0_ne_bot h
  · exact s0_ne_top h

theorem not_refutP_s1_s1 : ¬ Canon.refutP s1 s1 := by
  intro h
  rcases h with h | h | h | h
  · exact s1_inf_s1_ne_bot h
  · exact s1_ne_top h
  · exact s1_ne_bot h
  · exact s1_ne_top h

theorem not_refutP_s2_s2 : ¬ Canon.refutP s2 s2 := by
  intro h
  rcases h with h | h | h | h
  · exact s2_inf_s2_ne_bot h
  · exact s2_ne_top h
  · exact s2_ne_bot h
  · exact s2_ne_top h

/-! ### 真值函数的计算规则 -/

/-- 框架真值与基真值一致（存在性定理的副产物）。 -/
theorem M3_truth_eq_base (φ : Form) (ρ : Nat → PSet (Fin 3)) :
    M3.truth φ ρ = B3.truth φ ρ :=
  Canon.frame_truth (Fin 3) atomRel3 φ ρ

theorem M3_truth_imp (φ ψ : Form) (ρ : Nat → PSet (Fin 3)) :
    M3.truth (Form.imp φ ψ) ρ = (M3.truth φ ρ)ᶜ ⊔ M3.truth ψ ρ := rfl

theorem M3_truth_and (φ ψ : Form) (ρ : Nat → PSet (Fin 3)) :
    M3.truth (Form.and φ ψ) ρ = M3.truth φ ρ ⊓ M3.truth ψ ρ := rfl

theorem M3_truth_supp (a b : Form) (ρ : Nat → PSet (Fin 3)) :
    M3.truth (a ⊳ b) ρ = cst (Canon.suppP (M3.truth a ρ) (B3.truth b ρ)) := rfl

theorem M3_truth_refut (a b : Form) (ρ : Nat → PSet (Fin 3)) :
    M3.truth (a ⊲ b) ρ = cst (Canon.refutP (M3.truth a ρ) (B3.truth b ρ)) := rfl

theorem M3_truth_all (x : Nat) (φ : Form) (ρ : Nat → PSet (Fin 3)) :
    M3.truth (Form.all x φ) ρ = PSet.iInter (fun X => M3.truth φ (upd ρ x X)) := rfl

theorem M3_truth_bot (ρ : Nat → PSet (Fin 3)) : M3.truth Form.bot ρ = ⊥ := rfl

theorem M3_truth_top (ρ : Nat → PSet (Fin 3)) : M3.truth Form.top ρ = ⊤ := rfl

theorem B3_truth_imp (φ ψ : Form) (ρ : Nat → PSet (Fin 3)) :
    B3.truth (Form.imp φ ψ) ρ = (B3.truth φ ρ)ᶜ ⊔ B3.truth ψ ρ := rfl

theorem B3_truth_and (φ ψ : Form) (ρ : Nat → PSet (Fin 3)) :
    B3.truth (Form.and φ ψ) ρ = B3.truth φ ρ ⊓ B3.truth ψ ρ := rfl

theorem B3_truth_supp (a b : Form) (ρ : Nat → PSet (Fin 3)) :
    B3.truth (a ⊳ b) ρ = cst (Canon.suppP (B3.truth a ρ) (B3.truth b ρ)) := rfl

theorem B3_truth_refut (a b : Form) (ρ : Nat → PSet (Fin 3)) :
    B3.truth (a ⊲ b) ρ = cst (Canon.refutP (B3.truth a ρ) (B3.truth b ρ)) := rfl

theorem B3_truth_all (x : Nat) (φ : Form) (ρ : Nat → PSet (Fin 3)) :
    B3.truth (Form.all x φ) ρ = PSet.iInter (fun X => B3.truth φ (upd ρ x X)) := rfl

theorem B3_truth_bot (ρ : Nat → PSet (Fin 3)) : B3.truth Form.bot ρ = ⊥ := rfl

theorem B3_truth_top (ρ : Nat → PSet (Fin 3)) : B3.truth Form.top ρ = ⊤ := rfl

theorem M3_truth_F0 (ρ : Nat → PSet (Fin 3)) : M3.truth F0 ρ = ⊤ := rfl

theorem M3_truth_F1 (ρ : Nat → PSet (Fin 3)) : M3.truth F1 ρ = s0 := rfl

theorem M3_truth_F2 (ρ : Nat → PSet (Fin 3)) : M3.truth F2 ρ = s1 := rfl

theorem M3_truth_F3 (ρ : Nat → PSet (Fin 3)) : M3.truth F3 ρ = s2 := rfl

theorem M3_truth_F4 (ρ : Nat → PSet (Fin 3)) : M3.truth F4 ρ = s01 := rfl

theorem M3_truth_F5 (ρ : Nat → PSet (Fin 3)) :
    M3.truth F5 ρ = (if ρ 0 = s0 then s2 else s0) := rfl

theorem B3_truth_F0 (ρ : Nat → PSet (Fin 3)) : B3.truth F0 ρ = ⊤ := rfl

theorem B3_truth_F1 (ρ : Nat → PSet (Fin 3)) : B3.truth F1 ρ = s0 := rfl

theorem B3_truth_F2 (ρ : Nat → PSet (Fin 3)) : B3.truth F2 ρ = s1 := rfl

theorem B3_truth_F3 (ρ : Nat → PSet (Fin 3)) : B3.truth F3 ρ = s2 := rfl

theorem B3_truth_F4 (ρ : Nat → PSet (Fin 3)) : B3.truth F4 ρ = s01 := rfl

theorem B3_truth_F5 (ρ : Nat → PSet (Fin 3)) :
    B3.truth F5 ρ = (if ρ 0 = s0 then s2 else s0) := rfl

/-- 在 `rho1` 下 `F5` 的真值为 `s2`。 -/
theorem M3_truth_F5_rho1 : M3.truth F5 rho1 = s2 := by
  rw [M3_truth_F5]
  show (if s0 = s0 then s2 else s0) = s2
  exact if_pos rfl

/-- 在 `rho1` 下 `F5` 的基真值为 `s2`。 -/
theorem B3_truth_F5_rho1 : B3.truth F5 rho1 = s2 := by
  rw [B3_truth_F5]
  show (if s0 = s0 then s2 else s0) = s2
  exact if_pos rfl

/-- 全称闭包 `∀x F5` 的真值为 `⊥`。 -/
theorem B3_truth_all_F5 (ρ : Nat → PSet (Fin 3)) : B3.truth (Form.all 0 F5) ρ = ⊥ := by
  rw [B3_truth_all]
  apply PSet.eq_bot_of_le
  intro w hw
  have h0 : (if s0 = s0 then s2 else s0) w := hw s0
  have h1 : (if s1 = s0 then s2 else s0) w := hw s1
  rw [if_pos rfl] at h0
  rw [if_neg s1_ne_s0] at h1
  exact absurd (h0.symm.trans h1) (by decide)

/-- 全称闭包 `∀x F5` 在 `M3` 中的真值为 `⊥`。 -/
theorem M3_truth_all_F5 (ρ : Nat → PSet (Fin 3)) : M3.truth (Form.all 0 F5) ρ = ⊥ := by
  rw [M3_truth_eq_base, B3_truth_all_F5]

theorem B3_truth_and_F1_F2 (ρ : Nat → PSet (Fin 3)) :
    B3.truth (Form.and F1 F2) ρ = ⊥ := by
  rw [B3_truth_and, B3_truth_F1, B3_truth_F2, s0_inf_s1]

theorem B3_truth_and_F0_F2 (ρ : Nat → PSet (Fin 3)) :
    B3.truth (Form.and F0 F2) ρ = s1 := by
  rw [B3_truth_and, B3_truth_F0, B3_truth_F2, PSet.top_inf_eq]

theorem B3_truth_and_F3_F2 (ρ : Nat → PSet (Fin 3)) :
    B3.truth (Form.and F3 F2) ρ = ⊥ := by
  rw [B3_truth_and, B3_truth_F3, B3_truth_F2, s2_inf_s1]

theorem M3_truth_and_F1_F2 (ρ : Nat → PSet (Fin 3)) :
    M3.truth (Form.and F1 F2) ρ = ⊥ := by
  rw [M3_truth_and, M3_truth_F1, M3_truth_F2, s0_inf_s1]

theorem M3_truth_and_F0_F2 (ρ : Nat → PSet (Fin 3)) :
    M3.truth (Form.and F0 F2) ρ = s1 := by
  rw [M3_truth_and, M3_truth_F0, M3_truth_F2, PSet.top_inf_eq]

/-- 由具体赋值处的真值不为 `⊤` 得到不有效性。 -/
theorem M3_not_valid_of_truth_ne_top {φ : Form} {ρ : Nat → PSet (Fin 3)}
    (h : M3.truth φ ρ ≠ ⊤) : ¬ M3.Valid φ :=
  fun hv => h (hv ρ)

/-! ## 四、定稿第七节各条规则的有限反模型 -/

/-! ### 1. 支持传递（不支持） -/

theorem support_transitivity_not_valid :
    ¬ M3.Valid (Form.imp (F1 ⊳ F0) (Form.imp (F0 ⊳ F2) (F1 ⊳ F2))) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_supp, M3_truth_F1, M3_truth_F0,
    B3_truth_F0, B3_truth_F2, cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h | h
  · exact h (Or.inl (PSet.le_top s0))
  · exact h (Or.inr (Or.inl rfl))
  · exact not_suppP_s0_s1 h

theorem support_transitivity_not_derivable :
    ¬ Derivable (Form.imp (F1 ⊳ F0) (Form.imp (F0 ⊳ F2) (F1 ⊳ F2))) :=
  not_derivable_of_countermodel M3_isModel support_transitivity_not_valid

/-! ### 2. 反驳传递（不成立） -/

theorem refute_transitivity_not_valid :
    ¬ M3.Valid (Form.imp (F4 ⊲ F0) (Form.imp (F0 ⊲ F2) (F4 ⊲ F2))) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_refut, M3_truth_F4, M3_truth_F0,
    B3_truth_F0, B3_truth_F2, cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h | h
  · exact h (Or.inr (Or.inr (Or.inr rfl)))
  · exact h (Or.inr (Or.inl rfl))
  · exact not_refutP_s01_s1 h

theorem refute_transitivity_not_derivable :
    ¬ Derivable (Form.imp (F4 ⊲ F0) (Form.imp (F0 ⊲ F2) (F4 ⊲ F2))) :=
  not_derivable_of_countermodel M3_isModel refute_transitivity_not_valid

/-! ### 3. 拆合取支持者（不支持）

同时证明前提 `(F1 ∧ F2) ⊳ F2` **可推导**，因此该拆解规则不是可容许规则。 -/

theorem and_split_not_valid :
    ¬ M3.Valid (Form.imp ((Form.and F1 F2) ⊳ F2) (F1 ⊳ F2)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_supp, M3_truth_and, M3_truth_F1, M3_truth_F2,
    B3_truth_F2, s0_inf_s1, cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inl (PSet.bot_le s1))
  · exact not_suppP_s0_s1 h

/-- 结论 `F1 ⊳ F2` 在 `M3` 中不有效，故不可推导。 -/
theorem and_split_conclusion_not_valid : ¬ M3.Valid (F1 ⊳ F2) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_supp, M3_truth_F1, B3_truth_F2]
  apply cst_ne_top_of_not
  exact not_suppP_s0_s1

theorem and_split_not_derivable :
    ¬ Derivable (Form.imp ((Form.and F1 F2) ⊳ F2) (F1 ⊳ F2)) :=
  not_derivable_of_countermodel M3_isModel and_split_not_valid

theorem and_split_conclusion_not_derivable : ¬ Derivable (F1 ⊳ F2) :=
  not_derivable_of_countermodel M3_isModel and_split_conclusion_not_valid

/-- `F1 ∧ F2 ⊢ F2`：由合取消去得到。 -/
theorem nonderivable_entails_and_right : Entails (Form.and F1 F2) F2 :=
  fun _ _ _ h => h.2

/-- 拆合取支持者的**前提**是可推导的。 -/
theorem and_split_premise_derivable : Derivable ((Form.and F1 F2) ⊳ F2) :=
  Derivable.s1 nonderivable_entails_and_right

/-- 因此「由 `(a ∧ b) ⊳ φ` 得 `a ⊳ φ`」**不是**可容许规则。 -/
theorem and_split_not_admissible :
    ¬ (∀ a b φ : Form, Derivable ((Form.and a b) ⊳ φ) → Derivable (a ⊳ φ)) :=
  fun h => and_split_conclusion_not_derivable (h F1 F2 F2 and_split_premise_derivable)

/-! ### 4. 拆全称支持者（不支持） -/

theorem all_split_not_valid :
    ¬ M3.Valid (Form.imp ((Form.all 0 F5) ⊳ F2) (F5 ⊳ F2)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho1)
  simp only [M3_truth_imp, M3_truth_supp, M3_truth_all_F5, M3_truth_F5_rho1,
    B3_truth_F2, cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inl (PSet.bot_le s1))
  · exact not_suppP_s2_s1 h

theorem all_split_not_derivable :
    ¬ Derivable (Form.imp ((Form.all 0 F5) ⊳ F2) (F5 ⊳ F2)) :=
  not_derivable_of_countermodel M3_isModel all_split_not_valid

/-! ### 5. 拆嵌套关系（两种情形） -/

theorem nested_supp_not_valid :
    ¬ M3.Valid (Form.imp (F1 ⊳ (F2 ⊲ F1)) (F1 ⊳ F2)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_supp, M3_truth_F1, B3_truth_refut, B3_truth_F2,
    B3_truth_F1, cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inr (Or.inr (cst_eq_top_of (Canon.refutP s1 s0) (Or.inl s1_inf_s0))))
  · exact not_suppP_s0_s1 h

theorem nested_supp_not_derivable :
    ¬ Derivable (Form.imp (F1 ⊳ (F2 ⊲ F1)) (F1 ⊳ F2)) :=
  not_derivable_of_countermodel M3_isModel nested_supp_not_valid

theorem nested_refut_not_valid :
    ¬ M3.Valid (Form.imp (Form.bot ⊳ (F2 ⊲ F2)) (F2 ⊲ F2)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_supp, M3_truth_refut, M3_truth_bot, B3_truth_refut,
    B3_truth_F2, cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inl (PSet.bot_le _))
  · exact not_refutP_s1_s1 h

theorem nested_refut_not_derivable :
    ¬ Derivable (Form.imp (Form.bot ⊳ (F2 ⊲ F2)) (F2 ⊲ F2)) :=
  not_derivable_of_countermodel M3_isModel nested_refut_not_valid

/-! ### 6. 拆反驳支持关系

定稿中两种结论分别为 `a ⊲ d` 与 `a ⊲ d`（此处 `a = c = d = F1`），实例重合，
故只陈述一次。 -/

theorem refute_supp_not_valid :
    ¬ M3.Valid (Form.imp (F1 ⊲ (F1 ⊳ F1)) (F1 ⊲ F1)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_refut, B3_truth_supp, M3_truth_F1, B3_truth_F1,
    cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inr (Or.inr (Or.inr
      (cst_eq_top_of (Canon.suppP s0 s0) (Or.inl (PSet.le_refl s0))))))
  · exact not_refutP_s0_s0 h

theorem refute_supp_not_derivable :
    ¬ Derivable (Form.imp (F1 ⊲ (F1 ⊳ F1)) (F1 ⊲ F1)) :=
  not_derivable_of_countermodel M3_isModel refute_supp_not_valid

/-! ### 7. S7：不同主体分别支持不同命题（不支持合取） -/

theorem s7_not_valid :
    ¬ M3.Valid (Form.imp (Form.and (F0 ⊳ F3) (F2 ⊳ F2))
        ((Form.and F0 F2) ⊳ (Form.and F3 F2))) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_and, M3_truth_supp, M3_truth_F0, M3_truth_F2,
    B3_truth_F3, B3_truth_F2, B3_truth_and_F3_F2, PSet.top_inf_eq,
    cst_compl, cst_inf, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h ⟨Or.inr (Or.inl rfl), Or.inl (PSet.le_refl s1)⟩
  · exact not_suppP_s1_bot h

theorem s7_not_derivable :
    ¬ Derivable (Form.imp (Form.and (F0 ⊳ F3) (F2 ⊳ F2))
        ((Form.and F0 F2) ⊳ (Form.and F3 F2))) :=
  not_derivable_of_countermodel M3_isModel s7_not_valid

/-! ### 8. 反驳合取拆项（不支持） -/

theorem refut_and_not_valid :
    ¬ M3.Valid (Form.imp (F1 ⊲ (Form.and F1 F2)) (F1 ⊲ F1)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_refut, M3_truth_F1, B3_truth_and_F1_F2, B3_truth_F1,
    cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inr (Or.inr (Or.inl rfl)))
  · exact not_refutP_s0_s0 h

theorem refut_and_not_derivable :
    ¬ Derivable (Form.imp (F1 ⊲ (Form.and F1 F2)) (F1 ⊲ F1)) :=
  not_derivable_of_countermodel M3_isModel refut_and_not_valid

/-! ### 9. 反驳全称拆实例（不支持） -/

theorem refut_all_not_valid :
    ¬ M3.Valid (Form.imp (F3 ⊲ (Form.all 0 F5)) (F3 ⊲ F5)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho1)
  simp only [M3_truth_imp, M3_truth_refut, M3_truth_F3, B3_truth_all_F5,
    B3_truth_F5_rho1, cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inr (Or.inr (Or.inl rfl)))
  · exact not_refutP_s2_s2 h

theorem refut_all_not_derivable :
    ¬ Derivable (Form.imp (F3 ⊲ (Form.all 0 F5)) (F3 ⊲ F5)) :=
  not_derivable_of_countermodel M3_isModel refut_all_not_valid

/-! ### 10. 非命题性反驳逆后承

该规则带有语义副作用条件 `φ ⊢ ψ`。由于 `Entails` 对所有基结构量化，
`Entails F1 F0` 并不成立；这里用 `ψ := Form.top`（`Entails F1 Form.top` 成立）
给出规则形状的真实例，并另行给出定稿所要求的 `ψ := F0` 的具体结论。 -/

/-- `F1 ⊢ ⊤`。 -/
theorem entails_F1_top : Entails F1 Form.top := fun _ _ _ _ => trivial

/-- `M3 ⊨ F1 ⊲ ⊤`。 -/
theorem valid_refut_F1_top : M3.Valid (F1 ⊲ Form.top) := by
  intro ρ
  rw [M3_truth_refut, M3_truth_F1, B3_truth_top]
  exact cst_eq_top_of (Canon.refutP s0 ⊤) (Or.inr (Or.inr (Or.inr rfl)))

/-- `M3 ⊨ F1 ⊲ F0`。 -/
theorem valid_refut_F1_F0 : M3.Valid (F1 ⊲ F0) := by
  intro ρ
  rw [M3_truth_refut, M3_truth_F1, B3_truth_F0]
  exact cst_eq_top_of (Canon.refutP s0 ⊤) (Or.inr (Or.inr (Or.inr rfl)))

/-- 规则形状的真实例 `(F1 ⊲ ⊤) → (F1 ⊲ F1)` 不有效。 -/
theorem not_valid_refute_converse_instance :
    ¬ M3.Valid (Form.imp (F1 ⊲ Form.top) (F1 ⊲ F1)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_refut, M3_truth_F1, B3_truth_top, B3_truth_F1,
    cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inr (Or.inr (Or.inr rfl)))
  · exact not_refutP_s0_s0 h

/-- **非命题性反驳逆后承不（语义上）成立**。 -/
theorem not_valid_refute_converse :
    ¬ (∀ (t φ ψ : Form), Entails φ ψ → M3.Valid (Form.imp (t ⊲ ψ) (t ⊲ φ))) :=
  fun h => not_valid_refute_converse_instance (h F1 F1 Form.top entails_F1_top)

/-- 规则形状的真实例 `(F1 ⊲ ⊤) → (F1 ⊲ F1)` 不可推导。 -/
theorem not_derivable_refute_converse_top :
    ¬ Derivable (Form.imp (F1 ⊲ Form.top) (F1 ⊲ F1)) :=
  not_derivable_of_countermodel M3_isModel not_valid_refute_converse_instance

/-- 定稿所要求的实例 `(F1 ⊲ F0) → (F1 ⊲ F1)` 不有效。 -/
theorem not_valid_refute_converse_F0 :
    ¬ M3.Valid (Form.imp (F1 ⊲ F0) (F1 ⊲ F1)) := by
  apply M3_not_valid_of_truth_ne_top (ρ := rho0)
  simp only [M3_truth_imp, M3_truth_refut, M3_truth_F1, B3_truth_F0, B3_truth_F1,
    cst_compl, cst_sup]
  apply cst_ne_top_of_not
  intro h
  rcases h with h | h
  · exact h (Or.inr (Or.inr (Or.inr rfl)))
  · exact not_refutP_s0_s0 h

/-- `(F1 ⊲ F0) → (F1 ⊲ F1)` 不可推导。 -/
theorem not_derivable_refute_converse :
    ¬ Derivable (Form.imp (F1 ⊲ F0) (F1 ⊲ F1)) :=
  not_derivable_of_countermodel M3_isModel not_valid_refute_converse_F0

/-! ## 五、系统不蕴涵真（定稿第八节） -/

/-- `⊥` 支持一切：`⊥ ⊳ φ` 对任意 `φ` 可推导。 -/
theorem bot_supports_all (φ : Form) : Derivable (Form.bot ⊳ φ) :=
  Derivable.s1 (fun _ _ w h => absurd h (PSet.not_bot w))

/-- **系统不蕴涵真**：存在可推导的 `t ⊳ φ`，其 `φ` 在某模型中不有效。 -/
theorem not_truth_preserving :
    ¬ (∀ (t φ : Form), Derivable (t ⊳ φ) → ∀ (M : Frame), IsModel M → M.Valid φ) := by
  intro h
  have hv : M3.Valid Form.bot :=
    h Form.bot Form.bot (bot_supports_all Form.bot) M3 M3_isModel
  have h0 : (⊥ : PSet (Fin 3)) = ⊤ := hv rho0
  exact bot_ne_top h0

/-- **`F1 ⊳ F2` 既不有效也不可推导**：在 `M3` 中它失败，但同一模型中其他支持成立。 -/
theorem M3_support_does_not_imply_truth : ¬ M3.Valid (F1 ⊳ F2) ∧ ¬ Derivable (F1 ⊳ F2) :=
  ⟨and_split_conclusion_not_valid, and_split_conclusion_not_derivable⟩

end

end EvidenceLogic
