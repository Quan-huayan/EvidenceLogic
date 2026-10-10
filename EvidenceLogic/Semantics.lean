/-
# 背书逻辑 v1.0：语义（Semantics）

本文件给出对象语言的**两层语义**，并定义「模型」概念。

## 一、命题层：`PSet`

语义载体是「命题」构成的完备布尔代数。为使形式化自足（不依赖 Mathlib），
取具体实现 `PSet W := { holds : W → Prop }`（`W` 为「状态／世界」类型），
配备 `≤`、`⊓`、`⊔`、`ᶜ`、`⊤`、`⊥` 及任意交 `iInter`、任意并 `iUnion`。

## 二、经典基语义：`Base`（用于定义 `⊢`）

基结构把 `⊳`、`⊲` 当作二元关系符号，其解释是**真值层面**的函数
`suppI, refutI : PSet W → PSet W → PSet W`。让关系只依赖两个真值，
正是经典逻辑把 `t ⊳ φ` 视为原子公式的做法，它保证代入引理成立：

`B.truth (subst σ φ) ρ = B.truth φ (fun y => B.truth (σ y) ρ)`。

于是经典后承定义为

`Entails p q := ∀ (B : Base) ρ, B.truth p ρ ≤ B.truth q ρ`。

它包含一切经典一阶有效式，因此 S1／S2／E 的副作用条件都在此得到解释。

## 三、背书语义：`Frame` 与模型类 `IsModel`

`Frame` 把 `⊳`、`⊲` 解释为**语法索引的**关系
`supp, refut : PSet W → Form → (Nat → PSet W) → Prop`（第二个自变量是公式本身）。
这是本质性的：若关系只依赖真值，P1 会退化为平凡条件（见 README 讨论）。

`IsModel M` 的每个字段恰好是定稿一条规则在语义上的闭包条件：

| 字段 | 对应 |
|---|---|
| `classical` | 经典后承在模型内成立 |
| `agree` | 真值只依赖自由变元（标准一阶语义相合性） |
| `e` | **E** 经典等价替换 |
| `s1`／`s2` | **S1**／**S2** |
| `f1`／`f2`／`f3`／`f4` | **F1**／**F2**／**F3**／**F4** |
| `r1` | **R1** |
| `p1`／`p2` | **P1**／**P2** |

## 四、自由变元即全称概括

定稿 F1／F2／P2 形如「`∀x (t R p(x)) ⇒ t R ∀x p(x)`」。Hilbert 型系统中，
带自由变元的推导读作「对任意赋值成立」，故形式化时这几条规则以**开公式的推导**
为前提（见 `EvidenceLogic.Derivable`）：F1 由 `t R φ` 得 `t R ∀x φ`（`x ∉ FV(t)`）；
F2 由 `p R φ` 得 `(∀x p) R φ`（`x ∉ FV(φ)`）；P2 由 `a R c` 与 `(∀x c) S f` 得
`(∀x a) R ((∀x c) S f)`（`x ∉ FV(f)`）。这与 `IsModel.f1/f2/p2` 的形状一致。

## 五、实现注记

`Form` 是嵌套归纳类型（`atom` 的参数是 `List Form`）。若递归直接进入列表元素，
Lean 会退化为良基递归，等式便只是命题性的。为此 `truth` 与 `truths`
（以及 `truth_subst` 与 `truth_subst_list`、`truth_upd_notFree` 与
`truths_upd_notFree`）写成 **mutual 块**，使其成为结构递归，等式保持定义性。
-/
import EvidenceLogic.Prelude
import EvidenceLogic.Syntax

namespace EvidenceLogic

/-! ## 一、命题层 -/

/-- 命题（`W` 的状态集合）。 -/
structure PSet (W : Type) where
  /-- 该命题在状态 `w` 是否成立 -/
  holds : W → Prop

namespace PSet

variable {W : Type}

instance : CoeFun (PSet W) (fun _ => W → Prop) := ⟨PSet.holds⟩
instance : LE (PSet W) := ⟨fun X Y => ∀ w, X w → Y w⟩
instance : Top (PSet W) := ⟨⟨fun _ => True⟩⟩
instance : Bot (PSet W) := ⟨⟨fun _ => False⟩⟩
instance : Inf (PSet W) := ⟨fun X Y => ⟨fun w => X w ∧ Y w⟩⟩
instance : Sup (PSet W) := ⟨fun X Y => ⟨fun w => X w ∨ Y w⟩⟩
instance : Compl (PSet W) := ⟨fun X => ⟨fun w => ¬ X w⟩⟩

@[ext] theorem ext {X Y : PSet W} (h : ∀ w, X w ↔ Y w) : X = Y := by
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  have hxy : x = y := funext (fun w => propext (h w))
  rw [hxy]

/-- 任意交。 -/
def iInter {ι : Type} (f : ι → PSet W) : PSet W := ⟨fun w => ∀ i, f i w⟩

/-- 任意并。 -/
def iUnion {ι : Type} (f : ι → PSet W) : PSet W := ⟨fun w => ∃ i, f i w⟩

theorem le_refl (X : PSet W) : X ≤ X := fun _ h => h

theorem le_trans {X Y Z : PSet W} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) : X ≤ Z :=
  fun w hx => h₂ w (h₁ w hx)

theorem inf_le_left (X Y : PSet W) : X ⊓ Y ≤ X := fun _ h => h.1

theorem inf_le_right (X Y : PSet W) : X ⊓ Y ≤ Y := fun _ h => h.2

theorem le_inf {X Y Z : PSet W} (h₁ : Z ≤ X) (h₂ : Z ≤ Y) : Z ≤ X ⊓ Y :=
  fun _ hz => ⟨h₁ _ hz, h₂ _ hz⟩

theorem le_top (X : PSet W) : X ≤ ⊤ := fun _ _ => trivial

/-- `⊥` 不成立。 -/
theorem not_bot (w : W) : ¬ ((⊥ : PSet W) w) := fun h => h

theorem bot_le (X : PSet W) : ⊥ ≤ X := fun w h => absurd h (not_bot w)

/-- 若 `X ≤ Y`，则 `X ⊓ Z ≤ Y ⊓ Z`。 -/
theorem inf_le_inf_left {X Y Z : PSet W} (h : X ≤ Y) : X ⊓ Z ≤ Y ⊓ Z :=
  fun _ hw => ⟨h _ hw.1, hw.2⟩

/-- 若 `X ≤ Y`，则 `Z ⊓ X ≤ Z ⊓ Y`。 -/
theorem inf_le_inf_right {X Y Z : PSet W} (h : X ≤ Y) : Z ⊓ X ≤ Z ⊓ Y :=
  fun _ hw => ⟨hw.1, h _ hw.2⟩

@[simp] theorem inf_comm (X Y : PSet W) : X ⊓ Y = Y ⊓ X := by
  ext w; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

@[simp] theorem compl_inf_self (X : PSet W) : Xᶜ ⊓ X = ⊥ := by
  ext w; exact ⟨fun h => h.1 h.2, fun h => absurd h (not_bot w)⟩

@[simp] theorem compl_top : (⊤ : PSet W)ᶜ = ⊥ := by
  ext w; exact ⟨fun h => h trivial, fun h => absurd h (not_bot w)⟩

@[simp] theorem compl_bot : (⊥ : PSet W)ᶜ = ⊤ := by
  ext w; exact ⟨fun _ => trivial, fun _ => not_bot w⟩

/-- `⊤ ≤ X` 蕴含 `X = ⊤`。 -/
theorem eq_top_of_le {X : PSet W} (h : ⊤ ≤ X) : X = ⊤ := by
  ext w; exact ⟨fun _ => trivial, fun _ => h w trivial⟩

/-- `X ≤ ⊥` 蕴含 `X = ⊥`。 -/
theorem eq_bot_of_le {X : PSet W} (h : X ≤ ⊥) : X = ⊥ := by
  ext w; exact ⟨fun hw => h w hw, fun hw => absurd hw (not_bot w)⟩

/-- 若 `Y = ⊤`，则任何 `X ≤ Y`。 -/
theorem le_of_eq_top {X Y : PSet W} (h : Y = ⊤) : X ≤ Y := by
  rw [h]; exact le_top X

@[simp] theorem inf_top_eq (X : PSet W) : X ⊓ ⊤ = X := by
  ext w; exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

@[simp] theorem top_inf_eq (X : PSet W) : ⊤ ⊓ X = X := by
  ext w; exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

@[simp] theorem inf_bot_eq (X : PSet W) : X ⊓ ⊥ = ⊥ := by
  ext w; exact ⟨fun h => h.2, fun h => absurd h (not_bot w)⟩

@[simp] theorem bot_inf_eq (X : PSet W) : ⊥ ⊓ X = ⊥ := by
  ext w; exact ⟨fun h => h.1, fun h => absurd h (not_bot w)⟩

@[simp] theorem compl_compl (X : PSet W) : Xᶜᶜ = X := by
  ext w
  constructor
  · intro h
    by_cases hx : X w
    · exact hx
    · exact absurd hx h
  · intro hx h
    exact h hx

/-- `Xᶜ = ⊤` 蕴含 `X = ⊥`。 -/
theorem eq_bot_of_compl_eq_top {X : PSet W} (h : Xᶜ = ⊤) : X = ⊥ := by
  rw [← compl_compl X, h, compl_top]

/-- 若 `X ⊓ Y = ⊥`，则 `X ≤ Yᶜ`。 -/
theorem le_compl_of_inf_eq_bot {X Y : PSet W} (h : X ⊓ Y = ⊥) : X ≤ Yᶜ :=
  fun w hx hy => absurd (h ▸ (show (X ⊓ Y) w from ⟨hx, hy⟩)) (not_bot w)

/-- 若 `X ⊓ Y = ⊥`，则 `X ⊓ (Y ⊓ Z) = ⊥`。 -/
theorem inf_inf_eq_bot_of_left {X Y Z : PSet W} (h : X ⊓ Y = ⊥) :
    X ⊓ (Y ⊓ Z) = ⊥ := by
  apply eq_bot_of_le
  intro w hw
  exact absurd (h ▸ (show (X ⊓ Y) w from ⟨hw.1, hw.2.1⟩)) (not_bot w)

theorem iInter_le {ι : Type} (f : ι → PSet W) (i : ι) : iInter f ≤ f i := fun _ h => h i

theorem le_iInter {ι : Type} {Y : PSet W} (f : ι → PSet W) (h : ∀ i, Y ≤ f i) :
    Y ≤ iInter f := fun w hy i => h i w hy

/-- 若每项都是 `⊤`（索引类型非空），则任意交是 `⊤`。 -/
theorem iInter_eq_top {ι : Type} [Nonempty ι] {f : ι → PSet W} (h : ∀ i, f i = ⊤) :
    iInter f = ⊤ := by
  apply eq_top_of_le
  intro w _ i
  rw [h i]
  trivial

/-- 任意交的相合性。 -/
theorem iInter_congr {ι : Type} {f g : ι → PSet W} (h : ∀ i, f i = g i) :
    iInter f = iInter g := by
  apply ext
  intro w
  exact ⟨fun h1 i => by rw [← h i]; exact h1 i, fun h1 i => by rw [h i]; exact h1 i⟩

/-- 任意并的相合性。 -/
theorem iUnion_congr {ι : Type} {f g : ι → PSet W} (h : ∀ i, f i = g i) :
    iUnion f = iUnion g := by
  apply ext
  intro w
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← h i]; exact hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [h i]; exact hi⟩

/-- 恒常命题 `⟨fun _ => P⟩` 等于 `⊤` 当且仅当 `P` 成立（需给出一个状态）。 -/
theorem const_eq_top_iff {P : Prop} (w : W) : (⟨fun _ => P⟩ : PSet W) = ⊤ ↔ P := by
  constructor
  · intro h
    have hw : (⟨fun _ => P⟩ : PSet W) w := by rw [h]; trivial
    exact hw
  · intro hP
    apply eq_top_of_le
    intro w' _
    exact hP

end PSet

/-! ## 二、经典基语义 -/

/-- 基结构：`⊳`、`⊲` 被解释为真值层面的二元关系。 -/
structure Base where
  /-- 状态类型 -/
  W : Type
  /-- 原子谓词解释 -/
  atomRel : Nat → List (PSet W) → PSet W
  /-- `⊳` 的真值层面解释 -/
  suppI : PSet W → PSet W → PSet W
  /-- `⊲` 的真值层面解释 -/
  refutI : PSet W → PSet W → PSet W

namespace Base

/-- 关系符号的真值层面解释。 -/
def relI (B : Base) : Kind → PSet B.W → PSet B.W → PSet B.W
  | .supp => B.suppI
  | .refut => B.refutI

/- 基语义真值函数（及其列表版，写成 mutual 以保持结构递归）。 -/
mutual
  def truth (B : Base) : Form → (Nat → PSet B.W) → PSet B.W
    | .var y, ρ => ρ y
    | .atom i ts, ρ => B.atomRel i (truths B ρ ts)
    | .bot, _ => ⊥
    | .top, _ => ⊤
    | .not φ, ρ => (truth B φ ρ)ᶜ
    | .and φ ψ, ρ => truth B φ ρ ⊓ truth B ψ ρ
    | .or φ ψ, ρ => truth B φ ρ ⊔ truth B ψ ρ
    | .imp φ ψ, ρ => (truth B φ ρ)ᶜ ⊔ truth B ψ ρ
    | .all x φ, ρ => PSet.iInter (fun X : PSet B.W => truth B φ (upd ρ x X))
    | .ex x φ, ρ => PSet.iUnion (fun X : PSet B.W => truth B φ (upd ρ x X))
    | .supp t φ, ρ => B.suppI (truth B t ρ) (truth B φ ρ)
    | .refut t φ, ρ => B.refutI (truth B t ρ) (truth B φ ρ)

  /-- 列表版基语义真值。 -/
  def truths (B : Base) (ρ : Nat → PSet B.W) : List Form → List (PSet B.W)
    | [] => []
    | t :: ts => truth B t ρ :: truths B ρ ts
end

/- **不变性（基语义）**：`x` 若不在 `φ` 中自由出现，则 `x` 的赋值不影响真值。 -/
mutual
  theorem truth_upd_notFree (B : Base) (x : Nat) : ∀ (φ : Form), ¬ FreeIn x φ →
      ∀ (ρ : Nat → PSet B.W) (X : PSet B.W), B.truth φ (upd ρ x X) = B.truth φ ρ
    | .var y, h, ρ, X => by
        have hy : y ≠ x := fun hxy => h hxy.symm
        show upd ρ x X y = ρ y
        exact upd_noteq ρ hy X
    | .atom i ts, h, ρ, X => by
        show B.atomRel i (B.truths (upd ρ x X) ts) = B.atomRel i (B.truths ρ ts)
        rw [truths_upd_notFree B x ts (fun s hs ρ' X' =>
          truth_upd_notFree B x s (fun hc => h (freeInList_of_mem hs hc)) ρ' X') ρ X]
    | .bot, _, _, _ => rfl
    | .top, _, _, _ => rfl
    | .not φ, h, ρ, X => by
        show (B.truth φ (upd ρ x X))ᶜ = (B.truth φ ρ)ᶜ
        rw [truth_upd_notFree B x φ h ρ X]
    | .and φ ψ, h, ρ, X => by
        show B.truth φ (upd ρ x X) ⊓ B.truth ψ (upd ρ x X)
          = B.truth φ ρ ⊓ B.truth ψ ρ
        rw [truth_upd_notFree B x φ (fun hc => h (Or.inl hc)) ρ X,
          truth_upd_notFree B x ψ (fun hc => h (Or.inr hc)) ρ X]
    | .or φ ψ, h, ρ, X => by
        show B.truth φ (upd ρ x X) ⊔ B.truth ψ (upd ρ x X)
          = B.truth φ ρ ⊔ B.truth ψ ρ
        rw [truth_upd_notFree B x φ (fun hc => h (Or.inl hc)) ρ X,
          truth_upd_notFree B x ψ (fun hc => h (Or.inr hc)) ρ X]
    | .imp φ ψ, h, ρ, X => by
        show (B.truth φ (upd ρ x X))ᶜ ⊔ B.truth ψ (upd ρ x X)
          = (B.truth φ ρ)ᶜ ⊔ B.truth ψ ρ
        rw [truth_upd_notFree B x φ (fun hc => h (Or.inl hc)) ρ X,
          truth_upd_notFree B x ψ (fun hc => h (Or.inr hc)) ρ X]
    | .all z φ, h, ρ, X => by
        by_cases hxz : x = z
        · subst hxz
          apply PSet.iInter_congr
          intro Y
          show B.truth φ (upd (upd ρ x X) x Y) = B.truth φ (upd ρ x Y)
          rw [upd_upd_same]
        · have hφ : ¬ FreeIn x φ := fun hc => h ⟨hxz, hc⟩
          apply PSet.iInter_congr
          intro Y
          show B.truth φ (upd (upd ρ x X) z Y) = B.truth φ (upd ρ z Y)
          rw [upd_upd_comm ρ hxz X Y, truth_upd_notFree B x φ hφ (upd ρ z Y) X]
    | .ex z φ, h, ρ, X => by
        by_cases hxz : x = z
        · subst hxz
          apply PSet.iUnion_congr
          intro Y
          show B.truth φ (upd (upd ρ x X) x Y) = B.truth φ (upd ρ x Y)
          rw [upd_upd_same]
        · have hφ : ¬ FreeIn x φ := fun hc => h ⟨hxz, hc⟩
          apply PSet.iUnion_congr
          intro Y
          show B.truth φ (upd (upd ρ x X) z Y) = B.truth φ (upd ρ z Y)
          rw [upd_upd_comm ρ hxz X Y, truth_upd_notFree B x φ hφ (upd ρ z Y) X]
    | .supp a φ, h, ρ, X => by
        show B.suppI (B.truth a (upd ρ x X)) (B.truth φ (upd ρ x X))
          = B.suppI (B.truth a ρ) (B.truth φ ρ)
        rw [truth_upd_notFree B x a (fun hc => h (Or.inl hc)) ρ X,
          truth_upd_notFree B x φ (fun hc => h (Or.inr hc)) ρ X]
    | .refut a φ, h, ρ, X => by
        show B.refutI (B.truth a (upd ρ x X)) (B.truth φ (upd ρ x X))
          = B.refutI (B.truth a ρ) (B.truth φ ρ)
        rw [truth_upd_notFree B x a (fun hc => h (Or.inl hc)) ρ X,
          truth_upd_notFree B x φ (fun hc => h (Or.inr hc)) ρ X]

  /-- 列表版不变性。 -/
  theorem truths_upd_notFree (B : Base) (x : Nat) : ∀ (ts : List Form),
      (∀ s ∈ ts, ∀ (ρ : Nat → PSet B.W) (X : PSet B.W),
        B.truth s (upd ρ x X) = B.truth s ρ) →
      ∀ (ρ : Nat → PSet B.W) (X : PSet B.W),
        B.truths (upd ρ x X) ts = B.truths ρ ts
    | [], _, _, _ => rfl
    | s :: ss, h, ρ, X => by
        show B.truth s (upd ρ x X) :: B.truths (upd ρ x X) ss
          = B.truth s ρ :: B.truths ρ ss
        rw [h s (by simp) ρ X,
          truths_upd_notFree B x ss (fun t ht => h t (by simp [ht])) ρ X]
end

/- **代入引理（基语义）**：若每个 `σ y` 对 `y` 可代入，则代入与「先求 `σ` 后求真值」一致。 -/
mutual
  theorem truth_subst (B : Base) (σ : Nat → Form) : ∀ (φ : Form),
      (∀ y, FreeFor (σ y) y φ) → ∀ ρ : Nat → PSet B.W,
        B.truth (subst σ φ) ρ = B.truth φ (fun y => B.truth (σ y) ρ)
    | .var y, _, ρ => rfl
    | .atom i ts, hσ, ρ => by
        show B.atomRel i (B.truths ρ (substList σ ts))
          = B.atomRel i (B.truths (fun y => B.truth (σ y) ρ) ts)
        rw [truth_subst_list B σ ρ ts (fun s hs y => freeForList_elim (hσ y) hs)]
    | .bot, _, _ => rfl
    | .top, _, _ => rfl
    | .not φ, hσ, ρ => by
        show (B.truth (subst σ φ) ρ)ᶜ = (B.truth φ (fun y => B.truth (σ y) ρ))ᶜ
        rw [truth_subst B σ φ hσ ρ]
    | .and φ ψ, hσ, ρ => by
        show B.truth (subst σ φ) ρ ⊓ B.truth (subst σ ψ) ρ
          = B.truth φ (fun y => B.truth (σ y) ρ) ⊓ B.truth ψ (fun y => B.truth (σ y) ρ)
        rw [truth_subst B σ φ (fun y => (hσ y).1) ρ,
          truth_subst B σ ψ (fun y => (hσ y).2) ρ]
    | .or φ ψ, hσ, ρ => by
        show B.truth (subst σ φ) ρ ⊔ B.truth (subst σ ψ) ρ
          = B.truth φ (fun y => B.truth (σ y) ρ) ⊔ B.truth ψ (fun y => B.truth (σ y) ρ)
        rw [truth_subst B σ φ (fun y => (hσ y).1) ρ,
          truth_subst B σ ψ (fun y => (hσ y).2) ρ]
    | .imp φ ψ, hσ, ρ => by
        show (B.truth (subst σ φ) ρ)ᶜ ⊔ B.truth (subst σ ψ) ρ
          = (B.truth φ (fun y => B.truth (σ y) ρ))ᶜ ⊔ B.truth ψ (fun y => B.truth (σ y) ρ)
        rw [truth_subst B σ φ (fun y => (hσ y).1) ρ,
          truth_subst B σ ψ (fun y => (hσ y).2) ρ]
    | .all z φ, hσ, ρ => by
        have hσ' : ∀ y, FreeFor ((fun y => if y = z then Form.var z else σ y) y) y φ := by
          intro y
          show FreeFor (if y = z then Form.var z else σ y) y φ
          by_cases hy : y = z
          · subst hy; simpa using freeFor_var y φ
          · rw [if_neg hy]
            rcases hσ y with h1 | ⟨_, h2⟩
            · exact absurd h1.symm hy
            · exact h2
        have hfun : ∀ X : PSet B.W,
            (fun y => B.truth ((fun y => if y = z then Form.var z else σ y) y)
                (upd ρ z X))
              = upd (fun y => B.truth (σ y) ρ) z X := by
          intro X
          funext y
          show B.truth (if y = z then Form.var z else σ y) (upd ρ z X)
            = upd (fun y => B.truth (σ y) ρ) z X y
          by_cases hy : y = z
          · subst hy; simp [truth, upd]
          · have hnot : ¬ FreeIn z (σ y) := by
              rcases hσ y with h1 | ⟨h1, _⟩
              · exact absurd h1.symm hy
              · exact h1
            rw [if_neg hy, truth_upd_notFree B z (σ y) hnot ρ X]
            simp only [upd, if_neg hy]
        apply PSet.iInter_congr
        intro X
        rw [truth_subst B (fun y => if y = z then Form.var z else σ y) φ hσ' (upd ρ z X),
          hfun X]
    | .ex z φ, hσ, ρ => by
        have hσ' : ∀ y, FreeFor ((fun y => if y = z then Form.var z else σ y) y) y φ := by
          intro y
          show FreeFor (if y = z then Form.var z else σ y) y φ
          by_cases hy : y = z
          · subst hy; simpa using freeFor_var y φ
          · rw [if_neg hy]
            rcases hσ y with h1 | ⟨_, h2⟩
            · exact absurd h1.symm hy
            · exact h2
        have hfun : ∀ X : PSet B.W,
            (fun y => B.truth ((fun y => if y = z then Form.var z else σ y) y)
                (upd ρ z X))
              = upd (fun y => B.truth (σ y) ρ) z X := by
          intro X
          funext y
          show B.truth (if y = z then Form.var z else σ y) (upd ρ z X)
            = upd (fun y => B.truth (σ y) ρ) z X y
          by_cases hy : y = z
          · subst hy; simp [truth, upd]
          · have hnot : ¬ FreeIn z (σ y) := by
              rcases hσ y with h1 | ⟨h1, _⟩
              · exact absurd h1.symm hy
              · exact h1
            rw [if_neg hy, truth_upd_notFree B z (σ y) hnot ρ X]
            simp only [upd, if_neg hy]
        apply PSet.iUnion_congr
        intro X
        rw [truth_subst B (fun y => if y = z then Form.var z else σ y) φ hσ' (upd ρ z X),
          hfun X]
    | .supp a φ, hσ, ρ => by
        show B.suppI (B.truth (subst σ a) ρ) (B.truth (subst σ φ) ρ)
          = B.suppI (B.truth a (fun y => B.truth (σ y) ρ))
              (B.truth φ (fun y => B.truth (σ y) ρ))
        rw [truth_subst B σ a (fun y => (hσ y).1) ρ,
          truth_subst B σ φ (fun y => (hσ y).2) ρ]
    | .refut a φ, hσ, ρ => by
        show B.refutI (B.truth (subst σ a) ρ) (B.truth (subst σ φ) ρ)
          = B.refutI (B.truth a (fun y => B.truth (σ y) ρ))
              (B.truth φ (fun y => B.truth (σ y) ρ))
        rw [truth_subst B σ a (fun y => (hσ y).1) ρ,
          truth_subst B σ φ (fun y => (hσ y).2) ρ]

  /-- 列表版代入引理。 -/
  theorem truth_subst_list (B : Base) (σ : Nat → Form) (ρ : Nat → PSet B.W) :
      ∀ (ts : List Form), (∀ s ∈ ts, ∀ y, FreeFor (σ y) y s) →
        B.truths ρ (substList σ ts) = B.truths (fun y => B.truth (σ y) ρ) ts
    | [], _ => rfl
    | s :: ss, hs => by
        show B.truth (subst σ s) ρ :: B.truths ρ (substList σ ss)
          = B.truth s (fun y => B.truth (σ y) ρ)
              :: B.truths (fun y => B.truth (σ y) ρ) ss
        rw [truth_subst B σ s (hs s (by simp)) ρ,
          truth_subst_list B σ ρ ss (fun t ht => hs t (by simp [ht]))]
end

/-- **单变元实例化的代入引理**（基语义）。 -/
theorem truth_inst (B : Base) {t : Form} {x : Nat} {φ : Form} (h : FreeFor t x φ)
    (ρ : Nat → PSet B.W) :
    B.truth (inst x t φ) ρ = B.truth φ (upd ρ x (B.truth t ρ)) := by
  have hσ : ∀ y, FreeFor ((fun y => if y = x then t else Form.var y) y) y φ := by
    intro y
    show FreeFor (if y = x then t else Form.var y) y φ
    by_cases hy : y = x
    · subst hy; simpa using h
    · rw [if_neg hy]; exact freeFor_var y φ
  rw [inst, truth_subst B (fun y => if y = x then t else Form.var y) φ hσ ρ]
  congr 1
  funext y
  show B.truth (if y = x then t else Form.var y) ρ = upd ρ x (B.truth t ρ) y
  by_cases hy : y = x
  · subst hy; simp [upd]
  · simp [truth, upd, hy]

end Base

/-! ## 三、后承与等价 -/

/-- 经典后承 `p ⊢ q`：在所有基结构中有效。 -/
def Entails (p q : Form) : Prop :=
  ∀ (B : Base) (ρ : Nat → PSet B.W), B.truth p ρ ≤ B.truth q ρ

/-- 经典等价 `φ ⊣⊢ ψ`（元规则 E 的前提）。 -/
def CEquiv (p q : Form) : Prop := Entails p q ∧ Entails q p

/-- 经典等价记法（与定稿一致）：`φ ⊣⊢ ψ`。 -/
infix:20 " ⊣⊢ " => CEquiv

/-! ## 四、背书语义与模型类 -/

/-- 背书框架：`⊳`／`⊲` 被解释为**语法索引的**二元关系。 -/
structure Frame where
  /-- 状态类型 -/
  W : Type
  /-- 原子谓词解释 -/
  atomRel : Nat → List (PSet W) → PSet W
  /-- `⊳` 的解释 -/
  supp : PSet W → Form → (Nat → PSet W) → Prop
  /-- `⊲` 的解释 -/
  refut : PSet W → Form → (Nat → PSet W) → Prop

namespace Frame

/-- 关系符号的解释（`abbrev` 以便 `rw` 能看见其展开）。 -/
abbrev rel (M : Frame) : Kind → PSet M.W → Form → (Nat → PSet M.W) → Prop
  | .supp => M.supp
  | .refut => M.refut

/- 背书语义真值函数（关系子公式的真值是「恒常命题」）。 -/
mutual
  def truth (M : Frame) : Form → (Nat → PSet M.W) → PSet M.W
    | .var y, ρ => ρ y
    | .atom i ts, ρ => M.atomRel i (truths M ρ ts)
    | .bot, _ => ⊥
    | .top, _ => ⊤
    | .not φ, ρ => (truth M φ ρ)ᶜ
    | .and φ ψ, ρ => truth M φ ρ ⊓ truth M ψ ρ
    | .or φ ψ, ρ => truth M φ ρ ⊔ truth M ψ ρ
    | .imp φ ψ, ρ => (truth M φ ρ)ᶜ ⊔ truth M ψ ρ
    | .all x φ, ρ => PSet.iInter (fun X : PSet M.W => truth M φ (upd ρ x X))
    | .ex x φ, ρ => PSet.iUnion (fun X : PSet M.W => truth M φ (upd ρ x X))
    | .supp t φ, ρ => ⟨fun _ => M.supp (truth M t ρ) φ ρ⟩
    | .refut t φ, ρ => ⟨fun _ => M.refut (truth M t ρ) φ ρ⟩

  /-- 列表版背书语义真值。 -/
  def truths (M : Frame) (ρ : Nat → PSet M.W) : List Form → List (PSet M.W)
    | [] => []
    | t :: ts => truth M t ρ :: truths M ρ ts
end

/-- `truths` 对列表拼接是同态。 -/
theorem truths_append (M : Frame) (ρ : Nat → PSet M.W) : ∀ l₁ l₂ : List Form,
    M.truths ρ (l₁ ++ l₂) = M.truths ρ l₁ ++ M.truths ρ l₂
  | [], _ => rfl
  | _ :: ts, l₂ => by
      show M.truth _ ρ :: M.truths ρ (ts ++ l₂)
        = M.truth _ ρ :: (M.truths ρ ts ++ M.truths ρ l₂)
      rw [truths_append M ρ ts l₂]

/-- 若 `a` 与 `b` 在所有赋值下真值相同，则它们在原子谓词的参数列表中可以互换。 -/
theorem truths_cons_eq (M : Frame) {a b : Form}
    (h : ∀ ρ : Nat → PSet M.W, M.truth a ρ = M.truth b ρ)
    (ρ : Nat → PSet M.W) (pre post : List Form) :
    M.truths ρ (pre ++ a :: post) = M.truths ρ (pre ++ b :: post) := by
  rw [truths_append, truths_append]
  show M.truths ρ pre ++ M.truth a ρ :: M.truths ρ post
    = M.truths ρ pre ++ M.truth b ρ :: M.truths ρ post
  rw [h ρ]

/-- 公式在框架中有效：对任意赋值真值为 `⊤`。 -/
def Valid (M : Frame) (φ : Form) : Prop := ∀ ρ, M.truth φ ρ = ⊤

end Frame

/-- 模型类：与定稿各条规则对应的闭包条件。 -/
structure IsModel (M : Frame) : Prop where
  /-- 状态空间非空（否则所有命题坍缩为一个）。 -/
  nonempty : Nonempty M.W
  /-- 经典后承在模型内成立。 -/
  classical : ∀ p q : Form, Entails p q → ∀ ρ, M.truth p ρ ≤ M.truth q ρ
  /-- 真值只依赖自由变元。 -/
  agree : ∀ (φ : Form) (ρ ρ' : Nat → PSet M.W),
    (∀ x, FreeIn x φ → ρ x = ρ' x) → M.truth φ ρ = M.truth φ ρ'
  /-- **E**：经典等价替换不改变支持／反驳关系的成立。 -/
  e : ∀ (φ ψ : Form), (∀ ρ, M.truth φ ρ = M.truth ψ ρ) →
    ∀ (k : Kind) (X : PSet M.W) (ρ : Nat → PSet M.W), (M.rel k X φ ρ ↔ M.rel k X ψ ρ)
  /-- **S1**：`p ⊢ q ⇒ p ⊳ q`。 -/
  s1 : ∀ (p q : Form) (ρ : Nat → PSet M.W),
    M.truth p ρ ≤ M.truth q ρ → M.supp (M.truth p ρ) q ρ
  /-- **S2**：`(t ⊳ p) ∧ (p ⊢ q) ⇒ t ⊳ q`。 -/
  s2 : ∀ (X : PSet M.W) (p q : Form) (ρ : Nat → PSet M.W),
    M.supp X p ρ → M.truth p ρ ≤ M.truth q ρ → M.supp X q ρ
  /-- **F1**：`x ∉ FV(t)`，由 `t R φ` 得 `t R ∀x φ`。 -/
  f1 : ∀ (k : Kind) (t φ : Form) (x : Nat) (ρ : Nat → PSet M.W), ¬ FreeIn x t →
    (∀ X : PSet M.W, M.rel k (M.truth t (upd ρ x X)) φ (upd ρ x X)) →
    M.rel k (M.truth t ρ) (.all x φ) ρ
  /-- **F2**：`x ∉ FV(φ)`，由 `p R φ` 得 `(∀x p) R φ`。 -/
  f2 : ∀ (k : Kind) (p φ : Form) (x : Nat) (ρ : Nat → PSet M.W), ¬ FreeIn x φ →
    (∀ X : PSet M.W, M.rel k (M.truth p (upd ρ x X)) φ (upd ρ x X)) →
    M.rel k (M.truth (.all x p) ρ) φ ρ
  /-- **F3**：`(a R φ) ∧ (b R φ) ⇒ (a ∧ b) R φ`。 -/
  f3 : ∀ (k : Kind) (X Z : PSet M.W) (φ : Form) (ρ : Nat → PSet M.W),
    M.rel k X φ ρ → M.rel k Z φ ρ → M.rel k (X ⊓ Z) φ ρ
  /-- **F4**：`(t R φ) ∧ (t R ψ) ⇒ t R (φ ∧ ψ)`。 -/
  f4 : ∀ (k : Kind) (X : PSet M.W) (φ ψ : Form) (ρ : Nat → PSet M.W),
    M.rel k X φ ρ → M.rel k X ψ ρ → M.rel k X (.and φ ψ) ρ
  /-- **R1**：`t ⊳ ¬φ ⇒ t ⊲ φ`。 -/
  r1 : ∀ (X : PSet M.W) (φ : Form) (ρ : Nat → PSet M.W),
    M.supp X (.not φ) ρ → M.refut X φ ρ
  /-- **P1**：`(a R c) ∧ (b R d) ∧ ((c ∧ d) S f) ⇒ (a ∧ b) R ((c ∧ d) S f)`。 -/
  p1 : ∀ (kR kS : Kind) (a b c d f : Form) (ρ : Nat → PSet M.W),
    M.rel kR (M.truth a ρ) c ρ → M.rel kR (M.truth b ρ) d ρ →
    M.rel kS (M.truth c ρ ⊓ M.truth d ρ) f ρ →
    M.rel kR (M.truth a ρ ⊓ M.truth b ρ) (Kind.form kS (.and c d) f) ρ
  /-- **P2**：`x ∉ FV(f)`，由 `a R c` 与 `(∀x c) S f` 得 `(∀x a) R ((∀x c) S f)`。 -/
  p2 : ∀ (kR kS : Kind) (a c f : Form) (x : Nat) (ρ : Nat → PSet M.W), ¬ FreeIn x f →
    (∀ X : PSet M.W, M.rel kR (M.truth a (upd ρ x X)) c (upd ρ x X)) →
    M.rel kS (M.truth (.all x c) ρ) f ρ →
    M.rel kR (M.truth (.all x a) ρ) (Kind.form kS (.all x c) f) ρ

namespace Frame

/-- 由 `agree`：`x ∉ FV(φ)` 时 `x` 的赋值不影响 `φ` 的真值。 -/
theorem truth_upd_notFree (M : Frame) (hM : IsModel M) {x : Nat} {φ : Form}
    (h : ¬ FreeIn x φ) (ρ : Nat → PSet M.W) (X : PSet M.W) :
    M.truth φ (upd ρ x X) = M.truth φ ρ :=
  hM.agree φ _ _ (fun y hy => by
    have hyx : y ≠ x := fun hyx => h (hyx ▸ hy)
    exact upd_noteq ρ hyx X)

end Frame

end EvidenceLogic
