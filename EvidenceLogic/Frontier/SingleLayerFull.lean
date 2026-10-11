import EvidenceLogic.Frontier.SingleLayer

namespace EvidenceLogic

noncomputable section

open PSet

/-! ## 收尾单层情形：四个区域的逐点引理 + 拼接

`SingleLayer.lean` 已给：四个 λ-探针、`probe_pair`／`pair_at`（任意 `S`）、
`singleLayer_first`／`singleLayer_third`（`⟦p⟧ = ⟦p'⟧`、`⟦v⟧ = ⟦v'⟧`，无条件）、`P1_at`（`a ⊓ v` 区域）。

本文件补齐其余三个区域 P₂／P₃／P₄，拼出 `q = q'` 与 `singleLayer_full`。

**实现要点**（这是子代理反复卡住的地方）：**先用 `_at` 展开引理把 `.holds w` 变成显式的 `∧`／`→`，
再在显式形状上做投影与施用**——直接对 `(notAndS A B).holds w` 做 `.1` 投影在缺少期望类型时
elaborator 不肯归约，而经由 `↔` 引理则永远有明确类型。
-/

/-- 双重否定消去（本工程无 `by_contra` 策略）。 -/
theorem dne {P : Prop} (h : (P → False) → False) : P := Classical.byContradiction h

/-- `P → ¬¬P`。 -/
theorem not_not_intro {P : Prop} (h : P) : (P → False) → False := fun hn => hn h

/-! ### 四个探针的 `holds` 展开（全部 `Iff.rfl`） -/

@[simp] theorem andS_at {W : Type} (A B : PSet W) (w : W) :
    (andS A B).holds w ↔ A.holds w ∧ B.holds w := Iff.rfl

@[simp] theorem notAndS_at {W : Type} (A B : PSet W) (w : W) :
    (notAndS A B).holds w ↔ (A.holds w → False) ∧ B.holds w := Iff.rfl

@[simp] theorem notNotS_at {W : Type} (A B : PSet W) (w : W) :
    (notNotS A B).holds w ↔ (A.holds w → False) ∧ (B.holds w → False) := Iff.rfl

@[simp] theorem andNotS_at {W : Type} (A B : PSet W) (w : W) :
    (andNotS A B).holds w ↔ A.holds w ∧ (B.holds w → False) := Iff.rfl

/-! ### P₂：区域 `¬a w` 且 `v w`（探针 `notAndS`） -/

/-- **P₂**：`¬a w` 且 `v w` ⇒ `q w ↔ q' w`。 -/
theorem P2_at {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) (w : W)
    (hvW : (Canon.base W atomRel).truth v ρ w)
    (haW : ((Canon.base W atomRel).truth p ρ w) → False) :
    ((Canon.base W atomRel).truth q ρ w ↔ (Canon.base W atomRel).truth q' ρ w) := by
  have hw := pair_at atomRel notAndS hp hq hp' hq' hv hv' h ρ w
  have haW' : ((Canon.base W atomRel).truth p' ρ w) → False :=
    fun hp'W => haW ((eq_at (singleLayer_first atomRel hp hp' h ρ) w).mpr hp'W)
  have hv'W : (Canon.base W atomRel).truth v' ρ w :=
    (eq_at (singleLayer_third atomRel hv hv' h ρ) w).mp hvW
  have hL : (notAndS (notAndS ((Canon.base W atomRel).truth p ρ) ((Canon.base W atomRel).truth q ρ))
        ((Canon.base W atomRel).truth v ρ)).holds w ↔
      (((Canon.base W atomRel).truth q ρ w) → False) := by
    constructor
    · intro hc hq
      have hc' := (notAndS_at _ _ w).mp hc
      exact hc'.1 ((notAndS_at _ _ w).mpr ⟨haW, hq⟩)
    · intro hnq
      exact (notAndS_at _ _ w).mpr
        ⟨fun hc => hnq ((notAndS_at _ _ w).mp hc).2, hvW⟩
  have hR : (notAndS (notAndS ((Canon.base W atomRel).truth p' ρ) ((Canon.base W atomRel).truth q' ρ))
        ((Canon.base W atomRel).truth v' ρ)).holds w ↔
      (((Canon.base W atomRel).truth q' ρ w) → False) := by
    constructor
    · intro hc hq'
      have hc' := (notAndS_at _ _ w).mp hc
      exact hc'.1 ((notAndS_at _ _ w).mpr ⟨haW', hq'⟩)
    · intro hnq
      exact (notAndS_at _ _ w).mpr
        ⟨fun hc => hnq ((notAndS_at _ _ w).mp hc).2, hv'W⟩
  exact not_iff_not (hL.symm.trans (hw.trans hR))

/-! ### P₃：区域 `¬a w` 且 `¬v w`（探针 `notNotS`） -/

/-- **P₃**：`¬a w` 且 `¬v w` ⇒ `q w ↔ q' w`。 -/
theorem P3_at {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) (w : W)
    (haW : ((Canon.base W atomRel).truth p ρ w) → False)
    (hvW : ((Canon.base W atomRel).truth v ρ w) → False) :
    ((Canon.base W atomRel).truth q ρ w ↔ (Canon.base W atomRel).truth q' ρ w) := by
  have hw := pair_at atomRel notNotS hp hq hp' hq' hv hv' h ρ w
  have haW' : ((Canon.base W atomRel).truth p' ρ w) → False :=
    fun hp'W => haW ((eq_at (singleLayer_first atomRel hp hp' h ρ) w).mpr hp'W)
  have hv'W : ((Canon.base W atomRel).truth v' ρ w) → False :=
    fun hv'W' => hvW ((eq_at (singleLayer_third atomRel hv hv' h ρ) w).mpr hv'W')
  have hL : (notNotS (notNotS ((Canon.base W atomRel).truth p ρ) ((Canon.base W atomRel).truth q ρ))
        ((Canon.base W atomRel).truth v ρ)).holds w ↔
      ((((Canon.base W atomRel).truth q ρ w) → False) → False) := by
    constructor
    · intro hc hnq
      have hc' := (notNotS_at _ _ w).mp hc
      exact hc'.1 ((notNotS_at _ _ w).mpr ⟨haW, hnq⟩)
    · intro hnn
      exact (notNotS_at _ _ w).mpr
        ⟨fun hc => hnn ((notNotS_at _ _ w).mp hc).2, hvW⟩
  have hR : (notNotS (notNotS ((Canon.base W atomRel).truth p' ρ) ((Canon.base W atomRel).truth q' ρ))
        ((Canon.base W atomRel).truth v' ρ)).holds w ↔
      ((((Canon.base W atomRel).truth q' ρ w) → False) → False) := by
    constructor
    · intro hc hnq
      have hc' := (notNotS_at _ _ w).mp hc
      exact hc'.1 ((notNotS_at _ _ w).mpr ⟨haW', hnq⟩)
    · intro hnn
      exact (notNotS_at _ _ w).mpr
        ⟨fun hc => hnn ((notNotS_at _ _ w).mp hc).2, hv'W⟩
  have hnn : ((((Canon.base W atomRel).truth q ρ w) → False) → False) ↔
      ((((Canon.base W atomRel).truth q' ρ w) → False) → False) := hL.symm.trans (hw.trans hR)
  exact ⟨fun hq => dne (hnn.mp (not_not_intro hq)),
         fun hq' => dne (hnn.mpr (not_not_intro hq'))⟩

/-! ### P₄：区域 `a w` 且 `¬v w`（探针 `andNotS`） -/

/-- **P₄**：`a w` 且 `¬v w` ⇒ `q w ↔ q' w`。 -/
theorem P4_at {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) (w : W)
    (haW : (Canon.base W atomRel).truth p ρ w)
    (hvW : ((Canon.base W atomRel).truth v ρ w) → False) :
    ((Canon.base W atomRel).truth q ρ w ↔ (Canon.base W atomRel).truth q' ρ w) := by
  have hw := pair_at atomRel andNotS hp hq hp' hq' hv hv' h ρ w
  have haW' : (Canon.base W atomRel).truth p' ρ w :=
    (eq_at (singleLayer_first atomRel hp hp' h ρ) w).mp haW
  have hv'W : ((Canon.base W atomRel).truth v' ρ w) → False :=
    fun hv'W' => hvW ((eq_at (singleLayer_third atomRel hv hv' h ρ) w).mpr hv'W')
  have hL : (andNotS (andNotS ((Canon.base W atomRel).truth p ρ) ((Canon.base W atomRel).truth q ρ))
        ((Canon.base W atomRel).truth v ρ)).holds w ↔
      (((Canon.base W atomRel).truth q ρ w) → False) := by
    constructor
    · intro hc hq
      have hc' := (andNotS_at _ _ w).mp hc
      exact (andNotS_at _ _ w).mp hc'.1 |>.2 hq
    · intro hnq
      exact (andNotS_at _ _ w).mpr
        ⟨(andNotS_at _ _ w).mpr ⟨haW, hnq⟩, hvW⟩
  have hR : (andNotS (andNotS ((Canon.base W atomRel).truth p' ρ) ((Canon.base W atomRel).truth q' ρ))
        ((Canon.base W atomRel).truth v' ρ)).holds w ↔
      (((Canon.base W atomRel).truth q' ρ w) → False) := by
    constructor
    · intro hc hq'
      have hc' := (andNotS_at _ _ w).mp hc
      exact (andNotS_at _ _ w).mp hc'.1 |>.2 hq'
    · intro hnq
      exact (andNotS_at _ _ w).mpr
        ⟨(andNotS_at _ _ w).mpr ⟨haW', hnq⟩, hv'W⟩
  exact not_iff_not (hL.symm.trans (hw.trans hR))

/-! ### 拼接：`q = q'` 与 `singleLayer_full` -/

/-- **逐世界**：四个区域合并（`SingleLayer.P1_at` ＋ 本文件 P₂／P₃／P₄）。 -/
theorem q_at {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) (w : W) :
    (Canon.base W atomRel).truth q ρ w ↔ (Canon.base W atomRel).truth q' ρ w := by
  by_cases ha : (Canon.base W atomRel).truth p ρ w
  · by_cases hvW : (Canon.base W atomRel).truth v ρ w
    · exact P1_at atomRel hp hq hp' hq' hv hv' h ρ w hvW ha
    · exact P4_at atomRel hp hq hp' hq' hv hv' h ρ w ha hvW
  · by_cases hvW : (Canon.base W atomRel).truth v ρ w
    · exact P2_at atomRel hp hq hp' hq' hv hv' h ρ w hvW ha
    · exact P3_at atomRel hp hq hp' hq' hv hv' h ρ w ha hvW

/-- **单层第二分量**：`⟦q⟧ = ⟦q'⟧`。 -/
theorem singleLayer_second {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth q ρ = (Canon.base W atomRel).truth q' ρ :=
  PSet.ext (q_at atomRel hp hq hp' hq' hv hv' h ρ)

/-- **单层情形（完整）**：三条分量等式同时成立。 -/
theorem singleLayer_full {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth p ρ = (Canon.base W atomRel).truth p' ρ ∧
    (Canon.base W atomRel).truth q ρ = (Canon.base W atomRel).truth q' ρ ∧
    (Canon.base W atomRel).truth v ρ = (Canon.base W atomRel).truth v' ρ :=
  ⟨singleLayer_first atomRel hp hp' h ρ,
   singleLayer_second atomRel hp hq hp' hq' hv hv' h ρ,
   singleLayer_third atomRel hv hv' h ρ⟩

end

end EvidenceLogic
