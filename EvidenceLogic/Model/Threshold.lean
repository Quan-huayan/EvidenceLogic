/-
# 第三模型族：**阈值模型族**（Threshold）

本文件**不修改任何已有文件**，只在既有 `import` 之上补一批新结论。
它把 `Model/Canonical.lean` 的支持判据里的析取项 `X = ⊤` **一般化为任意固定阈值**：

    thSuppP U X Y  :=  X ≤ Y  ∨  X = U  ∨  Y = ⊤
    thRefutP U X Y :=  X ⊓ Y = ⊥  ∨  X = U  ∨  Y = ⊤

`U = ⊤` 时它几乎就是典范判据（`thRefutP ⊤` 与 `Canon.refutP` 只差一个**冗余**的
`Y = ⊥`，见 [`Analysis/Structure.lean`] 的 `refutP_iff_disjoint_or_top`）。
本文件证明**对每个 `U` 它都是模型**，于是得到一族**参数化的支持-蕴含不变量**：

    Derivable (p ⊳ q)  ⟹  ∀ρ, thSuppP U ⟦p⟧ρ ⟦q⟧ρ          （`th_supp_le`，对每个 `U`）

## 这一族补上了什么

1. **第三个模型族**（前两个是 `Canon.frame` 与 `strictFrame`）。与 `Canon.suppP_not_transitive`
   的对照是本文件的主要信息：**破坏支持传递的装置不是 `⊤` 这个具体集合**，
   而是"支持者恰好等于某个固定阈值"这一**形状**——
   `thSuppP_not_transitive` 对**任意** `U`、任意满足 `X ≤ U`、`X ≠ U`、`X ≰ Z`、`Z ≠ ⊤`
   的 `X`、`Z` 给出反例（`U = ⊤` 时即 `Canon.suppP_not_transitive`）。
2. **一族新的必要条件**：对每个 `U` 都有一条不变量。特别地，取 `U = ⊤` 时它回到
   典范框架的可靠性结论；取别的 `U` 则给出**新**的、与典范框架**不同**的约束
   （`thBase W atomRel U` 的真值随 `U` 变化，故这些约束**互相独立**）。
3. **一个对照点**：与 `strictFrame`（完全没有析取项、支持传递成立）相比，本族说明
   "多加一个析取项"并不必然破坏传递性——真正起作用的是析取项的**形状**
   （`X = U` 是"恰好等于阈值"，而 `Y = ⊤` 是"被支持者是重言式"）。

## 强度声明（不要夸大）

* 本文件**不**证明 `TransferLemma`，**不**证明 `TruthPropagation`，
  **不**对 N3 账本（`System/NonAdmissible.lean` 第十一节）的残余两条作任何断言；
* 本族**只给出必要条件**（不变量），**不**给出任何反例：与 `strictFrame` 一样，
  它**验证**了许多被定稿拒绝的规则（例如支持传递在本族中也成立——注意：本族的
  `thSuppP` 不传递**只说明这个关系不是预序**，而要成为 N3 反例还需要
  **可推导的**两个前提，那正是尚未解决的部分）；
* 与 `Frontier/Threshold` 无关：本文件不涉及 `⊣⊢`／转移引理。

## 技术注记

* 逐字段验证 `IsModel` 十三个字段（**不**用 `Derivable.soundness` 反推）；
  这样做的副产品是：本族的模型性**不依赖**任何前沿假设；
* 支持侧四条 PSet 引理（`thSuppP_inf`／`_and`／`_iInter`／`_of_iInter`）与
  `Canonical.lean` 的同名引理逐支同构，只把 `X = ⊤` 换成 `X = U`；
* 反驳侧三条（`thRefutP_inf`／`_and`／`_iInter`／`_of_iInter`）同理；
* 未使用的绑定一律写 `_`，不使用 `sorry`／`axiom`／`admit`。
-/
import EvidenceLogic.Model.Strict

namespace EvidenceLogic

open PSet

open scoped Classical

/-! ## 1. 阈值判据与真值层面的小引理 -/

/-- **阈值支持判据**：`X ≤ Y`，或支持者恰为阈值 `U`，或被支持命题为 `⊤`。 -/
abbrev thSuppP {W : Type} (U X Y : PSet W) : Prop := X ≤ Y ∨ X = U ∨ Y = ⊤

/-- **阈值反驳判据**：`X ⊓ Y = ⊥`，或支持者恰为阈值 `U`，或被反驳命题为 `⊤`。

（`Y = ⊥` 那一项被 `X ⊓ ⊥ = ⊥` 吸收，故不必写出——与 `Canon.refutP` 的本质形式一致。） -/
abbrev thRefutP {W : Type} (U X Y : PSet W) : Prop := X ⊓ Y = ⊥ ∨ X = U ∨ Y = ⊤

/-- `X ⊓ X = X`。 -/
theorem th_inf_self {W : Type} (X : PSet W) : X ⊓ X = X := by
  apply PSet.ext
  intro w
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- 若每项都等于 `U`，则任意交等于 `U`。 -/
theorem th_iInter_of_const {W ι : Type} [Nonempty ι] {f : ι → PSet W} {U : PSet W}
    (h : ∀ i, f i = U) : PSet.iInter f = U := by
  apply PSet.ext
  intro w
  constructor
  · intro hw
    obtain ⟨i⟩ := ‹Nonempty ι›
    rw [← h i]
    exact hw i
  · intro hw i
    rw [h i]
    exact hw

/-- 阈值支持判据在第二个自变量上单调。 -/
theorem thSuppP_mono {W : Type} {U X Y Z : PSet W} (h : thSuppP U X Y) (hYZ : Y ≤ Z) :
    thSuppP U X Z := by
  rcases h with h | h | h
  · exact Or.inl (PSet.le_trans h hYZ)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (PSet.eq_top_of_le (h ▸ hYZ)))

/-- **F3（支持）**：合取主体。 -/
theorem thSuppP_inf {W : Type} {U X Z Y : PSet W} (h₁ : thSuppP U X Y)
    (h₂ : thSuppP U Z Y) : thSuppP U (X ⊓ Z) Y := by
  rcases h₁ with h₁ | h₁ | h₁
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (fun _ hw => h₁ _ hw.1)
    · exact Or.inl (PSet.le_trans (PSet.inf_le_left _ _) h₁)
    · exact Or.inr (Or.inr h₂)
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (PSet.le_trans (PSet.inf_le_right _ _) h₂)
    · exact Or.inr (Or.inl (by rw [h₁, h₂, th_inf_self]))
    · exact Or.inr (Or.inr h₂)
  · exact Or.inr (Or.inr h₁)

/-- **F4（支持）**：同一主体合取引入。 -/
theorem thSuppP_and {W : Type} {U X Y Z : PSet W} (h₁ : thSuppP U X Y)
    (h₂ : thSuppP U X Z) : thSuppP U X (Y ⊓ Z) := by
  rcases h₁ with h₁ | h₁ | h₁
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (PSet.le_inf h₁ h₂)
    · exact Or.inr (Or.inl h₂)
    · exact Or.inl (by rw [h₂, PSet.inf_top_eq]; exact h₁)
  · exact Or.inr (Or.inl h₁)
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (by rw [h₁, PSet.top_inf_eq]; exact h₂)
    · exact Or.inr (Or.inl h₂)
    · exact Or.inr (Or.inr (by rw [h₁, h₂, PSet.top_inf_eq]))

/-- **F1（支持）**：若每个 `T X` 都被 `Xt` 支持，则 `⋂ X, T X` 也被 `Xt` 支持。 -/
theorem thSuppP_iInter {W : Type} {U Xt : PSet W} {T : PSet W → PSet W}
    (h : ∀ X, thSuppP U Xt (T X)) : thSuppP U Xt (PSet.iInter T) := by
  by_cases hU : Xt = U
  · exact Or.inr (Or.inl hU)
  · refine Or.inl (PSet.le_iInter T (fun X => ?_))
    rcases h X with hX | hX | hX
    · exact hX
    · exact absurd hX hU
    · exact PSet.le_of_eq_top hX

/-- **F2（支持）**：若每个 `T X` 都支持 `Y`，则 `⋂ X, T X` 支持 `Y`。 -/
theorem thSuppP_of_iInter {W : Type} {U Y : PSet W} {T : PSet W → PSet W}
    (h : ∀ X, thSuppP U (T X) Y) : thSuppP U (PSet.iInter T) Y := by
  by_cases hY : Y = ⊤
  · exact Or.inr (Or.inr hY)
  · by_cases hle : ∃ X, T X ≤ Y
    · obtain ⟨X₀, hX₀⟩ := hle
      exact Or.inl (PSet.le_trans (PSet.iInter_le T X₀) hX₀)
    · have hall : ∀ X, T X = U := by
        intro X
        rcases h X with hX | hX | hX
        · exact absurd hX (fun hc => hle ⟨X, hc⟩)
        · exact hX
        · exact absurd hX hY
      haveI : Nonempty (PSet W) := ⟨⊥⟩
      exact Or.inr (Or.inl (th_iInter_of_const hall))

/-- **F3（反驳）**：合取主体。 -/
theorem thRefutP_inf {W : Type} {U X Z Y : PSet W} (h₁ : thRefutP U X Y)
    (h₂ : thRefutP U Z Y) : thRefutP U (X ⊓ Z) Y := by
  rcases h₁ with h₁ | h₁ | h₁
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (PSet.eq_bot_of_le (PSet.le_trans
        (PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) (PSet.inf_le_left _ _))
          (PSet.inf_le_right _ _)) (le_of_eq_pset h₁)))
    · exact Or.inl (PSet.eq_bot_of_le (PSet.le_trans
        (PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) (PSet.inf_le_left _ _))
          (PSet.inf_le_right _ _)) (le_of_eq_pset h₁)))
    · exact Or.inr (Or.inr h₂)
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (PSet.eq_bot_of_le (PSet.le_trans
        (PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) (PSet.inf_le_right _ _))
          (PSet.inf_le_right _ _)) (le_of_eq_pset h₂)))
    · exact Or.inr (Or.inl (by rw [h₁, h₂, th_inf_self]))
    · exact Or.inr (Or.inr h₂)
  · exact Or.inr (Or.inr h₁)

/-- **F4（反驳）**：同一主体合取引入。 -/
theorem thRefutP_and {W : Type} {U X Y Z : PSet W} (h₁ : thRefutP U X Y)
    (h₂ : thRefutP U X Z) : thRefutP U X (Y ⊓ Z) := by
  rcases h₁ with h₁ | h₁ | h₁
  · have hle : X ⊓ (Y ⊓ Z) ≤ X ⊓ Y :=
      PSet.le_inf (PSet.inf_le_left _ _)
        (PSet.le_trans (PSet.inf_le_right _ _) (PSet.inf_le_left _ _))
    exact Or.inl (PSet.eq_bot_of_le (PSet.le_trans hle (le_of_eq_pset h₁)))
  · exact Or.inr (Or.inl h₁)
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (by rw [h₁, PSet.top_inf_eq]; exact h₂)
    · exact Or.inr (Or.inl h₂)
    · exact Or.inr (Or.inr (by rw [h₁, h₂, PSet.top_inf_eq]))

/-- **F1（反驳）**：若每个 `T X` 都被 `Xt` 反驳，则 `⋂ X, T X` 也被 `Xt` 反驳。 -/
theorem thRefutP_iInter {W : Type} {U Xt : PSet W} {T : PSet W → PSet W}
    (h : ∀ X, thRefutP U Xt (T X)) : thRefutP U Xt (PSet.iInter T) := by
  by_cases hU : Xt = U
  · exact Or.inr (Or.inl hU)
  · by_cases hle : ∃ X, Xt ⊓ T X = ⊥
    · obtain ⟨X₀, hX₀⟩ := hle
      have hle' : Xt ⊓ PSet.iInter T ≤ Xt ⊓ T X₀ :=
        PSet.le_inf (PSet.inf_le_left _ _)
          (PSet.le_trans (PSet.inf_le_right _ _) (PSet.iInter_le T X₀))
      exact Or.inl (PSet.eq_bot_of_le (PSet.le_trans hle' (le_of_eq_pset hX₀)))
    · have hall : ∀ X, T X = ⊤ := by
        intro X
        rcases h X with hX | hX | hX
        · exact absurd hX (fun hc => hle ⟨X, hc⟩)
        · exact absurd hX hU
        · exact hX
      haveI : Nonempty (PSet W) := ⟨⊥⟩
      exact Or.inr (Or.inr (PSet.iInter_eq_top hall))

/-- **F2（反驳）**：若每个 `T X` 都反驳 `Y`，则 `⋂ X, T X` 反驳 `Y`。 -/
theorem thRefutP_of_iInter {W : Type} {U Y : PSet W} {T : PSet W → PSet W}
    (h : ∀ X, thRefutP U (T X) Y) : thRefutP U (PSet.iInter T) Y := by
  by_cases hY : Y = ⊤
  · exact Or.inr (Or.inr hY)
  · by_cases hle : ∃ X, T X ⊓ Y = ⊥
    · obtain ⟨X₀, hX₀⟩ := hle
      have hle' : PSet.iInter T ⊓ Y ≤ T X₀ ⊓ Y :=
        PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) (PSet.iInter_le T X₀))
          (PSet.inf_le_right _ _)
      exact Or.inl (PSet.eq_bot_of_le (PSet.le_trans hle' (le_of_eq_pset hX₀)))
    · have hall : ∀ X, T X = U := by
        intro X
        rcases h X with hX | hX | hX
        · exact absurd hX (fun hc => hle ⟨X, hc⟩)
        · exact hX
        · exact absurd hX hY
      haveI : Nonempty (PSet W) := ⟨⊥⟩
      exact Or.inr (Or.inl (th_iInter_of_const hall))

/-- **R1**：`X ⊳ ¬φ ⇒ X ⊲ φ`。 -/
theorem thRefutP_of_thSuppP_compl {W : Type} {U X Y : PSet W} (h : thSuppP U X Yᶜ) :
    thRefutP U X Y := by
  rcases h with h | h | h
  · have hle : X ⊓ Y ≤ Yᶜ ⊓ Y :=
      PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) h) (PSet.inf_le_right _ _)
    refine Or.inl (PSet.eq_bot_of_le (PSet.le_trans hle ?_))
    rw [PSet.compl_inf_self]
    exact PSet.le_refl _
  · exact Or.inr (Or.inl h)
  · exact Or.inl (by rw [PSet.eq_bot_of_compl_eq_top h, PSet.inf_bot_eq])

/-! ## 2. 阈值基结构与框架 -/

/-- 阈值基结构。 -/
abbrev thBase (W : Type) (atomRel : Nat → List (PSet W) → PSet W) (U : PSet W) : Base :=
  { W := W, atomRel := atomRel
    suppI := fun X Y => (⟨fun _ => thSuppP U X Y⟩ : PSet W)
    refutI := fun X Y => (⟨fun _ => thRefutP U X Y⟩ : PSet W) }

/-- **阈值框架**（与 `Canon.frame` 同形：被支持／被反驳公式的真值取在基结构层）。 -/
abbrev thFrame (W : Type) (atomRel : Nat → List (PSet W) → PSet W) (U : PSet W) : Frame :=
  { W := W, atomRel := atomRel
    supp := fun X φ ρ => thSuppP U X ((thBase W atomRel U).truth φ ρ)
    refut := fun X φ ρ => thRefutP U X ((thBase W atomRel U).truth φ ρ) }

/- 阈值框架与阈值基结构的真值一致（与 `Canon.frame_truth` 逐支同构）。 -/
mutual
  /-- 公式版。 -/
  theorem th_frame_truth (W : Type) (atomRel : Nat → List (PSet W) → PSet W) (U : PSet W) :
      ∀ (φ : Form) (ρ : Nat → PSet W),
        (thFrame W atomRel U).truth φ ρ = (thBase W atomRel U).truth φ ρ
    | .var y, ρ => rfl
    | .atom i ts, ρ => by
        show atomRel i ((thFrame W atomRel U).truths ρ ts)
          = atomRel i ((thBase W atomRel U).truths ρ ts)
        rw [th_frame_truths W atomRel U ρ ts]
    | .bot, _ => rfl
    | .top, _ => rfl
    | .not φ, ρ => by
        show ((thFrame W atomRel U).truth φ ρ)ᶜ = ((thBase W atomRel U).truth φ ρ)ᶜ
        rw [th_frame_truth W atomRel U φ ρ]
    | .and φ ψ, ρ => by
        show (thFrame W atomRel U).truth φ ρ ⊓ (thFrame W atomRel U).truth ψ ρ
          = (thBase W atomRel U).truth φ ρ ⊓ (thBase W atomRel U).truth ψ ρ
        rw [th_frame_truth W atomRel U φ ρ, th_frame_truth W atomRel U ψ ρ]
    | .or φ ψ, ρ => by
        show (thFrame W atomRel U).truth φ ρ ⊔ (thFrame W atomRel U).truth ψ ρ
          = (thBase W atomRel U).truth φ ρ ⊔ (thBase W atomRel U).truth ψ ρ
        rw [th_frame_truth W atomRel U φ ρ, th_frame_truth W atomRel U ψ ρ]
    | .imp φ ψ, ρ => by
        show ((thFrame W atomRel U).truth φ ρ)ᶜ ⊔ (thFrame W atomRel U).truth ψ ρ
          = ((thBase W atomRel U).truth φ ρ)ᶜ ⊔ (thBase W atomRel U).truth ψ ρ
        rw [th_frame_truth W atomRel U φ ρ, th_frame_truth W atomRel U ψ ρ]
    | .all x φ, ρ => by
        apply PSet.iInter_congr
        intro X
        show (thFrame W atomRel U).truth φ (upd ρ x X)
          = (thBase W atomRel U).truth φ (upd ρ x X)
        rw [th_frame_truth W atomRel U φ (upd ρ x X)]
    | .ex x φ, ρ => by
        apply PSet.iUnion_congr
        intro X
        show (thFrame W atomRel U).truth φ (upd ρ x X)
          = (thBase W atomRel U).truth φ (upd ρ x X)
        rw [th_frame_truth W atomRel U φ (upd ρ x X)]
    | .supp t φ, ρ => by
        apply PSet.ext
        intro _
        show thSuppP U ((thFrame W atomRel U).truth t ρ) ((thBase W atomRel U).truth φ ρ)
          ↔ thSuppP U ((thBase W atomRel U).truth t ρ) ((thBase W atomRel U).truth φ ρ)
        rw [th_frame_truth W atomRel U t ρ]
    | .refut t φ, ρ => by
        apply PSet.ext
        intro _
        show thRefutP U ((thFrame W atomRel U).truth t ρ) ((thBase W atomRel U).truth φ ρ)
          ↔ thRefutP U ((thBase W atomRel U).truth t ρ) ((thBase W atomRel U).truth φ ρ)
        rw [th_frame_truth W atomRel U t ρ]

  /-- 列表版。 -/
  theorem th_frame_truths (W : Type) (atomRel : Nat → List (PSet W) → PSet W) (U : PSet W)
      (ρ : Nat → PSet W) : ∀ (ts : List Form),
        (thFrame W atomRel U).truths ρ ts = (thBase W atomRel U).truths ρ ts
    | [] => rfl
    | t :: ts => by
        show (thFrame W atomRel U).truth t ρ :: (thFrame W atomRel U).truths ρ ts
          = (thBase W atomRel U).truth t ρ :: (thBase W atomRel U).truths ρ ts
        rw [th_frame_truth W atomRel U t ρ, th_frame_truths W atomRel U ρ ts]
end

/-! ## 3. 对每个阈值 `U` 都是模型 -/

/-- **存在性定理（第三模型族）**：对任意非空 `W`、任意 `atomRel` 与**任意**阈值
`U : PSet W`，阈值框架 `thFrame W atomRel U` 都是模型。

十三个字段逐一验证（**不**借助 `Derivable.soundness`，故模型性不依赖任何前沿假设）：
`classical`／`agree`／`e`／`s1`／`s2`／`r1` 由 `≤` 与相合性直接给出；
`f1`–`f4`／`p1`／`p2` 用第 1 节的 PSet 引理；
其中 `p1`／`p2` 的要点仍是「被支持公式是关系式时其真值为 `⊤`」。 -/
theorem th_isModel (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    (U : PSet W) : IsModel (thFrame W atomRel U) where
  nonempty := inferInstance
  classical := by
    intro p q hent ρ
    rw [th_frame_truth W atomRel U p ρ, th_frame_truth W atomRel U q ρ]
    exact hent (thBase W atomRel U) ρ
  agree := by
    intro φ ρ ρ' h
    rw [th_frame_truth W atomRel U φ ρ, th_frame_truth W atomRel U φ ρ']
    exact Base.truth_agree (thBase W atomRel U) φ ρ ρ' h
  e := by
    intro φ ψ h k X ρ
    have hφψ : (thBase W atomRel U).truth φ ρ = (thBase W atomRel U).truth ψ ρ := by
      rw [← th_frame_truth W atomRel U φ ρ, ← th_frame_truth W atomRel U ψ ρ]
      exact h ρ
    cases k
    · show thSuppP U X ((thBase W atomRel U).truth φ ρ)
          ↔ thSuppP U X ((thBase W atomRel U).truth ψ ρ)
      rw [hφψ]
    · show thRefutP U X ((thBase W atomRel U).truth φ ρ)
          ↔ thRefutP U X ((thBase W atomRel U).truth ψ ρ)
      rw [hφψ]
  s1 := by
    intro p q ρ h
    rw [th_frame_truth W atomRel U q ρ] at h
    exact Or.inl h
  s2 := by
    intro X p q ρ h₁ h₂
    rw [th_frame_truth W atomRel U p ρ, th_frame_truth W atomRel U q ρ] at h₂
    exact thSuppP_mono h₁ h₂
  f1 := by
    intro k t φ x ρ hx H
    have hxt : ∀ X : PSet W, (thFrame W atomRel U).truth t (upd ρ x X)
        = (thBase W atomRel U).truth t ρ := by
      intro X
      rw [th_frame_truth W atomRel U t (upd ρ x X)]
      exact Base.truth_upd_notFree (thBase W atomRel U) x t hx ρ X
    rw [th_frame_truth W atomRel U t ρ]
    cases k
    · show thSuppP U ((thBase W atomRel U).truth t ρ)
          (PSet.iInter (fun X : PSet W => (thBase W atomRel U).truth φ (upd ρ x X)))
      apply thSuppP_iInter
      intro X
      have hX := H X
      rw [hxt X] at hX
      exact hX
    · show thRefutP U ((thBase W atomRel U).truth t ρ)
          (PSet.iInter (fun X : PSet W => (thBase W atomRel U).truth φ (upd ρ x X)))
      apply thRefutP_iInter
      intro X
      have hX := H X
      rw [hxt X] at hX
      exact hX
  f2 := by
    intro k p φ x ρ hx H
    have hφ : ∀ X : PSet W,
        (thBase W atomRel U).truth φ (upd ρ x X) = (thBase W atomRel U).truth φ ρ :=
      fun X => Base.truth_upd_notFree (thBase W atomRel U) x φ hx ρ X
    rw [th_frame_truth W atomRel U (.all x p) ρ]
    cases k
    · show thSuppP U (PSet.iInter (fun X : PSet W => (thBase W atomRel U).truth p (upd ρ x X)))
          ((thBase W atomRel U).truth φ ρ)
      apply thSuppP_of_iInter
      intro X
      have hX : thSuppP U ((thFrame W atomRel U).truth p (upd ρ x X))
          ((thBase W atomRel U).truth φ (upd ρ x X)) := H X
      rw [th_frame_truth W atomRel U p (upd ρ x X), hφ X] at hX
      exact hX
    · show thRefutP U (PSet.iInter (fun X : PSet W => (thBase W atomRel U).truth p (upd ρ x X)))
          ((thBase W atomRel U).truth φ ρ)
      apply thRefutP_of_iInter
      intro X
      have hX : thRefutP U ((thFrame W atomRel U).truth p (upd ρ x X))
          ((thBase W atomRel U).truth φ (upd ρ x X)) := H X
      rw [th_frame_truth W atomRel U p (upd ρ x X), hφ X] at hX
      exact hX
  f3 := by
    intro k X Z φ ρ h₁ h₂
    cases k
    · show thSuppP U (X ⊓ Z) ((thBase W atomRel U).truth φ ρ)
      exact thSuppP_inf h₁ h₂
    · show thRefutP U (X ⊓ Z) ((thBase W atomRel U).truth φ ρ)
      exact thRefutP_inf h₁ h₂
  f4 := by
    intro k X φ ψ ρ h₁ h₂
    cases k
    · show thSuppP U X ((thBase W atomRel U).truth φ ρ ⊓ (thBase W atomRel U).truth ψ ρ)
      exact thSuppP_and h₁ h₂
    · show thRefutP U X ((thBase W atomRel U).truth φ ρ ⊓ (thBase W atomRel U).truth ψ ρ)
      exact thRefutP_and h₁ h₂
  r1 := by
    intro X φ ρ h
    exact thRefutP_of_thSuppP_compl h
  p1 := by
    intro kR kS a b c d f ρ h₁ h₂ h₃
    have keyS : (thBase W atomRel U).truth (Kind.form kS (.and c d) f) ρ = ⊤ := by
      cases kS
      · have h := h₃
        rw [th_frame_truth W atomRel U c ρ, th_frame_truth W atomRel U d ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show thSuppP U ((thBase W atomRel U).truth (Form.and c d) ρ)
          ((thBase W atomRel U).truth f ρ)
        exact h
      · have h := h₃
        rw [th_frame_truth W atomRel U c ρ, th_frame_truth W atomRel U d ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show thRefutP U ((thBase W atomRel U).truth (Form.and c d) ρ)
          ((thBase W atomRel U).truth f ρ)
        exact h
    cases kR
    · show thSuppP U ((thFrame W atomRel U).truth a ρ ⊓ (thFrame W atomRel U).truth b ρ)
          ((thBase W atomRel U).truth (Kind.form kS (.and c d) f) ρ)
      rw [keyS]
      exact Or.inr (Or.inr rfl)
    · show thRefutP U ((thFrame W atomRel U).truth a ρ ⊓ (thFrame W atomRel U).truth b ρ)
          ((thBase W atomRel U).truth (Kind.form kS (.and c d) f) ρ)
      rw [keyS]
      exact Or.inr (Or.inr rfl)
  p2 := by
    intro kR kS a c f x ρ hx h₁ h₂
    have keyS : (thBase W atomRel U).truth (Kind.form kS (.all x c) f) ρ = ⊤ := by
      cases kS
      · have h := h₂
        rw [th_frame_truth W atomRel U (.all x c) ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show thSuppP U ((thBase W atomRel U).truth (Form.all x c) ρ)
          ((thBase W atomRel U).truth f ρ)
        exact h
      · have h := h₂
        rw [th_frame_truth W atomRel U (.all x c) ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show thRefutP U ((thBase W atomRel U).truth (Form.all x c) ρ)
          ((thBase W atomRel U).truth f ρ)
        exact h
    cases kR
    · show thSuppP U ((thFrame W atomRel U).truth (.all x a) ρ)
          ((thBase W atomRel U).truth (Kind.form kS (.all x c) f) ρ)
      rw [keyS]
      exact Or.inr (Or.inr rfl)
    · show thRefutP U ((thFrame W atomRel U).truth (.all x a) ρ)
          ((thBase W atomRel U).truth (Kind.form kS (.all x c) f) ρ)
      rw [keyS]
      exact Or.inr (Or.inr rfl)

/-! ## 4. 参数化的支持-蕴含不变量

一族不变量，每个阈值 `U` 一条。`U = ⊤` 时它就是典范框架的可靠性结论；
取别的 `U` 则给出**不同**的约束（`thBase W atomRel U` 的真值随 `U` 变化）。 -/

/-- **阈值模型族上的支持-蕴含不变量**：对**任意** `U : PSet W` 与**全量** `Derivable`
（含元规则 `E`、无任何片段限制），可推导的支持式满足阈值判据：

    `⟦p⟧ρ ≤ ⟦q⟧ρ ∨ ⟦p⟧ρ = U ∨ ⟦q⟧ρ = ⊤`

由 `th_isModel` ＋ `Derivable.soundness` ＋ `Derivable.supp_of_valid` 得到。 -/
theorem th_supp_le (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    (U : PSet W) {p q : Form} (h : Derivable (p ⊳ q)) :
    ∀ ρ : Nat → PSet W,
      thSuppP U ((thBase W atomRel U).truth p ρ) ((thBase W atomRel U).truth q ρ) := by
  intro ρ
  have hM : IsModel (thFrame W atomRel U) := th_isModel W atomRel U
  have hv : (thFrame W atomRel U).truth (p ⊳ q) ρ = ⊤ :=
    Derivable.soundness (thFrame W atomRel U) hM h ρ
  have hs : (thFrame W atomRel U).supp ((thFrame W atomRel U).truth p ρ) q ρ :=
    Derivable.supp_of_valid (thFrame W atomRel U) hM hv
  rw [th_frame_truth W atomRel U p ρ] at hs
  exact hs

/-! ## 5. 破坏传递性的装置是「阈值形状」，而不是 `⊤` 这个具体集合 -/

/-- **阈值支持判据对任意 `U` 都不传递**：只要 `X ≤ U`、`X ≠ U`、`X ≰ Z`、`Z ≠ ⊤`，
就有 `thSuppP U X U`、`thSuppP U U Z` 而 `¬ thSuppP U X Z`。

`U = ⊤` 时第一个假设自动成立，这条即
`Analysis/Structure.suppP_not_transitive`——所以**真正起作用的不是 `⊤` 本身**，
而是"支持者恰好等于某个固定阈值"这一形状。 -/
theorem thSuppP_not_transitive {W : Type} {U X Z : PSet W} (hXU : X ≤ U) (hne : X ≠ U)
    (hXZ : ¬ X ≤ Z) (hZ : Z ≠ ⊤) :
    thSuppP U X U ∧ thSuppP U U Z ∧ ¬ thSuppP U X Z :=
  ⟨Or.inl hXU, Or.inr (Or.inl rfl),
    fun h => h.elim hXZ (fun h' => h'.elim hne (fun htop => hZ htop))⟩

/- **具体见证（`Fin 3`，`U = {0,1} ≠ ⊤`）**：三个集合互不相同且非 `⊤`，
给出一个**阈值不是 `⊤`** 的传递性反例。 -/
namespace ThWitness

/-- `{0}`。 -/
abbrev v0 : PSet (Fin 3) := ⟨fun i => i = 0⟩

/-- `{0,1}`（本节的阈值 `U`）。 -/
abbrev v01 : PSet (Fin 3) := ⟨fun i => i = 0 ∨ i = 1⟩

/-- `{1}`。 -/
abbrev v1 : PSet (Fin 3) := ⟨fun i => i = 1⟩

theorem v0_le_v01 : v0 ≤ v01 := fun _ h => Or.inl h

theorem not_v0_le_v1 : ¬ v0 ≤ v1 :=
  fun h => absurd (h 0 rfl) (by decide)

theorem v0_ne_v01 : v0 ≠ v01 := by
  intro h
  have h1 : v01 (1 : Fin 3) := Or.inr rfl
  rw [← h] at h1
  exact absurd h1 (by decide)

theorem v1_ne_top : v1 ≠ (⊤ : PSet (Fin 3)) :=
  fun h => absurd (show (⊤ : PSet (Fin 3)) (2 : Fin 3) from trivial)
    (fun h2 => by rw [← h] at h2; exact absurd h2 (by decide))

/-- **阈值族中的传递性反例**（阈值 `U = {0,1}`，**不是** `⊤`）。 -/
theorem witness : thSuppP v01 v0 v01 ∧ thSuppP v01 v01 v1 ∧ ¬ thSuppP v01 v0 v1 :=
  thSuppP_not_transitive v0_le_v01 v0_ne_v01 not_v0_le_v1 v1_ne_top

end ThWitness

end EvidenceLogic
