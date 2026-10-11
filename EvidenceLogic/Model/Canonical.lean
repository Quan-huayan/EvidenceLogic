/-
# 背书逻辑 v1.0：典范（自由）模型族（Canonical）

本文件给出模型类的**具体模型族**：对任意状态类型 `W` 与任意原子谓词解释
`atomRel : Nat → List (PSet W) → PSet W`，构造一个框架并证明它是模型。

    支持： `X ⊳ φ`  ⟺  `X ≤ ⟦φ⟧`  或  `X = ⊤`  或  `⟦φ⟧ = ⊤`
    反驳： `X ⊲ φ`  ⟺  `X ⊓ ⟦φ⟧ = ⊥` 或 `X = ⊤` 或 `⟦φ⟧ = ⊥` 或 `⟦φ⟧ = ⊤`

这里 `X` 是支持者的真值，即「公式即项」的直接体现。

## 设计理由

定稿第七节要求**不**包含支持传递、反驳传递等规则，因此语义不能退化为朴素的
「`X ≤ Y` 蕴含」读法（否则支持传递将成为有效式）。上式中的附加析取项正是
打破传递性的装置：

* `X = ⊤`：自相矛盾的支持者——它既支持一切也反驳一切，与定稿第八节
  「同一支持者若同时支持 `φ` 和 `¬φ` 会支持一切」的精神一致；
* `⟦φ⟧ = ⊤`（一切支持有效命题）与 `⟦φ⟧ = ⊥` 使 **R1** 成立。

## 主要结论

* `frame_truth`：典范框架的真值与基真值一致；
* `isModel`：**任意** `W` 与 `atomRel` 下 `frame` 都是模型（存在性定理）；
* 因此 `EvidenceLogic.System.NonDerivable` 中的反模型只需选择 `W` 与 `atomRel`。
-/
import EvidenceLogic.System.Derivable

namespace EvidenceLogic
namespace Canon

open PSet

variable {W : Type}

/-! ## 关系判据 -/

/-- 支持的命题层判据：`X ≤ Y`，或支持者为 `⊤`，或命题为 `⊤`。 -/
abbrev suppP (X Y : PSet W) : Prop := X ≤ Y ∨ X = ⊤ ∨ Y = ⊤

/-- 反驳的命题层判据：`X ⊓ Y = ⊥`，或支持者为 `⊤`，或命题为 `⊥`／`⊤`。 -/
abbrev refutP (X Y : PSet W) : Prop := X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊥ ∨ Y = ⊤

/-- 由种类选择判据。 -/
abbrev relP (k : Kind) (X Y : PSet W) : Prop :=
  match k with
  | .supp => suppP X Y
  | .refut => refutP X Y

/-- 真值层面的 `⊳` 解释。 -/
abbrev suppI (X Y : PSet W) : PSet W := ⟨fun _ => suppP X Y⟩

/-- 真值层面的 `⊲` 解释。 -/
abbrev refutI (X Y : PSet W) : PSet W := ⟨fun _ => refutP X Y⟩

/-- 相应的经典基结构。 -/
abbrev base (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := suppI, refutI := refutI }

/-- 典范框架。 -/
abbrev frame (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Frame :=
  { W := W
    atomRel := atomRel
    supp := fun X φ ρ => suppP X ((base W atomRel).truth φ ρ)
    refut := fun X φ ρ => refutP X ((base W atomRel).truth φ ρ) }

/-! ## 判据的基本性质 -/

theorem suppP_top_right (X : PSet W) : suppP X ⊤ := Or.inr (Or.inr rfl)

theorem refutP_top_right (X : PSet W) : refutP X ⊤ := Or.inr (Or.inr (Or.inr rfl))

/-- 若 `X ≤ Y` 且 `Y = ⊥`，则 `X = ⊥`。 -/
theorem eq_bot_of_le_bot {X Y : PSet W} (h : X ≤ Y) (hY : Y = ⊥) : X = ⊥ :=
  eq_bot_of_le (hY ▸ h)

/-- `suppP` 在第二个自变量上单调。 -/
theorem suppP_mono {X Y Z : PSet W} (h : suppP X Y) (hYZ : Y ≤ Z) : suppP X Z := by
  rcases h with h | h | h
  · exact Or.inl (le_trans h hYZ)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (eq_top_of_le (h ▸ hYZ)))

/-- F3（支持）：合取主体。 -/
theorem suppP_inf {X Z Y : PSet W} (h₁ : suppP X Y) (h₂ : suppP Z Y) : suppP (X ⊓ Z) Y := by
  rcases h₁ with h₁ | h₁ | h₁
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (fun _ hw => h₁ _ hw.1)
    · exact Or.inl (by rw [h₂, inf_top_eq]; exact h₁)
    · exact Or.inr (Or.inr h₂)
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (by rw [h₁, top_inf_eq]; exact h₂)
    · exact Or.inr (Or.inl (by rw [h₁, h₂, top_inf_eq]))
    · exact Or.inr (Or.inr h₂)
  · exact Or.inr (Or.inr h₁)

/-- F4（支持）：同一主体合取引入。 -/
theorem suppP_and {X Y Z : PSet W} (h₁ : suppP X Y) (h₂ : suppP X Z) :
    suppP X (Y ⊓ Z) := by
  rcases h₁ with h₁ | h₁ | h₁
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (le_inf h₁ h₂)
    · exact Or.inr (Or.inl h₂)
    · exact Or.inl (by rw [h₂, inf_top_eq]; exact h₁)
  · exact Or.inr (Or.inl h₁)
  · rcases h₂ with h₂ | h₂ | h₂
    · exact Or.inl (by rw [h₁, top_inf_eq]; exact h₂)
    · exact Or.inr (Or.inl h₂)
    · exact Or.inr (Or.inr (by rw [h₁, h₂, top_inf_eq]))

/-- F3（反驳）：合取主体。 -/
theorem refutP_inf {X Z Y : PSet W} (h₁ : refutP X Y) (h₂ : refutP Z Y) :
    refutP (X ⊓ Z) Y := by
  rcases h₁ with h₁ | h₁ | h₁ | h₁
  · exact Or.inl (eq_bot_of_le_bot
      (show (X ⊓ Z) ⊓ Y ≤ X ⊓ Y from fun _ hw => ⟨hw.1.1, hw.2⟩) h₁)
  · rcases h₂ with h₂ | h₂ | h₂ | h₂
    · exact Or.inl (by rw [h₁, top_inf_eq]; exact h₂)
    · exact Or.inr (Or.inl (by rw [h₁, h₂, top_inf_eq]))
    · exact Or.inr (Or.inr (Or.inl h₂))
    · exact Or.inr (Or.inr (Or.inr h₂))
  · exact Or.inl (by rw [h₁, inf_bot_eq])
  · exact Or.inr (Or.inr (Or.inr h₁))

/-- F4（反驳）：同一主体合取引入。 -/
theorem refutP_and {X Y Z : PSet W} (h₁ : refutP X Y) (h₂ : refutP X Z) :
    refutP X (Y ⊓ Z) := by
  rcases h₁ with h₁ | h₁ | h₁ | h₁
  · exact Or.inl (eq_bot_of_le_bot
      (show X ⊓ (Y ⊓ Z) ≤ X ⊓ Y from fun _ hw => ⟨hw.1, hw.2.1⟩) h₁)
  · exact Or.inr (Or.inl h₁)
  · exact Or.inr (Or.inr (Or.inl (by rw [h₁, bot_inf_eq])))
  · rcases h₂ with h₂ | h₂ | h₂ | h₂
    · exact Or.inl (by rw [h₁, top_inf_eq]; exact h₂)
    · exact Or.inr (Or.inl h₂)
    · exact Or.inr (Or.inr (Or.inl (by rw [h₁, h₂, top_inf_eq])))
    · exact Or.inr (Or.inr (Or.inr (by rw [h₁, h₂, top_inf_eq])))

/-- **R1**：`X ⊳ ¬φ ⇒ X ⊲ φ`。 -/
theorem refutP_of_suppP_compl {X Y : PSet W} (h : suppP X Yᶜ) : refutP X Y := by
  rcases h with h | h | h
  · exact Or.inl (eq_bot_of_le (fun w hw => h w hw.1 hw.2))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl (eq_bot_of_compl_eq_top h)))

/-! ## 两个真值函数一致 -/

/- 框架真值与基真值一致。 -/
mutual
  theorem frame_truth (W : Type) (atomRel : Nat → List (PSet W) → PSet W) :
      ∀ (φ : Form) (ρ : Nat → PSet W),
        (frame W atomRel).truth φ ρ = (base W atomRel).truth φ ρ
    | .var y, ρ => rfl
    | .atom i ts, ρ => by
        show atomRel i ((frame W atomRel).truths ρ ts)
          = atomRel i ((base W atomRel).truths ρ ts)
        rw [frame_truths W atomRel ρ ts]
    | .bot, _ => rfl
    | .top, _ => rfl
    | .not φ, ρ => by
        show ((frame W atomRel).truth φ ρ)ᶜ = ((base W atomRel).truth φ ρ)ᶜ
        rw [frame_truth W atomRel φ ρ]
    | .and φ ψ, ρ => by
        show (frame W atomRel).truth φ ρ ⊓ (frame W atomRel).truth ψ ρ
          = (base W atomRel).truth φ ρ ⊓ (base W atomRel).truth ψ ρ
        rw [frame_truth W atomRel φ ρ, frame_truth W atomRel ψ ρ]
    | .or φ ψ, ρ => by
        show (frame W atomRel).truth φ ρ ⊔ (frame W atomRel).truth ψ ρ
          = (base W atomRel).truth φ ρ ⊔ (base W atomRel).truth ψ ρ
        rw [frame_truth W atomRel φ ρ, frame_truth W atomRel ψ ρ]
    | .imp φ ψ, ρ => by
        show ((frame W atomRel).truth φ ρ)ᶜ ⊔ (frame W atomRel).truth ψ ρ
          = ((base W atomRel).truth φ ρ)ᶜ ⊔ (base W atomRel).truth ψ ρ
        rw [frame_truth W atomRel φ ρ, frame_truth W atomRel ψ ρ]
    | .all x φ, ρ => by
        apply PSet.iInter_congr
        intro X
        show (frame W atomRel).truth φ (upd ρ x X) = (base W atomRel).truth φ (upd ρ x X)
        rw [frame_truth W atomRel φ (upd ρ x X)]
    | .ex x φ, ρ => by
        apply PSet.iUnion_congr
        intro X
        show (frame W atomRel).truth φ (upd ρ x X) = (base W atomRel).truth φ (upd ρ x X)
        rw [frame_truth W atomRel φ (upd ρ x X)]
    | .supp t φ, ρ => by
        apply PSet.ext
        intro w
        show suppP ((frame W atomRel).truth t ρ) ((base W atomRel).truth φ ρ)
          ↔ suppP ((base W atomRel).truth t ρ) ((base W atomRel).truth φ ρ)
        rw [frame_truth W atomRel t ρ]
    | .refut t φ, ρ => by
        apply PSet.ext
        intro w
        show refutP ((frame W atomRel).truth t ρ) ((base W atomRel).truth φ ρ)
          ↔ refutP ((base W atomRel).truth t ρ) ((base W atomRel).truth φ ρ)
        rw [frame_truth W atomRel t ρ]

  /-- 列表版。 -/
  theorem frame_truths (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
      (ρ : Nat → PSet W) : ∀ (ts : List Form),
        (frame W atomRel).truths ρ ts = (base W atomRel).truths ρ ts
    | [] => rfl
    | t :: ts => by
        show (frame W atomRel).truth t ρ :: (frame W atomRel).truths ρ ts
          = (base W atomRel).truth t ρ :: (base W atomRel).truths ρ ts
        rw [frame_truth W atomRel t ρ, frame_truths W atomRel ρ ts]
end

/-! ## 基真值只依赖自由变元 -/

/- 基真值的相合性（只依赖自由变元）。 -/
mutual
  theorem base_agree (W : Type) (atomRel : Nat → List (PSet W) → PSet W) :
      ∀ (φ : Form) (ρ ρ' : Nat → PSet W),
        (∀ x, FreeIn x φ → ρ x = ρ' x) →
        (base W atomRel).truth φ ρ = (base W atomRel).truth φ ρ'
    | .var y, ρ, ρ', h => h y rfl
    | .atom i ts, ρ, ρ', h => by
        show atomRel i ((base W atomRel).truths ρ ts)
          = atomRel i ((base W atomRel).truths ρ' ts)
        rw [base_truths_agree W atomRel ρ ρ' ts
          (fun s hs x hx => h x (freeInList_of_mem hs hx))]
    | .bot, _, _, _ => rfl
    | .top, _, _, _ => rfl
    | .not φ, ρ, ρ', h => by
        show ((base W atomRel).truth φ ρ)ᶜ = ((base W atomRel).truth φ ρ')ᶜ
        rw [base_agree W atomRel φ ρ ρ' h]
    | .and φ ψ, ρ, ρ', h => by
        show (base W atomRel).truth φ ρ ⊓ (base W atomRel).truth ψ ρ
          = (base W atomRel).truth φ ρ' ⊓ (base W atomRel).truth ψ ρ'
        rw [base_agree W atomRel φ ρ ρ' (fun x hx => h x (Or.inl hx)),
          base_agree W atomRel ψ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .or φ ψ, ρ, ρ', h => by
        show (base W atomRel).truth φ ρ ⊔ (base W atomRel).truth ψ ρ
          = (base W atomRel).truth φ ρ' ⊔ (base W atomRel).truth ψ ρ'
        rw [base_agree W atomRel φ ρ ρ' (fun x hx => h x (Or.inl hx)),
          base_agree W atomRel ψ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .imp φ ψ, ρ, ρ', h => by
        show ((base W atomRel).truth φ ρ)ᶜ ⊔ (base W atomRel).truth ψ ρ
          = ((base W atomRel).truth φ ρ')ᶜ ⊔ (base W atomRel).truth ψ ρ'
        rw [base_agree W atomRel φ ρ ρ' (fun x hx => h x (Or.inl hx)),
          base_agree W atomRel ψ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .all z φ, ρ, ρ', h => by
        apply PSet.iInter_congr
        intro X
        show (base W atomRel).truth φ (upd ρ z X) = (base W atomRel).truth φ (upd ρ' z X)
        apply base_agree W atomRel φ _ _
        intro x hx
        by_cases hxz : x = z
        · subst hxz; rw [upd_same, upd_same]
        · rw [upd_noteq ρ hxz X, upd_noteq ρ' hxz X]
          exact h x ⟨hxz, hx⟩
    | .ex z φ, ρ, ρ', h => by
        apply PSet.iUnion_congr
        intro X
        show (base W atomRel).truth φ (upd ρ z X) = (base W atomRel).truth φ (upd ρ' z X)
        apply base_agree W atomRel φ _ _
        intro x hx
        by_cases hxz : x = z
        · subst hxz; rw [upd_same, upd_same]
        · rw [upd_noteq ρ hxz X, upd_noteq ρ' hxz X]
          exact h x ⟨hxz, hx⟩
    | .supp a φ, ρ, ρ', h => by
        show suppI ((base W atomRel).truth a ρ) ((base W atomRel).truth φ ρ)
          = suppI ((base W atomRel).truth a ρ') ((base W atomRel).truth φ ρ')
        rw [base_agree W atomRel a ρ ρ' (fun x hx => h x (Or.inl hx)),
          base_agree W atomRel φ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .refut a φ, ρ, ρ', h => by
        show refutI ((base W atomRel).truth a ρ) ((base W atomRel).truth φ ρ)
          = refutI ((base W atomRel).truth a ρ') ((base W atomRel).truth φ ρ')
        rw [base_agree W atomRel a ρ ρ' (fun x hx => h x (Or.inl hx)),
          base_agree W atomRel φ ρ ρ' (fun x hx => h x (Or.inr hx))]

  /-- 列表版。 -/
  theorem base_truths_agree (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
      (ρ ρ' : Nat → PSet W) : ∀ (ts : List Form),
        (∀ s ∈ ts, ∀ x, FreeIn x s → ρ x = ρ' x) →
        (base W atomRel).truths ρ ts = (base W atomRel).truths ρ' ts
    | [], _ => rfl
    | s :: ss, h => by
        show (base W atomRel).truth s ρ :: (base W atomRel).truths ρ ss
          = (base W atomRel).truth s ρ' :: (base W atomRel).truths ρ' ss
        rw [base_agree W atomRel s ρ ρ' (fun x hx => h s (by simp) x hx),
          base_truths_agree W atomRel ρ ρ' ss
            (fun t ht x hx => h t (by simp [ht]) x hx)]
end

/-- 基真值的（不）相关性：`x ∉ FV(φ)` 时 `x` 的赋值不影响真值。 -/
theorem base_truth_upd_notFree (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
    {x : Nat} {φ : Form} (h : ¬ FreeIn x φ) (ρ : Nat → PSet W) (X : PSet W) :
    (base W atomRel).truth φ (upd ρ x X) = (base W atomRel).truth φ ρ :=
  base_agree W atomRel φ _ _ (fun y hy => upd_noteq ρ (fun (hyx : y = x) => h (hyx ▸ hy)) X)

/-! ## F1／F2 的无穷交引理 -/

/-- **F1（支持）**：若每个 `T X` 都被 `Xt` 支持，则 `⋂ X, T X` 也被 `Xt` 支持。 -/
theorem suppP_iInter {Xt : PSet W} {T : PSet W → PSet W} (h : ∀ X, suppP Xt (T X)) :
    suppP Xt (PSet.iInter T) := by
  by_cases ht : Xt = ⊤
  · exact Or.inr (Or.inl ht)
  · have hle : ∀ X, Xt ≤ T X := by
      intro X
      rcases h X with hX | hX | hX
      · exact hX
      · exact absurd hX ht
      · exact PSet.le_of_eq_top hX
    exact Or.inl (PSet.le_iInter T hle)

/-- **F1（反驳）**：若每个 `T X` 都被 `Xt` 反驳，则 `⋂ X, T X` 也被 `Xt` 反驳。 -/
theorem refutP_iInter {Xt : PSet W} {T : PSet W → PSet W} (h : ∀ X, refutP Xt (T X)) :
    refutP Xt (PSet.iInter T) := by
  haveI : Nonempty (PSet W) := ⟨⊥⟩
  by_cases ht : Xt = ⊤
  · exact Or.inr (Or.inl ht)
  · by_cases hbot : ∃ X, T X = ⊥
    · obtain ⟨X₀, hX₀⟩ := hbot
      exact Or.inl (by
        have hI : PSet.iInter T = ⊥ := PSet.eq_bot_of_le (hX₀ ▸ PSet.iInter_le T X₀)
        rw [hI, PSet.inf_bot_eq])
    · by_cases htop : ∀ X, T X = ⊤
      · exact Or.inr (Or.inr (Or.inr (PSet.iInter_eq_top htop)))
      · have htop' : ∃ X, T X ≠ ⊤ := by
          by_cases hc : ∃ X, T X ≠ ⊤
          · exact hc
          · exact absurd (fun X => Classical.byContradiction (fun hX => hc ⟨X, hX⟩)) htop
        obtain ⟨X₀, hX₀⟩ := htop'
        rcases h X₀ with hX | hX | hX | hX
        · exact Or.inl (eq_bot_of_le_bot (PSet.inf_le_inf_right (PSet.iInter_le T X₀)) hX)
        · exact absurd hX ht
        · exact absurd hX (fun hh => hbot ⟨X₀, hh⟩)
        · exact absurd hX hX₀

/-- **F2（支持）**：若每个 `T X` 都支持 `Y`，则 `⋂ X, T X` 支持 `Y`。 -/
theorem suppP_of_iInter {Y : PSet W} {T : PSet W → PSet W} (h : ∀ X, suppP (T X) Y) :
    suppP (PSet.iInter T) Y := by
  haveI : Nonempty (PSet W) := ⟨⊥⟩
  by_cases hY : Y = ⊤
  · exact Or.inr (Or.inr hY)
  · by_cases hle : ∃ X, T X ≤ Y
    · obtain ⟨X₀, hX₀⟩ := hle
      exact Or.inl (PSet.le_trans (PSet.iInter_le T X₀) hX₀)
    · have hle' : ∀ X, ¬ (T X ≤ Y) := fun X hX => hle ⟨X, hX⟩
      have hall : ∀ X, T X = ⊤ := by
        intro X
        rcases h X with hX | hX | hX
        · exact absurd hX (hle' X)
        · exact hX
        · exact absurd hX hY
      exact Or.inr (Or.inl (PSet.iInter_eq_top hall))

/-- **F2（反驳）**：若每个 `T X` 都反驳 `Y`，则 `⋂ X, T X` 反驳 `Y`。 -/
theorem refutP_of_iInter {Y : PSet W} {T : PSet W → PSet W} (h : ∀ X, refutP (T X) Y) :
    refutP (PSet.iInter T) Y := by
  haveI : Nonempty (PSet W) := ⟨⊥⟩
  by_cases hY : Y = ⊥
  · exact Or.inr (Or.inr (Or.inl hY))
  by_cases hY' : Y = ⊤
  · exact Or.inr (Or.inr (Or.inr hY'))
  by_cases hle : ∃ X, T X ⊓ Y = ⊥
  · obtain ⟨X₀, hX₀⟩ := hle
    exact Or.inl (eq_bot_of_le_bot (PSet.inf_le_inf_left (PSet.iInter_le T X₀)) hX₀)
  · have hle' : ∀ X, ¬ (T X ⊓ Y = ⊥) := fun X hX => hle ⟨X, hX⟩
    have hall : ∀ X, T X = ⊤ := by
      intro X
      rcases h X with hX | hX | hX | hX
      · exact absurd hX (hle' X)
      · exact hX
      · exact absurd hX hY
      · exact absurd hX hY'
    exact Or.inr (Or.inl (PSet.iInter_eq_top hall))

/-! ## 存在性定理 -/

/-- **存在性定理**：对任意状态类型 `W` 与任意原子谓词解释 `atomRel`，
典范框架 `Canon.frame W atomRel` 都是模型。

定稿各条规则在此得到满足：`s1`／`s2` 来自 `≤` 的传递性，`f1`／`f2` 来自无穷交引理，
`p1`／`p2` 利用「内层关系为真时其真值为 `⊤`」这一事实。 -/
theorem isModel (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W) :
    IsModel (frame W atomRel) where
  nonempty := inferInstance
  classical := by
    intro p q hent ρ
    rw [frame_truth W atomRel p ρ, frame_truth W atomRel q ρ]
    exact hent (base W atomRel) ρ
  agree := by
    intro φ ρ ρ' h
    rw [frame_truth W atomRel φ ρ, frame_truth W atomRel φ ρ']
    exact base_agree W atomRel φ ρ ρ' h
  e := by
    intro φ ψ h k X ρ
    have hφψ : (base W atomRel).truth φ ρ = (base W atomRel).truth ψ ρ := by
      rw [← frame_truth W atomRel φ ρ, ← frame_truth W atomRel ψ ρ]
      exact h ρ
    cases k
    · show suppP X ((base W atomRel).truth φ ρ) ↔ suppP X ((base W atomRel).truth ψ ρ)
      rw [hφψ]
    · show refutP X ((base W atomRel).truth φ ρ) ↔ refutP X ((base W atomRel).truth ψ ρ)
      rw [hφψ]
  s1 := by
    intro p q ρ h
    rw [frame_truth W atomRel p ρ, frame_truth W atomRel q ρ] at h
    rw [frame_truth W atomRel p ρ]
    exact Or.inl h
  s2 := by
    intro X p q ρ h₁ h₂
    rw [frame_truth W atomRel p ρ, frame_truth W atomRel q ρ] at h₂
    exact suppP_mono h₁ h₂
  f1 := by
    intro k t φ x ρ hx H
    have hxt : ∀ X : PSet W,
        (frame W atomRel).truth t (upd ρ x X) = (base W atomRel).truth t ρ := by
      intro X
      rw [frame_truth W atomRel t (upd ρ x X)]
      exact base_truth_upd_notFree W atomRel hx ρ X
    rw [frame_truth W atomRel t ρ]
    cases k
    · show suppP ((base W atomRel).truth t ρ)
          (PSet.iInter (fun X : PSet W => (base W atomRel).truth φ (upd ρ x X)))
      apply suppP_iInter
      intro X
      have hX := H X
      rw [hxt X] at hX
      exact hX
    · show refutP ((base W atomRel).truth t ρ)
          (PSet.iInter (fun X : PSet W => (base W atomRel).truth φ (upd ρ x X)))
      apply refutP_iInter
      intro X
      have hX := H X
      rw [hxt X] at hX
      exact hX
  f2 := by
    intro k p φ x ρ hx H
    have hφ : ∀ X : PSet W,
        (base W atomRel).truth φ (upd ρ x X) = (base W atomRel).truth φ ρ :=
      fun X => base_truth_upd_notFree W atomRel hx ρ X
    rw [frame_truth W atomRel (.all x p) ρ]
    cases k
    · show suppP (PSet.iInter (fun X : PSet W => (base W atomRel).truth p (upd ρ x X)))
          ((base W atomRel).truth φ ρ)
      apply suppP_of_iInter
      intro X
      have hX := H X
      change suppP ((frame W atomRel).truth p (upd ρ x X))
        ((base W atomRel).truth φ (upd ρ x X)) at hX
      rw [frame_truth W atomRel p (upd ρ x X), hφ X] at hX
      exact hX
    · show refutP (PSet.iInter (fun X : PSet W => (base W atomRel).truth p (upd ρ x X)))
          ((base W atomRel).truth φ ρ)
      apply refutP_of_iInter
      intro X
      have hX := H X
      change refutP ((frame W atomRel).truth p (upd ρ x X))
        ((base W atomRel).truth φ (upd ρ x X)) at hX
      rw [frame_truth W atomRel p (upd ρ x X), hφ X] at hX
      exact hX
  f3 := by
    intro k X Z φ ρ h₁ h₂
    cases k
    · show suppP (X ⊓ Z) ((base W atomRel).truth φ ρ)
      exact suppP_inf h₁ h₂
    · show refutP (X ⊓ Z) ((base W atomRel).truth φ ρ)
      exact refutP_inf h₁ h₂
  f4 := by
    intro k X φ ψ ρ h₁ h₂
    cases k
    · show suppP X ((base W atomRel).truth φ ρ ⊓ (base W atomRel).truth ψ ρ)
      exact suppP_and h₁ h₂
    · show refutP X ((base W atomRel).truth φ ρ ⊓ (base W atomRel).truth ψ ρ)
      exact refutP_and h₁ h₂
  r1 := by
    intro X φ ρ h
    exact refutP_of_suppP_compl h
  p1 := by
    intro kR kS a b c d f ρ h₁ h₂ h₃
    have keyS : (base W atomRel).truth (Kind.form kS (.and c d) f) ρ = ⊤ := by
      cases kS
      · have h := h₃
        rw [frame_truth W atomRel c ρ, frame_truth W atomRel d ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show suppP ((base W atomRel).truth c ρ ⊓ (base W atomRel).truth d ρ)
          ((base W atomRel).truth f ρ)
        exact h
      · have h := h₃
        rw [frame_truth W atomRel c ρ, frame_truth W atomRel d ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show refutP ((base W atomRel).truth c ρ ⊓ (base W atomRel).truth d ρ)
          ((base W atomRel).truth f ρ)
        exact h
    cases kR
    · show suppP ((frame W atomRel).truth a ρ ⊓ (frame W atomRel).truth b ρ)
          ((base W atomRel).truth (Kind.form kS (.and c d) f) ρ)
      rw [keyS, frame_truth W atomRel a ρ, frame_truth W atomRel b ρ]
      exact suppP_top_right _
    · show refutP ((frame W atomRel).truth a ρ ⊓ (frame W atomRel).truth b ρ)
          ((base W atomRel).truth (Kind.form kS (.and c d) f) ρ)
      rw [keyS, frame_truth W atomRel a ρ, frame_truth W atomRel b ρ]
      exact refutP_top_right _
  p2 := by
    intro kR kS a c f x ρ hx h₁ h₂
    have keyS : (base W atomRel).truth (Kind.form kS (.all x c) f) ρ = ⊤ := by
      cases kS
      · have h := h₂
        rw [frame_truth W atomRel (.all x c) ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show suppP (PSet.iInter (fun X : PSet W => (base W atomRel).truth c (upd ρ x X)))
          ((base W atomRel).truth f ρ)
        exact h
      · have h := h₂
        rw [frame_truth W atomRel (.all x c) ρ] at h
        apply PSet.eq_top_of_le
        intro w _
        show refutP (PSet.iInter (fun X : PSet W => (base W atomRel).truth c (upd ρ x X)))
          ((base W atomRel).truth f ρ)
        exact h
    cases kR
    · show suppP ((frame W atomRel).truth (.all x a) ρ)
          ((base W atomRel).truth (Kind.form kS (.all x c) f) ρ)
      rw [keyS, frame_truth W atomRel (.all x a) ρ]
      exact suppP_top_right _
    · show refutP ((frame W atomRel).truth (.all x a) ρ)
          ((base W atomRel).truth (Kind.form kS (.all x c) f) ρ)
      rw [keyS, frame_truth W atomRel (.all x a) ρ]
      exact refutP_top_right _

end Canon
end EvidenceLogic
