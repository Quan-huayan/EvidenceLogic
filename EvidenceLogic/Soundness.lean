/-
# 背书逻辑 v1.0：可靠性（Soundness）

本文件证明**可靠性定理**：

    若 `⊢ᴱ φ`，则 `φ` 在所有模型中有效（`M ⊨ φ`）。

即定稿的每条规则都在模型类中成立。这是后续「不可推导性」结论的基础：
若某命题有反模型，则它不可推导。

## 证明要点

* **E**：需要上下文填入的真值相合性 `Frame.plug_congr`。对 `⊳`／`⊲` 的**第二个**
  自变量（被支持／被反驳的公式）使用 `IsModel.e`；对第一个自变量使用真值同余。
* **S1**／**S2**：由 `IsModel.classical` 把 `⊢` 化为模型内 `≤`，再用 `s1`／`s2`。
* **F1**／**F2**：规则以开公式推导为前提，其有效性恰是 `f1`／`f2` 的条件
  （前提对**所有**赋值成立）。
* **P1**／**P2**：`p1`／`p2` 直接给出。

辅助引理 `rel_of_valid`／`valid_of_rel` 在「关系成立」与「关系公式真值为 `⊤`」
之间转换（需要一个状态，由 `IsModel.nonempty` 提供）。
-/
import EvidenceLogic.Derivable

namespace EvidenceLogic
namespace Frame

open PSet

/-- 关系公式的有效性等价于相应关系成立（`w` 用于处理「恒常命题」）。 -/
theorem truth_rel_eq_top_iff (M : Frame) (w : M.W) {k : Kind} {a b : Form}
    {ρ : Nat → PSet M.W} :
    M.truth (Kind.form k a b) ρ = ⊤ ↔ M.rel k (M.truth a ρ) b ρ := by
  cases k
  · exact PSet.const_eq_top_iff w
  · exact PSet.const_eq_top_iff w

/-- **上下文填入的真值相合性**：若 `φ` 与 `ψ` 在所有赋值下真值相同，
则把它们填入同一上下文的任意位置也得到相同真值。 -/
theorem plug_congr (M : Frame) (hM : IsModel M) : ∀ (C : Ctx) (φ ψ : Form),
    (∀ ρ, M.truth φ ρ = M.truth ψ ρ) →
    ∀ ρ, M.truth (C.plug φ) ρ = M.truth (C.plug ψ) ρ
  | .hole, _, _, h => h
  | .atom i pre c post, φ, ψ, h => fun ρ => by
      show M.atomRel i (M.truths ρ (pre ++ Ctx.plug c φ :: post))
        = M.atomRel i (M.truths ρ (pre ++ Ctx.plug c ψ :: post))
      rw [truths_cons_eq M (plug_congr M hM c φ ψ h) ρ pre post]
  | .not c, φ, ψ, h => fun ρ => by
      show (M.truth (Ctx.plug c φ) ρ)ᶜ = (M.truth (Ctx.plug c ψ) ρ)ᶜ
      rw [plug_congr M hM c φ ψ h ρ]
  | .andL c ψ', φ, ψ, h => fun ρ => by
      show M.truth (Ctx.plug c φ) ρ ⊓ M.truth ψ' ρ
        = M.truth (Ctx.plug c ψ) ρ ⊓ M.truth ψ' ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .andR φ' c, φ, ψ, h => fun ρ => by
      show M.truth φ' ρ ⊓ M.truth (Ctx.plug c φ) ρ
        = M.truth φ' ρ ⊓ M.truth (Ctx.plug c ψ) ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .orL c ψ', φ, ψ, h => fun ρ => by
      show M.truth (Ctx.plug c φ) ρ ⊔ M.truth ψ' ρ
        = M.truth (Ctx.plug c ψ) ρ ⊔ M.truth ψ' ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .orR φ' c, φ, ψ, h => fun ρ => by
      show M.truth φ' ρ ⊔ M.truth (Ctx.plug c φ) ρ
        = M.truth φ' ρ ⊔ M.truth (Ctx.plug c ψ) ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .impL c ψ', φ, ψ, h => fun ρ => by
      show (M.truth (Ctx.plug c φ) ρ)ᶜ ⊔ M.truth ψ' ρ
        = (M.truth (Ctx.plug c ψ) ρ)ᶜ ⊔ M.truth ψ' ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .impR φ' c, φ, ψ, h => fun ρ => by
      show (M.truth φ' ρ)ᶜ ⊔ M.truth (Ctx.plug c φ) ρ
        = (M.truth φ' ρ)ᶜ ⊔ M.truth (Ctx.plug c ψ) ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .all x c, φ, ψ, h => fun ρ => by
      apply PSet.iInter_congr
      intro X
      show M.truth (Ctx.plug c φ) (upd ρ x X) = M.truth (Ctx.plug c ψ) (upd ρ x X)
      rw [plug_congr M hM c φ ψ h (upd ρ x X)]
  | .ex x c, φ, ψ, h => fun ρ => by
      apply PSet.iUnion_congr
      intro X
      show M.truth (Ctx.plug c φ) (upd ρ x X) = M.truth (Ctx.plug c ψ) (upd ρ x X)
      rw [plug_congr M hM c φ ψ h (upd ρ x X)]
  | .suppL c ψ', φ, ψ, h => fun ρ => by
      apply PSet.ext
      intro w
      show M.supp (M.truth (Ctx.plug c φ) ρ) ψ' ρ ↔ M.supp (M.truth (Ctx.plug c ψ) ρ) ψ' ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .suppR t c, φ, ψ, h => fun ρ => by
      apply PSet.ext
      intro w
      show M.supp (M.truth t ρ) (Ctx.plug c φ) ρ ↔ M.supp (M.truth t ρ) (Ctx.plug c ψ) ρ
      exact hM.e (Ctx.plug c φ) (Ctx.plug c ψ) (plug_congr M hM c φ ψ h) .supp (M.truth t ρ) ρ
  | .refutL c ψ', φ, ψ, h => fun ρ => by
      apply PSet.ext
      intro w
      show M.refut (M.truth (Ctx.plug c φ) ρ) ψ' ρ ↔ M.refut (M.truth (Ctx.plug c ψ) ρ) ψ' ρ
      rw [plug_congr M hM c φ ψ h ρ]
  | .refutR t c, φ, ψ, h => fun ρ => by
      apply PSet.ext
      intro w
      show M.refut (M.truth t ρ) (Ctx.plug c φ) ρ ↔ M.refut (M.truth t ρ) (Ctx.plug c ψ) ρ
      exact hM.e (Ctx.plug c φ) (Ctx.plug c ψ) (plug_congr M hM c φ ψ h) .refut (M.truth t ρ) ρ

end Frame

namespace Derivable

open PSet

/-- 由经典等价得到模型内的真值相等。 -/
theorem truth_eq_of_cequiv {M : Frame} (hM : IsModel M) {φ ψ : Form} (h : φ ⊣⊢ ψ) :
    ∀ ρ, M.truth φ ρ = M.truth ψ ρ :=
  fun ρ => PSet.ext (fun w =>
    ⟨fun h1 => hM.classical φ ψ h.1 ρ w h1, fun h2 => hM.classical ψ φ h.2 ρ w h2⟩)

/-- 关系成立蕴含关系公式有效（`k` 可变）。 -/
theorem valid_rel (M : Frame) (hM : IsModel M) {k : Kind} {a b : Form}
    {ρ : Nat → PSet M.W} (h : M.rel k (M.truth a ρ) b ρ) :
    M.truth (Kind.form k a b) ρ = ⊤ :=
  (Frame.truth_rel_eq_top_iff M (Classical.choice hM.nonempty)).mpr h

/-- 有效的关系公式蕴含关系成立（`k` 可变）。 -/
theorem rel_of_valid (M : Frame) (hM : IsModel M) {k : Kind} {a b : Form}
    {ρ : Nat → PSet M.W} (h : M.truth (Kind.form k a b) ρ = ⊤) :
    M.rel k (M.truth a ρ) b ρ :=
  (Frame.truth_rel_eq_top_iff M (Classical.choice hM.nonempty)).mp h

/-- `M ⊨ a ⊳ b` 蕴含 `M.supp` 关系成立（`k = ⊳`，便于与记法统一）。 -/
theorem supp_of_valid (M : Frame) (hM : IsModel M) {a b : Form} {ρ : Nat → PSet M.W}
    (h : M.truth (a ⊳ b) ρ = ⊤) : M.supp (M.truth a ρ) b ρ :=
  (Frame.truth_rel_eq_top_iff M (Classical.choice hM.nonempty) :
      M.truth (Kind.form .supp a b) ρ = ⊤ ↔ M.supp (M.truth a ρ) b ρ).mp h

/-- 反之：`M.supp` 关系成立给出 `M ⊨ a ⊳ b`。 -/
theorem valid_supp (M : Frame) (hM : IsModel M) {a b : Form} {ρ : Nat → PSet M.W}
    (h : M.supp (M.truth a ρ) b ρ) : M.truth (a ⊳ b) ρ = ⊤ :=
  (Frame.truth_rel_eq_top_iff M (Classical.choice hM.nonempty) :
      M.truth (Kind.form .supp a b) ρ = ⊤ ↔ M.supp (M.truth a ρ) b ρ).mpr h

/-- `M ⊨ a ⊲ b` 蕴含 `M.refut` 关系成立。 -/
theorem refut_of_valid (M : Frame) (hM : IsModel M) {a b : Form} {ρ : Nat → PSet M.W}
    (h : M.truth (a ⊲ b) ρ = ⊤) : M.refut (M.truth a ρ) b ρ :=
  (Frame.truth_rel_eq_top_iff M (Classical.choice hM.nonempty) :
      M.truth (Kind.form .refut a b) ρ = ⊤ ↔ M.refut (M.truth a ρ) b ρ).mp h

/-- 反之：`M.refut` 关系成立给出 `M ⊨ a ⊲ b`。 -/
theorem valid_refut (M : Frame) (hM : IsModel M) {a b : Form} {ρ : Nat → PSet M.W}
    (h : M.refut (M.truth a ρ) b ρ) : M.truth (a ⊲ b) ρ = ⊤ :=
  (Frame.truth_rel_eq_top_iff M (Classical.choice hM.nonempty) :
      M.truth (Kind.form .refut a b) ρ = ⊤ ↔ M.refut (M.truth a ρ) b ρ).mpr h

/-- **可靠性定理**：可推导的公式在所有模型中有效。 -/
theorem soundness (M : Frame) (hM : IsModel M) : ∀ {φ : Form}, Derivable φ → M.Valid φ
  | _, @Derivable.e φ ψ γ δ hrep heq hγ => by
      obtain ⟨C, hγeq, hδeq⟩ := hrep
      have hφψ := truth_eq_of_cequiv hM heq
      have hγ' : M.Valid (C.plug φ) := by
        rw [← hγeq]
        exact soundness M hM hγ
      rw [hδeq]
      intro ρ
      rw [← Frame.plug_congr M hM C φ ψ hφψ ρ]
      exact hγ' ρ
  | _, @Derivable.s1 p q h => fun ρ =>
      valid_supp M hM (hM.s1 p q ρ (hM.classical p q h ρ))
  | _, @Derivable.s2 t p q h₁ h => fun ρ =>
      valid_supp M hM (hM.s2 (M.truth t ρ) p q ρ
        (supp_of_valid M hM (soundness M hM h₁ ρ))
        (hM.classical p q h ρ))
  | _, @Derivable.f1 k t φ x hx h => fun ρ =>
      valid_rel M hM (hM.f1 k t φ x ρ hx
        (fun X => rel_of_valid M hM (soundness M hM h (upd ρ x X))))
  | _, @Derivable.f2 k p φ x hx h => fun ρ =>
      valid_rel M hM (hM.f2 k p φ x ρ hx
        (fun X => rel_of_valid M hM (soundness M hM h (upd ρ x X))))
  | _, @Derivable.f3 k a b φ h₁ h₂ => fun ρ =>
      valid_rel M hM (hM.f3 k (M.truth a ρ) (M.truth b ρ) φ ρ
        (rel_of_valid M hM (soundness M hM h₁ ρ))
        (rel_of_valid M hM (soundness M hM h₂ ρ)))
  | _, @Derivable.f4 k t φ ψ h₁ h₂ => fun ρ =>
      valid_rel M hM (hM.f4 k (M.truth t ρ) φ ψ ρ
        (rel_of_valid M hM (soundness M hM h₁ ρ))
        (rel_of_valid M hM (soundness M hM h₂ ρ)))
  | _, @Derivable.r1 t φ h => fun ρ =>
      valid_refut M hM (hM.r1 (M.truth t ρ) φ ρ
        (supp_of_valid M hM (soundness M hM h ρ)))
  | _, @Derivable.p1 kR kS a b c d f h₁ h₂ h₃ => fun ρ =>
      valid_rel M hM (hM.p1 kR kS a b c d f ρ
        (rel_of_valid M hM (soundness M hM h₁ ρ))
        (rel_of_valid M hM (soundness M hM h₂ ρ))
        (rel_of_valid M hM (soundness M hM h₃ ρ)))
  | _, @Derivable.p2 kR kS a c f x h₁ h₂ hx => fun ρ =>
      valid_rel M hM (hM.p2 kR kS a c f x ρ hx
        (fun X => rel_of_valid M hM (soundness M hM h₁ (upd ρ x X)))
        (rel_of_valid M hM (soundness M hM h₂ ρ)))

end Derivable

end EvidenceLogic
