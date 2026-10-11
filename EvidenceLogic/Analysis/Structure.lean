/-
# 证据语义的结构事实（Structure）

本文件把「证据语义」的结构性质单独列出并机器验证，供
[`docs/证据语义解读.md`](../../docs/证据语义解读.md) 的解读引用。

**证据语义**（`Canonical.lean`，也是唯一已知的模型族）：

```
X ⊳ Y  ⟺  X ≤ Y  ∨  X = ⊤  ∨  Y = ⊤          （suppP）
X ⊲ Y  ⟺  X ⊓ Y = ⊥  ∨  X = ⊤  ∨  Y = ⊥  ∨  Y = ⊤   （refutP）
```

其中每个析取项都有明确的"证据学"读法（见解读文档第二节）。本文件收集的
事实说明这套语义在**两个极端证据** `⊥`（空内容）与 `⊤`（全内容／自相矛盾）处
是**退化的**：它们既支持一切也反驳一切；反之，一切证据都支持／反驳 `⊤` 与 `⊥`。
这正是"支持不传递"与"反驳不传递"能够成立、而 P1／P2 仍然有内容的语义根源。
-/
import EvidenceLogic.System.NonDerivable

namespace EvidenceLogic

noncomputable section

open scoped Classical

namespace Canon

variable {W : Type}

/-! ## 一、退化支持者：`⊥` 与 `⊤` 支持／反驳一切 -/

/-- 空内容支持者支持一切（析取项 `X ≤ Y`）。 -/
theorem suppP_bot_left (Y : PSet W) : suppP ⊥ Y := Or.inl (PSet.bot_le Y)

/-- 全内容支持者支持一切（析取项 `X = ⊤`）。 -/
theorem suppP_top_left (Y : PSet W) : suppP ⊤ Y := Or.inr (Or.inl rfl)

/-- 空内容支持者反驳一切（析取项 `X ⊓ Y = ⊥`）。 -/
theorem refutP_bot_left (Y : PSet W) : refutP ⊥ Y :=
  Or.inl (PSet.eq_bot_of_le (fun _ h => h.1))

/-- 全内容支持者反驳一切（析取项 `X = ⊤`）。 -/
theorem refutP_top_left (Y : PSet W) : refutP ⊤ Y := Or.inr (Or.inl rfl)

/-! ## 二、反之：一切证据都支持／反驳 `⊤` 与 `⊥` -/

/-- 一切支持者都反驳 `⊥`（析取项 `Y = ⊥`）。 -/
theorem refutP_bot_right (X : PSet W) : refutP X ⊥ :=
  Or.inr (Or.inr (Or.inl rfl))

/-- **一切支持者都支持 `⊥`，当且仅当该支持者本身退化**（`⊥` 或 `⊤`）。 -/
theorem suppP_bot_right [Nonempty W] {X : PSet W} :
    suppP X ⊥ ↔ X = ⊥ ∨ X = ⊤ := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl (PSet.eq_bot_of_le h)
    · exact Or.inr h
    · exfalso
      obtain ⟨w⟩ := ‹Nonempty W›
      exact PSet.not_bot w (h.symm ▸ trivial)
  · rintro (h | h)
    · exact Or.inl (h.symm ▸ PSet.le_refl (⊥ : PSet W))
    · exact Or.inr (Or.inl h)

/-! ## 三、支持自反、但不传递；反驳连自反都不成立 -/

/-- 支持自反（析取项 `X ≤ X`）。 -/
theorem suppP_refl (X : PSet W) : suppP X X := Or.inl (PSet.le_refl X)

/-- **支持不传递**（在 `M3` 的命题上给出具体反例）：`s0 ⊳ ⊤`、`⊤ ⊳ s1`，而 `¬ s0 ⊳ s1`。

这正是定稿明确拒绝「支持传递」的语义根据：三个析取项使支持关系只是**自反关系**，
而不是预序，因此不能作为范畴的 hom 关系。 -/
theorem suppP_not_transitive :
    suppP s0 (⊤ : PSet (Fin 3)) ∧ suppP (⊤ : PSet (Fin 3)) s1
      ∧ ¬ suppP s0 s1 :=
  ⟨suppP_top_right _, Or.inr (Or.inl rfl), not_suppP_s0_s1⟩

/-- **反驳连自反性都不成立**：`¬ s0 ⊲ s0`（`X ⊓ X = ⊥` 只在退化支持者处成立）。 -/
theorem refutP_not_refl : ¬ refutP (s0 : PSet (Fin 3)) s0 := not_refutP_s0_s0

/-! ## 六、判据的**本质形式**：写出来的析取项里有两个是冗余的

`Canonical.lean` 为了可读性把判据写成三项／四项。实际上：

* `suppP X Y ↔ X ≤ Y ∨ X = ⊤`（写出来的 `Y = ⊤` 冗余：`Y = ⊤` 时 `X ≤ ⊤` 已成立）；
* `refutP X Y ↔ X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊤`（写出来的 `Y = ⊥` 冗余：`X ⊓ ⊥ = ⊥` 已成立）。

于是"本质判据"是：支持**两项**，反驳**三项**。各析取项的分工（下半段为分析，非机器验证）：

| 析取项 | 分工 |
|---|---|
| `X ≤ Y` / `X ⊓ Y = ⊥` | 实质读法：内容包含／内容不相容 |
| `X = ⊤` | 自相矛盾支持者爆炸（§8）；**也是唯一破坏传递性的装置**（`suppP_not_transitive`） |
| `Y = ⊤`（反驳侧） | P1／P2 在 `kR = ⊲` 时所需：被反驳的内层关系式真值恒为 `⊤` |

R1 只需用到支持侧的 `X = ⊤` 与反驳侧的 `X ⊓ Y = ⊥`／`X = ⊤` 三项，**不需要**任何"端点"析取项。 -/

/-- **`suppP` 的第三个析取项冗余**：本质形式是"两个析取项"。 -/
theorem suppP_iff_le_or_top {X Y : PSet W} : suppP X Y ↔ X ≤ Y ∨ X = ⊤ := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl (h.symm ▸ PSet.le_top X)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **`refutP` 的第三个析取项冗余**：本质形式是"三个析取项"。 -/
theorem refutP_iff_disjoint_or_top {X Y : PSet W} :
    refutP X Y ↔ X ⊓ Y = ⊥ ∨ X = ⊤ ∨ Y = ⊤ := by
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (PSet.eq_bot_of_le (fun _ hw => h ▸ hw.2))
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

/-- 若传递的两个环节都由 `≤` 项成立，则结论也成立——故传递的失败**必然**经由 `X = ⊤` 项。
这解释了 `suppP_not_transitive` 的见证为何取中间项 `⊤`。 -/
theorem suppP_transitive_of_le_links {X Y Z : PSet W} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
    suppP X Z :=
  Or.inl (PSet.le_trans h₁ h₂)

/-! ## 七、关系式的真值是常值命题 -/

/-- 任意框架中，关系式 `a ⊳ b` 的真值不随世界变化（是**常值命题**）。 -/
theorem truth_supp_is_const (M : Frame) (a b : Form) (ρ : Nat → PSet M.W) :
    M.truth (a ⊳ b) ρ = (⟨fun _ => M.supp (M.truth a ρ) b ρ⟩ : PSet M.W) := rfl

/-- 典范框架中同理，真值恰为 `suppP` 的常值命题。 -/
theorem canon_truth_supp_is_const (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
    (a b : Form) (ρ : Nat → PSet W) :
    (Canon.frame W atomRel).truth (a ⊳ b) ρ =
      (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth a ρ)
        ((Canon.base W atomRel).truth b ρ)⟩ : PSet W) := rfl

/-! ## 五、可推导的关系式是"内容空洞的重言式" -/

/-- 可推导的关系式在任意模型中有效。 -/
theorem derivable_rel_valid {M : Frame} (hM : IsModel M) {a b : Form}
    (h : Derivable (a ⊳ b)) : M.Valid (a ⊳ b) :=
  Derivable.soundness M hM h

/-- 结合 `derivable_rel_truth_eq_top`：可推导的关系式在任意模型、任意赋值下真值为 `⊤`，
即作为**命题**是重言式。这是「系统不蕴涵真」（定稿第八节）的语义根源。 -/
theorem derivable_rel_is_tautology {M : Frame} (hM : IsModel M) {a b : Form}
    (h : Derivable (a ⊳ b)) (ρ : Nat → PSet M.W) : M.truth (a ⊳ b) ρ = ⊤ :=
  derivable_rel_valid hM h ρ

end Canon

end

end EvidenceLogic
