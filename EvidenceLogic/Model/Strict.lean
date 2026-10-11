/-
# 第二模型族：**严格蕴含框架**（Strict）

本文件**不修改任何已有文件**，只在既有 `import` 之上补一批新结论。
它给出 `Model/Canonical.lean` 之外的**第二个模型族**，并由此得到全量
`Derivable`（含元规则 **E**、无任何片段限制）的**无条件**支持-蕴含不变量。

## 1. 这一族是什么

定稿把 `⊳` 解释为

    X ⊳ Y  ⟺  X ≤ Y ∨ X = ⊤ ∨ Y = ⊤            （`Canon.suppP`）

并明确写道：「语义不能退化为朴素的 `X ≤ Y` 蕴含读法（否则支持传递将成为有效式）」
（见 `Model/Canonical.lean` 开头与 `docs/设计说明.md`）。本文件把那个**被拒绝的朴素读法**
本身做成一个结构，并**证明它也是模型**：

    严格蕴含框架：`M.supp X φ ρ := X ≤ ⟦φ⟧`，
                  `M.refut X φ ρ := X ⊓ ⟦φ⟧ = ⊥ ∨ ⟦φ⟧ = ⊤`

于是定稿的那句设计理由成为一条**定理**（`strict_transitivity_rule_valid`）：
在严格蕴含框架中支持传递的规则形式**成立**。**这丝毫不削弱**典范模型族上的结论
（`System/NonAdmissible.lean` 的反例全部取自典范框架，本文件与它们不冲突）：
它说明的是「拒绝朴素读法」是**语义设计的取舍**，而不是逻辑上的必然——
两个框架都是同一公理系统的模型。

## 2. 为什么这一族有用：无条件的不变量

`Frontier/EFree.lean`／`RestrictedE.lean`／`Conditional.lean` 三处的支持-蕴含不变量
要么禁用／限制 `E`，要么以未证的 `TransferLemma` 为假设；在**典范**框架上对全量
`Derivable` 归纳时，唯一闭合不了的是 `E` 的「洞在顶层」那一支
（归约到 `docs/讨论与局限.md` 第 2 节的公开问题）。

严格蕴含框架里**没有这个缺口**：它的 `supp` 字段里被支持公式的真值取在**基结构层**
（与 `Canon.frame` 同形），而 `supp` 的内容恰是「两个真值之间的 `≤`」；于是典范框架里
那个需要「分量相等」的搬运步骤在**同一框架内**是定义性的。`IsModel` 的十三个字段
逐一成立后，`Derivable.soundness` 直接把不变量交出来：

    Derivable (p ⊳ q)  ⟹  ∀ρ, ⟦p⟧_{strict} ρ ≤ ⟦q⟧_{strict} ρ      （`strict_supp_le`，无条件）

这是本工程**第一条对全量 `Derivable`（允许任意 `E`）无条件成立的支持-蕴含不变量**。

## 3. 文件内容

1. 第 0 节：两个小工具（`le_of_eq_pset`、`upd_self_eq`）；
2. 第 1 节：**任意基结构**上的相合性 `Base.truth_agree`（`Canon.base_agree` 的一般化）；
3. 第 2 节：严格蕴含基结构／框架、`strict_frame_truth`、`strict_isModel`；
4. 第 3 节：`strict_supp_le`（无条件不变量）与三条推论
   （`strict_transitivity_rule_valid`、`strict_transitivity_valid`、`strict_s7_valid`）。

## 4. 强度声明

本文件**只**给出第二个模型族与它的无条件不变量。它**不**证明 `TransferLemma`，
**不**证明 `TruthPropagation`，**不**对 N3 账本（`System/NonAdmissible.lean` 第十一节）
的任一条作断言：严格蕴含框架**验证**的规则更多（例如支持传递），因此它**不能**
用来构造任何 N3 反例。它对第 2 节所述公开问题的作用是**结构性的**：
把「不变量为什么在典范框架上难」定位到 `suppP` 的析取项 `Y = ⊤` 上
（严格框架没有这一项，缺口随即消失）。

## 5. 技术注记

* 与前几个文件一样：不用 `induction` 于 `Form`；`mutual` 块内递归调用**显式给出**
  公式隐变量；`mutual` 之前只放普通块注释；
* `strict_isModel` 的各字段**不**引用自身（不用 `Frame.truth_upd_notFree`），
  而用 `strict_frame_truth` ＋ 基结构层的 `Base.truth_upd_notFree`／`Base.truth_agree`，
  以免在结构字面量里出现自引用；
* 未使用的绑定一律写 `_`，不使用 `sorry`／`axiom`／`admit`。
-/
import EvidenceLogic.Model.Soundness

namespace EvidenceLogic

open PSet

open scoped Classical

/-! ## 0. 两个小工具 -/

/-- 等式蕴含 `≤`（显式给出，避免依赖 `.le` 记法的实例解析）。 -/
theorem le_of_eq_pset {W : Type} {X Y : PSet W} (h : X = Y) : X ≤ Y := fun _ hx => h ▸ hx

/-- 同一赋值的自更新是原赋值：`upd ρ x (ρ x) = ρ`。 -/
theorem upd_self_eq {W : Type} (ρ : Nat → W) (x : Nat) : upd ρ x (ρ x) = ρ := by
  funext y
  by_cases hy : y = x
  · subst hy; rw [upd_same]
  · rw [upd_noteq ρ hy]

/-! ## 1. 任意基结构上的相合性：真值只依赖自由变元

`Model/Canonical.lean` 已有**典范基结构**的专用版本 `Canon.base_agree`；本节把它
一般化到**任意**基结构 `B : Base`，因为第 2 节的第二模型族要证 `IsModel.agree`
时不能借用典范基结构的结论。

对公式与列表写成 `mutual`（`.atom` 情形需要列表版）；递归调用一律显式给出公式隐变量
（理由见 `Frontier/RestrictedE.lean` 注 3）。 -/

namespace Base

/- 基真值的相合性（只依赖自由变元）。 -/
mutual
  /-- 公式版。 -/
  theorem truth_agree (B : Base) :
      ∀ (φ : Form) (ρ ρ' : Nat → PSet B.W),
        (∀ x, FreeIn x φ → ρ x = ρ' x) → B.truth φ ρ = B.truth φ ρ'
    | .var y, ρ, ρ', h => h y rfl
    | .atom i ts, ρ, ρ', h => by
        show B.atomRel i (B.truths ρ ts) = B.atomRel i (B.truths ρ' ts)
        rw [truths_agree B ρ ρ' ts (fun s hs x hx => h x (freeInList_of_mem hs hx))]
    | .bot, _, _, _ => rfl
    | .top, _, _, _ => rfl
    | .not φ, ρ, ρ', h => by
        show (B.truth φ ρ)ᶜ = (B.truth φ ρ')ᶜ
        rw [truth_agree B φ ρ ρ' h]
    | .and φ ψ, ρ, ρ', h => by
        show B.truth φ ρ ⊓ B.truth ψ ρ = B.truth φ ρ' ⊓ B.truth ψ ρ'
        rw [truth_agree B φ ρ ρ' (fun x hx => h x (Or.inl hx)),
          truth_agree B ψ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .or φ ψ, ρ, ρ', h => by
        show B.truth φ ρ ⊔ B.truth ψ ρ = B.truth φ ρ' ⊔ B.truth ψ ρ'
        rw [truth_agree B φ ρ ρ' (fun x hx => h x (Or.inl hx)),
          truth_agree B ψ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .imp φ ψ, ρ, ρ', h => by
        show (B.truth φ ρ)ᶜ ⊔ B.truth ψ ρ = (B.truth φ ρ')ᶜ ⊔ B.truth ψ ρ'
        rw [truth_agree B φ ρ ρ' (fun x hx => h x (Or.inl hx)),
          truth_agree B ψ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .all z φ, ρ, ρ', h => by
        apply PSet.iInter_congr
        intro X
        show B.truth φ (upd ρ z X) = B.truth φ (upd ρ' z X)
        apply truth_agree B φ _ _
        intro x hx
        by_cases hxz : x = z
        · subst hxz; rw [upd_same, upd_same]
        · rw [upd_noteq ρ hxz X, upd_noteq ρ' hxz X]
          exact h x ⟨hxz, hx⟩
    | .ex z φ, ρ, ρ', h => by
        apply PSet.iUnion_congr
        intro X
        show B.truth φ (upd ρ z X) = B.truth φ (upd ρ' z X)
        apply truth_agree B φ _ _
        intro x hx
        by_cases hxz : x = z
        · subst hxz; rw [upd_same, upd_same]
        · rw [upd_noteq ρ hxz X, upd_noteq ρ' hxz X]
          exact h x ⟨hxz, hx⟩
    | .supp a φ, ρ, ρ', h => by
        show B.suppI (B.truth a ρ) (B.truth φ ρ) = B.suppI (B.truth a ρ') (B.truth φ ρ')
        rw [truth_agree B a ρ ρ' (fun x hx => h x (Or.inl hx)),
          truth_agree B φ ρ ρ' (fun x hx => h x (Or.inr hx))]
    | .refut a φ, ρ, ρ', h => by
        show B.refutI (B.truth a ρ) (B.truth φ ρ) = B.refutI (B.truth a ρ') (B.truth φ ρ')
        rw [truth_agree B a ρ ρ' (fun x hx => h x (Or.inl hx)),
          truth_agree B φ ρ ρ' (fun x hx => h x (Or.inr hx))]

  /-- 列表版。 -/
  theorem truths_agree (B : Base) (ρ ρ' : Nat → PSet B.W) : ∀ (ts : List Form),
      (∀ s ∈ ts, ∀ x, FreeIn x s → ρ x = ρ' x) → B.truths ρ ts = B.truths ρ' ts
    | [], _ => rfl
    | s :: ss, h => by
        show B.truth s ρ :: B.truths ρ ss = B.truth s ρ' :: B.truths ρ' ss
        rw [truth_agree B s ρ ρ' (fun x hx => h s (by simp) x hx),
          truths_agree B ρ ρ' ss (fun t ht x hx => h t (by simp [ht]) x hx)]
end

end Base

/-! ## 2. 严格蕴含基结构与框架 -/

/-- **严格蕴含基结构**的 `⊳` 解释：真值层面就是内容包含 `X ≤ Y`（**朴素读法**）。 -/
abbrev strictSuppI {W : Type} (X Y : PSet W) : PSet W := ⟨fun _ => X ≤ Y⟩

/-- **严格蕴含基结构**的 `⊲` 解释：`X ⊓ Y = ⊥`，或被反驳公式退化为 `⊤`。

第二个析取项不可省：`R1`（`t ⊳ ¬φ ⇒ t ⊲ φ`）在 `⟦φ⟧ = ⊤` 时正是靠它成立。 -/
abbrev strictRefutI {W : Type} (X Y : PSet W) : PSet W := ⟨fun _ => X ⊓ Y = ⊥ ∨ Y = ⊤⟩

/-- 严格蕴含基结构。 -/
abbrev strictBase (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Base :=
  { W := W, atomRel := atomRel
    suppI := fun X Y => strictSuppI X Y
    refutI := fun X Y => strictRefutI X Y }

/-- **严格蕴含框架**：`M.supp X φ ρ` 就是 `X ≤ ⟦φ⟧`（朴素蕴含读法）；
`M.refut X φ ρ` 是 `X ⊓ ⟦φ⟧ = ⊥ ∨ ⟦φ⟧ = ⊤`。

与 `Canon.frame` 同形：被支持／被反驳公式的真值取在**基结构层**。 -/
abbrev strictFrame (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Frame :=
  { W := W, atomRel := atomRel
    supp := fun X φ ρ => X ≤ (strictBase W atomRel).truth φ ρ
    refut := fun X φ ρ => X ⊓ (strictBase W atomRel).truth φ ρ = ⊥
      ∨ (strictBase W atomRel).truth φ ρ = ⊤ }

/- 严格蕴含框架与严格蕴含基结构的真值一致。

与 `Canon.frame_truth` 逐支同构：两个结构的差别只在 `supp`／`suppI` 的取法上，
而在 `⊳`／`⊲` 两处，两侧的差别恰好被 `X ≤ Y`（以及 `X ⊓ Y = ⊥ ∨ Y = ⊤`）
这个**只依赖两个真值**的命题吸收掉。 -/
mutual
  /-- 公式版。 -/
  theorem strict_frame_truth (W : Type) (atomRel : Nat → List (PSet W) → PSet W) :
      ∀ (φ : Form) (ρ : Nat → PSet W),
        (strictFrame W atomRel).truth φ ρ = (strictBase W atomRel).truth φ ρ
    | .var y, ρ => rfl
    | .atom i ts, ρ => by
        show atomRel i ((strictFrame W atomRel).truths ρ ts)
          = atomRel i ((strictBase W atomRel).truths ρ ts)
        rw [strict_frame_truths W atomRel ρ ts]
    | .bot, _ => rfl
    | .top, _ => rfl
    | .not φ, ρ => by
        show ((strictFrame W atomRel).truth φ ρ)ᶜ = ((strictBase W atomRel).truth φ ρ)ᶜ
        rw [strict_frame_truth W atomRel φ ρ]
    | .and φ ψ, ρ => by
        show (strictFrame W atomRel).truth φ ρ ⊓ (strictFrame W atomRel).truth ψ ρ
          = (strictBase W atomRel).truth φ ρ ⊓ (strictBase W atomRel).truth ψ ρ
        rw [strict_frame_truth W atomRel φ ρ, strict_frame_truth W atomRel ψ ρ]
    | .or φ ψ, ρ => by
        show (strictFrame W atomRel).truth φ ρ ⊔ (strictFrame W atomRel).truth ψ ρ
          = (strictBase W atomRel).truth φ ρ ⊔ (strictBase W atomRel).truth ψ ρ
        rw [strict_frame_truth W atomRel φ ρ, strict_frame_truth W atomRel ψ ρ]
    | .imp φ ψ, ρ => by
        show ((strictFrame W atomRel).truth φ ρ)ᶜ ⊔ (strictFrame W atomRel).truth ψ ρ
          = ((strictBase W atomRel).truth φ ρ)ᶜ ⊔ (strictBase W atomRel).truth ψ ρ
        rw [strict_frame_truth W atomRel φ ρ, strict_frame_truth W atomRel ψ ρ]
    | .all x φ, ρ => by
        apply PSet.iInter_congr
        intro X
        show (strictFrame W atomRel).truth φ (upd ρ x X)
          = (strictBase W atomRel).truth φ (upd ρ x X)
        rw [strict_frame_truth W atomRel φ (upd ρ x X)]
    | .ex x φ, ρ => by
        apply PSet.iUnion_congr
        intro X
        show (strictFrame W atomRel).truth φ (upd ρ x X)
          = (strictBase W atomRel).truth φ (upd ρ x X)
        rw [strict_frame_truth W atomRel φ (upd ρ x X)]
    | .supp t φ, ρ => by
        apply PSet.ext
        intro _
        show ((strictFrame W atomRel).truth t ρ ≤ (strictBase W atomRel).truth φ ρ)
          ↔ ((strictBase W atomRel).truth t ρ ≤ (strictBase W atomRel).truth φ ρ)
        rw [strict_frame_truth W atomRel t ρ]
    | .refut t φ, ρ => by
        apply PSet.ext
        intro _
        show ((strictFrame W atomRel).truth t ρ ⊓ (strictBase W atomRel).truth φ ρ = ⊥
              ∨ (strictBase W atomRel).truth φ ρ = ⊤)
          ↔ ((strictBase W atomRel).truth t ρ ⊓ (strictBase W atomRel).truth φ ρ = ⊥
              ∨ (strictBase W atomRel).truth φ ρ = ⊤)
        rw [strict_frame_truth W atomRel t ρ]

  /-- 列表版。 -/
  theorem strict_frame_truths (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
      (ρ : Nat → PSet W) : ∀ (ts : List Form),
        (strictFrame W atomRel).truths ρ ts = (strictBase W atomRel).truths ρ ts
    | [] => rfl
    | t :: ts => by
        show (strictFrame W atomRel).truth t ρ :: (strictFrame W atomRel).truths ρ ts
          = (strictBase W atomRel).truth t ρ :: (strictBase W atomRel).truths ρ ts
        rw [strict_frame_truth W atomRel t ρ, strict_frame_truths W atomRel ρ ts]
end

/-- **存在性定理（第二模型族）**：对任意**非空** `W` 与任意原子谓词解释 `atomRel`，
严格蕴含框架 `strictFrame W atomRel` 都是模型。

与 `Canon.isModel` 的对照是本文件的主要信息：**同一个公理系统至少有两个模型族**，
它们的 `⊳` 解释不同（`≤` 对 `suppP`），因此「哪一族是对的」不是逻辑问题而是设计取舍。
各字段逐一验证：`classical`／`agree`／`e`／`s1`／`s2`／`f3`／`f4`／`r1` 由 `≤`
与 `agree` 直接给出；`f1`／`f2` 由 `Base.truth_upd_notFree` ＋ `≤` 的任意交性质给出；
`p1`／`p2` 的要点是「被支持公式是关系式时其真值为 `⊤`」，由第三个前提直接算出。 -/
theorem strict_isModel (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W) :
    IsModel (strictFrame W atomRel) where
  nonempty := inferInstance
  classical := by
    intro p q hent ρ
    rw [strict_frame_truth W atomRel p ρ, strict_frame_truth W atomRel q ρ]
    exact hent (strictBase W atomRel) ρ
  agree := by
    intro φ ρ ρ' h
    rw [strict_frame_truth W atomRel φ ρ, strict_frame_truth W atomRel φ ρ']
    exact Base.truth_agree (strictBase W atomRel) φ ρ ρ' h
  e := by
    intro φ ψ h k X ρ
    have hφψ : (strictBase W atomRel).truth φ ρ = (strictBase W atomRel).truth ψ ρ := by
      rw [← strict_frame_truth W atomRel φ ρ, ← strict_frame_truth W atomRel ψ ρ]
      exact h ρ
    cases k
    · show X ≤ (strictBase W atomRel).truth φ ρ ↔ X ≤ (strictBase W atomRel).truth ψ ρ
      rw [hφψ]
    · show (X ⊓ (strictBase W atomRel).truth φ ρ = ⊥
            ∨ (strictBase W atomRel).truth φ ρ = ⊤)
          ↔ (X ⊓ (strictBase W atomRel).truth ψ ρ = ⊥
            ∨ (strictBase W atomRel).truth ψ ρ = ⊤)
      rw [hφψ]
  s1 := by
    intro p q ρ h
    rw [strict_frame_truth W atomRel q ρ] at h
    exact h
  s2 := by
    intro X p q ρ h₁ h₂
    rw [strict_frame_truth W atomRel p ρ, strict_frame_truth W atomRel q ρ] at h₂
    exact PSet.le_trans h₁ h₂
  f1 := by
    intro k t φ x ρ hx H
    cases k
    · show (strictFrame W atomRel).truth t ρ
        ≤ PSet.iInter (fun X : PSet W => (strictBase W atomRel).truth φ (upd ρ x X))
      refine PSet.le_iInter _ (fun X => ?_)
      have hstep : (strictFrame W atomRel).truth t (upd ρ x X)
          = (strictFrame W atomRel).truth t ρ := by
        rw [strict_frame_truth W atomRel t (upd ρ x X), strict_frame_truth W atomRel t ρ]
        exact Base.truth_upd_notFree (strictBase W atomRel) x t hx ρ X
      rw [← hstep]
      exact H X
    · haveI : Nonempty (PSet W) := ⟨⊥⟩
      by_cases htop : ∀ X : PSet W, (strictBase W atomRel).truth φ (upd ρ x X) = ⊤
      · right
        exact PSet.iInter_eq_top htop
      · left
        have hex : ∃ X : PSet W, (strictBase W atomRel).truth φ (upd ρ x X) ≠ ⊤ := by
          apply Classical.byContradiction
          intro hc
          exact htop (fun X => Classical.byContradiction (fun hX => hc ⟨X, hX⟩))
        obtain ⟨X₀, hX₀⟩ := hex
        have hstep : (strictFrame W atomRel).truth t (upd ρ x X₀)
            = (strictFrame W atomRel).truth t ρ := by
          rw [strict_frame_truth W atomRel t (upd ρ x X₀), strict_frame_truth W atomRel t ρ]
          exact Base.truth_upd_notFree (strictBase W atomRel) x t hx ρ X₀
        have hbot : (strictFrame W atomRel).truth t ρ
            ⊓ (strictBase W atomRel).truth φ (upd ρ x X₀) = ⊥ := by
          rcases H X₀ with h | h
          · rw [hstep] at h
            exact h
          · exact absurd h hX₀
        apply PSet.eq_bot_of_le
        refine PSet.le_trans (PSet.le_inf (PSet.inf_le_left _ _)
          (PSet.le_trans (PSet.inf_le_right _ _) (PSet.iInter_le _ X₀))) ?_
        exact le_of_eq_pset hbot
  f2 := by
    intro k p φ x ρ hx H
    cases k
    · have h3 : (strictFrame W atomRel).truth p (upd ρ x (ρ x))
          = (strictFrame W atomRel).truth p ρ := by
        rw [strict_frame_truth W atomRel p (upd ρ x (ρ x)), strict_frame_truth W atomRel p ρ]
        exact Base.truth_agree (strictBase W atomRel) p _ _
          (fun y _ => congrFun (upd_self_eq ρ x) y)
      have h2 : (strictBase W atomRel).truth φ (upd ρ x (ρ x))
          = (strictBase W atomRel).truth φ ρ :=
        Base.truth_upd_notFree (strictBase W atomRel) x φ hx ρ (ρ x)
      have hmid : (strictFrame W atomRel).truth p ρ ≤ (strictBase W atomRel).truth φ ρ := by
        have hrel : (strictFrame W atomRel).truth p (upd ρ x (ρ x))
            ≤ (strictBase W atomRel).truth φ (upd ρ x (ρ x)) := H (ρ x)
        rw [h3, h2] at hrel
        exact hrel
      exact PSet.le_trans (PSet.le_trans (PSet.iInter_le _ (ρ x)) (le_of_eq_pset h3)) hmid
    · haveI : Nonempty (PSet W) := ⟨⊥⟩
      by_cases htop : (strictBase W atomRel).truth φ ρ = ⊤
      · right
        exact htop
      · left
        have hall : ∀ X : PSet W, (strictFrame W atomRel).truth p (upd ρ x X)
            ≤ ((strictBase W atomRel).truth φ ρ)ᶜ := by
          intro X
          have hX : (strictFrame W atomRel).truth p (upd ρ x X)
                ⊓ (strictBase W atomRel).truth φ (upd ρ x X) = ⊥
              ∨ (strictBase W atomRel).truth φ (upd ρ x X) = ⊤ := H X
          rw [Base.truth_upd_notFree (strictBase W atomRel) x φ hx ρ X] at hX
          rcases hX with h | h
          · exact PSet.le_compl_of_inf_eq_bot h
          · exact absurd h htop
        have hcompl : (strictFrame W atomRel).truth (Form.all x p) ρ
            ≤ ((strictBase W atomRel).truth φ ρ)ᶜ :=
          PSet.le_trans (PSet.iInter_le _ ⊥) (hall ⊥)
        apply PSet.eq_bot_of_le
        have hchain : (strictFrame W atomRel).truth (Form.all x p) ρ
              ⊓ (strictBase W atomRel).truth φ ρ
            ≤ ((strictBase W atomRel).truth φ ρ)ᶜ ⊓ (strictBase W atomRel).truth φ ρ :=
          PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) hcompl) (PSet.inf_le_right _ _)
        rw [PSet.compl_inf_self] at hchain
        exact hchain
  f3 := by
    intro k X Z φ ρ h₁ h₂
    cases k
    · show X ⊓ Z ≤ (strictBase W atomRel).truth φ ρ
      exact PSet.le_trans (PSet.inf_le_left _ _) h₁
    · show (X ⊓ Z) ⊓ (strictBase W atomRel).truth φ ρ = ⊥
          ∨ (strictBase W atomRel).truth φ ρ = ⊤
      rcases h₁ with h₁ | h₁
      · rcases h₂ with h₂ | h₂
        · left
          apply PSet.eq_bot_of_le
          refine PSet.le_trans (PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _)
            (PSet.inf_le_left _ _)) (PSet.inf_le_right _ _)) ?_
          exact le_of_eq_pset h₁
        · right
          exact h₂
      · right
        exact h₁
  f4 := by
    intro k X φ ψ ρ h₁ h₂
    cases k
    · show X ≤ (strictBase W atomRel).truth φ ρ ⊓ (strictBase W atomRel).truth ψ ρ
      exact PSet.le_inf h₁ h₂
    · show X ⊓ ((strictBase W atomRel).truth φ ρ ⊓ (strictBase W atomRel).truth ψ ρ) = ⊥
          ∨ (strictBase W atomRel).truth φ ρ ⊓ (strictBase W atomRel).truth ψ ρ = ⊤
      rcases h₁ with h₁ | h₁
      · left
        apply PSet.eq_bot_of_le
        refine PSet.le_trans (PSet.le_inf (PSet.inf_le_left _ _)
          (PSet.le_trans (PSet.inf_le_right _ _) (PSet.inf_le_left _ _))) ?_
        exact le_of_eq_pset h₁
      · rcases h₂ with h₂ | h₂
        · left
          rw [h₁, PSet.top_inf_eq]
          exact h₂
        · right
          rw [h₁, h₂, PSet.top_inf_eq]
  r1 := by
    intro X φ ρ h
    have h' : X ≤ ((strictBase W atomRel).truth φ ρ)ᶜ := h
    left
    apply PSet.eq_bot_of_le
    refine PSet.le_trans (PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) h')
      (PSet.inf_le_right _ _)) ?_
    rw [PSet.compl_inf_self]
    exact PSet.le_refl _
  p1 := by
    intro kR kS a b c d f ρ _ _ h₃
    have keyS : (strictBase W atomRel).truth (Kind.form kS (.and c d) f) ρ = ⊤ := by
      cases kS
      · have h := h₃
        rw [strict_frame_truth W atomRel c ρ, strict_frame_truth W atomRel d ρ] at h
        apply PSet.eq_top_of_le
        intro _ _
        show (strictBase W atomRel).truth (Form.and c d) ρ
          ≤ (strictBase W atomRel).truth f ρ
        exact h
      · have h := h₃
        rw [strict_frame_truth W atomRel c ρ, strict_frame_truth W atomRel d ρ] at h
        apply PSet.eq_top_of_le
        intro _ _
        show (strictBase W atomRel).truth (Form.and c d) ρ
            ⊓ (strictBase W atomRel).truth f ρ = ⊥
          ∨ (strictBase W atomRel).truth f ρ = ⊤
        exact h
    cases kR
    · show (strictFrame W atomRel).truth a ρ ⊓ (strictFrame W atomRel).truth b ρ
        ≤ (strictBase W atomRel).truth (Kind.form kS (.and c d) f) ρ
      rw [keyS]
      exact PSet.le_top _
    · show (strictFrame W atomRel).truth a ρ ⊓ (strictFrame W atomRel).truth b ρ
          ⊓ (strictBase W atomRel).truth (Kind.form kS (.and c d) f) ρ = ⊥
        ∨ (strictBase W atomRel).truth (Kind.form kS (.and c d) f) ρ = ⊤
      exact Or.inr keyS
  p2 := by
    intro kR kS a c f x ρ hx _ h₂
    have keyS : (strictBase W atomRel).truth (Kind.form kS (.all x c) f) ρ = ⊤ := by
      cases kS
      · have h := h₂
        rw [strict_frame_truth W atomRel (Form.all x c) ρ] at h
        apply PSet.eq_top_of_le
        intro _ _
        show (strictBase W atomRel).truth (Form.all x c) ρ
          ≤ (strictBase W atomRel).truth f ρ
        exact h
      · have h := h₂
        rw [strict_frame_truth W atomRel (Form.all x c) ρ] at h
        apply PSet.eq_top_of_le
        intro _ _
        show (strictBase W atomRel).truth (Form.all x c) ρ
            ⊓ (strictBase W atomRel).truth f ρ = ⊥
          ∨ (strictBase W atomRel).truth f ρ = ⊤
        exact h
    cases kR
    · show (strictFrame W atomRel).truth (Form.all x a) ρ
        ≤ (strictBase W atomRel).truth (Kind.form kS (.all x c) f) ρ
      rw [keyS]
      exact PSet.le_top _
    · show (strictFrame W atomRel).truth (Form.all x a) ρ
          ⊓ (strictBase W atomRel).truth (Kind.form kS (.all x c) f) ρ = ⊥
        ∨ (strictBase W atomRel).truth (Kind.form kS (.all x c) f) ρ = ⊤
      exact Or.inr keyS

/-! ## 3. 无条件不变量与三条推论 -/

/-- **严格蕴含框架上的支持-蕴含不变量（无条件）**：对**全量** `Derivable`
（含元规则 `E`、无任何片段限制），可推导的支持式在严格蕴含基结构上满足内容包含。

证明只有一行实质内容：`strict_isModel` ＋ `Derivable.soundness` 给出
`M ⊨ p ⊳ q`，而 `M.supp` 按定义就是 `≤`（`Derivable.supp_of_valid`），
再用 `strict_frame_truth` 把两侧搬回基结构层。
**这是本工程第一条对全量 `Derivable` 无条件成立的支持-蕴含不变量。** -/
theorem strict_supp_le (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    {p q : Form} (h : Derivable (p ⊳ q)) :
    ∀ ρ : Nat → PSet W,
      (strictBase W atomRel).truth p ρ ≤ (strictBase W atomRel).truth q ρ := by
  intro ρ
  have hM : IsModel (strictFrame W atomRel) := strict_isModel W atomRel
  have hv : (strictFrame W atomRel).truth (p ⊳ q) ρ = ⊤ :=
    Derivable.soundness (strictFrame W atomRel) hM h ρ
  have hs : (strictFrame W atomRel).supp ((strictFrame W atomRel).truth p ρ) q ρ :=
    Derivable.supp_of_valid (strictFrame W atomRel) hM hv
  rw [strict_frame_truth W atomRel p ρ] at hs
  exact hs

/-- **严格蕴含框架上的支持传递：分量不等式**（全量 `Derivable`、**无条件**）。
两条前提各给一次 `strict_supp_le`，串联即得。这个"链"是
[`Frontier/NoRelFragment.lean`] 中「结论的两个分量关系自由 ⇒ 典范框架有效」的直接来源：
**中间公式可以任意**（可以含关系子公式）。 -/
theorem strict_supp_le_trans (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    {a b c : Form} (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c)) :
    ∀ ρ : Nat → PSet W,
      (strictBase W atomRel).truth a ρ ≤ (strictBase W atomRel).truth c ρ :=
  fun ρ => PSet.le_trans (strict_supp_le W atomRel h₁ ρ) (strict_supp_le W atomRel h₂ ρ)

/-- **定稿设计理由的机器验证**：在严格蕴含框架里，支持传递的**规则形式**
（前提在框架中有效则结论有效）成立——这正是 `Model/Canonical.lean` 开头
「语义不能退化为朴素的 `X ≤ Y` 蕴含读法（否则支持传递将成为有效式）」所述的反事实。

证明不需要任何赋值：`M.truth (a ⊳ b) ρ = ⊤` 就是 `⟦a⟧ρ ≤ ⟦b⟧ρ`，
两条合起来即得结论的真值为 `⊤`。 -/
theorem strict_transitivity_rule_valid (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
    {a b c : Form} (h₁ : (strictFrame W atomRel).Valid (a ⊳ b))
    (h₂ : (strictFrame W atomRel).Valid (b ⊳ c)) :
    (strictFrame W atomRel).Valid (a ⊳ c) := by
  intro ρ
  apply PSet.eq_top_of_le
  intro w _
  have hab : (strictFrame W atomRel).truth a ρ ≤ (strictBase W atomRel).truth b ρ :=
    (PSet.const_eq_top_iff w).mp (h₁ ρ)
  have hbc : (strictBase W atomRel).truth b ρ ≤ (strictBase W atomRel).truth c ρ := by
    rw [← strict_frame_truth W atomRel b ρ]
    exact (PSet.const_eq_top_iff w).mp (h₂ ρ)
  exact PSet.le_trans hab hbc

/-- **严格蕴含框架上的支持传递（可推导版）**：两个前提都可推导时结论在框架中有效。
（与上一条不同：这里只要求前提**可推导**，不要求它们在框架中有效。） -/
theorem strict_transitivity_valid (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b c : Form}
    (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c)) :
    (strictFrame W atomRel).Valid (a ⊳ c) := by
  intro ρ
  have hle : (strictFrame W atomRel).truth a ρ ≤ (strictBase W atomRel).truth c ρ := by
    rw [strict_frame_truth W atomRel a ρ]
    exact strict_supp_le_trans W atomRel h₁ h₂ ρ
  exact PSet.eq_top_of_le (fun _ _ => hle)

/-- **严格蕴含框架上的 S7（可推导版）**：两个前提都可推导时结论在框架中有效。 -/
theorem strict_s7_valid (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    {a b φ ψ : Form} (h₁ : Derivable (a ⊳ φ)) (h₂ : Derivable (b ⊳ ψ)) :
    (strictFrame W atomRel).Valid (Form.and a b ⊳ Form.and φ ψ) := by
  intro ρ
  have hb : (strictBase W atomRel).truth (Form.and φ ψ) ρ
      = (strictBase W atomRel).truth φ ρ ⊓ (strictBase W atomRel).truth ψ ρ := rfl
  have hle : (strictFrame W atomRel).truth (Form.and a b) ρ
      ≤ (strictBase W atomRel).truth (Form.and φ ψ) ρ := by
    rw [hb, strict_frame_truth W atomRel (Form.and a b) ρ]
    refine PSet.le_inf ?_ ?_
    · exact PSet.le_trans (PSet.le_trans (PSet.inf_le_left _ _)
        (strict_supp_le W atomRel h₁ ρ)) (PSet.le_refl _)
    · exact PSet.le_trans (PSet.le_trans (PSet.inf_le_right _ _)
        (strict_supp_le W atomRel h₂ ρ)) (PSet.le_refl _)
  exact PSet.eq_top_of_le (fun _ _ => hle)

end EvidenceLogic
