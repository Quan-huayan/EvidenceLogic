/-
# 前沿：**关系自由片段**上的支持-蕴含不变量与两条 N3 障碍的收窄

本文件**不修改任何已有文件**，只在既有 `import` 之上补一批新结论。
它把 `Model/Strict.lean` 的无条件不变量经「关系自由公式真值与 `suppI`／`refutI`
无关」这座桥搬到**典范框架**上，从而在**全量** `Derivable`（允许任意 `E`）下
拿到一个**无条件**的片段结果，并把两条尚未攻下的 N3 障碍**收窄到关系子公式**。

## 0. 这条结果的强度与**对照表**（务必连同结论一起读，不要夸大）

| 结果 | 片段／假设 | 结论 |
|---|---|---|
| `EFree.noE_supp_le` | 禁用 `E`（`Derivable₀`），任意公式 | 典范框架上 `⟦p⟧ ≤ ⟦q⟧` |
| `RestrictedE.supp_le₁_canon` | 受限 `E`（源公式 `NoRel`），任意公式 | 同上 |
| `Conditional.supp_le_of_transferLemma_canon` | **全量 `Derivable`**，但假设 `TransferLemma` | 同上 |
| **本文件 `supp_le_canon_of_noRel`** | **全量 `Derivable`（无假设）**，但 `p`、`q` 都 `NoRel` | 同上 |
| **`Model/Strict.lean` `strict_supp_le`** | **全量 `Derivable`（无假设）**，任意公式，但在**严格蕴含框架**上 | 严格框架上 `⟦p⟧ ≤ ⟦q⟧` |

即：本文件用「分量关系自由」换掉了 `Conditional.lean` 的 `TransferLemma` 假设——
**这是一条新的、与 `TransferLemma` 无关的路线**，而不是它的推论。

**注意**：`NoRel` 是一个**语义上很强**的限制（分量里不得出现 `⊳`／`⊲`，包括作为
原子谓词的参数），因此本文件**不是**「支持传递／S7 不可容许」的证明，也**没有**
解决公开的相合性问题。它的确切贡献是第 3 节的两条**障碍**：关系自由区的反模型
被**空前地**排除掉了，剩下的窗口被压缩到「至少一个分量含关系子公式」。

## 1. 文件内容

1. 第 1 节：`truth_noRel_congr`——`NoRel` 公式的真值与 `suppI`／`refutI` 的取法无关
   （`RestrictedE.truth_botBase_eq_canon` 与 `Transfer.truth_projBase₁_eq_canon`
   都是它的特例），以及到 `Canon.base`／`strictBase` 的两条推论；
2. 第 2 节：`supp_le_canon_of_noRel`——**全量 `Derivable` ＋ `NoRel` 分量**的
   条件零假设支持-蕴含不变量（典范基结构版与典范框架版）；
3. 第 3 节：**结论分量**关系自由区——`transitivity_le_canon_of_noRel`／
   `transitivity_valid_canon_of_noRel`（**中间公式可以任意**，由 `strict_supp_le_trans` 串联）、
   `s7_valid_canon_of_noRel`，以及两条同形的必要条件
   `countermodel_needs_rel`／`s7_countermodel_needs_rel`（**结论的某个分量必须含关系子公式**）。

## 2. 为什么第 2、3 节成立（一句话）

`strict_supp_le` 给出**严格蕴含基结构**上的 `⟦p⟧ ≤ ⟦q⟧`；而 `NoRel` 公式的真值
与 `suppI`／`refutI` 无关（第 1 节），于是这条不等式在**典范基结构**上同样成立。
第 3 节的支持传递版更进一步：把 `strict_supp_le` 对两条前提各用一次并**串联**，
直接得到 `⟦a⟧_strict ≤ ⟦c⟧_strict`——**完全不需要中间公式 `b` 关系自由**。
关键点是：严格框架的 `supp` 内容**没有任何析取项**，所以这里**不需要**典范框架
那条「三个析取项」的分析——`suppP` 的那个 `Y = ⊤` 析取项（`Analysis/Structure.lean`
第六节指出它是唯一破坏传递性的装置）在关系自由分量上被整条绕开。

## 3. 技术注记

* 不用 `induction` 于 `Form`；`mutual` 块内递归调用**显式给出**公式隐变量；
* `Canon.base W atomRel` 与 `mkBase W atomRel Canon.suppI Canon.refutI` 是**定义性**
  相等的（两个结构字面量的字段相同），故第 1 节的推论直接 `exact`；
* 未使用的绑定一律写 `_`，不使用 `sorry`／`axiom`／`admit`。
-/
import EvidenceLogic.Model.Strict
import EvidenceLogic.Model.Threshold
import EvidenceLogic.Frontier.RestrictedE

namespace EvidenceLogic

open PSet

open scoped Classical

/-! ## 1. 关系自由公式的真值与 `suppI`／`refutI` 无关 -/

/-- 两个共用 `W` 与 `atomRel`、只差 `suppI`／`refutI` 的基结构。 -/
abbrev mkBase (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
    (suppI refutI : PSet W → PSet W → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := suppI, refutI := refutI }

/- **`NoRel` 公式的真值与 `suppI`／`refutI` 的取法无关**。

`NoRel` 把 `.supp`／`.refut` 两个构造子排除掉，而这两支正是唯一用到
`suppI`／`refutI` 的地方；其余各支逐一同构。对公式与列表写成 `mutual`
（`.atom` 情形需要列表版）；递归调用显式给出公式隐变量。 -/
mutual
  /-- 公式版。 -/
  theorem truth_noRel_congr {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
      (s₁ r₁ s₂ r₂ : PSet W → PSet W → PSet W) :
      ∀ {φ : Form}, NoRel φ → ∀ ρ : Nat → PSet W,
        (mkBase W atomRel s₁ r₁).truth φ ρ = (mkBase W atomRel s₂ r₂).truth φ ρ
    | .var _, _, _ => rfl
    | .atom i ts, h, ρ => by
        show atomRel i ((mkBase W atomRel s₁ r₁).truths ρ ts)
          = atomRel i ((mkBase W atomRel s₂ r₂).truths ρ ts)
        rw [truth_noRel_congr_list atomRel s₁ r₁ s₂ r₂ ρ h]
    | .bot, _, _ => rfl
    | .top, _, _ => rfl
    | .not φ, h, ρ => by
        show ((mkBase W atomRel s₁ r₁).truth φ ρ)ᶜ = ((mkBase W atomRel s₂ r₂).truth φ ρ)ᶜ
        rw [truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := φ) h ρ]
    | .and φ ψ, h, ρ => by
        show (mkBase W atomRel s₁ r₁).truth φ ρ ⊓ (mkBase W atomRel s₁ r₁).truth ψ ρ
          = (mkBase W atomRel s₂ r₂).truth φ ρ ⊓ (mkBase W atomRel s₂ r₂).truth ψ ρ
        rw [truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := φ) h.1 ρ,
          truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := ψ) h.2 ρ]
    | .or φ ψ, h, ρ => by
        show (mkBase W atomRel s₁ r₁).truth φ ρ ⊔ (mkBase W atomRel s₁ r₁).truth ψ ρ
          = (mkBase W atomRel s₂ r₂).truth φ ρ ⊔ (mkBase W atomRel s₂ r₂).truth ψ ρ
        rw [truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := φ) h.1 ρ,
          truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := ψ) h.2 ρ]
    | .imp φ ψ, h, ρ => by
        show ((mkBase W atomRel s₁ r₁).truth φ ρ)ᶜ ⊔ (mkBase W atomRel s₁ r₁).truth ψ ρ
          = ((mkBase W atomRel s₂ r₂).truth φ ρ)ᶜ ⊔ (mkBase W atomRel s₂ r₂).truth ψ ρ
        rw [truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := φ) h.1 ρ,
          truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := ψ) h.2 ρ]
    | .all x φ, h, ρ => by
        apply PSet.iInter_congr
        intro X
        show (mkBase W atomRel s₁ r₁).truth φ (upd ρ x X)
          = (mkBase W atomRel s₂ r₂).truth φ (upd ρ x X)
        exact truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := φ) h (upd ρ x X)
    | .ex x φ, h, ρ => by
        apply PSet.iUnion_congr
        intro X
        show (mkBase W atomRel s₁ r₁).truth φ (upd ρ x X)
          = (mkBase W atomRel s₂ r₂).truth φ (upd ρ x X)
        exact truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := φ) h (upd ρ x X)
    | .supp _ _, h, _ => absurd h noRel_supp
    | .refut _ _, h, _ => absurd h noRel_refut

  /-- 列表版。 -/
  theorem truth_noRel_congr_list {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
      (s₁ r₁ s₂ r₂ : PSet W → PSet W → PSet W) (ρ : Nat → PSet W) :
      ∀ {ts : List Form}, NoRelList ts →
        (mkBase W atomRel s₁ r₁).truths ρ ts = (mkBase W atomRel s₂ r₂).truths ρ ts
    | [], _ => rfl
    | t :: ts, h => by
        show (mkBase W atomRel s₁ r₁).truth t ρ :: (mkBase W atomRel s₁ r₁).truths ρ ts
          = (mkBase W atomRel s₂ r₂).truth t ρ :: (mkBase W atomRel s₂ r₂).truths ρ ts
        rw [truth_noRel_congr atomRel s₁ r₁ s₂ r₂ (φ := t) h.1 ρ,
          truth_noRel_congr_list atomRel s₁ r₁ s₂ r₂ ρ h.2]
end

/-- `NoRel` 公式在**任意**基结构与典范基结构上真值相同。 -/
theorem truth_noRel_eq_canon {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    (s r : PSet W → PSet W → PSet W) {φ : Form} (h : NoRel φ) (ρ : Nat → PSet W) :
    (mkBase W atomRel s r).truth φ ρ = (Canon.base W atomRel).truth φ ρ :=
  truth_noRel_congr atomRel s r Canon.suppI Canon.refutI (φ := φ) h ρ

/-- 严格蕴含基结构与典范基结构在 `NoRel` 公式上真值相同（第 2 节的桥）。 -/
theorem truth_strictBase_eq_canon {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {φ : Form} (h : NoRel φ) (ρ : Nat → PSet W) :
    (strictBase W atomRel).truth φ ρ = (Canon.base W atomRel).truth φ ρ :=
  truth_noRel_eq_canon atomRel (fun X Y => strictSuppI X Y) (fun X Y => strictRefutI X Y) h ρ

/-- `Canon.base` 与 `strictBase` 在 `NoRel` 公式上真值相同（同一事实的另一种写法）。 -/
theorem truth_canon_eq_strictBase {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {φ : Form} (h : NoRel φ) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth φ ρ = (strictBase W atomRel).truth φ ρ :=
  (truth_strictBase_eq_canon atomRel h ρ).symm

/-! ## 2. 关系自由分量上的支持-蕴含不变量（全量 `Derivable`，无假设） -/

/-- **支持-蕴含不变量（关系自由分量，典范基结构，无条件）**：对**全量** `Derivable`
（含元规则 `E`、无任何片段限制），若支持式 `p ⊳ q` 的两个分量都**不含关系子公式**，
则该不等式在典范基结构上成立。

证明：`strict_supp_le` 给出严格蕴含基结构上的不等式，再由
`truth_strictBase_eq_canon`（第 1 节）把它搬到典范基结构。**不使用 `TransferLemma`。** -/
theorem supp_le_canon_base_of_noRel (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {p q : Form} (h : Derivable (p ⊳ q))
    (hp : NoRel p) (hq : NoRel q) :
    ∀ ρ : Nat → PSet W,
      (Canon.base W atomRel).truth p ρ ≤ (Canon.base W atomRel).truth q ρ := by
  intro ρ
  have hle := strict_supp_le W atomRel h ρ
  rw [truth_strictBase_eq_canon atomRel hp ρ, truth_strictBase_eq_canon atomRel hq ρ] at hle
  exact hle

/-- **支持-蕴含不变量（关系自由分量，典范框架，无条件）**：形状与
`RestrictedE.supp_le₁_canon`／`Conditional.supp_le_of_transferLemma_canon` 一致，
但**没有任何假设**（后者需要 `TransferLemma`）且**不限制 `E`**（前者需要受限 `E`），
代价是两个分量必须 `NoRel`。 -/
theorem supp_le_canon_of_noRel (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {p q : Form} (h : Derivable (p ⊳ q))
    (hp : NoRel p) (hq : NoRel q) :
    ∀ ρ : Nat → PSet W,
      (Canon.frame W atomRel).truth p ρ ≤ (Canon.frame W atomRel).truth q ρ := by
  intro ρ
  rw [Canon.frame_truth W atomRel p ρ, Canon.frame_truth W atomRel q ρ]
  exact supp_le_canon_base_of_noRel W atomRel h hp hq ρ

/-! ## 3. 两条 N3 障碍的收窄：**结论的两个分量**必须含关系子公式 -/

/-- **支持传递：结论分量的不等式（全量 `Derivable`、无条件）**：只要**结论**
`a ⊳ c` 的两个分量关系自由，就有 `⟦a⟧ ≤ ⟦c⟧`，而**中间公式 `b` 可以任意**
（可以含关系子公式）。

证明走 [`Model/Strict.lean`]：`strict_supp_le_trans` 在**严格蕴含框架**上把两条前提串成
`⟦a⟧_strict ≤ ⟦c⟧_strict`（那里没有任何析取项），再把两侧用
`truth_strictBase_eq_canon`（第 1 节）搬回典范基结构。

**这严格强于**只用典范框架能得到的版本（那一版还要求 `NoRel b`）：
`a`、`c` 是**结论**的分量，`b` 只是中间项。 -/
theorem transitivity_le_canon_of_noRel (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b c : Form}
    (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c)) (ha : NoRel a) (hc : NoRel c) :
    ∀ ρ : Nat → PSet W,
      (Canon.base W atomRel).truth a ρ ≤ (Canon.base W atomRel).truth c ρ := by
  intro ρ
  have hchain := strict_supp_le_trans W atomRel h₁ h₂ ρ
  rwa [truth_strictBase_eq_canon atomRel ha ρ, truth_strictBase_eq_canon atomRel hc ρ] at hchain

/-- **支持传递（结论分量关系自由区）**：若**结论** `a ⊳ c` 的两个分量都关系自由，
则 `a ⊳ c` 在**一切**典范框架中有效——于是 `not_derivable_of_countermodel`
在这条路线上**走不通**。

注意假设里**没有** `NoRel b`：中间公式可以任意。 -/
theorem transitivity_valid_canon_of_noRel (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b c : Form}
    (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c)) (ha : NoRel a) (hc : NoRel c) :
    (Canon.frame W atomRel).Valid (a ⊳ c) := by
  intro ρ
  have hle : (Canon.frame W atomRel).truth a ρ ≤ (Canon.base W atomRel).truth c ρ := by
    rw [Canon.frame_truth W atomRel a ρ]
    exact transitivity_le_canon_of_noRel W atomRel h₁ h₂ ha hc ρ
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth a ρ)
    ((Canon.base W atomRel).truth c ρ)⟩ : PSet W) = ⊤
  exact PSet.eq_top_of_le (fun _ _ => Or.inl hle)

/-- **S7（关系自由区）**：若四条分量子公式都关系自由，则 `(a ∧ b) ⊳ (φ ∧ ψ)`
在**一切**典范框架中有效。

与支持传递不同，这里必须要求 `a`、`b` 也关系自由：第 2 节给出的是
**无析取项**的强不等式 `⟦a⟧ ≤ ⟦φ⟧`、`⟦b⟧ ≤ ⟦ψ⟧`，合取即得。 -/
theorem s7_valid_canon_of_noRel (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b φ ψ : Form}
    (h₁ : Derivable (a ⊳ φ)) (h₂ : Derivable (b ⊳ ψ))
    (ha : NoRel a) (hφ : NoRel φ) (hb : NoRel b) (hψ : NoRel ψ) :
    (Canon.frame W atomRel).Valid (Form.and a b ⊳ Form.and φ ψ) := by
  intro ρ
  have hbase : (Canon.base W atomRel).truth (Form.and φ ψ) ρ
      = (Canon.frame W atomRel).truth φ ρ ⊓ (Canon.frame W atomRel).truth ψ ρ := by
    rw [show (Canon.base W atomRel).truth (Form.and φ ψ) ρ
        = (Canon.base W atomRel).truth φ ρ ⊓ (Canon.base W atomRel).truth ψ ρ from rfl,
      ← Canon.frame_truth W atomRel φ ρ, ← Canon.frame_truth W atomRel ψ ρ]
  have hle₁ : (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth φ ρ :=
    supp_le_canon_of_noRel W atomRel h₁ ha hφ ρ
  have hle₂ : (Canon.frame W atomRel).truth b ρ ≤ (Canon.frame W atomRel).truth ψ ρ :=
    supp_le_canon_of_noRel W atomRel h₂ hb hψ ρ
  have hleft : (Canon.frame W atomRel).truth (Form.and a b) ρ
      ≤ (Canon.base W atomRel).truth (Form.and φ ψ) ρ := by
    rw [hbase]
    exact PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) hle₁)
      (PSet.le_trans (PSet.inf_le_right _ _) hle₂)
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth (Form.and a b) ρ)
    ((Canon.base W atomRel).truth (Form.and φ ψ) ρ)⟩ : PSet W) = ⊤
  exact PSet.eq_top_of_le (fun _ _ => Or.inl hleft)

/-- **反模型的必要条件（支持传递，机器验证）**：若 `a ⊳ c` 在某个典范框架中不有效，
而两个前提都可推导，则**结论的两个分量 `a`、`c` 不可能都**关系自由——
即反模型**必须**让 `a` 或 `c` 含关系子公式；中间公式 `b` 不受此限制。 -/
theorem countermodel_needs_rel (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b c : Form}
    (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c))
    (h : ¬ (Canon.frame W atomRel).Valid (a ⊳ c)) : ¬ (NoRel a ∧ NoRel c) :=
  fun hac => h (transitivity_valid_canon_of_noRel W atomRel h₁ h₂ hac.1 hac.2)

/-- **反模型的必要条件（S7，机器验证）**：与上一条**同形**——结论
`(a ∧ b) ⊳ (φ ∧ ψ)` 的两个分量不可能都关系自由
（`NoRel (a ∧ b)` 按定义就是 `NoRel a ∧ NoRel b`）。 -/
theorem s7_countermodel_needs_rel (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b φ ψ : Form}
    (h₁ : Derivable (a ⊳ φ)) (h₂ : Derivable (b ⊳ ψ))
    (h : ¬ (Canon.frame W atomRel).Valid (Form.and a b ⊳ Form.and φ ψ)) :
    ¬ (NoRel (Form.and a b) ∧ NoRel (Form.and φ ψ)) :=
  fun hrel => h (s7_valid_canon_of_noRel W atomRel h₁ h₂
    hrel.1.1 hrel.2.1 hrel.1.2 hrel.2.2)

/-- S7 反模型必要条件的**展开写法**（与 4 条分量子公式一一对应，便于与其它障碍并读）。 -/
theorem s7_countermodel_needs_rel' (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b φ ψ : Form}
    (h₁ : Derivable (a ⊳ φ)) (h₂ : Derivable (b ⊳ ψ))
    (h : ¬ (Canon.frame W atomRel).Valid (Form.and a b ⊳ Form.and φ ψ)) :
    ¬ (NoRel a ∧ NoRel φ ∧ NoRel b ∧ NoRel ψ) :=
  fun hrel => s7_countermodel_needs_rel W atomRel h₁ h₂ h
    ⟨⟨hrel.1, hrel.2.2.1⟩, ⟨hrel.2.1, hrel.2.2.2⟩⟩

/-! ### 由阈值族得到的第三条必要条件（「被支持公式在每个非典范阈值模型中都为 `⊤`」）

`System/NonAdmissible.lean` 第十二节已把反例处**中间项真值**逼成 `⊤`
（`support_transitivity_middle_truth_top`）。把**阈值族**（`Model/Threshold.lean`）接上去，
可以再逼一层：若中间公式 `b` **关系自由**（于是 `⟦b⟧` 与 `suppI`／`refutI` 无关），
则在**每一个**阈值 `U ≠ ⊤` 的模型里，**被支持公式 `c` 的真值都必须是 `⊤`**。 -/

/-- **第三条必要条件（机器验证）**：设 `Derivable (b ⊳ c)`、`b` 关系自由，
且在典范基结构上 `⟦b⟧ρ = ⊤`（反例处由 `support_transitivity_middle_truth_top` 被迫成立）。
则对**任意** `U ≠ ⊤`，都有 `(thBase W atomRel U).truth c ρ = ⊤`。

理由：`th_supp_le` 给出 `thSuppP U ⟦b⟧_{th_U} ⟦c⟧_{th_U}`；由 `NoRel b` 把
`⟦b⟧_{th_U}` 换成 `⟦b⟧_C = ⊤`，三项析取中 `⊤ = U` 被 `U ≠ ⊤` 排除，剩下即得。

**读法**：这是对 `c` 的一条**跨模型**限制——若 `c` 关系自由，则
`⟦c⟧_{th_U} = ⟦c⟧_C = ⊤`，与「反例处 `⟦c⟧_C ≠ ⊤`」直接矛盾；
故 `c` 必须含关系子公式，且它在**所有**非典范阈值模型中都取全集。 -/
theorem canon_middle_noRel_supported_top_in_threshold (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {b c : Form} (h₂ : Derivable (b ⊳ c))
    (hb : NoRel b) (ρ : Nat → PSet W)
    (hb_top : (Canon.base W atomRel).truth b ρ = ⊤) (U : PSet W) (hU : U ≠ ⊤) :
    (thBase W atomRel U).truth c ρ = ⊤ := by
  have h1 := th_supp_le W atomRel U h₂ ρ
  have hb' : (thBase W atomRel U).truth b ρ = ⊤ := by
    rw [truth_noRel_eq_canon atomRel (fun X Y => (⟨fun _ => thSuppP U X Y⟩ : PSet W))
      (fun X Y => (⟨fun _ => thRefutP U X Y⟩ : PSet W)) (φ := b) hb ρ]
    exact hb_top
  rw [hb'] at h1
  rcases h1 with h | h | h
  · exact PSet.eq_top_of_le h
  · exact absurd h.symm hU
  · exact h

/-! ## 4. 与既有障碍链的关系（不要夸大）

* `System/NonAdmissible.lean` 第十一节的两条必然条件
  （`support_transitivity_middle_truth_top`：反例处 `⟦b⟧ = ⊤`；
  `countermodel_formula_truth_ne_top`：反例处 `⟦c⟧ ≠ ⊤`）说的是**真值形状**；
  本文件的必要条件说的是**语法形状**：**结论的两个分量**中必须有一个含关系子公式
  （中间公式 `b` 反而可以任意）。两者**互相独立**，可以同时对反例施加限制；
* `RestrictedE`／`Conditional` 与本文件是**三条互不包含**的路线：
  前者限制 `E` 的源公式，中者以 `TransferLemma` 为假设，本文件要求**结论分量** `NoRel`；
* 因此本文件**没有**攻下账本中剩下两条（`docs/主要结果.md` 第 6 节），
  它做的是**把窗口关小**：现在任何反例都必须同时满足
  「中间公式真值为 `⊤`」与「结论的某个分量含关系子公式」。
-/

end EvidenceLogic
