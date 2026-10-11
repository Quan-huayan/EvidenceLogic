/-
# TrackI：**投影基结构**与「转移引理」的可证半边

本文件**不修改任何已有文件**，只在既有 `import` 之上补一批新结论。
它把 `EvidenceLogic/RestrictedE.lean`（受限 `E` 片段）沿**另一条轴**再扩一格。

## 1. 背景

`RestrictedE` 的核心不变量 `supp_le₁_canon` 归纳到 `Derivable₁.e` 时，只剩
「洞在顶层」那一支要闭合：那里只有 `Derivable₁ γ` 与 `γ ⊣⊢ ψ`（`ψ = a ⊳ b`）。
`RestrictedE` 能闭合它靠的是 `NoRel φ`：关系自由公式在「全空基结构」与「典范基结构」
上真值相同（`truth_botBase_eq_canon`），于是得到 `⊤ ≤ ⊥`。

一旦源公式含关系子公式，`botBase` 那条路就断了。取而代之的问题是**转移引理**：

> 两个关系式**经典等价**（`u ⊳ v ⊣⊢ u' ⊳ v'`）时，
> 分量在**典范基结构**上的真值是否被迫相等？

## 2. 边界刻画（务必连同结论一起读，不要夸大）

* 第 1、2 节是**可证的那一半**：原型是 `projBase₁`／`projBase₂`（分别取第一／第二投影的
  基结构）加两条基无关性引理，由此得到 `cequiv_rel_components_of_noRel`。
  它把 `RestrictedE` 的片段沿**另一条轴**再扩一格：原先只允许 `E` 的源公式关系自由
  （`NoRel`），现在还可以处理「源是**分量关系自由**的关系式、目标是**分量关系自由**的
  关系式」的 `E` 步；
* 第 3 节是**断掉的那一半**：一旦分量含关系子公式，投影基结构与典范基结构对同一公式的
  真值**不再一致**（因为典范框架的真值走 `suppP`，而投影基走投影函数），该方法失效。
  一般转移引理 `TransferLemma` 只作为 `Prop` 陈述，本文件**不证**；
* 本文件**不**声称一般转移引理成立，也**不**声称它归约到 `TruthPropagation`。
  归约尝试的结论见第 4 节：`TransferLemma` 的前提是**两个关系式之间**的经典等价，
  而 `TruthPropagation` 的前提是 `Derivable (t ⊳ c)` 加典范真值 `⟦t⟧ = ⊤`；
  两者之间没有可用的桥梁，故无条件归约写不出来。第 4 节给出
  ①能证出的最接近的一半（`holeAtTop_of_transferLemma`）、
  ②机器验证的形态见证（`holeAtTop_source_need_not_be_supp`）、③卡住的确切位置。

## 3. 文件内容

1. `projBase₁`／`projBase₂` 与 `truth_projBase₁_eq_canon`／`truth_projBase₂_eq_canon`
   （照 `truth_botBase_eq_canon` 的 `mutual` 写法）；
2. `cequiv_rel_components_of_noRel`：**主结论**（分量关系自由时的转移引理）；
3. `TransferLemma`：一般转移引理，**只陈述不证**；及其特例回归
   `cequiv_rel_components_of_transferLemma`；
4. 第 4 节的归约尝试与形态见证。

## 4. 技术注记

* 不使用 `induction` 于 `Form`（嵌套归纳）；`NoRel`／`truth` 在复合形状上**不是**
  定义性可归约的，故递归调用一律**显式给出公式隐变量**（`(φ := φ)`）；
* Lean 4 不允许文档注释紧邻 `mutual`，故 `mutual` 前只用普通块注释；
  块注释可嵌套，故注释正文里不出现字面斜杠加短横线；
* 未使用的绑定一律写 `_`，不使用 `sorry`／`axiom`／`admit`，
  以保证 `lake env lean TrackI.lean` **零错误零警告**。
-/
import EvidenceLogic.Frontier.RestrictedE
import EvidenceLogic.System.NonAdmissible

namespace EvidenceLogic

noncomputable section

open PSet

/-! ## 1. 两个投影基结构及其基无关性 -/

/-- 支持取第一投影的基结构：`a ⊳ b` 的真值恰为 `⟦a⟧`。 -/
abbrev projBase₁ (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := fun X _ => X, refutI := fun _ _ => ⊥ }

/-- 支持取第二投影的基结构：`a ⊳ b` 的真值恰为 `⟦b⟧`。 -/
abbrev projBase₂ (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := fun _ Y => Y, refutI := fun _ _ => ⊥ }

/- **`NoRel` 公式的真值与 `suppI` 的取法无关（第一投影版）**。

对公式与列表写成 `mutual`（`.atom` 情形需要列表版引理）；`NoRel` 把 `.supp`／`.refut`
两个构造子排除掉，而这两支正是唯一用到 `suppI`／`refutI` 的地方。
递归调用显式给出公式隐变量（见 `RestrictedE` 注 3）。 -/
mutual
  /-- 公式版。 -/
  theorem truth_projBase₁_eq_canon {W : Type} (atomRel : Nat → List (PSet W) → PSet W) :
      ∀ {φ : Form}, NoRel φ → ∀ ρ : Nat → PSet W,
        (projBase₁ W atomRel).truth φ ρ = (Canon.base W atomRel).truth φ ρ
    | .var _, _, _ => rfl
    | .atom i ts, h, ρ => by
        show atomRel i ((projBase₁ W atomRel).truths ρ ts)
          = atomRel i ((Canon.base W atomRel).truths ρ ts)
        rw [truth_projBase₁_eq_canon_list atomRel ρ h]
    | .bot, _, _ => rfl
    | .top, _, _ => rfl
    | .not φ, h, ρ => by
        show ((projBase₁ W atomRel).truth φ ρ)ᶜ = ((Canon.base W atomRel).truth φ ρ)ᶜ
        exact congrArg Compl.compl (truth_projBase₁_eq_canon atomRel (φ := φ) h ρ)
    | .and φ ψ, h, ρ => by
        show (projBase₁ W atomRel).truth φ ρ ⊓ (projBase₁ W atomRel).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊓ (Canon.base W atomRel).truth ψ ρ
        rw [truth_projBase₁_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_projBase₁_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .or φ ψ, h, ρ => by
        show (projBase₁ W atomRel).truth φ ρ ⊔ (projBase₁ W atomRel).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [truth_projBase₁_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_projBase₁_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .imp φ ψ, h, ρ => by
        show ((projBase₁ W atomRel).truth φ ρ)ᶜ ⊔ (projBase₁ W atomRel).truth ψ ρ
          = ((Canon.base W atomRel).truth φ ρ)ᶜ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [truth_projBase₁_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_projBase₁_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .all x φ, h, ρ => by
        apply PSet.iInter_congr
        intro X
        show (projBase₁ W atomRel).truth φ (upd ρ x X)
          = (Canon.base W atomRel).truth φ (upd ρ x X)
        exact truth_projBase₁_eq_canon atomRel (φ := φ) h (upd ρ x X)
    | .ex x φ, h, ρ => by
        apply PSet.iUnion_congr
        intro X
        show (projBase₁ W atomRel).truth φ (upd ρ x X)
          = (Canon.base W atomRel).truth φ (upd ρ x X)
        exact truth_projBase₁_eq_canon atomRel (φ := φ) h (upd ρ x X)
    | .supp _ _, h, _ => absurd h noRel_supp
    | .refut _ _, h, _ => absurd h noRel_refut

  /-- 列表版。 -/
  theorem truth_projBase₁_eq_canon_list {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
      (ρ : Nat → PSet W) : ∀ {ts : List Form}, NoRelList ts →
        (projBase₁ W atomRel).truths ρ ts = (Canon.base W atomRel).truths ρ ts
    | [], _ => rfl
    | t :: ts, h => by
        show (projBase₁ W atomRel).truth t ρ :: (projBase₁ W atomRel).truths ρ ts
          = (Canon.base W atomRel).truth t ρ :: (Canon.base W atomRel).truths ρ ts
        rw [truth_projBase₁_eq_canon atomRel (φ := t) h.1 ρ,
          truth_projBase₁_eq_canon_list atomRel ρ h.2]
end

/- **`NoRel` 公式的真值与 `suppI` 的取法无关（第二投影版）**。

与第一投影版逐支同构，只把 `projBase₁` 换成 `projBase₂`。 -/
mutual
  /-- 公式版。 -/
  theorem truth_projBase₂_eq_canon {W : Type} (atomRel : Nat → List (PSet W) → PSet W) :
      ∀ {φ : Form}, NoRel φ → ∀ ρ : Nat → PSet W,
        (projBase₂ W atomRel).truth φ ρ = (Canon.base W atomRel).truth φ ρ
    | .var _, _, _ => rfl
    | .atom i ts, h, ρ => by
        show atomRel i ((projBase₂ W atomRel).truths ρ ts)
          = atomRel i ((Canon.base W atomRel).truths ρ ts)
        rw [truth_projBase₂_eq_canon_list atomRel ρ h]
    | .bot, _, _ => rfl
    | .top, _, _ => rfl
    | .not φ, h, ρ => by
        show ((projBase₂ W atomRel).truth φ ρ)ᶜ = ((Canon.base W atomRel).truth φ ρ)ᶜ
        exact congrArg Compl.compl (truth_projBase₂_eq_canon atomRel (φ := φ) h ρ)
    | .and φ ψ, h, ρ => by
        show (projBase₂ W atomRel).truth φ ρ ⊓ (projBase₂ W atomRel).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊓ (Canon.base W atomRel).truth ψ ρ
        rw [truth_projBase₂_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_projBase₂_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .or φ ψ, h, ρ => by
        show (projBase₂ W atomRel).truth φ ρ ⊔ (projBase₂ W atomRel).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [truth_projBase₂_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_projBase₂_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .imp φ ψ, h, ρ => by
        show ((projBase₂ W atomRel).truth φ ρ)ᶜ ⊔ (projBase₂ W atomRel).truth ψ ρ
          = ((Canon.base W atomRel).truth φ ρ)ᶜ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [truth_projBase₂_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_projBase₂_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .all x φ, h, ρ => by
        apply PSet.iInter_congr
        intro X
        show (projBase₂ W atomRel).truth φ (upd ρ x X)
          = (Canon.base W atomRel).truth φ (upd ρ x X)
        exact truth_projBase₂_eq_canon atomRel (φ := φ) h (upd ρ x X)
    | .ex x φ, h, ρ => by
        apply PSet.iUnion_congr
        intro X
        show (projBase₂ W atomRel).truth φ (upd ρ x X)
          = (Canon.base W atomRel).truth φ (upd ρ x X)
        exact truth_projBase₂_eq_canon atomRel (φ := φ) h (upd ρ x X)
    | .supp _ _, h, _ => absurd h noRel_supp
    | .refut _ _, h, _ => absurd h noRel_refut

  /-- 列表版。 -/
  theorem truth_projBase₂_eq_canon_list {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
      (ρ : Nat → PSet W) : ∀ {ts : List Form}, NoRelList ts →
        (projBase₂ W atomRel).truths ρ ts = (Canon.base W atomRel).truths ρ ts
    | [], _ => rfl
    | t :: ts, h => by
        show (projBase₂ W atomRel).truth t ρ :: (projBase₂ W atomRel).truths ρ ts
          = (Canon.base W atomRel).truth t ρ :: (Canon.base W atomRel).truths ρ ts
        rw [truth_projBase₂_eq_canon atomRel (φ := t) h.1 ρ,
          truth_projBase₂_eq_canon_list atomRel ρ h.2]
end

/-! ## 2. 主结论：分量关系自由时的转移引理 -/

/-- **转移引理（分量关系自由版）**：关系式的经典等价**迫使分量在典范基上真值相等**——
只要分量不含关系子公式。

证明：把 `h.1`（`Entails (u ⊳ v) (u' ⊳ v')`）实例化到 `projBase₁ W atomRel`；
该基的 `suppI` 取第一投影，故 `(u ⊳ v)` 的真值**定义性地**恰为 `⟦u⟧`，于是得
`⟦u⟧ ≤ ⟦u'⟧`；`h.2` 给出反向，合起来 `⟦u⟧ = ⟦u'⟧`（`PSet.ext`）；
再用第 1 节的基无关性（`hu`、`hu'`）搬到 `Canon.base`。
第二个分量同理换用 `projBase₂` 与 `hv`、`hv'`。 -/
theorem cequiv_rel_components_of_noRel {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {u v u' v' : Form} (hu : NoRel u) (hv : NoRel v) (hu' : NoRel u') (hv' : NoRel v')
    (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) :
    ((Canon.base W atomRel).truth u ρ = (Canon.base W atomRel).truth u' ρ) ∧
    ((Canon.base W atomRel).truth v ρ = (Canon.base W atomRel).truth v' ρ) := by
  constructor
  · -- 第一个分量：`projBase₁` 把它投影出来
    have hle₁ : (projBase₁ W atomRel).truth u ρ ≤ (projBase₁ W atomRel).truth u' ρ :=
      h.1 (projBase₁ W atomRel) ρ
    have hle₂ : (projBase₁ W atomRel).truth u' ρ ≤ (projBase₁ W atomRel).truth u ρ :=
      h.2 (projBase₁ W atomRel) ρ
    have heq : (projBase₁ W atomRel).truth u ρ = (projBase₁ W atomRel).truth u' ρ := by
      apply PSet.ext
      intro w
      exact ⟨fun hw => hle₁ w hw, fun hw => hle₂ w hw⟩
    exact (truth_projBase₁_eq_canon atomRel (φ := u) hu ρ).symm.trans
      (heq.trans (truth_projBase₁_eq_canon atomRel (φ := u') hu' ρ))
  · -- 第二个分量：`projBase₂` 把它投影出来
    have hle₁ : (projBase₂ W atomRel).truth v ρ ≤ (projBase₂ W atomRel).truth v' ρ :=
      h.1 (projBase₂ W atomRel) ρ
    have hle₂ : (projBase₂ W atomRel).truth v' ρ ≤ (projBase₂ W atomRel).truth v ρ :=
      h.2 (projBase₂ W atomRel) ρ
    have heq : (projBase₂ W atomRel).truth v ρ = (projBase₂ W atomRel).truth v' ρ := by
      apply PSet.ext
      intro w
      exact ⟨fun hw => hle₁ w hw, fun hw => hle₂ w hw⟩
    exact (truth_projBase₂_eq_canon atomRel (φ := v) hv ρ).symm.trans
      (heq.trans (truth_projBase₂_eq_canon atomRel (φ := v') hv' ρ))

/-! ## 3. 一般转移引理（只陈述，不证） -/

/-- **一般转移引理（本文件不证）**：去掉 `NoRel` 后，关系式的经典等价是否仍迫使分量在
    典范基上真值相等。这是「公式模 `⊣⊢` 的代数与典范真值相合」的局部形式，
    即 `docs/讨论与局限.md` 第 2 节的公开问题在关系式上的投影。 -/
def TransferLemma : Prop :=
  ∀ {W : Type} (atomRel : Nat → List (PSet W) → PSet W) {u v u' v' : Form},
    ((u ⊳ v) ⊣⊢ (u' ⊳ v')) →
    ∀ ρ, (Canon.base W atomRel).truth u ρ = (Canon.base W atomRel).truth u' ρ ∧
         (Canon.base W atomRel).truth v ρ = (Canon.base W atomRel).truth v' ρ

/-- `TransferLemma` 直接蕴含 `cequiv_rel_components_of_noRel`：后者是前者丢掉
    `NoRel` 假设后的特例（这一步只说明一般陈述确实涵盖第 2 节，不是新信息）。 -/
theorem cequiv_rel_components_of_transferLemma (h : TransferLemma) {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W) {u v u' v' : Form}
    (heq : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) :
    ((Canon.base W atomRel).truth u ρ = (Canon.base W atomRel).truth u' ρ) ∧
    ((Canon.base W atomRel).truth v ρ = (Canon.base W atomRel).truth v' ρ) :=
  h (W := W) atomRel heq ρ

/-! ## 4. 归约尝试：`TransferLemma → TruthPropagation`

`TruthPropagation`（`EvidenceLogic/NonAdmissible.lean` 第十二节）说：

    `Derivable (t ⊳ c)` 且典范框架里 `⟦t⟧ = ⊤` 时，必有 `⟦c⟧ = ⊤`。

**结论（如实报告）：无条件归约写不出来，卡在「造不出一条可用的经典等价」。**

* `TransferLemma` 的**前提**是两个**关系式之间**的经典等价 `⊣⊢`；
  `TruthPropagation` 的**前提**是 `Derivable (t ⊳ c)` 与一条框架真值等式。
  从后者造不出一条涉及 `(t ⊳ c)` 的、非平凡的 `⊣⊢`：可靠性只给出
  「在模型里真值为 `⊤`」，而不是「与某个关系式经典等价」；唯一处处可用的
  `CEquiv` 是自反的 `(t ⊳ c) ⊣⊢ (t ⊳ c)`，把它交给 `TransferLemma` 只能得到
  `⟦t⟧ = ⟦t⟧` 与 `⟦c⟧ = ⟦c⟧`，对 `⟦c⟧ = ⊤` 毫无信息；
* 真正需要转移的是 `E` 的「洞在顶层」那一支：那里有 `Derivable φ` 与
  `φ ⊣⊢ (t ⊳ c)`，要证 `⟦t⟧ = ⊤ → ⟦c⟧ = ⊤`。此时 `TransferLemma` **能**用的情形
  恰好是 `φ` 本身为关系式 `u ⊳ v`（这就是下面 `holeAtTop_of_transferLemma` 证出的那一半）；
* 但 `φ` **不必**是关系式（下面 `holeAtTop_source_need_not_be_supp` 给出机器验证的实例），
  于是 `TransferLemma` 在其唯一需要的位置上可能根本没有前提可用。

**卡住的那一步（实测报错，两次都在同一处断掉）。**

1. 无条件归约：把 `TransferLemma` 从**现有假设**中能提供的信息榨干（唯一处处可用的
   `CEquiv` 是自反的 `(t ⊳ c) ⊣⊢ (t ⊳ c)`）后，剩下的目标是 `⟦c⟧ = ⊤`：

       error: Type mismatch
         h₂
       has type
         (Canon.base W atomRel).truth c ρ = (Canon.base W atomRel).truth c ρ
       but is expected to have type
         (Canon.base W atomRel).truth c ρ = ⊤

2. `TruthPropagation` 归纳里**唯一**需要转移的那一步（`E` 的「洞在顶层」）：
   那里能提供的假设是 `Derivable φ` 与 `φ ⊣⊢ (t ⊳ c)`，而 `φ` **不是**已知的关系式，
   于是 `TransferLemma` 连**应用**都做不到：

       error: Application type mismatch: The argument
         heq
       has type
         φ ⊣⊢ t ⊳ c
       but is expected to have type
         ?m.8 ⊳ ?m.9 ⊣⊢ ?m.10 ⊳ ?m.11

   即 `TransferLemma` 的**前提形态**（两个**关系式**之间的经典等价）与 `E` 在该步
   能给出的假设形态**不匹配**。这不是「还差几行 `rw`」，而是缺少一条桥梁：要把
   `Derivable γ`／`γ ⊣⊢ t ⊳ c` 换成关于分量的 `⊣⊢`／真值等式，正是
   `docs/讨论与局限.md` 第 2 节的完备性／相合性问题本身。

   因此下面两条只把缺口精确指出来，**不**冒充归约：
   `holeAtTop_of_transferLemma` 是 `TransferLemma` 真正覆盖的那一半
   （源公式本身是关系式），`holeAtTop_source_need_not_be_supp` 则给出机器验证的实例：
   源公式**可以不是**关系式，故那一半并不是全部。 -/

/-- **`TransferLemma` 能闭合的那一半「洞在顶层」步**：源公式**本身是关系式**时，
    只要它的第二个分量在该赋值处真值为 `⊤`，转移引理就把这个 `⊤` 传给目标关系式的
    第二个分量。

    `ih` 就是归纳假设在源公式上的实例（`PropInv (u ⊳ v)`）。证明只用
    `TransferLemma` 的两条分量等式与 `Canon.frame_truth`（命题性等式），
    不需要 `[Nonempty W]`，也不需要源的推导 `Derivable (u ⊳ v)`。 -/
theorem holeAtTop_of_transferLemma (htl : TransferLemma) {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W) {u v t c : Form}
    (heq : (u ⊳ v) ⊣⊢ (t ⊳ c)) (ρ : Nat → PSet W)
    (ih : (Canon.frame W atomRel).truth u ρ = ⊤ → (Canon.frame W atomRel).truth v ρ = ⊤)
    (ht : (Canon.frame W atomRel).truth t ρ = ⊤) :
    (Canon.frame W atomRel).truth c ρ = ⊤ := by
  obtain ⟨hu, hv⟩ := htl (W := W) atomRel heq ρ
  have ht' : (Canon.base W atomRel).truth t ρ = ⊤ := by
    rw [← Canon.frame_truth W atomRel t ρ]
    exact ht
  have hu' : (Canon.base W atomRel).truth u ρ = ⊤ := hu.trans ht'
  have hu'' : (Canon.frame W atomRel).truth u ρ = ⊤ := by
    rw [Canon.frame_truth W atomRel u ρ]
    exact hu'
  have hv' : (Canon.frame W atomRel).truth v ρ = ⊤ := ih hu''
  have hv'' : (Canon.base W atomRel).truth v ρ = ⊤ := by
    rw [← Canon.frame_truth W atomRel v ρ]
    exact hv'
  have hc : (Canon.base W atomRel).truth c ρ = ⊤ := hv.symm.trans hv''
  rw [Canon.frame_truth W atomRel c ρ]
  exact hc

/-- `(t ⊳ c) ∧ ⊤` 与 `t ⊳ c` 经典等价（在两个方向上分别用 `⊓` 的左投影与
    `PSet.le_inf`／`PSet.le_top`）。 -/
theorem cequiv_and_top (t c : Form) : (Form.and (t ⊳ c) Form.top) ⊣⊢ (t ⊳ c) := by
  constructor
  · intro B ρ
    show B.truth (t ⊳ c) ρ ⊓ ⊤ ≤ B.truth (t ⊳ c) ρ
    exact PSet.inf_le_left _ _
  · intro B ρ
    show B.truth (t ⊳ c) ρ ≤ B.truth (t ⊳ c) ρ ⊓ ⊤
    exact PSet.le_inf (PSet.le_refl _) (PSet.le_top _)

/-- 反向的 `cequiv_and_top`（供 `E` 使用，其方向是「源 `⊣⊢` 目标」）。 -/
theorem cequiv_top_and (t c : Form) : (t ⊳ c) ⊣⊢ (Form.and (t ⊳ c) Form.top) :=
  ⟨(cequiv_and_top t c).2, (cequiv_and_top t c).1⟩

/-- `Form.top ⊳ Form.top` 可推导（`S1`，因为 `Entails Form.top Form.top`）。 -/
theorem top_supp_top_derivable : Derivable (Form.top ⊳ Form.top) :=
  Derivable.s1 (p := Form.top) (q := Form.top) (fun _ _ => PSet.le_refl _)

/-- `(Form.top ⊳ Form.top) ∧ Form.top` 可推导：由 `top_supp_top_derivable`
    经一次 `E`（上下文取洞）得到。 -/
theorem and_top_derivable : Derivable (Form.and (Form.top ⊳ Form.top) Form.top) :=
  Derivable.e (φ := Form.top ⊳ Form.top)
    (ψ := Form.and (Form.top ⊳ Form.top) Form.top)
    (γ := Form.top ⊳ Form.top)
    (δ := Form.and (Form.top ⊳ Form.top) Form.top)
    ⟨Ctx.hole, rfl, rfl⟩ (cequiv_top_and Form.top Form.top) top_supp_top_derivable

/-- `(Form.top ⊳ Form.top) ∧ Form.top` **不是**关系式形状（构造子不同）。 -/
theorem not_supp_and_top :
    ¬ ∃ u v : Form, Form.and (Form.top ⊳ Form.top) Form.top = (u ⊳ v) := by
  rintro ⟨u, v, h⟩
  cases h

/-- **形态见证（机器验证）**：存在一个**不是**关系式的公式 `φ`，满足
    `Derivable φ` 且 `φ ⊣⊢ (Form.top ⊳ Form.top)`（后者是关系式）。

    这正是 `E` 的「洞在顶层」步（结论为关系式）所需的配置，而 `φ` 不是关系式，
    因此 `TransferLemma` 的前提（两个**关系式**之间的经典等价）在那里用不上。
    取 `φ := (Form.top ⊳ Form.top) ∧ Form.top`。

    **注意**：这不是 `TruthPropagation` 的反例——该实例里 `⟦Form.top⟧ = ⊤`，
    结论当然成立；它只否证「源公式必是关系式，故 `TransferLemma` 必定可用」这条捷径。 -/
theorem holeAtTop_source_need_not_be_supp :
    ∃ φ : Form, (¬ ∃ u v : Form, φ = (u ⊳ v)) ∧ Derivable φ ∧
      (φ ⊣⊢ (Form.top ⊳ Form.top)) :=
  ⟨Form.and (Form.top ⊳ Form.top) Form.top, not_supp_and_top, and_top_derivable,
    cequiv_and_top Form.top Form.top⟩

/-- **「洞在顶层」那一步的规则实例形状**（一般 `φ`）：上下文取洞时，`E` 由
    `Derivable φ` 与 `φ ⊣⊢ (t ⊳ c)` 给出 `Derivable (t ⊳ c)`——源公式 `φ` 是任意的，
    结论是关系式。这正是 `TruthPropagation` 的归纳里唯一需要转移的那一步。 -/
theorem holeAtTop_step_derivable {φ t c : Form} (hd : Derivable φ) (heq : φ ⊣⊢ (t ⊳ c)) :
    Derivable (t ⊳ c) :=
  Derivable.e (φ := φ) (ψ := t ⊳ c) (γ := φ) (δ := t ⊳ c)
    ⟨Ctx.hole, rfl, rfl⟩ heq hd

end

end EvidenceLogic
