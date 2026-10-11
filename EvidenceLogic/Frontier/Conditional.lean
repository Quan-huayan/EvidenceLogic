/-
# TrackJ：**`TransferLemma` ⇒ `Derivable` 上的支持-蕴含不变量（典范框架版）**

本文件**不修改任何已有文件**，只在既有 `import` 之上补一批新结论。

## 0. 这条结果的**强度**（务必连同结论一起读，不要夸大）

* 本文件**没有**证明 `TransferLemma`（`EvidenceLogic/Transfer.lean` 第 3 节）：
  它是本文件的**假设** `htl : TransferLemma`；
* 因此结论**全部是条件化的**：**假如**一般转移引理成立，则

  > `Derivable`（**含元规则 `E`、无任何片段限制**）上的**支持-蕴含不变量**在
  > **一切典范框架**上成立（`supp_le_of_cequiv_canon`），
  > 从而支持传递与 S7 的结论在**一切**典范框架中有效
  > （`transitivity_valid_canon_of_transferLemma`／`s7_valid_canon_of_transferLemma`）。

* 本文件**不**声称 `TransferLemma` 成立；**不**声称 `TruthPropagation`
  已被证明或已被反驳；**不**对 `TruthPropagation` 作任何断言。

## 0.1 为什么只能对**典范框架**陈述（本文件的关键取舍）

`TransferLemma` 的分量等式活在 **`Canon.base` 的 `Base.truth`** 上，
而 `Frame.truth` 与 `Base.truth` 在 Lean 看来**不是定义性相等**
（`M : Frame` 是变量时 `Frame.truth` 不会归约到 `Base.truth`；见
`EvidenceLogic/RestrictedE.lean` 第 2 节注 1 与 `docs/设计说明.md` 第八节）。
**只有典范框架**有一条**命题性**桥梁 `Canon.frame_truth`：

    (Canon.frame W atomRel).truth φ ρ = (Canon.base W atomRel).truth φ ρ

于是本文件把不变量限制在典范框架上（与 `RestrictedE.supp_le₁_canon` 完全平行），
并用 `transfer_frame`（第 4 节）把 `TransferLemma` 的两条分量等式
经 `Canon.frame_truth` 搬到 `Canon.frame` 一侧；此后**全部搬运都在 frame 层完成**。

## 1. 关键结构性发现（本文件的主要新信息）

`EFree`／`RestrictedE` 都报告过：对 `Derivable` 归纳验证支持侧不变量时，
**唯一**闭合不了的是 `E` 的「洞在顶层」那一支，那一支归约到公开的相合性问题。
本文件的观察是：把归纳的 motive 从「`φ` 是支持式」换成
**「`φ` 与某个支持式经典等价」**：

    motive φ := ∀ {a b}, (φ ⊣⊢ (a ⊳ b)) → ∀ ρ, ⟦a⟧ρ ≤ ⟦b⟧ρ

于是 `E` 的那一支**自动闭合**：那里有 `γ = C.plug φ`、`δ = C.plug ψ`、`φ ⊣⊢ ψ`，
由 `cequiv_plug`（对 `Ctx` 的显式消去子递归）得 `γ ⊣⊢ δ`，与目标假设
`δ ⊣⊢ (a ⊳ b)` 复合（`cequiv_trans`）即得 `γ ⊣⊢ (a ⊳ b)`，
**归纳假设直接适用**——**不需要 `TransferLemma`，也不需要任何相干性／相合性输入**。

对照 `Transfer.lean` 第 4 节：那里正确指出 `TransferLemma` 的**前提形态**是两个
**关系式之间**的 `⊣⊢`，而 `E` 支给出的前提是 `φ ⊣⊢ (t ⊳ c)`（`φ` 一般不是关系式），
故那里 `TransferLemma` **连应用都做不到**（并给出机器验证的形态见证
`holeAtTop_source_need_not_be_supp`）。本文件的结论是：
**在正确的 motive 下，`E` 支根本不需要转移引理**；`TransferLemma` 的位置被
**移到**九条非 `E` 规则上，那里两边的分量都是规则显式写出来的公式，前提形态恰好匹配。

## 2. 文件内容

1. `pset_le_of_eq`（`cequiv_trans`／`cequiv_refl` 由 `Initiality.lean` 提供）；
2. `plug_truth`（基语义层逐赋值真值等式，用显式消去子 `Ctx.rec` ＋ 列表版辅助引理
   `plug_truths_aux`）与 `cequiv_plug`：**`E` 支的核心工具**；
3. 形状冲突引理 `support_not_cequiv_refut`：**反驳式与支持式不可能经典等价**
   （在 `suppI ≡ ⊥`、`refutI ≡ ⊤` 的基结构上，`⊣⊢` 的第一个方向就是 `⊤ ≤ ⊥`），
   及其 `Kind.form Kind.refut` 书写版 `support_not_cequiv_form`；
4. `transfer_frame`：把 `TransferLemma` 的分量等式经 `Canon.frame_truth`
   从 `Canon.base` 搬到 `Canon.frame`（**本文件的关键桥**）；
   以及 `inv_supp_of_ih_supp`／`inv_supp_of_two_ih_supp`；
5. `supp_le_of_cequiv_canon`：**主目标**（典范框架版支持-蕴含不变量，模 `⊣⊢`）。
   注意它的**第一个显式参数是假设** `htl : TransferLemma`——本文件的结论全是
   「**假如** `TransferLemma` 成立」这一条件句的形式化，故 `htl` 必须出现在陈述里；
6. `supp_le_of_transferLemma_canon`：形状与 `EFree.noE_supp_le` 一致的推论
   （把 `htl` 传出，用于 N3 障碍）；
7. `transitivity_valid_canon_of_transferLemma`／`s7_valid_canon_of_transferLemma`：
   把条件化前沿写成定理。

## 3. 九条规则支各自用到什么

| 支 | `TransferLemma`（经 `transfer_frame`）提供 | 其余输入 |
|---|---|---|
| `s1` | `⟦a⟧ = ⟦p⟧`、`⟦b⟧ = ⟦q⟧` | `IsModel.classical p q h` |
| `s2` | `⟦a⟧ = ⟦t⟧`、`⟦b⟧ = ⟦q⟧` | 归纳假设 + `classical` + `le_trans` |
| `f1` | `⟦a⟧ = ⟦t⟧`、`⟦b⟧ = ⟦∀x φ⟧` | `truth_upd_notFree`、`le_iInter` |
| `f2` | `⟦a⟧ = ⟦∀x p⟧`、`⟦b⟧ = ⟦φ⟧` | `iInter_le`、`truth_upd_notFree` |
| `f3` | `⟦a⟧ = ⟦a₀ ∧ b₀⟧`、`⟦b⟧ = ⟦φ⟧` | `inf_le_left` |
| `f4` | `⟦a⟧ = ⟦t⟧`、`⟦b⟧ = ⟦φ ∧ ψ⟧` | 归纳假设 ×2、`le_inf` |
| `r1` | **用不上**：结论是反驳式，与支持式不可能经典等价 | `support_not_cequiv_refut`（第 3 节，已证） |
| `p1` | `⟦a⟧ = ⟦a₀ ∧ b₀⟧`、`⟦b⟧ = ⟦(c ∧ d) S f⟧` | `le_of_eq_top` ＋ `Derivable.soundness` |
| `p2` | `⟦a⟧ = ⟦∀x a₀⟧`、`⟦b⟧ = ⟦(∀x c) S f⟧` | `le_of_eq_top` ＋ `Derivable.soundness` |

注：`p1`／`p2` 里「结论第二项是可推导关系式故真值为 `⊤`」一步用
`Derivable.soundness`（`Soundness.lean`，**已存在且不依赖本文件**），它给出的正是
**frame** 层的 `Valid`，与本文件「两侧统一用 `(Canon.frame W atomRel).truth`」吻合。

## 4. 技术注记（本次实测的 Lean 事实）

* **注 A（`E` 支为什么不需要相干性）**：`cequiv_plug` 的证明只用
  `Ctx` 的结构递归：把洞填进上下文后，两侧只差**洞那一处**的真值，
  而那一处在每个基结构与赋值上真值相同（归纳假设）。它**对任意公式**成立，
  不要求 `NoRel`，也不要求任何模型论输入；
* **注 B（`Base.truth` 是 mutual fixpoint）**：`Base.truth` 与 `Base.truths` 是
  `mutual` 块，故复合公式上的等式**不是**定义性可归约的；需要时要用
  `Base.truth.eq_11`／`eq_12` 等**方程引理**；
* **注 C（方程编译器的坑）**：用**方程风格**写「尾部带 `∀ ρ`」的定理时，Lean 4
  的方程编译器会把该 `∀ ρ` 误当成模式，报
  `Ctx.hole has type Ctx but is expected to have type Base`；故 `plug_truth` 必须用
  `Ctx.rec` 显式消去子书写；
* **注 D（`Kind.form` 的 `.supp` 分支不可合并）**：`cases k` 生成的动机把
  `Kind.form Kind.supp t φ` 与 `t ⊳ φ` 之间的等式锁成**命题性**的，
  于是 `.supp` 分支无法与 `.refut` 分支用同一个形状冲突引理处理，
  故形状冲突引理只对 `Kind.refut` 陈述；
* **注 E（frame↔base 的搬运只能用 `Canon.frame_truth`）**：该等式是**命题性**的，
  不能用 `rfl` 代替；`transfer_frame` 的每一支都要显式 `rw` 一次；
* 未使用的绑定一律写 `_`，不使用 `sorry`／`axiom`／`admit`。
-/
import EvidenceLogic.Frontier.Transfer
import EvidenceLogic.Analysis.Initiality
import EvidenceLogic.Model.Soundness
import EvidenceLogic.Frontier.EFree

namespace EvidenceLogic

noncomputable section

open PSet

/-! ## 1. 经典等价的基本引理

`CEquiv` 的传递性与自反性由 [`Initiality.lean`](Initiality.lean) 提供
（`cequiv_trans`、`cequiv_refl`），本文件直接复用，不重复声明。 -/

/-- 等式即 `≤`（显式给出，以免依赖 `.le` 记法的实例解析）。 -/
theorem pset_le_of_eq {W : Type} {X Y : PSet W} (h : X = Y) : X ≤ Y := fun _ hx => h ▸ hx

/-! ## 2. 上下文填入保持经典等价（`E` 支的核心工具） -/

/-- 列表辅助引理（在 `plug_truth` 的 `.atom` 支使用）：对前缀 `pre` 归纳。 -/
theorem plug_truths_aux (B : Base) (C : Ctx) {φ ψ : Form}
    (h : ∀ ρ : Nat → PSet B.W,
      B.truth (Ctx.plug C φ) ρ = B.truth (Ctx.plug C ψ) ρ) :
    ∀ (ρ : Nat → PSet B.W) (pre post : List Form),
      B.truths ρ (pre ++ Ctx.plug C φ :: post)
      = B.truths ρ (pre ++ Ctx.plug C ψ :: post)
  | ρ, [], post => by
      show B.truth (Ctx.plug C φ) ρ :: B.truths ρ post
        = B.truth (Ctx.plug C ψ) ρ :: B.truths ρ post
      rw [h ρ]
  | ρ, u :: us, post => by
      show B.truth u ρ :: B.truths ρ (us ++ Ctx.plug C φ :: post)
        = B.truth u ρ :: B.truths ρ (us ++ Ctx.plug C ψ :: post)
      rw [plug_truths_aux B C h ρ us post]

/-- **上下文填入的真值相等（基语义层，单个基结构）**：若 `φ` 与 `ψ` 在**这一个**基结构
    的一切赋值下真值相同，则填进任意上下文后仍如此。

    用显式消去子 `Ctx.rec`（不用方程风格：见文件头注 C）。
    `.atom` 支由列表版 `plug_truths_aux` 给出。 -/
theorem plug_truth (B : Base) {φ ψ : Form}
    (h : ∀ ρ : Nat → PSet B.W, B.truth φ ρ = B.truth ψ ρ) :
    ∀ (C : Ctx) (ρ : Nat → PSet B.W), B.truth (C.plug φ) ρ = B.truth (C.plug ψ) ρ :=
  Ctx.rec (motive := fun C => ∀ ρ : Nat → PSet B.W,
      B.truth (C.plug φ) ρ = B.truth (C.plug ψ) ρ)
    h
    (fun i pre c post (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.atomRel i (B.truths ρ (pre ++ Ctx.plug c φ :: post))
        = B.atomRel i (B.truths ρ (pre ++ Ctx.plug c ψ :: post))
      rw [plug_truths_aux B c (fun ρ' => ih ρ') ρ pre post])
    (fun c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show (B.truth (Ctx.plug c φ) ρ)ᶜ = (B.truth (Ctx.plug c ψ) ρ)ᶜ
      rw [ih ρ])
    (fun c ψ' (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.truth (Ctx.plug c φ) ρ ⊓ B.truth ψ' ρ
        = B.truth (Ctx.plug c ψ) ρ ⊓ B.truth ψ' ρ
      rw [ih ρ])
    (fun ψ' c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.truth ψ' ρ ⊓ B.truth (Ctx.plug c φ) ρ
        = B.truth ψ' ρ ⊓ B.truth (Ctx.plug c ψ) ρ
      rw [ih ρ])
    (fun c ψ' (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.truth (Ctx.plug c φ) ρ ⊔ B.truth ψ' ρ
        = B.truth (Ctx.plug c ψ) ρ ⊔ B.truth ψ' ρ
      rw [ih ρ])
    (fun ψ' c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.truth ψ' ρ ⊔ B.truth (Ctx.plug c φ) ρ
        = B.truth ψ' ρ ⊔ B.truth (Ctx.plug c ψ) ρ
      rw [ih ρ])
    (fun c ψ' (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show (B.truth (Ctx.plug c φ) ρ)ᶜ ⊔ B.truth ψ' ρ
        = (B.truth (Ctx.plug c ψ) ρ)ᶜ ⊔ B.truth ψ' ρ
      rw [ih ρ])
    (fun ψ' c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show (B.truth ψ' ρ)ᶜ ⊔ B.truth (Ctx.plug c φ) ρ
        = (B.truth ψ' ρ)ᶜ ⊔ B.truth (Ctx.plug c ψ) ρ
      rw [ih ρ])
    (fun x c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show PSet.iInter (fun X : PSet B.W => B.truth (Ctx.plug c φ) (upd ρ x X))
        = PSet.iInter (fun X : PSet B.W => B.truth (Ctx.plug c ψ) (upd ρ x X))
      apply PSet.iInter_congr
      intro X
      exact ih (upd ρ x X))
    (fun x c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show PSet.iUnion (fun X : PSet B.W => B.truth (Ctx.plug c φ) (upd ρ x X))
        = PSet.iUnion (fun X : PSet B.W => B.truth (Ctx.plug c ψ) (upd ρ x X))
      apply PSet.iUnion_congr
      intro X
      exact ih (upd ρ x X))
    (fun c ψ' (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.suppI (B.truth (Ctx.plug c φ) ρ) (B.truth ψ' ρ)
        = B.suppI (B.truth (Ctx.plug c ψ) ρ) (B.truth ψ' ρ)
      rw [ih ρ])
    (fun t c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.suppI (B.truth t ρ) (B.truth (Ctx.plug c φ) ρ)
        = B.suppI (B.truth t ρ) (B.truth (Ctx.plug c ψ) ρ)
      rw [ih ρ])
    (fun c ψ' (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.refutI (B.truth (Ctx.plug c φ) ρ) (B.truth ψ' ρ)
        = B.refutI (B.truth (Ctx.plug c ψ) ρ) (B.truth ψ' ρ)
      rw [ih ρ])
    (fun t c (ih : ∀ ρ : Nat → PSet B.W,
        B.truth (Ctx.plug c φ) ρ = B.truth (Ctx.plug c ψ) ρ) ρ => by
      show B.refutI (B.truth t ρ) (B.truth (Ctx.plug c φ) ρ)
        = B.refutI (B.truth t ρ) (B.truth (Ctx.plug c ψ) ρ)
      rw [ih ρ])

/-- **`φ ⊣⊢ ψ` 经上下文填入后仍经典等价**：`(C.plug φ) ⊣⊢ (C.plug ψ)`。

    由 `plug_truth` 在**同一个** `B`、`ρ` 上取双向即得。
    **本引理对任意 `φ` 成立，不要求 `NoRel`，也不需要 `TransferLemma`**
    ——这正是 `E` 支自动闭合的全部原因（文件头第 1 节）。 -/
theorem cequiv_plug (C : Ctx) {φ ψ : Form} (h : φ ⊣⊢ ψ) :
    (C.plug φ) ⊣⊢ (C.plug ψ) :=
  ⟨fun B ρ => fun _ hw => (plug_truth B (fun ρ' =>
      PSet.ext (fun w => ⟨fun h1 => h.1 B ρ' w h1, fun h2 => h.2 B ρ' w h2⟩)) C ρ) ▸ hw,
   fun B ρ => fun _ hw => (plug_truth B (fun ρ' =>
      PSet.ext (fun w => ⟨fun h1 => h.1 B ρ' w h1, fun h2 => h.2 B ρ' w h2⟩)) C ρ) ▸ hw⟩

/-! ## 3. 形状冲突引理：反驳式不可能与支持式经典等价

取基结构把 `suppI` 恒定为 `⊥`、`refutI` 恒定为 `⊤`（值域 `PUnit` 以保证不平庸）。
于是在**任何**赋值处都有 `⟦u ⊲ v⟧ = ⊤` 与 `⟦a ⊳ b⟧ = ⊥`；
`⊣⊢` 的第一个方向 `⟦u ⊲ v⟧ ≤ ⟦a ⊳ b⟧` 立刻给出 `⊤ ≤ ⊥`。 -/

/-- 形状冲突用的基结构：`suppI ≡ ⊥`、`refutI ≡ ⊤`。 -/
abbrev shapeBase : Base :=
  { W := PUnit, atomRel := fun _ _ => (⊤ : PSet PUnit),
    suppI := fun _ _ => ⊥, refutI := fun _ _ => ⊤ }

/-- **形状冲突引理（已证）**：任何反驳式都与任何支持式**不**经典等价。

    只用 `⊣⊢` 的第一个方向：在 `shapeBase` 上 `⟦u ⊲ v⟧ = ⊤`、`⟦a ⊳ b⟧ = ⊥`
    （两条约化是定义性的），于是该方向就是 `⊤ ≤ ⊥`。
    不需要 `W` 非空，也不需要 `atomRel` 的任何性质。 -/
theorem support_not_cequiv_refut {u v a b : Form} :
    ¬ ((u ⊲ v) ⊣⊢ (a ⊳ b)) := by
  intro h
  have hle : (⊤ : PSet PUnit) ≤ ⊥ := h.1 shapeBase (fun _ => ⊤)
  exact not_bot PUnit.unit (hle PUnit.unit trivial)

/-- 形状冲突引理的「`Kind.form Kind.refut` 书写」版本（`f1`–`f4`／`p1`／`p2` 的
    `k = ⊲` 情形里结论第二项写成 `Kind.form`，与 `Form.refut` 只是定义性相同，
    故单列一条；只对 `Kind.refut` 陈述的理由见文件头注 D）。 -/
theorem support_not_cequiv_form {t φ a b : Form} :
    ¬ (Kind.form Kind.refut t φ ⊣⊢ (a ⊳ b)) := by
  intro h
  exact absurd h (show ¬ ((t ⊲ φ) ⊣⊢ (a ⊳ b)) from
    support_not_cequiv_refut (u := t) (v := φ) (a := a) (b := b))

/-! ## 4. 关键桥 `transfer_frame` 与两条归纳假设辅助引理 -/

/-- **关键桥**：把 `TransferLemma` 的分量等式从 `Canon.base` 搬到 `Canon.frame`，
    用的是**命题性**桥梁 `Canon.frame_truth`。

    这正是本文件能把主目标限制在**典范框架**上、从而绕开
    「`Frame.truth` 与 `Base.truth` 不是定义性相等」的原因（文件头 0.1 节）。 -/
theorem transfer_frame (htl : TransferLemma) (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {u v u' v' : Form}
    (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) :
    (Canon.frame W atomRel).truth u ρ = (Canon.frame W atomRel).truth u' ρ ∧
    (Canon.frame W atomRel).truth v ρ = (Canon.frame W atomRel).truth v' ρ := by
  obtain ⟨h1, h2⟩ := htl (W := W) atomRel h ρ
  refine ⟨?_, ?_⟩
  · rw [Canon.frame_truth W atomRel u ρ, Canon.frame_truth W atomRel u' ρ]; exact h1
  · rw [Canon.frame_truth W atomRel v ρ, Canon.frame_truth W atomRel v' ρ]; exact h2

/-- **一个归纳假设的「支持式实例」**（`f1`／`f2` 与 `f4` 用）。

    `f1`–`f4` 的规则结论形状是 `Kind.form k …`，`k` 是**变量**，而不变量必须把 `k`
    分成 `⊳`／`⊲` 两支。`cases k` **之后**归纳假设的类型已锁在 `Kind.form .supp …`
    或 `Kind.form .refut …` 上，无法再按另一支实例化，故在 `cases k` **之前**调用
    本引理（它把实例取在 `k = Kind.supp`）。 -/
theorem inv_supp_of_ih_supp {M : Frame} {a φ : Form}
    (ih : ∀ {a' b' : Form}, ((a ⊳ φ) ⊣⊢ (a' ⊳ b')) →
      ∀ ρ : Nat → PSet M.W, M.truth a' ρ ≤ M.truth b' ρ) :
    ∀ ρ : Nat → PSet M.W, M.truth a ρ ≤ M.truth φ ρ :=
  ih (cequiv_refl (a ⊳ φ))

/-- **两个归纳假设的「支持式实例」**（`f3` 用）。 -/
theorem inv_supp_of_two_ih_supp {M : Frame} {a b φ : Form}
    (ih₁ : ∀ {a' b' : Form}, ((a ⊳ φ) ⊣⊢ (a' ⊳ b')) →
      ∀ ρ : Nat → PSet M.W, M.truth a' ρ ≤ M.truth b' ρ)
    (ih₂ : ∀ {a' b' : Form}, ((b ⊳ φ) ⊣⊢ (a' ⊳ b')) →
      ∀ ρ : Nat → PSet M.W, M.truth a' ρ ≤ M.truth b' ρ) :
    (∀ ρ : Nat → PSet M.W, M.truth a ρ ≤ M.truth φ ρ) ∧
    (∀ ρ : Nat → PSet M.W, M.truth b ρ ≤ M.truth φ ρ) :=
  ⟨ih₁ (cequiv_refl (a ⊳ φ)), ih₂ (cequiv_refl (b ⊳ φ))⟩

/-! ## 5. 主目标：模 `⊣⊢` 的支持-蕴含不变量（**典范框架**版） -/

/-- **支持-蕴含不变量（模 `⊣⊢`，典范框架版）**：只要 `φ` 与某个支持式经典等价，
    该支持式的分量在典范框架的一切赋值处满足 `≤`。

    对 `Derivable` 归纳（显式消去子 `Derivable.rec`），motive

        fun φ _ => ∀ {a b}, (φ ⊣⊢ (a ⊳ b)) → ∀ ρ, ⟦a⟧ρ ≤ ⟦b⟧ρ

    **`e` 支**：`cequiv_plug` 补出 `γ = C.plug φ` 与 `δ = C.plug ψ` 的经典等价，
    与目标假设复合后**直接交给归纳假设**——这一支**不用** `TransferLemma`。
    **九条规则支**：用 `transfer_frame`（`TransferLemma` ＋ `Canon.frame_truth`）
    把规则产生的分量与目标分量在**框架层**对上。 -/
theorem supp_le_of_cequiv_canon (htl : TransferLemma) (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) :
    ∀ {φ : Form}, Derivable φ →
    ∀ {a b : Form}, (φ ⊣⊢ (a ⊳ b)) →
    ∀ ρ : Nat → PSet W,
      (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ :=
  Derivable.rec
    (motive := fun φ _ => ∀ {a b : Form}, (φ ⊣⊢ (a ⊳ b)) →
      ∀ ρ : Nat → PSet W,
        (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ)
    -- e：**不用 TransferLemma**，只用 `cequiv_plug` ＋ 归纳假设
    (fun {φ ψ γ δ} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ)
        (_ : Derivable γ)
        (ih : ∀ {a b : Form}, (γ ⊣⊢ (a ⊳ b)) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ) => by
      obtain ⟨C, hγeq, hδeq⟩ := hrep
      intro a b hbab
      rw [hδeq] at hbab
      exact ih (cequiv_trans (hγeq.symm ▸ cequiv_plug C heq) hbab))
    -- s1：`p ⊢ q ⇒ p ⊳ q`
    (fun {p q} (h : Entails p q) => by
      intro a b hab ρ
      obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
      have hcl : (Canon.frame W atomRel).truth p ρ ≤ (Canon.frame W atomRel).truth q ρ :=
        (Canon.isModel W atomRel).classical p q h ρ
      exact PSet.le_trans (pset_le_of_eq h1.symm) (PSet.le_trans hcl (pset_le_of_eq h2)))
    -- s2：`(t ⊳ p) ∧ (p ⊢ q) ⇒ t ⊳ q`
    (fun {t p q} (_ : Derivable (t ⊳ p)) (h : Entails p q)
        (ih : ∀ {a b : Form}, ((t ⊳ p) ⊣⊢ (a ⊳ b)) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ) => by
      intro a b hab ρ
      obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
      have hmid : (Canon.frame W atomRel).truth t ρ ≤ (Canon.frame W atomRel).truth p ρ :=
        ih (cequiv_refl (t ⊳ p)) ρ
      have hcl : (Canon.frame W atomRel).truth p ρ ≤ (Canon.frame W atomRel).truth q ρ :=
        (Canon.isModel W atomRel).classical p q h ρ
      exact PSet.le_trans (pset_le_of_eq h1.symm)
        (PSet.le_trans hmid (PSet.le_trans hcl (pset_le_of_eq h2))))
    -- f1：`t R φ ⇒ t R ∀x φ`
    (fun {k t φ x} (hx : ¬ FreeIn x t) (_ : Derivable (Kind.form k t φ))
        (ih : ∀ {a b : Form}, (Kind.form k t φ ⊣⊢ (a ⊳ b)) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ) => by
      cases k
      · have hle := inv_supp_of_ih_supp (M := Canon.frame W atomRel) (a := t) (φ := φ) ih
        intro a b hab ρ
        obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
        refine PSet.le_trans (pset_le_of_eq h1.symm) (PSet.le_trans ?_ (pset_le_of_eq h2))
        show (Canon.frame W atomRel).truth t ρ
          ≤ PSet.iInter (fun X : PSet W => (Canon.frame W atomRel).truth φ (upd ρ x X))
        refine PSet.le_iInter _ (fun X => ?_)
        exact (Frame.truth_upd_notFree (Canon.frame W atomRel) (Canon.isModel W atomRel)
          hx ρ X) ▸ hle (upd ρ x X)
      · intro a b hab
        exact fun _ => absurd hab (support_not_cequiv_form (t := t) (φ := Form.all x φ)
          (a := a) (b := b)))
    -- f2：`p R φ ⇒ (∀x p) R φ`
    (fun {k p φ x} (hx : ¬ FreeIn x φ) (_ : Derivable (Kind.form k p φ))
        (ih : ∀ {a b : Form}, (Kind.form k p φ ⊣⊢ (a ⊳ b)) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ) => by
      cases k
      · have hle := inv_supp_of_ih_supp (M := Canon.frame W atomRel) (a := p) (φ := φ) ih
        intro a b hab ρ
        obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
        refine PSet.le_trans (pset_le_of_eq h1.symm) (PSet.le_trans ?_ (pset_le_of_eq h2))
        show PSet.iInter (fun X : PSet W => (Canon.frame W atomRel).truth p (upd ρ x X))
          ≤ (Canon.frame W atomRel).truth φ ρ
        refine PSet.le_trans (PSet.iInter_le _ (ρ x)) ?_
        exact (Frame.truth_upd_notFree (Canon.frame W atomRel) (Canon.isModel W atomRel)
          hx ρ (ρ x)) ▸ hle (upd ρ x (ρ x))
      · intro a b hab
        exact fun _ => absurd hab (support_not_cequiv_form (t := Form.all x p) (φ := φ)
          (a := a) (b := b)))
    -- f3：`(a R φ) ∧ (b R φ) ⇒ (a ∧ b) R φ`
    (fun {k a b φ} (_ : Derivable (Kind.form k a φ)) (_ : Derivable (Kind.form k b φ))
        (ih₁ : ∀ {a' b' : Form}, (Kind.form k a φ ⊣⊢ (a' ⊳ b')) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a' ρ ≤ (Canon.frame W atomRel).truth b' ρ)
        (ih₂ : ∀ {a' b' : Form}, (Kind.form k b φ ⊣⊢ (a' ⊳ b')) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a' ρ ≤ (Canon.frame W atomRel).truth b' ρ) => by
      cases k
      · obtain ⟨h₁, _⟩ := inv_supp_of_two_ih_supp (M := Canon.frame W atomRel)
          (a := a) (b := b) (φ := φ) ih₁ ih₂
        intro a' b' hab ρ
        obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
        refine PSet.le_trans (pset_le_of_eq h1.symm) (PSet.le_trans ?_ (pset_le_of_eq h2))
        show (Canon.frame W atomRel).truth (Form.and a b) ρ
          ≤ (Canon.frame W atomRel).truth φ ρ
        intro w hw
        exact h₁ ρ w hw.1
      · intro a' b' hab
        exact fun _ => absurd hab (support_not_cequiv_form (t := Form.and a b) (φ := φ)
          (a := a') (b := b')))
    -- f4：`(t R φ) ∧ (t R ψ) ⇒ t R (φ ∧ ψ)`
    (fun {k t φ ψ} (_ : Derivable (Kind.form k t φ)) (_ : Derivable (Kind.form k t ψ))
        (ih₁ : ∀ {a' b' : Form}, (Kind.form k t φ ⊣⊢ (a' ⊳ b')) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a' ρ ≤ (Canon.frame W atomRel).truth b' ρ)
        (ih₂ : ∀ {a' b' : Form}, (Kind.form k t ψ ⊣⊢ (a' ⊳ b')) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a' ρ ≤ (Canon.frame W atomRel).truth b' ρ) => by
      cases k
      · have h₁ : ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth t ρ ≤ (Canon.frame W atomRel).truth φ ρ :=
          inv_supp_of_ih_supp (M := Canon.frame W atomRel) (a := t) (φ := φ) ih₁
        have h₂ : ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth t ρ ≤ (Canon.frame W atomRel).truth ψ ρ :=
          inv_supp_of_ih_supp (M := Canon.frame W atomRel) (a := t) (φ := ψ) ih₂
        intro a' b' hab ρ
        obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
        refine PSet.le_trans (pset_le_of_eq h1.symm) (PSet.le_trans ?_ (pset_le_of_eq h2))
        show (Canon.frame W atomRel).truth t ρ
          ≤ (Canon.frame W atomRel).truth (Form.and φ ψ) ρ
        exact PSet.le_inf (h₁ ρ) (h₂ ρ)
      · intro a' b' hab
        exact fun _ => absurd hab (support_not_cequiv_form (t := t) (φ := Form.and φ ψ)
          (a := a') (b := b')))
    -- r1：结论是反驳式，与支持式不可能经典等价（形状冲突引理；归纳假设用不上）
    (fun {t φ} (_ : Derivable (t ⊳ .not φ))
        (_ : ∀ {a b : Form}, ((t ⊳ .not φ) ⊣⊢ (a ⊳ b)) →
          ∀ ρ : Nat → PSet W,
            (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ) => by
      intro a b hbab
      exact fun _ => absurd hbab (support_not_cequiv_refut (u := t) (v := φ)
        (a := a) (b := b)))
    -- p1：`(a R c) ∧ (b R d) ∧ ((c ∧ d) S f) ⇒ (a ∧ b) R ((c ∧ d) S f)`
    (fun {kR kS a₀ b₀ c d f} (_ : Derivable (Kind.form kR a₀ c))
        (_ : Derivable (Kind.form kR b₀ d)) (h₃ : Derivable (Kind.form kS (.and c d) f))
        _ _ _ => by
      cases kR
      · intro a b hab ρ
        obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
        refine PSet.le_trans (pset_le_of_eq h1.symm) (PSet.le_trans ?_ (pset_le_of_eq h2))
        exact PSet.le_of_eq_top (Derivable.soundness (Canon.frame W atomRel)
          (Canon.isModel W atomRel) h₃ ρ)
      · intro a b hab
        exact fun _ => absurd hab (support_not_cequiv_form (t := Form.and a₀ b₀)
          (φ := Kind.form kS (Form.and c d) f) (a := a) (b := b)))
    -- p2：`(a R c) ∧ ((∀x c) S f) ⇒ (∀x a) R ((∀x c) S f)`
    (fun {kR kS a₀ c f x} (_ : Derivable (Kind.form kR a₀ c))
        (h₂ : Derivable (Kind.form kS (.all x c) f)) (_ : ¬ FreeIn x f)
        _ _ => by
      cases kR
      · intro a b hab ρ
        obtain ⟨h1, h2⟩ := transfer_frame htl W atomRel hab ρ
        refine PSet.le_trans (pset_le_of_eq h1.symm) (PSet.le_trans ?_ (pset_le_of_eq h2))
        exact PSet.le_of_eq_top (Derivable.soundness (Canon.frame W atomRel)
          (Canon.isModel W atomRel) h₂ ρ)
      · intro a b hab
        exact fun _ => absurd hab (support_not_cequiv_form (t := Form.all x a₀)
          (φ := Kind.form kS (Form.all x c) f) (a := a) (b := b)))

/-- **主目标的直接推论**（形状与 `EFree.noE_supp_le`／`RestrictedE.supp_le₁_canon` 一致）：
    由 `Derivable (a ⊳ b)` 得 `⟦a⟧ρ ≤ ⟦b⟧ρ`（对一切赋值），**假设** `TransferLemma` 成立。 -/
theorem supp_le_of_transferLemma_canon (htl : TransferLemma) (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b : Form} (h : Derivable (a ⊳ b)) :
    ∀ ρ, (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ :=
  supp_le_of_cequiv_canon htl W atomRel h (cequiv_refl (a ⊳ b))

/-! ## 6. 两条推论：把条件化前沿写成定理 -/

/-- **一般转移引理 ⇒ 支持传递的结论在一切典范框架中有效**（条件化的 N3 障碍）。
    写法照 `EFree.noE_transitivity_valid_canon`／`RestrictedE.transitivity_valid_canon₁`。 -/
theorem transitivity_valid_canon_of_transferLemma (htl : TransferLemma) (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b c : Form}
    (h₁ : Derivable (a ⊳ b)) (h₂ : Derivable (b ⊳ c)) :
    (Canon.frame W atomRel).Valid (a ⊳ c) := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  intro ρ
  have hle : (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth c ρ :=
    PSet.le_trans (supp_le_of_transferLemma_canon htl W atomRel h₁ ρ)
      (supp_le_of_transferLemma_canon htl W atomRel h₂ ρ)
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth a ρ)
    ((Canon.base W atomRel).truth c ρ)⟩ : PSet W) = ⊤
  refine (PSet.const_eq_top_iff w₀).mpr (Or.inl ?_)
  rwa [← Canon.frame_truth W atomRel c ρ]

/-- **一般转移引理 ⇒ S7（不同主体合取）的结论在一切典范框架中有效**（同型版本）。
    写法照 `EFree.noE_s7_valid_canon`／`RestrictedE.s7_valid_canon₁`。 -/
theorem s7_valid_canon_of_transferLemma (htl : TransferLemma) (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b φ ψ : Form}
    (h₁ : Derivable (a ⊳ φ)) (h₂ : Derivable (b ⊳ ψ)) :
    (Canon.frame W atomRel).Valid (Form.and a b ⊳ Form.and φ ψ) := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  intro ρ
  have hle₁ : (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth φ ρ :=
    supp_le_of_transferLemma_canon htl W atomRel h₁ ρ
  have hle₂ : (Canon.frame W atomRel).truth b ρ ≤ (Canon.frame W atomRel).truth ψ ρ :=
    supp_le_of_transferLemma_canon htl W atomRel h₂ ρ
  have hleft : (Canon.frame W atomRel).truth a ρ ⊓ (Canon.frame W atomRel).truth b ρ
      ≤ (Canon.frame W atomRel).truth φ ρ ⊓ (Canon.frame W atomRel).truth ψ ρ :=
    PSet.le_inf (PSet.le_trans (PSet.inf_le_left _ _) hle₁)
      (PSet.le_trans (PSet.inf_le_right _ _) hle₂)
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth (Form.and a b) ρ)
    ((Canon.base W atomRel).truth (Form.and φ ψ) ρ)⟩ : PSet W) = ⊤
  refine (PSet.const_eq_top_iff w₀).mpr (Or.inl ?_)
  rw [← Canon.frame_truth W atomRel (Form.and φ ψ) ρ]
  exact hleft

/-! ## 7. 强度声明（再次强调，勿夸大）

以上结论**全部以 `TransferLemma` 为假设**（`htl`），且**只对典范框架陈述**。本文件：

* **没有**证明 `TransferLemma`，也**没有**给出它的任何部分进展；
* **没有**声称 `TruthPropagation` 成立或不成立——本文件与它无任何交互；
* 只证明了「motive 换成模 `⊣⊢` 之后，`E` 的洞自动闭合」，从而把全量 `Derivable` 的
  支持-蕴含不变量在**典范框架**上**精确地**归约到 `TransferLemma`
  （九个规则支各用一次它的分量等式，经 `transfer_frame` 搬到框架层），
  并给出两条条件化的前沿推论；
* 限定在典范框架是**必须**的：只有典范框架有命题性桥梁 `Canon.frame_truth`
  （`Frame.truth` 与 `Base.truth` 非定义性相等，见文件头 0.1 节）。 -/

end

end EvidenceLogic
