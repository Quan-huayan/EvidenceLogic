/-
# TrackE：**无 E 片段**的支持侧不变量，与「支持传递／S7 的反模型法失效」

本文件**不修改任何已有文件**，只在 `import EvidenceLogic` 之上补一批新结论。

## 0. 这条结果的**强度**（务必连同结论一起读，不要夸大）

「支持传递」与「S7（不同主体合取）」的反模型法之所以走不通，已知的障碍是
**真值传播引理**：它在对 `Derivable` 归纳时，除元规则 `E` 的「洞在顶层」那一支外
都能闭合，而那一支恰好归约到本工程公开的**完备性／相合性**问题
（见 `EvidenceLogic/NonAdmissible.lean` 第十一、十二节与 `docs/讨论与局限.md` 第 2 节）。

本文件因此**只做无 E 片段**（`Derivable₀`：`Derivable` 去掉构造子 `e`）。去掉 `E`
之后那个洞就不存在了，支持侧的不变量可以真正证出来，于是本文件得到的是：

> **任何支持传递／S7 的 N3 见证，至少有一个前提的推导不是无 E 的。**

精确形式：若两个前提都有**无 E 的推导**，则结论在**一切**典范框架中有效，
因而**不存在**典范框架反模型——而本工程全部反模型都是典范框架，故反模型法失效。
换言之，见证的某个前提**不存在无 E 的推导**，即它的**每个**推导都要用到元规则 `E`。

这是本文件的**全部**强度：它**没有**证明支持传递／S7 的规则级非可容许性，
也**没有**证明它们在 `Derivable` 下不可导出。**全量版本（允许 `E`）仍然归约到
`TruthPropagation`／相合性的公开问题**，本文件对它没有任何推进。

## 1. 文件内容

1. `Derivable₀`：九个构造子（与 `Derivable` 的 `s1 s2 f1 f2 f3 f4 r1 p1 p2` 形状完全一致，
   只去掉 `e`），以及包含关系 `Derivable₀.toDerivable : Derivable₀ φ → Derivable φ`；
2. `noE_soundness₀`：无 E 片段的可靠性（九个分支照 `Soundness.lean` 改写，无 `plug_congr`）；
3. `noE_supp_le`：**核心不变量**——由 `Derivable₀ (a ⊳ b)` 得 `⟦a⟧ρ ≤ ⟦b⟧ρ`。
   注意**反驳侧的同型不变量是假的**（`r1` 立刻给出反例：`Entails p q` 时有
   `Derivable₀ (p ⊳ ¬q)`，但 `⟦p⟧ ≰ ⟦q⟧` 一般成立），故本不变量**只**覆盖支持侧；
   形式化时把它表述为「结论形如 `a ⊳ b` 的公式」上的谓词 `SuppInv`，其余形状取 `True`；
4. `noE_transitivity_valid_canon` / `noE_s7_valid_canon`：由第 3 步把不变量用在
   典范框架上，得到两条**机器验证的障碍**——相应结论在**一切**典范框架中有效，
   于是 `not_derivable_of_countermodel` 这条路（反模型法）对无 E 片段失效。

## 2. 技术注记（沿用本仓库既有约定）

* 不使用 `induction` 于 `Form`（嵌套归纳）；对 `Derivable₀` 的归纳**用显式消去子
  `Derivable₀.rec`**，并把归纳索引位保持为**变量**（`SuppInv`）——两者缺一不可：
  索引位写成 `a ⊳ b` 时，`f1`–`f4`／`p1`／`p2` 的结论形状 `Kind.form k …` 会卡在 `k` 上；
  而方程式风格的结构递归会因索引位不是裸变量而要求终止性证明（`failed to eliminate
  recursive application`），用消去子则不需要任何终止性证明。`Form` 的形状分歧一律用
  `cases`（如 `f1`–`f4` 里的 `cases k`）；
* 不在 `PSet` 层用 `decide`，不使用 `fin_cases`，不使用 `sorry`／`axiom`／`admit`；
* 未使用的绑定一律写 `_`，以保证 `lake env lean TrackE.lean` **零警告**。
-/
import EvidenceLogic.Model.Canonical
import EvidenceLogic.Model.Soundness

namespace EvidenceLogic

noncomputable section

open PSet

/-! ## 1. 无 E 的推导关系 `Derivable₀` -/

/-- **无 E 片段**的可推导关系：`Derivable` 去掉元规则 `E` 后的**九个**构造子。

各构造子的形状与 `Derivable` 的同名构造子**完全一致**（参数名、隐式性、副作用条件），
唯一的差别是不含 `e`。 -/
inductive Derivable₀ : Form → Prop where
  /-- **S1** 后承支持：`p ⊢ q ⇒ p ⊳ q`。 -/
  | s1 {p q : Form} (h : Entails p q) : Derivable₀ (p ⊳ q)
  /-- **S2** 后承封闭：`(t ⊳ p) ∧ (p ⊢ q) ⇒ t ⊳ q`。 -/
  | s2 {t p q : Form} (h₁ : Derivable₀ (t ⊳ p)) (h : Entails p q) : Derivable₀ (t ⊳ q)
  /-- **F1** 同一主体全称引入：`x ∉ FV(t)`，`t R φ ⇒ t R ∀x φ`。 -/
  | f1 {k : Kind} {t φ : Form} {x : Nat} (hx : ¬ FreeIn x t)
      (h : Derivable₀ (Kind.form k t φ)) : Derivable₀ (Kind.form k t (.all x φ))
  /-- **F2** 全称主体：`x ∉ FV(φ)`，`p R φ ⇒ (∀x p) R φ`。 -/
  | f2 {k : Kind} {p φ : Form} {x : Nat} (hx : ¬ FreeIn x φ)
      (h : Derivable₀ (Kind.form k p φ)) : Derivable₀ (Kind.form k (.all x p) φ)
  /-- **F3** 合取主体：`(a R φ) ∧ (b R φ) ⇒ (a ∧ b) R φ`。 -/
  | f3 {k : Kind} {a b φ : Form} (h₁ : Derivable₀ (Kind.form k a φ))
      (h₂ : Derivable₀ (Kind.form k b φ)) : Derivable₀ (Kind.form k (.and a b) φ)
  /-- **F4** 同一主体合取引入：`(t R φ) ∧ (t R ψ) ⇒ t R (φ ∧ ψ)`。 -/
  | f4 {k : Kind} {t φ ψ : Form} (h₁ : Derivable₀ (Kind.form k t φ))
      (h₂ : Derivable₀ (Kind.form k t ψ)) : Derivable₀ (Kind.form k t (.and φ ψ))
  /-- **R1** 否定反驳：`t ⊳ ¬φ ⇒ t ⊲ φ`。 -/
  | r1 {t φ : Form} (h : Derivable₀ (t ⊳ .not φ)) : Derivable₀ (t ⊲ φ)
  /-- **P1** 二元合取推广（`R,S` 各自独立取 `⊳`／`⊲`）。 -/
  | p1 {kR kS : Kind} {a b c d f : Form} (h₁ : Derivable₀ (Kind.form kR a c))
      (h₂ : Derivable₀ (Kind.form kR b d)) (h₃ : Derivable₀ (Kind.form kS (.and c d) f)) :
      Derivable₀ (Kind.form kR (.and a b) (Kind.form kS (.and c d) f))
  /-- **P2** 全称推广（`R,S` 各自独立取 `⊳`／`⊲`）。 -/
  | p2 {kR kS : Kind} {a c f : Form} {x : Nat} (h₁ : Derivable₀ (Kind.form kR a c))
      (h₂ : Derivable₀ (Kind.form kS (.all x c) f)) (hx : ¬ FreeIn x f) :
      Derivable₀ (Kind.form kR (.all x a) (Kind.form kS (.all x c) f))

/-- 系统内可推导的记法：`⊢₀ φ`。 -/
scoped notation:25 "⊢₀ " φ:25 => Derivable₀ φ

namespace Derivable₀

/-- **包含关系**：无 E 片段的推导都是全系统 `Derivable` 的推导。 -/
theorem toDerivable : ∀ {φ : Form}, Derivable₀ φ → Derivable φ
  | _, @Derivable₀.s1 _ _ h => Derivable.s1 h
  | _, @Derivable₀.s2 _ _ _ h₁ h => Derivable.s2 (toDerivable h₁) h
  | _, @Derivable₀.f1 _ _ _ _ hx h => Derivable.f1 hx (toDerivable h)
  | _, @Derivable₀.f2 _ _ _ _ hx h => Derivable.f2 hx (toDerivable h)
  | _, @Derivable₀.f3 _ _ _ _ h₁ h₂ => Derivable.f3 (toDerivable h₁) (toDerivable h₂)
  | _, @Derivable₀.f4 _ _ _ _ h₁ h₂ => Derivable.f4 (toDerivable h₁) (toDerivable h₂)
  | _, @Derivable₀.r1 _ _ h => Derivable.r1 (toDerivable h)
  | _, @Derivable₀.p1 _ _ _ _ _ _ _ h₁ h₂ h₃ =>
      Derivable.p1 (toDerivable h₁) (toDerivable h₂) (toDerivable h₃)
  | _, @Derivable₀.p2 _ _ _ _ _ _ h₁ h₂ hx =>
      Derivable.p2 (toDerivable h₁) (toDerivable h₂) hx

end Derivable₀

/-! ## 2. 无 E 片段的可靠性 -/

/-- **无 E 片段的可靠性**：九个分支照 `Soundness.lean` 的对应分支改写。
由于不含构造子 `E`，此处**不需要** `Frame.plug_congr`，也不需要 `Ctx`。 -/
theorem noE_soundness₀ (M : Frame) (hM : IsModel M) : ∀ {φ : Form}, Derivable₀ φ → M.Valid φ
  | _, @Derivable₀.s1 p q h => fun ρ =>
      Derivable.valid_supp M hM (hM.s1 p q ρ (hM.classical p q h ρ))
  | _, @Derivable₀.s2 t p q h₁ h => fun ρ =>
      Derivable.valid_supp M hM (hM.s2 (M.truth t ρ) p q ρ
        (Derivable.supp_of_valid M hM (noE_soundness₀ M hM h₁ ρ))
        (hM.classical p q h ρ))
  | _, @Derivable₀.f1 k t φ x hx h => fun ρ =>
      Derivable.valid_rel M hM (hM.f1 k t φ x ρ hx
        (fun X => Derivable.rel_of_valid M hM (noE_soundness₀ M hM h (upd ρ x X))))
  | _, @Derivable₀.f2 k p φ x hx h => fun ρ =>
      Derivable.valid_rel M hM (hM.f2 k p φ x ρ hx
        (fun X => Derivable.rel_of_valid M hM (noE_soundness₀ M hM h (upd ρ x X))))
  | _, @Derivable₀.f3 k a b φ h₁ h₂ => fun ρ =>
      Derivable.valid_rel M hM (hM.f3 k (M.truth a ρ) (M.truth b ρ) φ ρ
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₁ ρ))
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₂ ρ)))
  | _, @Derivable₀.f4 k t φ ψ h₁ h₂ => fun ρ =>
      Derivable.valid_rel M hM (hM.f4 k (M.truth t ρ) φ ψ ρ
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₁ ρ))
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₂ ρ)))
  | _, @Derivable₀.r1 t φ h => fun ρ =>
      Derivable.valid_refut M hM (hM.r1 (M.truth t ρ) φ ρ
        (Derivable.supp_of_valid M hM (noE_soundness₀ M hM h ρ)))
  | _, @Derivable₀.p1 kR kS a b c d f h₁ h₂ h₃ => fun ρ =>
      Derivable.valid_rel M hM (hM.p1 kR kS a b c d f ρ
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₁ ρ))
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₂ ρ))
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₃ ρ)))
  | _, @Derivable₀.p2 kR kS a c f x h₁ h₂ hx => fun ρ =>
      Derivable.valid_rel M hM (hM.p2 kR kS a c f x ρ hx
        (fun X => Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₁ (upd ρ x X)))
        (Derivable.rel_of_valid M hM (noE_soundness₀ M hM h₂ ρ)))

/-! ## 3. 核心不变量（支持侧）

不变量只在**支持侧**成立：对形如 `a ⊳ b` 的公式要求 `⟦a⟧ρ ≤ ⟦b⟧ρ`，其余形状不作要求
（`True`）。把它写成 `Form` 上的谓词 `SuppInv` 是为了让归纳的索引位保持**变量**
（否则 `f1`–`f4`／`p1`／`p2` 的结论形状 `Kind.form k …` 会卡在 `k` 上）。

**为什么反驳侧没有同型不变量**：反驳侧的对应断言
（`Derivable₀ (a ⊲ b)` 得 `⟦a⟧ρ ⊓ ⟦b⟧ρ = ⊥`）是**假的**。
`R1` 单独看确实给出 `⟦a⟧ ≤ ⟦¬b⟧`（于是此时两真值确实不相交），但 `P1` 在
`kR = ⊲`、`kS = ⊳` 时会摧毁它：两个前提只保证 `⟦a⟧ ⊓ ⟦c⟧ = ⊥`、`⟦b⟧ ⊓ ⟦d⟧ = ⊥`，
而结论的第二项 `(c ∧ d) S f` 由可靠性真值为 `⊤`，于是该断言就**必须**给出
`⟦a⟧ ⊓ ⟦b⟧ = ⊥`——取 `a := b := ⊤`、`c := d := ⊥` 即得反例
（两个前提 `⊤ ⊲ ⊥` 由 `R1 ∘ S1` 可推导，因为 `¬⊥` 是有效式；
第三前提 `(⊥ ∧ ⊥) ⊳ f` 由 `S1` 给出）。故本节只声称支持侧。 -/

/-- **支持侧不变量**：结论形如 `a ⊳ b` 时要求 `⟦a⟧ρ ≤ ⟦b⟧ρ`，其余形状恒真。

`Form` 上的 12 个构造子全部列出（不用通配缺省），以便 `SuppInv M (a ⊳ b)`
按定义归约。 -/
def SuppInv (M : Frame) : Form → Prop
  | .supp a b => ∀ ρ : Nat → PSet M.W, M.truth a ρ ≤ M.truth b ρ
  | .var _ => True
  | .atom _ _ => True
  | .bot => True
  | .top => True
  | .not _ => True
  | .and _ _ => True
  | .or _ _ => True
  | .imp _ _ => True
  | .all _ _ => True
  | .ex _ _ => True
  | .refut _ _ => True

/-- **核心不变量（无 E 片段）**：`Derivable₀ φ` 蕴含 `SuppInv M φ`。

九个分支的闭合方式（对照任务书第三步）：
`s1`／`s2` 用 `IsModel.classical`（`E` 分支不存在，故无需 `plug_congr`）；
`f1` 用 `Frame.truth_upd_notFree` 把 `⟦t⟧(upd ρ x X)` 换回 `⟦t⟧ρ` 再套归纳假设；
`f2` 取 `iInter` 的分量 `X := ρ x`；`f3`／`f4` 逐点／`le_inf`；
`p1`／`p2` 用第二步的 `noE_soundness₀` 断言结论第二项（关系式）的真值为 `⊤`，
于是只需 `≤ ⊤`；`r1` 的结论是反驳式，落入 `SuppInv` 的 `True` 分支。 -/
theorem noE_supp_le_inv {M : Frame} (hM : IsModel M) :
    ∀ {φ : Form}, Derivable₀ φ → SuppInv M φ :=
  Derivable₀.rec (motive := fun φ _ => SuppInv M φ)
    -- s1
    (fun {p q} (h : Entails p q) => by
      intro ρ
      exact hM.classical p q h ρ)
    -- s2
    (fun {t p q} (h₁ : Derivable₀ (t ⊳ p)) (h : Entails p q) (ih : SuppInv M (t ⊳ p)) => by
      have ih' : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth p ρ := ih
      intro ρ
      exact PSet.le_trans (ih' ρ) (hM.classical p q h ρ))
    -- f1
    (fun {k t φ x} (hx : ¬ FreeIn x t) (_ : Derivable₀ (Kind.form k t φ))
        (ih : SuppInv M (Kind.form k t φ)) => by
      cases k
      · have ih' : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth φ ρ := ih
        intro ρ
        show M.truth t ρ ≤ PSet.iInter (fun X : PSet M.W => M.truth φ (upd ρ x X))
        refine PSet.le_iInter (fun X : PSet M.W => M.truth φ (upd ρ x X)) (fun X => ?_)
        exact (Frame.truth_upd_notFree M hM hx ρ X) ▸ ih' (upd ρ x X)
      · trivial)
    -- f2
    (fun {k p φ x} (hx : ¬ FreeIn x φ) (_ : Derivable₀ (Kind.form k p φ))
        (ih : SuppInv M (Kind.form k p φ)) => by
      cases k
      · have ih' : ∀ ρ : Nat → PSet M.W, M.truth p ρ ≤ M.truth φ ρ := ih
        intro ρ
        show PSet.iInter (fun X : PSet M.W => M.truth p (upd ρ x X)) ≤ M.truth φ ρ
        refine PSet.le_trans
          (PSet.iInter_le (fun X : PSet M.W => M.truth p (upd ρ x X)) (ρ x)) ?_
        exact (Frame.truth_upd_notFree M hM hx ρ (ρ x)) ▸ ih' (upd ρ x (ρ x))
      · trivial)
    -- f3
    (fun {k a b φ} (_ : Derivable₀ (Kind.form k a φ)) (_ : Derivable₀ (Kind.form k b φ))
        (ih₁ : SuppInv M (Kind.form k a φ)) (ih₂ : SuppInv M (Kind.form k b φ)) => by
      cases k
      · have i₁ : ∀ ρ : Nat → PSet M.W, M.truth a ρ ≤ M.truth φ ρ := ih₁
        have i₂ : ∀ ρ : Nat → PSet M.W, M.truth b ρ ≤ M.truth φ ρ := ih₂
        intro ρ w hw
        exact i₁ ρ w hw.1
      · trivial)
    -- f4
    (fun {k t φ ψ} (_ : Derivable₀ (Kind.form k t φ)) (_ : Derivable₀ (Kind.form k t ψ))
        (ih₁ : SuppInv M (Kind.form k t φ)) (ih₂ : SuppInv M (Kind.form k t ψ)) => by
      cases k
      · have i₁ : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth φ ρ := ih₁
        have i₂ : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth ψ ρ := ih₂
        intro ρ
        exact PSet.le_inf (i₁ ρ) (i₂ ρ)
      · trivial)
    -- r1
    (fun {t φ} (_ : Derivable₀ (t ⊳ .not φ)) (_ : SuppInv M (t ⊳ .not φ)) => trivial)
    -- p1
    (fun {kR kS a b c d f} (_ : Derivable₀ (Kind.form kR a c))
        (_ : Derivable₀ (Kind.form kR b d)) (h₃ : Derivable₀ (Kind.form kS (.and c d) f))
        _ _ _ => by
      cases kR
      · intro ρ
        exact PSet.le_of_eq_top (noE_soundness₀ M hM h₃ ρ)
      · trivial)
    -- p2
    (fun {kR kS a c f x} (_ : Derivable₀ (Kind.form kR a c))
        (h₂ : Derivable₀ (Kind.form kS (.all x c) f)) _ _ _ => by
      cases kR
      · intro ρ
        exact PSet.le_of_eq_top (noE_soundness₀ M hM h₂ ρ)
      · trivial)

/-- **核心不变量（支持侧，任务书第 3 步的陈述形状）**：
由 `Derivable₀ (a ⊳ b)` 得 `⟦a⟧ρ ≤ ⟦b⟧ρ`（对一切赋值）。 -/
theorem noE_supp_le {M : Frame} (hM : IsModel M) {a b : Form} (h : Derivable₀ (a ⊳ b)) :
    ∀ ρ : Nat → PSet M.W, M.truth a ρ ≤ M.truth b ρ :=
  noE_supp_le_inv hM h

/-! ## 4. 两条机器验证的障碍（反模型法失效）

把第 3 步的不变量用在**典范框架**上：两个前提给出
`⟦a⟧ ≤ ⟦b⟧ ≤ ⟦c⟧`，而典范框架里 `supp` 就是 `suppP`，第一析取项 `⟦a⟧ ≤ ⟦c⟧`
成立即得关系式真值为 `⊤`（`PSet.const_eq_top_iff`）。

**注意这并不等于「规则不可导出」**：它说明的是「反模型法对无 E 片段失效」，
即任何支持传递／S7 的 N3 见证都不可能在典范框架里被否证；
结合第 1 步的包含关系，它给出文件头所述的那条受限于无 E 片段的结论。 -/

/-- **支持传递的无 E 障碍**：若 `Derivable₀ (a ⊳ b)` 且 `Derivable₀ (b ⊳ c)`，
则 `a ⊳ c` 在**一切**典范框架中有效——于是 `not_derivable_of_countermodel` 走不通。 -/
theorem noE_transitivity_valid_canon (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b c : Form}
    (h₁ : Derivable₀ (a ⊳ b)) (h₂ : Derivable₀ (b ⊳ c)) :
    (Canon.frame W atomRel).Valid (a ⊳ c) := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  have hM : IsModel (Canon.frame W atomRel) := Canon.isModel W atomRel
  intro ρ
  have hle : (Canon.frame W atomRel).truth a ρ ≤ (Canon.base W atomRel).truth c ρ := by
    rw [← Canon.frame_truth W atomRel c ρ]
    exact PSet.le_trans (noE_supp_le hM h₁ ρ) (noE_supp_le hM h₂ ρ)
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth a ρ)
    ((Canon.base W atomRel).truth c ρ)⟩ : PSet W) = ⊤
  exact (PSet.const_eq_top_iff w₀).mpr (Or.inl hle)

/-- **S7（不同主体合取）的无 E 障碍**：若 `Derivable₀ (a ⊳ φ)` 且
`Derivable₀ (b ⊳ ψ)`，则 `(a ∧ b) ⊳ (φ ∧ ψ)` 在**一切**典范框架中有效。 -/
theorem noE_s7_valid_canon (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b φ ψ : Form}
    (h₁ : Derivable₀ (a ⊳ φ)) (h₂ : Derivable₀ (b ⊳ ψ)) :
    (Canon.frame W atomRel).Valid (Form.and a b ⊳ Form.and φ ψ) := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  have hM : IsModel (Canon.frame W atomRel) := Canon.isModel W atomRel
  intro ρ
  have hle₁ : (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth φ ρ :=
    noE_supp_le hM h₁ ρ
  have hle₂ : (Canon.frame W atomRel).truth b ρ ≤ (Canon.frame W atomRel).truth ψ ρ :=
    noE_supp_le hM h₂ ρ
  have hleft : (Canon.frame W atomRel).truth a ρ ⊓ (Canon.frame W atomRel).truth b ρ
      ≤ (Canon.base W atomRel).truth φ ρ ⊓ (Canon.base W atomRel).truth ψ ρ := by
    refine PSet.le_inf ?_ ?_
    · exact PSet.le_trans (PSet.inf_le_left _ _)
        (by rw [← Canon.frame_truth W atomRel φ ρ]; exact hle₁)
    · exact PSet.le_trans (PSet.inf_le_right _ _)
        (by rw [← Canon.frame_truth W atomRel ψ ρ]; exact hle₂)
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth (Form.and a b) ρ)
    ((Canon.base W atomRel).truth (Form.and φ ψ) ρ)⟩ : PSet W) = ⊤
  exact (PSet.const_eq_top_iff w₀).mpr (Or.inl hleft)

/-! ## 5. 强度声明（再次强调，勿夸大）

以上第 3、4 步**只覆盖无 E 片段**。因此第 4 步的确切内容是：

> **任何支持传递／S7 的 N3 见证，至少有一个前提的推导不是无 E 的
> （即其推导在顶层用了元规则 `E`）。**

它**不是**「支持传递／S7 不可容许」，也**不是**「它们在 `Derivable` 下不可导出」。
全量版本（允许 `E`）仍归约到 `TruthPropagation`／相合性公开问题
（`EvidenceLogic/NonAdmissible.lean` 第十一、十二节）：
去掉 `E` 只是把「洞在顶层」那一支消掉，从而让支持侧不变量可证。 -/

end

end EvidenceLogic
