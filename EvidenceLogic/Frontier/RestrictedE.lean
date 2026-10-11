/-
# TrackH：**受限 E 片段**在**典范框架**上的支持-蕴含不变量

本文件**不修改任何已有文件**，只在既有 `import` 之上补一批新结论。
它是 `EvidenceLogic/EFree.lean`（**完全禁用 `E`**）的**严格扩张**。

## 0. 这条结果的**强度**（务必连同结论一起读，不要夸大）

`EFree` 只处理不含元规则 `E` 的推导。那里支持侧不变量 `noE_supp_le` 之所以可证，
是因为对 `Derivable₀` 归纳时根本不存在 `E` 的「洞在顶层」那一支——而那一支恰好归约到
本工程公开的**相合性／完备性**问题（见 `EvidenceLogic/NonAdmissible.lean` 第十一、十二节
与 `docs/讨论与局限.md` 第 2 节）。

本文件把缺口**缩小一格**：允许 `E`，但**每次 `E` 的源公式必须不含关系子公式**
（谓词 `NoRel`：既不出现 `⊳`／`⊲` 作为子公式，也不把它们放进原子谓词的参数里）。
在这个受限片段 `Derivable₁` 上，支持-蕴含不变量在**一切典范框架**上成立，于是得到：

> **任何支持传递／S7 的 N3 见证，至少有一个前提的推导在顶层用了 `E`，
> 且该 `E` 的源公式含关系子公式**（即“嵌套关系重写”）。

精确形式：若两个前提都有**受限 E 的推导** `Derivable₁`，则结论在**一切**典范框架中
有效（`transitivity_valid_canon₁`／`s7_valid_canon₁`），因而**不存在**典范框架反模型；
而本工程全部反模型都取自典范框架，故反模型法对这一片段失效。

**这不是**「支持传递／S7 不可容许」，**也不是**「它们在 `Derivable` 下不可导出」，
更**不是**规则级的非可容许性。**全量版本（允许任意 `E`）仍然归约到
`TruthPropagation`／相合性的公开问题**，本文件对它没有任何推进：
本文件只证明了「`E` 的源公式不含关系子公式时，那个洞是**空集**」。

**同样重要的是，本文件的不变量只对典范框架陈述**（`supp_le₁_canon`），
**不**声称任意 `IsModel M` 上的不变量——那在**陈述层面**就有缺口，理由见第 2 节注 1。
因此两条障碍也只在典范框架上陈述。

## 1. 文件内容

1. `NoRel`／`NoRelList`：「不含关系子公式」的谓词（`Form` 是**嵌套**归纳类型，
   `atom` 的参数是 `List Form`，故写成 `mutual`，照抄 `Base.truth`／`Base.truths` 的形状），
   以及 `noRel_of_plug`（上下文填入后仍不含关系子公式则原公式也不含）；
2. `botBase`：把 `suppI`／`refutI` 都取 `⊥` 的“全空基结构”，以及
   `truth_botBase_eq_canon`：`NoRel` 公式在 `botBase` 与 `Canon.base` 上真值相同
   （两边只有 `suppI`／`refutI` 不同，而 `NoRel` 公式用不到它们）；
3. `Derivable₁`：九条同 `Derivable`，第十条是**受限 `E`**（源公式需 `NoRel`），
   加上 `Derivable₁.toDerivable : Derivable₁ φ → Derivable φ` 与可靠性 `soundness₁`；
4. `SupInv`、`supp_inv_false_canon`（“洞在顶层且 `δ` 是支持式”在典范框架下是空集）、
   `supInv_plug_canon`（上下文填入保持 `SupInv`）与 `supp_le₁_canon`：**核心不变量**；
5. `transitivity_valid_canon₁`／`s7_valid_canon₁`：两条机器验证的障碍。

## 2. 技术注记（含本次发现的三条 Lean 事实）

* 不使用 `induction` 于 `Form`（嵌套归纳）；对 `Derivable₁` 的归纳**用显式消去子
  `Derivable₁.rec`**，并把归纳索引位保持为**变量**（`SupInv`）；
* **注 1（为什么不能对任意模型陈述不变量）**：`M.truth φ ρ` 与
  `(Canon.base M.W M.atomRel).truth φ ρ` **不是定义性相等**——`Frame.truth` 与 `Base.truth`
  分别读 `Frame.supp` 与 `Base.suppI` 两个**不同字段**。只有 `Canon.frame` 才有
  `Canon.frame_truth` 这条**命题性**等式可用。因此在任意 `IsModel M` 下，
  「洞在顶层」那一支要在 `M` 上得 `M.truth φ₀ ρ = ⊤` 就只能循环（需要 `M.truth (a ⊳ b) ρ = ⊤`，
  正是待证者）。本文件因此把不变量限制在典范框架；
* **注 2**：Lean 4 **不允许**在 `mutual` 之前挂文档注释（以「斜杠加短横线」开头的注释块）
  ——那会报 `unexpected token 'mutual'`；必须改用普通块注释（同样以「斜杠加短横线」开头）。
* **注 3**：`NoRel`／`truth` 在复合形状上**不是**定义性可归约的，故递归调用一律**显式给出
  公式隐变量**（`(φ := φ)`／`(a := …)`），否则隐变量会从目标反推成整项（如 `φ.not`）；
* `noRel_of_plug` 用方程风格结构递归，`.not`／`.andL` 等支先用 `have` 把 `NoRel (C.plug a)`
  重述成目标形状（定义性归约把 `.plug` 展开）；
* 未使用的绑定一律写 `_`，不使用 `sorry`／`axiom`／`admit`，
  以保证 `lake env lean TrackH.lean` **零错误零警告**。
-/
import EvidenceLogic.Model.Canonical
import EvidenceLogic.Model.Soundness
import EvidenceLogic.Frontier.EFree

namespace EvidenceLogic

noncomputable section

open PSet

/-! ## 1. 谓词「不含关系子公式」 -/

/- **不含关系子公式**：`φ` 中不出现 `⊳`／`⊲`（包括出现在原子谓词的参数列表里）。

`Form` 是**嵌套**归纳类型（`.atom i ts` 里 `ts : List Form`），故与列表版 `NoRelList`
写成 `mutual`（形状照抄 `Base.truth`／`Base.truths`；注意注 2：`mutual` 前不能用文档注释）。 -/
mutual
  /-- 公式不含关系子公式。 -/
  def NoRel : Form → Prop
    | .var _ => True
    | .atom _ ts => NoRelList ts
    | .bot => True
    | .top => True
    | .not φ => NoRel φ
    | .and φ ψ => NoRel φ ∧ NoRel ψ
    | .or φ ψ => NoRel φ ∧ NoRel ψ
    | .imp φ ψ => NoRel φ ∧ NoRel ψ
    | .all _ φ => NoRel φ
    | .ex _ φ => NoRel φ
    | .supp _ _ => False
    | .refut _ _ => False

  /-- 列表版：每一项都不含关系子公式。 -/
  def NoRelList : List Form → Prop
    | [] => True
    | t :: ts => NoRel t ∧ NoRelList ts
end

/-- 支持式**不**「不含关系子公式」。 -/
theorem noRel_supp {a b : Form} : ¬ NoRel (a ⊳ b) := id

/-- 反驳式**不**「不含关系子公式」。 -/
theorem noRel_refut {a b : Form} : ¬ NoRel (a ⊲ b) := id

/-- 从 `NoRelList (q ++ u :: rest)` 取出中间项 `u` 的 `NoRel`。 -/
theorem noRel_of_mid {q rest : List Form} {u : Form}
    (h : NoRelList (q ++ u :: rest)) : NoRel u := by
  induction q with
  | nil => exact h.1
  | cons _ _ ih => exact ih h.2

/-- `Ctx.plug a` 不含关系子公式蕴含 `a` 不含关系子公式。

方程风格结构递归（结构化于 `Ctx`，无需终止性证明）。`.atom` 支用 `noRel_of_mid`
从参数列表里取出落在洞上的那一项；其余支先用 `have` 把前提重述成目标形状（注 3）。 -/
theorem noRel_of_plug : ∀ (C : Ctx) {a : Form}, NoRel (C.plug a) → NoRel a
  | .hole, _, h => h
  | .atom i pre c post, a, h =>
      noRel_of_plug c (noRel_of_mid (q := pre) (rest := post) (u := Ctx.plug c a) h)
  | .not c, a, h => by
      have hc : NoRel (Ctx.plug c a) := h
      exact noRel_of_plug c hc
  | .andL c ψ, a, h => by
      have h' : NoRel (Form.and (Ctx.plug c a) ψ) := h
      exact noRel_of_plug c h'.1
  | .andR φ' c, a, h => by
      have h' : NoRel (Form.and φ' (Ctx.plug c a)) := h
      exact noRel_of_plug c h'.2
  | .orL c ψ, a, h => by
      have h' : NoRel (Form.or (Ctx.plug c a) ψ) := h
      exact noRel_of_plug c h'.1
  | .orR φ' c, a, h => by
      have h' : NoRel (Form.or φ' (Ctx.plug c a)) := h
      exact noRel_of_plug c h'.2
  | .impL c ψ, a, h => by
      have h' : NoRel (Form.imp (Ctx.plug c a) ψ) := h
      exact noRel_of_plug c h'.1
  | .impR φ' c, a, h => by
      have h' : NoRel (Form.imp φ' (Ctx.plug c a)) := h
      exact noRel_of_plug c h'.2
  | .all x c, a, h => by
      have hc : NoRel (Ctx.plug c a) := h
      exact noRel_of_plug c hc
  | .ex x c, a, h => by
      have hc : NoRel (Ctx.plug c a) := h
      exact noRel_of_plug c hc
  | .suppL c ψ, a, h => by
      have h' : NoRel (Form.supp (Ctx.plug c a) ψ) := h
      exact (h' : False).elim
  | .suppR t c, a, h => by
      have h' : NoRel (Form.supp t (Ctx.plug c a)) := h
      exact (h' : False).elim
  | .refutL c ψ, a, h => by
      have h' : NoRel (Form.refut (Ctx.plug c a) ψ) := h
      exact (h' : False).elim
  | .refutR t c, a, h => by
      have h' : NoRel (Form.refut t (Ctx.plug c a)) := h
      exact (h' : False).elim

/-! ## 2. 全空基结构与 `NoRel` 公式的真值

`botBase W atomRel` 把 `suppI`／`refutI` 都取 `⊥`。它与典范基结构 `Canon.base W atomRel`
的**唯一**差别就在这两个字段上，而 `NoRel` 公式用不到它们，故真值相同。 -/

/-- **全空基结构**：`suppI ≡ ⊥`、`refutI ≡ ⊥`。 -/
abbrev botBase (W : Type) (atomRel : Nat → List (PSet W) → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := fun _ _ => ⊥, refutI := fun _ _ => ⊥ }

/- **`NoRel` 公式的真值与 `suppI`／`refutI` 无关**：全空基结构与典范基结构一致。

对公式与列表写成 `mutual`（`.atom` 情形需要列表版引理）；`NoRel` 把 `.supp`／`.refut`
两个构造子排除掉，而这两支正是唯一用到 `suppI`／`refutI` 的地方。
递归调用显式给出公式隐变量（注 3）。 -/
mutual
  /-- 公式版。 -/
  theorem truth_botBase_eq_canon {W : Type} (atomRel : Nat → List (PSet W) → PSet W) :
      ∀ {φ : Form}, NoRel φ → ∀ ρ : Nat → PSet W,
        (botBase W atomRel).truth φ ρ = (Canon.base W atomRel).truth φ ρ
    | .var _, _, _ => rfl
    | .atom i ts, h, ρ => by
        show atomRel i ((botBase W atomRel).truths ρ ts)
          = atomRel i ((Canon.base W atomRel).truths ρ ts)
        rw [truth_botBase_eq_canon_list atomRel ρ h]
    | .bot, _, _ => rfl
    | .top, _, _ => rfl
    | .not φ, h, ρ => by
        show ((botBase W atomRel).truth φ ρ)ᶜ = ((Canon.base W atomRel).truth φ ρ)ᶜ
        exact congrArg Compl.compl (truth_botBase_eq_canon atomRel (φ := φ) h ρ)
    | .and φ ψ, h, ρ => by
        show (botBase W atomRel).truth φ ρ ⊓ (botBase W atomRel).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊓ (Canon.base W atomRel).truth ψ ρ
        rw [truth_botBase_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_botBase_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .or φ ψ, h, ρ => by
        show (botBase W atomRel).truth φ ρ ⊔ (botBase W atomRel).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [truth_botBase_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_botBase_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .imp φ ψ, h, ρ => by
        show ((botBase W atomRel).truth φ ρ)ᶜ ⊔ (botBase W atomRel).truth ψ ρ
          = ((Canon.base W atomRel).truth φ ρ)ᶜ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [truth_botBase_eq_canon atomRel (φ := φ) h.1 ρ,
          truth_botBase_eq_canon atomRel (φ := ψ) h.2 ρ]
    | .all x φ, h, ρ => by
        apply PSet.iInter_congr
        intro X
        show (botBase W atomRel).truth φ (upd ρ x X)
          = (Canon.base W atomRel).truth φ (upd ρ x X)
        exact truth_botBase_eq_canon atomRel (φ := φ) h (upd ρ x X)
    | .ex x φ, h, ρ => by
        apply PSet.iUnion_congr
        intro X
        show (botBase W atomRel).truth φ (upd ρ x X)
          = (Canon.base W atomRel).truth φ (upd ρ x X)
        exact truth_botBase_eq_canon atomRel (φ := φ) h (upd ρ x X)
    | .supp _ _, h, _ => absurd h noRel_supp
    | .refut _ _, h, _ => absurd h noRel_refut

  /-- 列表版。 -/
  theorem truth_botBase_eq_canon_list {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
      (ρ : Nat → PSet W) : ∀ {ts : List Form}, NoRelList ts →
        (botBase W atomRel).truths ρ ts = (Canon.base W atomRel).truths ρ ts
    | [], _ => rfl
    | t :: ts, h => by
        show (botBase W atomRel).truth t ρ :: (botBase W atomRel).truths ρ ts
          = (Canon.base W atomRel).truth t ρ :: (Canon.base W atomRel).truths ρ ts
        rw [truth_botBase_eq_canon atomRel (φ := t) h.1 ρ,
          truth_botBase_eq_canon_list atomRel ρ h.2]
end

/-! ## 3. 受限推导关系 `Derivable₁` -/

/-- **受限 E 片段**的可推导关系：`Derivable` 的九个非 `E` 构造子形状完全一致，
第十个构造子 `e` 是**受限 `E`**——要求源公式 `φ` **不含关系子公式**（`NoRel φ`）。 -/
inductive Derivable₁ : Form → Prop where
  /-- **S1** 后承支持：`p ⊢ q ⇒ p ⊳ q`。 -/
  | s1 {p q : Form} (h : Entails p q) : Derivable₁ (p ⊳ q)
  /-- **S2** 后承封闭：`(t ⊳ p) ∧ (p ⊢ q) ⇒ t ⊳ q`。 -/
  | s2 {t p q : Form} (h₁ : Derivable₁ (t ⊳ p)) (h : Entails p q) : Derivable₁ (t ⊳ q)
  /-- **F1** 同一主体全称引入：`x ∉ FV(t)`，`t R φ ⇒ t R ∀x φ`。 -/
  | f1 {k : Kind} {t φ : Form} {x : Nat} (hx : ¬ FreeIn x t)
      (h : Derivable₁ (Kind.form k t φ)) : Derivable₁ (Kind.form k t (.all x φ))
  /-- **F2** 全称主体：`x ∉ FV(φ)`，`p R φ ⇒ (∀x p) R φ`。 -/
  | f2 {k : Kind} {p φ : Form} {x : Nat} (hx : ¬ FreeIn x φ)
      (h : Derivable₁ (Kind.form k p φ)) : Derivable₁ (Kind.form k (.all x p) φ)
  /-- **F3** 合取主体：`(a R φ) ∧ (b R φ) ⇒ (a ∧ b) R φ`。 -/
  | f3 {k : Kind} {a b φ : Form} (h₁ : Derivable₁ (Kind.form k a φ))
      (h₂ : Derivable₁ (Kind.form k b φ)) : Derivable₁ (Kind.form k (.and a b) φ)
  /-- **F4** 同一主体合取引入：`(t R φ) ∧ (t R ψ) ⇒ t R (φ ∧ ψ)`。 -/
  | f4 {k : Kind} {t φ ψ : Form} (h₁ : Derivable₁ (Kind.form k t φ))
      (h₂ : Derivable₁ (Kind.form k t ψ)) : Derivable₁ (Kind.form k t (.and φ ψ))
  /-- **R1** 否定反驳：`t ⊳ ¬φ ⇒ t ⊲ φ`。 -/
  | r1 {t φ : Form} (h : Derivable₁ (t ⊳ .not φ)) : Derivable₁ (t ⊲ φ)
  /-- **P1** 二元合取推广（`R,S` 各自独立取 `⊳`／`⊲`）。 -/
  | p1 {kR kS : Kind} {a b c d f : Form} (h₁ : Derivable₁ (Kind.form kR a c))
      (h₂ : Derivable₁ (Kind.form kR b d)) (h₃ : Derivable₁ (Kind.form kS (.and c d) f)) :
      Derivable₁ (Kind.form kR (.and a b) (Kind.form kS (.and c d) f))
  /-- **P2** 全称推广（`R,S` 各自独立取 `⊳`／`⊲`）。 -/
  | p2 {kR kS : Kind} {a c f : Form} {x : Nat} (h₁ : Derivable₁ (Kind.form kR a c))
      (h₂ : Derivable₁ (Kind.form kS (.all x c) f)) (hx : ¬ FreeIn x f) :
      Derivable₁ (Kind.form kR (.all x a) (Kind.form kS (.all x c) f))
  /-- **E（受限）** 经典等价替换：在 `φ ⊣⊢ ψ` 且 `φ` **不含关系子公式**时，
      `γ` 中的 `φ` 可换成 `ψ`。去掉 `hNoRel` 即回到 `Derivable.e`。 -/
  | e {φ ψ γ δ : Form} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ) (hNoRel : NoRel φ)
      (hγ : Derivable₁ γ) : Derivable₁ δ

/-- 系统内可推导的记法：`⊢₁ φ`。 -/
scoped notation:25 "⊢₁ " φ:25 => Derivable₁ φ

namespace Derivable₁

/-- **包含关系**：受限 E 片段的推导都是全系统 `Derivable` 的推导。 -/
theorem toDerivable : ∀ {φ : Form}, Derivable₁ φ → Derivable φ
  | _, @Derivable₁.s1 _ _ h => Derivable.s1 h
  | _, @Derivable₁.s2 _ _ _ h₁ h => Derivable.s2 (toDerivable h₁) h
  | _, @Derivable₁.f1 _ _ _ _ hx h => Derivable.f1 hx (toDerivable h)
  | _, @Derivable₁.f2 _ _ _ _ hx h => Derivable.f2 hx (toDerivable h)
  | _, @Derivable₁.f3 _ _ _ _ h₁ h₂ => Derivable.f3 (toDerivable h₁) (toDerivable h₂)
  | _, @Derivable₁.f4 _ _ _ _ h₁ h₂ => Derivable.f4 (toDerivable h₁) (toDerivable h₂)
  | _, @Derivable₁.r1 _ _ h => Derivable.r1 (toDerivable h)
  | _, @Derivable₁.p1 _ _ _ _ _ _ _ h₁ h₂ h₃ =>
      Derivable.p1 (toDerivable h₁) (toDerivable h₂) (toDerivable h₃)
  | _, @Derivable₁.p2 _ _ _ _ _ _ h₁ h₂ hx =>
      Derivable.p2 (toDerivable h₁) (toDerivable h₂) hx
  | _, @Derivable₁.e _ _ _ _ hrep heq _ hγ => Derivable.e hrep heq (toDerivable hγ)

end Derivable₁

/-- **受限 E 片段的可靠性**：十个分支照 `Soundness.lean` 改写。
`e` 支用 `Frame.plug_congr` ＋ `Derivable.truth_eq_of_cequiv`（受限性此处用不到），
其余九支与 `EFree.noE_soundness₀` 相同。 -/
theorem soundness₁ (M : Frame) (hM : IsModel M) : ∀ {φ : Form}, Derivable₁ φ → M.Valid φ
  | _, @Derivable₁.e φ ψ γ δ hrep heq _ hγ => by
      obtain ⟨C, hγeq, hδeq⟩ := hrep
      have hφψ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ :=
        Derivable.truth_eq_of_cequiv hM heq
      have hγ' : M.Valid (C.plug φ) := hγeq ▸ soundness₁ M hM hγ
      rw [hδeq]
      intro ρ
      rw [← Frame.plug_congr M hM C φ ψ hφψ ρ]
      exact hγ' ρ
  | _, @Derivable₁.s1 p q h => fun ρ =>
      Derivable.valid_supp M hM (hM.s1 p q ρ (hM.classical p q h ρ))
  | _, @Derivable₁.s2 t p q h₁ h => fun ρ =>
      Derivable.valid_supp M hM (hM.s2 (M.truth t ρ) p q ρ
        (Derivable.supp_of_valid M hM (soundness₁ M hM h₁ ρ))
        (hM.classical p q h ρ))
  | _, @Derivable₁.f1 k t φ x hx h => fun ρ =>
      Derivable.valid_rel M hM (hM.f1 k t φ x ρ hx
        (fun X => Derivable.rel_of_valid M hM (soundness₁ M hM h (upd ρ x X))))
  | _, @Derivable₁.f2 k p φ x hx h => fun ρ =>
      Derivable.valid_rel M hM (hM.f2 k p φ x ρ hx
        (fun X => Derivable.rel_of_valid M hM (soundness₁ M hM h (upd ρ x X))))
  | _, @Derivable₁.f3 k a b φ h₁ h₂ => fun ρ =>
      Derivable.valid_rel M hM (hM.f3 k (M.truth a ρ) (M.truth b ρ) φ ρ
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₁ ρ))
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₂ ρ)))
  | _, @Derivable₁.f4 k t φ ψ h₁ h₂ => fun ρ =>
      Derivable.valid_rel M hM (hM.f4 k (M.truth t ρ) φ ψ ρ
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₁ ρ))
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₂ ρ)))
  | _, @Derivable₁.r1 t φ h => fun ρ =>
      Derivable.valid_refut M hM (hM.r1 (M.truth t ρ) φ ρ
        (Derivable.supp_of_valid M hM (soundness₁ M hM h ρ)))
  | _, @Derivable₁.p1 kR kS a b c d f h₁ h₂ h₃ => fun ρ =>
      Derivable.valid_rel M hM (hM.p1 kR kS a b c d f ρ
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₁ ρ))
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₂ ρ))
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₃ ρ)))
  | _, @Derivable₁.p2 kR kS a c f x h₁ h₂ hx => fun ρ =>
      Derivable.valid_rel M hM (hM.p2 kR kS a c f x ρ hx
        (fun X => Derivable.rel_of_valid M hM (soundness₁ M hM h₁ (upd ρ x X)))
        (Derivable.rel_of_valid M hM (soundness₁ M hM h₂ ρ)))

/-! ## 4. 核心不变量（支持侧，**典范框架**上）

不变量只在**支持侧**成立（理由同 `EFree` 第 3 节：反驳侧的同型断言被 `P1` 摧毁）。
把它写成 `Form` 上的谓词 `SupInv`（与 `EFree.SuppInv` 同形但**新名**，避免重名），
让 `Derivable₁.rec` 的归纳索引位保持**变量**。 -/

/-- **支持侧不变量**：结论形如 `a ⊳ b` 时要求 `⟦a⟧ρ ≤ ⟦b⟧ρ`，其余形状恒真。

`Form` 的 12 个构造子全部列出（不用通配缺省），以便 `SupInv M (a ⊳ b)` 按定义归约。 -/
def SupInv (M : Frame) : Form → Prop
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

/-- **非支持式形状的公式满足 `SupInv`**：`SupInv` 只在 `.supp` 上要求真值不等式，
在其余 11 个构造子上恒真；故只要 `ψ` 不是支持式形状即得。 -/
theorem supInv_of_not_supp {M : Frame} {ψ : Form} (h : ¬ ∃ a b : Form, ψ = .supp a b) :
    SupInv M ψ := by
  cases ψ with
  | var _ => trivial
  | atom _ _ => trivial
  | bot => trivial
  | top => trivial
  | not _ => trivial
  | and _ _ => trivial
  | or _ _ => trivial
  | imp _ _ => trivial
  | all _ _ => trivial
  | ex _ _ => trivial
  | refut _ _ => trivial
  | supp a b => exact absurd ⟨a, b, rfl⟩ h

/-- **「洞在顶层且 `δ` 是支持式」在典范框架下是空集**（任务书第 4 步「洞在顶层」那一支）。

设 `φ` 不含关系子公式、`φ ⊣⊢ ψ`、`ψ = a ⊳ b`，且 `γ = φ` 有受限推导。
在**同一个** `W`、`atomRel` 上：
1. `Canon.isModel` ＋ `soundness₁` 用在 `hγd` 上，得 `(Canon.frame W atomRel).truth φ ρ₀ = ⊤`；
2. `φ ⊣⊢ ψ` 在**全空基结构** `botBase W atomRel` 处取值，配合 `ψ = a ⊳ b`（其真值为 `⊥`）
   得 `(botBase W atomRel).truth φ ρ₀ = ⊥`；
3. `truth_botBase_eq_canon`（用 `hNoRel`）把第 2 步搬到 `Canon.base`，再用
   `Canon.frame_truth` 搬到 `Canon.frame`，与第 1 步的 `= ⊤` 矛盾。
取一个世界（`Nonempty W`）即得 `False`。

**注 1**：这里 `Canon.frame_truth` 是**命题性**等式，不能替换成 `rfl`；
也因此本引理只在**典范框架**上成立（任意 `IsModel M` 下第 1 步与第 2 步不在同一个结构上）。 -/
theorem supp_inv_false_canon {W : Type} [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {φ ψ γ : Form} (hNoRel : NoRel φ)
    (hγd : Derivable₁ γ) (hγeq : γ = φ) (heq : φ ⊣⊢ ψ)
    (hψ : ∃ a b : Form, ψ = .supp a b) :
    False := by
  obtain ⟨a, b, rfl⟩ := hψ
  have hcanon : IsModel (Canon.frame W atomRel) := Canon.isModel W atomRel
  have hφvalid : ∀ ρ : Nat → PSet W, (Canon.frame W atomRel).truth φ ρ = ⊤ := by
    rw [← hγeq]
    exact soundness₁ (Canon.frame W atomRel) hcanon hγd
  obtain ⟨ρ₀⟩ : Nonempty (Nat → PSet W) := ⟨fun _ => ⊥⟩
  -- 第 2 步：全空基结构上 `φ` 的真值为 `⊥`
  have hbot : (Canon.base W atomRel).truth φ ρ₀ = ⊥ := by
    have hle : (botBase W atomRel).truth φ ρ₀ ≤ (botBase W atomRel).truth (a ⊳ b) ρ₀ :=
      heq.1 (botBase W atomRel) ρ₀
    have hb : (botBase W atomRel).truth φ ρ₀ = ⊥ := by
      rw [show (botBase W atomRel).truth (a ⊳ b) ρ₀ = ⊥ from rfl] at hle
      exact PSet.eq_bot_of_le hle
    exact (truth_botBase_eq_canon atomRel (φ := φ) hNoRel ρ₀).symm.trans hb
  -- 第 3 步：把 `⊥` 搬到典范框架
  have hbot' : (Canon.frame W atomRel).truth φ ρ₀ = ⊥ := by
    rw [Canon.frame_truth W atomRel φ ρ₀]
    exact hbot
  have htop : (Canon.frame W atomRel).truth φ ρ₀ = ⊤ := hφvalid ρ₀
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  exact PSet.not_bot w₀ (show (⊥ : PSet W) w₀ from (hbot'.symm.trans htop) ▸ trivial)

/-- **上下文填入保持 `SupInv`（典范框架版）**：若 `NoRel φ`、`φ`／`ψ` 逐赋值真值相同、
`γ = C.plug φ` 且 `γ` 有受限推导，则 `SupInv M (C.plug φ)` 蕴含 `SupInv M (C.plug ψ)`。

对 `C` 的 15 个构造子逐一处理（用显式消去子 `Ctx.rec`，归纳位保持为变量）。
关键观察：`SupInv` 只在结果形状是 `.supp` 时非平凡，而 `C.plug ψ` 是 `.supp`
恰好只在三种情形发生：

* `C = .hole`（洞在顶层，`C.plug ψ = ψ`）：由 `supp_inv_false_canon` 证为空集；
* `C = .suppL c ψ'`（结果是 `(c.plug ψ) ⊳ ψ'`）：此时 `SupInv M (C.plug φ)` 按定义恰好是
  `∀ ρ, ⟦c.plug φ⟧ρ ≤ ⟦ψ'⟧ρ`，用 `Frame.plug_congr` 把左边换成 `⟦c.plug ψ⟧ρ` 即得；
* `C = .suppR t c`（结果是 `t ⊳ (c.plug ψ)`）：同理，归纳假设是 `∀ ρ, ⟦t⟧ρ ≤ ⟦c.plug φ⟧ρ`，
  与 `plug_congr` 传递即得；
* 其余 11 个构造子的结果形状上 `SupInv` 按定义为 `True`，直接 `trivial`。 -/
theorem supInv_plug_canon {M : Frame} (hM : IsModel M) :
    ∀ (C : Ctx) {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
      (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = C.plug φ →
      (C.plug φ = γ → Derivable₁ γ) → SupInv M (C.plug φ) → SupInv M (C.plug ψ) :=
  Ctx.rec (motive := fun C => ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
      (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = C.plug φ →
      (C.plug φ = γ → Derivable₁ γ) → SupInv M (C.plug φ) → SupInv M (C.plug ψ))
    -- hole：洞在顶层，由 `supp_inv_false_canon` 证为空集
    (fun {φ ψ γ} (hNoRel : NoRel φ) (heq : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) (hγ : γ = Ctx.plug Ctx.hole φ)
        (hd : Ctx.plug Ctx.hole φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug Ctx.hole φ)) => by
      haveI : Nonempty M.W := hM.nonempty
      have hγφ : γ = φ := hγ.trans (by rfl)
      by_cases hψ : ∃ a b : Form, ψ = .supp a b
      · exact absurd (supp_inv_false_canon (W := M.W) M.atomRel hNoRel (hd hγ.symm) hγφ heq hψ)
          not_false
      · exact supInv_of_not_supp hψ)
    -- atom
    (fun i pre c post (_ : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.atom i pre c post) φ)
        (_ : Ctx.plug (Ctx.atom i pre c post) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.atom i pre c post) φ)) => trivial)
    -- not
    (fun c (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.not c) φ)
        (_ : Ctx.plug (Ctx.not c) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.not c) φ)) => trivial)
    -- andL
    (fun c ψ' (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.andL c ψ') φ)
        (_ : Ctx.plug (Ctx.andL c ψ') φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.andL c ψ') φ)) => trivial)
    -- andR
    (fun φ' c (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.andR φ' c) φ)
        (_ : Ctx.plug (Ctx.andR φ' c) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.andR φ' c) φ)) => trivial)
    -- orL
    (fun c ψ' (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.orL c ψ') φ)
        (_ : Ctx.plug (Ctx.orL c ψ') φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.orL c ψ') φ)) => trivial)
    -- orR
    (fun φ' c (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.orR φ' c) φ)
        (_ : Ctx.plug (Ctx.orR φ' c) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.orR φ' c) φ)) => trivial)
    -- impL
    (fun c ψ' (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.impL c ψ') φ)
        (_ : Ctx.plug (Ctx.impL c ψ') φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.impL c ψ') φ)) => trivial)
    -- impR
    (fun φ' c (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.impR φ' c) φ)
        (_ : Ctx.plug (Ctx.impR φ' c) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.impR φ' c) φ)) => trivial)
    -- all
    (fun x c (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.all x c) φ)
        (_ : Ctx.plug (Ctx.all x c) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.all x c) φ)) => trivial)
    -- ex
    (fun x c (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.ex x c) φ)
        (_ : Ctx.plug (Ctx.ex x c) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.ex x c) φ)) => trivial)
    -- suppL：结果是支持式，用归纳假设的真值不等式
    (fun c ψ' (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (h : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.suppL c ψ') φ)
        (_ : Ctx.plug (Ctx.suppL c ψ') φ = γ → Derivable₁ γ)
        (hge : SupInv M (Ctx.plug (Ctx.suppL c ψ') φ)) => by
      have hstep : ∀ ρ : Nat → PSet M.W, M.truth (Ctx.plug c φ) ρ = M.truth (Ctx.plug c ψ) ρ :=
        Frame.plug_congr M hM c φ ψ h
      have hφ : ∀ ρ : Nat → PSet M.W, M.truth (Ctx.plug c φ) ρ ≤ M.truth ψ' ρ := hge
      intro ρ
      show M.truth (Ctx.plug c ψ) ρ ≤ M.truth ψ' ρ
      rw [← hstep ρ]
      exact hφ ρ)
    -- suppR：结果是支持式，用归纳假设的真值不等式
    (fun t c (ih : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (h : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.suppR t c) φ)
        (_ : Ctx.plug (Ctx.suppR t c) φ = γ → Derivable₁ γ)
        (hge : SupInv M (Ctx.plug (Ctx.suppR t c) φ)) => by
      have hstep : ∀ ρ : Nat → PSet M.W, M.truth (Ctx.plug c φ) ρ = M.truth (Ctx.plug c ψ) ρ :=
        Frame.plug_congr M hM c φ ψ h
      have hφ : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth (Ctx.plug c φ) ρ := hge
      intro ρ
      show M.truth t ρ ≤ M.truth (Ctx.plug c ψ) ρ
      exact PSet.le_trans (hφ ρ) ((hstep ρ) ▸ PSet.le_refl _))
    -- refutL
    (fun c ψ' (_ : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.refutL c ψ') φ)
        (_ : Ctx.plug (Ctx.refutL c ψ') φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.refutL c ψ') φ)) => trivial)
    -- refutR
    (fun t c (_ : ∀ {φ ψ γ : Form}, NoRel φ → (φ ⊣⊢ ψ) →
        (∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ) → γ = Ctx.plug c φ →
        (Ctx.plug c φ = γ → Derivable₁ γ) → SupInv M (Ctx.plug c φ) → SupInv M (Ctx.plug c ψ))
        {φ ψ γ} (_ : NoRel φ) (_ : φ ⊣⊢ ψ)
        (_ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ)
        (_ : γ = Ctx.plug (Ctx.refutR t c) φ)
        (_ : Ctx.plug (Ctx.refutR t c) φ = γ → Derivable₁ γ)
        (_ : SupInv M (Ctx.plug (Ctx.refutR t c) φ)) => trivial)
/-- **核心不变量（受限 E 片段，支持侧，典范框架）**：`Derivable₁ φ` 蕴含 `SupInv M φ`。

十个分支：九条非 `e` 支与 `EFree.noE_supp_le_inv` 逐一对应（`hM` 取
`Canon.isModel W atomRel`）；`e` 支把 `hγ`（源公式的推导）交给 `supInv_plug_canon`，
其中洞在顶层时由 `supp_inv_false_canon` 证为空集。 -/
theorem supp_le_inv₁_canon {M : Frame} (hM : IsModel M) :
    ∀ {φ : Form}, Derivable₁ φ → SupInv M φ :=
  Derivable₁.rec (motive := fun φ _ => SupInv M φ)
    -- s1
    (fun {p q} (h : Entails p q) => by
      intro ρ
      exact hM.classical p q h ρ)
    -- s2
    (fun {t p q} (_ : Derivable₁ (t ⊳ p)) (h : Entails p q)
        (ih : SupInv M (t ⊳ p)) => by
      have ih' : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth p ρ := ih
      intro ρ
      exact PSet.le_trans (ih' ρ) (hM.classical p q h ρ))
    -- f1
    (fun {k t φ x} (hx : ¬ FreeIn x t) (_ : Derivable₁ (Kind.form k t φ))
        (ih : SupInv M (Kind.form k t φ)) => by
      cases k
      · have ih' : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth φ ρ := ih
        intro ρ
        show M.truth t ρ ≤ PSet.iInter (fun X : PSet M.W => M.truth φ (upd ρ x X))
        refine PSet.le_iInter (fun X : PSet M.W => M.truth φ (upd ρ x X)) (fun X => ?_)
        exact (Frame.truth_upd_notFree M hM hx ρ X) ▸ ih' (upd ρ x X)
      · trivial)
    -- f2
    (fun {k p φ x} (hx : ¬ FreeIn x φ) (_ : Derivable₁ (Kind.form k p φ))
        (ih : SupInv M (Kind.form k p φ)) => by
      cases k
      · have ih' : ∀ ρ : Nat → PSet M.W, M.truth p ρ ≤ M.truth φ ρ := ih
        intro ρ
        show PSet.iInter (fun X : PSet M.W => M.truth p (upd ρ x X)) ≤ M.truth φ ρ
        refine PSet.le_trans
          (PSet.iInter_le (fun X : PSet M.W => M.truth p (upd ρ x X)) (ρ x)) ?_
        exact (Frame.truth_upd_notFree M hM hx ρ (ρ x)) ▸ ih' (upd ρ x (ρ x))
      · trivial)
    -- f3
    (fun {k a b φ} (_ : Derivable₁ (Kind.form k a φ)) (_ : Derivable₁ (Kind.form k b φ))
        (ih₁ : SupInv M (Kind.form k a φ)) (ih₂ : SupInv M (Kind.form k b φ)) => by
      cases k
      · have i₁ : ∀ ρ : Nat → PSet M.W, M.truth a ρ ≤ M.truth φ ρ := ih₁
        intro ρ w hw
        exact i₁ ρ w hw.1
      · trivial)
    -- f4
    (fun {k t φ ψ} (_ : Derivable₁ (Kind.form k t φ)) (_ : Derivable₁ (Kind.form k t ψ))
        (ih₁ : SupInv M (Kind.form k t φ)) (ih₂ : SupInv M (Kind.form k t ψ)) => by
      cases k
      · have i₁ : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth φ ρ := ih₁
        have i₂ : ∀ ρ : Nat → PSet M.W, M.truth t ρ ≤ M.truth ψ ρ := ih₂
        intro ρ
        exact PSet.le_inf (i₁ ρ) (i₂ ρ)
      · trivial)
    -- r1
    (fun {t φ} (_ : Derivable₁ (t ⊳ .not φ)) (_ : SupInv M (t ⊳ .not φ)) => trivial)
    -- p1
    (fun {kR kS a b c d f} (_ : Derivable₁ (Kind.form kR a c))
        (_ : Derivable₁ (Kind.form kR b d)) (h₃ : Derivable₁ (Kind.form kS (.and c d) f))
        _ _ _ => by
      cases kR
      · intro ρ
        exact PSet.le_of_eq_top (soundness₁ M hM h₃ ρ)
      · trivial)
    -- p2
    (fun {kR kS a c f x} (_ : Derivable₁ (Kind.form kR a c))
        (h₂ : Derivable₁ (Kind.form kS (.all x c) f)) _ _ _ => by
      cases kR
      · intro ρ
        exact PSet.le_of_eq_top (soundness₁ M hM h₂ ρ)
      · trivial)
    -- e（受限）
    (fun {φ ψ γ δ} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ) (hNoRel : NoRel φ)
        (hγd : Derivable₁ γ) (ih : SupInv M γ) => by
      obtain ⟨C, hγeq, hδeq⟩ := hrep
      have hφψ : ∀ ρ : Nat → PSet M.W, M.truth φ ρ = M.truth ψ ρ :=
        Derivable.truth_eq_of_cequiv hM heq
      have hgd : C.plug φ = γ → Derivable₁ γ := fun h => h ▸ hγd
      rw [hδeq]
      exact supInv_plug_canon hM C hNoRel heq hφψ hγeq hgd (hγeq ▸ ih))

/-- **核心不变量（典范框架版，任务书 (A) 的精确形状）**：
由 `Derivable₁ (a ⊳ b)` 得 `(Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ`
（对一切赋值）。两侧都用 `Canon.frame` 的 truth（与 `EFree.noE_supp_le` 形状一致）。 -/
theorem supp_le₁_canon (W : Type) [Nonempty W] (atomRel : Nat → List (PSet W) → PSet W)
    {a b : Form} (h : Derivable₁ (a ⊳ b)) :
    ∀ ρ : Nat → PSet W, (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth b ρ :=
  supp_le_inv₁_canon (Canon.isModel W atomRel) h

/-! ## 5. 两条障碍（反模型法对受限 E 片段失效） -/

/-- **支持传递的受限 E 障碍**：若 `Derivable₁ (a ⊳ b)` 且 `Derivable₁ (b ⊳ c)`，
则 `a ⊳ c` 在**一切**典范框架中有效——于是 `not_derivable_of_countermodel` 走不通。

形状照抄 `EFree.noE_transitivity_valid_canon`，只把 `Derivable₀` 换成 `Derivable₁`、
`noE_supp_le` 换成 `supp_le₁_canon`。 -/
theorem transitivity_valid_canon₁ (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b c : Form}
    (h₁ : Derivable₁ (a ⊳ b)) (h₂ : Derivable₁ (b ⊳ c)) :
    (Canon.frame W atomRel).Valid (a ⊳ c) := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  have hM : IsModel (Canon.frame W atomRel) := Canon.isModel W atomRel
  intro ρ
  have hle : (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth c ρ :=
    PSet.le_trans (supp_le₁_canon W atomRel h₁ ρ) (supp_le₁_canon W atomRel h₂ ρ)
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth a ρ)
    ((Canon.base W atomRel).truth c ρ)⟩ : PSet W) = ⊤
  refine (PSet.const_eq_top_iff w₀).mpr (Or.inl ?_)
  rwa [← Canon.frame_truth W atomRel c ρ]

/-- **S7（不同主体合取）的受限 E 障碍**：若 `Derivable₁ (a ⊳ φ)` 且
`Derivable₁ (b ⊳ ψ)`，则 `(a ∧ b) ⊳ (φ ∧ ψ)` 在**一切**典范框架中有效。 -/
theorem s7_valid_canon₁ (W : Type) [Nonempty W]
    (atomRel : Nat → List (PSet W) → PSet W) {a b φ ψ : Form}
    (h₁ : Derivable₁ (a ⊳ φ)) (h₂ : Derivable₁ (b ⊳ ψ)) :
    (Canon.frame W atomRel).Valid (Form.and a b ⊳ Form.and φ ψ) := by
  obtain ⟨w₀⟩ := (inferInstance : Nonempty W)
  have hM : IsModel (Canon.frame W atomRel) := Canon.isModel W atomRel
  intro ρ
  have hle₁ : (Canon.frame W atomRel).truth a ρ ≤ (Canon.frame W atomRel).truth φ ρ :=
    supp_le₁_canon W atomRel h₁ ρ
  have hle₂ : (Canon.frame W atomRel).truth b ρ ≤ (Canon.frame W atomRel).truth ψ ρ :=
    supp_le₁_canon W atomRel h₂ ρ
  have hleft : (Canon.frame W atomRel).truth a ρ ⊓ (Canon.frame W atomRel).truth b ρ
      ≤ (Canon.frame W atomRel).truth φ ρ ⊓ (Canon.frame W atomRel).truth ψ ρ := by
    refine PSet.le_inf ?_ ?_
    · exact PSet.le_trans (PSet.inf_le_left _ _) hle₁
    · exact PSet.le_trans (PSet.inf_le_right _ _) hle₂
  show (⟨fun _ => Canon.suppP ((Canon.frame W atomRel).truth (Form.and a b) ρ)
    ((Canon.base W atomRel).truth (Form.and φ ψ) ρ)⟩ : PSet W) = ⊤
  refine (PSet.const_eq_top_iff w₀).mpr (Or.inl ?_)
  rw [← Canon.frame_truth W atomRel (Form.and φ ψ) ρ]
  exact hleft

/-! ## 6. 强度声明（再次强调，勿夸大）

以上第 4、5 步**只覆盖受限 E 片段**（每次 `E` 的源公式不含关系子公式），
且不变量**只在典范框架上陈述**（`supp_le₁_canon`）。因此第 5 步的确切内容是：

> **任何支持传递／S7 的 N3 见证，至少有一个前提的推导在顶层用了 `E`
> （即其推导不属于 `Derivable₁`），且该 `E` 的源公式含关系子公式。**

它**不是**「支持传递／S7 不可容许」，也**不是**「它们在 `Derivable` 下不可导出」，
更**不是**规则级非可容许性；本文件也**不**声称任意 `IsModel` 模型上的不变量
（那在陈述层面就有缺口：`M.truth` 与 `Canon.base` 的 `truth` 不是定义性相等）。
全量版本（允许任意 `E`）仍归约到 `TruthPropagation`／相合性公开问题
（`EvidenceLogic/NonAdmissible.lean` 第十一、十二节）：
本文件只证明了「`E` 的源不含关系子公式时那个洞是空集」，此外没有推进。 -/

end

end EvidenceLogic
