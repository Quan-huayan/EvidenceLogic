/-
# 证据项的 `Type` 值呈现（Evidence）

`Derivable : Form → Prop` 把"可推导"当作**证明**（proof-irrelevant）。本文件给出同一
公理系统的 **`Type` 值呈现** `Ev`：十个构造子与 `Derivable` 逐一对应，但证据项是**数据**。

## 核心事实（本文件重点）

* `Ev φ → Derivable φ` 可定义（把数据遗忘为命题性证明）；
* **`Derivable φ → Ev φ` 在 Lean 的核里不可定义**：`Derivable` 位于 `Prop`，
  而 `Ev φ : Type`，Lean 的核**禁止**从 `Prop` 大消去（large elimination）到 `Type`。
  实测报错为

  ```
  error: recursor `EvidenceLogic.System.Derivable.casesOn` can only eliminate into `Prop`
  error(nested.lean.propRecLargeElim): Tactic `cases` failed with a nested error …
  ```

  所以这不是"尚未证明"，而是**核层面禁止**：

  ```lean
  -- 不可定义（保留以示障碍）
  -- def Ev.ofDerivable : ∀ {φ : Form}, Derivable φ → Ev φ
  ```

## 为什么这一点重要

"用 `Prop` 还是 `Type` 呈现公理系统"是一个**实质承诺**，不是风格问题：

* 选 `Prop`（现状）：够用于"推得出推不出"，且证明无关；但**无法**在证明上做计算
  ——没有正规形、没有可判定的 inversion、没有从证明中抽取的结构。因此
  "`Derivable` 的正向刻画"在**当前呈现下连陈述都受限**：只能在 `Prop` 层陈述
  "存在某种形状"（例如 `derivable_cequiv_rel`），而不能抽取该形状。
* 选 `Type`（本文件的 `Ev`）：证据项成为可计算的数据（`Ev.ruleTag` 即一例），
  这才可能承载 Curry–Howard／justification-logic 的"证据项"层，
  也才可能做将来的正规形与正向刻画。

结论：**若要把背书逻辑做成带证明项的演算（并据此攻完备性／N3 的语法侧），
必须从一开始就用 `Type` 值（或 `Sort` 值）的推导关系**；在 `Prop` 呈现上补是补不回来的。
详见 [`docs/证据语义解读.md`](../../docs/证据语义解读.md) 第五节。
-/
import EvidenceLogic.System.Derivable

namespace EvidenceLogic

/-- 证据项：与 `Derivable` 同构的 **`Type` 值**呈现，每个构造子对应定稿一条规则。 -/
inductive Ev : Form → Type where
  /-- **E** 经典等价替换：`φ ⊣⊢ ψ` 时，`γ` 中的 `φ` 可换成 `ψ`。 -/
  | e {φ ψ γ δ : Form} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ) (hγ : Ev γ) : Ev δ
  /-- **S1** 后承支持：`p ⊢ q ⇒ p ⊳ q`。 -/
  | s1 {p q : Form} (h : Entails p q) : Ev (p ⊳ q)
  /-- **S2** 后承封闭。 -/
  | s2 {t p q : Form} (h₁ : Ev (t ⊳ p)) (h : Entails p q) : Ev (t ⊳ q)
  /-- **F1** 同一主体全称引入。 -/
  | f1 {k : Kind} {t φ : Form} {x : Nat} (hx : ¬ FreeIn x t) (h : Ev (Kind.form k t φ)) :
      Ev (Kind.form k t (.all x φ))
  /-- **F2** 全称主体。 -/
  | f2 {k : Kind} {p φ : Form} {x : Nat} (hx : ¬ FreeIn x φ) (h : Ev (Kind.form k p φ)) :
      Ev (Kind.form k (.all x p) φ)
  /-- **F3** 合取主体。 -/
  | f3 {k : Kind} {a b φ : Form} (h₁ : Ev (Kind.form k a φ)) (h₂ : Ev (Kind.form k b φ)) :
      Ev (Kind.form k (.and a b) φ)
  /-- **F4** 同一主体合取引入。 -/
  | f4 {k : Kind} {t φ ψ : Form} (h₁ : Ev (Kind.form k t φ)) (h₂ : Ev (Kind.form k t ψ)) :
      Ev (Kind.form k t (.and φ ψ))
  /-- **R1** 否定反驳。 -/
  | r1 {t φ : Form} (h : Ev (t ⊳ .not φ)) : Ev (t ⊲ φ)
  /-- **P1** 二元合取推广。 -/
  | p1 {kR kS : Kind} {a b c d f : Form} (h₁ : Ev (Kind.form kR a c))
      (h₂ : Ev (Kind.form kR b d)) (h₃ : Ev (Kind.form kS (.and c d) f)) :
      Ev (Kind.form kR (.and a b) (Kind.form kS (.and c d) f))
  /-- **P2** 全称推广。 -/
  | p2 {kR kS : Kind} {a c f : Form} {x : Nat} (h₁ : Ev (Kind.form kR a c))
      (h₂ : Ev (Kind.form kS (.all x c) f)) (hx : ¬ FreeIn x f) :
      Ev (Kind.form kR (.all x a) (Kind.form kS (.all x c) f))

namespace Ev

/-- 证据项 ⟹ 可推导（遗忘计算内容）。注意这是**单向**的：反向被核禁止（见文件头）。 -/
theorem toDerivable : ∀ {φ : Form}, Ev φ → Derivable φ
  | _, .e hrep heq hγ => Derivable.e hrep heq (toDerivable hγ)
  | _, .s1 h => Derivable.s1 h
  | _, .s2 h₁ h => Derivable.s2 (toDerivable h₁) h
  | _, .f1 hx h => Derivable.f1 hx (toDerivable h)
  | _, .f2 hx h => Derivable.f2 hx (toDerivable h)
  | _, .f3 h₁ h₂ => Derivable.f3 (toDerivable h₁) (toDerivable h₂)
  | _, .f4 h₁ h₂ => Derivable.f4 (toDerivable h₁) (toDerivable h₂)
  | _, .r1 h => Derivable.r1 (toDerivable h)
  | _, .p1 h₁ h₂ h₃ => Derivable.p1 (toDerivable h₁) (toDerivable h₂) (toDerivable h₃)
  | _, .p2 h₁ h₂ hx => Derivable.p2 (toDerivable h₁) (toDerivable h₂) hx

/-- 证据项的"最后一步规则"标签。**这是可计算的数据函数**（对 `Ev` 结构递归），
而 `Prop` 值的 `Derivable` 给不出这样的函数——这就是"证据项是数据"的具体含义。 -/
def ruleTag : ∀ {φ : Form}, Ev φ → Nat
  | _, .e _ _ _ => 0
  | _, .s1 _ => 1
  | _, .s2 _ _ => 2
  | _, .f1 _ _ => 3
  | _, .f2 _ _ => 4
  | _, .f3 _ _ => 5
  | _, .f4 _ _ => 6
  | _, .r1 _ => 7
  | _, .p1 _ _ _ => 8
  | _, .p2 _ _ _ => 9

end Ev

/-- 由证据项的存在性得可推导性（`Nonempty` 在 `Prop` 中，故这一步合法）。 -/
theorem ev_to_derivable {φ : Form} (h : Nonempty (Ev φ)) : Derivable φ :=
  h.elim Ev.toDerivable

end EvidenceLogic
