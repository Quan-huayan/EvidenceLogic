/-
# 背书逻辑 v1.0：公理系统（Derivable）

本文件形式化定稿第三、四、五、六节的公理系统：一个 Hilbert 型推导关系
`Derivable : Form → Prop`。每条构造子对应定稿的一条规则。

## 规则与构造子的对应

| 构造子 | 定稿规则 | 形式 |
|---|---|---|
| `e` | **E** 经典等价替换（元规则） | 由 `φ ⊣⊢ ψ` 与 `Replace φ ψ γ δ`，从 `γ` 得 `δ` |
| `s1` | **S1** 后承支持 | `p ⊢ q ⇒ p ⊳ q` |
| `s2` | **S2** 后承封闭 | `(t ⊳ p) ∧ (p ⊢ q) ⇒ t ⊳ q` |
| `f1` | **F1** 同一主体全称引入 | `x ∉ FV(t)`，`t R φ ⇒ t R ∀x φ` |
| `f2` | **F2** 全称主体 | `x ∉ FV(φ)`，`p R φ ⇒ (∀x p) R φ` |
| `f3` | **F3** 合取主体 | `(a R φ) ∧ (b R φ) ⇒ (a ∧ b) R φ` |
| `f4` | **F4** 同一主体合取引入 | `(t R φ) ∧ (t R ψ) ⇒ t R (φ ∧ ψ)` |
| `r1` | **R1** 否定反驳 | `t ⊳ ¬φ ⇒ t ⊲ φ` |
| `p1` | **P1** 二元合取推广 | `(a R c) ∧ (b R d) ∧ ((c ∧ d) S f) ⇒ (a ∧ b) R ((c ∧ d) S f)` |
| `p2` | **P2** 全称推广 | `x ∉ FV(f)`，`(a R c) ∧ ((∀x c) S f) ⇒ (∀x a) R ((∀x c) S f)` |

其中 `R, S ∈ {⊳, ⊲}` 由 `Kind` 统一处理，因此 `p1`／`p2` 各自覆盖 4 种 `R,S` 组合，
而 `f1`–`f4` 通过 `Kind` 同时覆盖 `R = ⊳` 与 `R = ⊲`。

## 关于 F1／F2／P2 的形状

定稿写作「`∀x (t R p(x)) ⇒ t R ∀x p(x)`」。由于带自由变元的推导在本系统中
读作「对任意赋值成立」（见 `EvidenceLogic.Semantics` 第四节），
这几条规则以**开公式的推导**为前提，即：由 `t R φ`（`x` 可在 `φ` 中自由出现）
推出 `t R ∀x φ`（副作用条件 `x ∉ FV(t)`）。`f2`、`p2` 同理。

## 明确**不**包含的规则

定稿第七节列出的规则不在此归纳定义中，特别地没有：支持传递、反驳传递、
拆合取／全称支持者、拆嵌套关系、非命题性反驳逆后承、以及 S7（不同主体合取）。
`EvidenceLogic.NonDerivable` 用模型论证明这些都不是可推导的。
-/
import EvidenceLogic.Semantics

namespace EvidenceLogic

/-- 背书逻辑 v1.0 的可推导关系。 -/
inductive Derivable : Form → Prop where
  /-- **E** 经典等价替换：`φ ⊣⊢ ψ` 时，`γ` 中的 `φ` 可换成 `ψ`。 -/
  | e {φ ψ γ δ : Form} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ) (hγ : Derivable γ) :
      Derivable δ
  /-- **S1** 后承支持：`p ⊢ q ⇒ p ⊳ q`。 -/
  | s1 {p q : Form} (h : Entails p q) : Derivable (p ⊳ q)
  /-- **S2** 后承封闭：`(t ⊳ p) ∧ (p ⊢ q) ⇒ t ⊳ q`。 -/
  | s2 {t p q : Form} (h₁ : Derivable (t ⊳ p)) (h : Entails p q) : Derivable (t ⊳ q)
  /-- **F1** 同一主体全称引入：`x ∉ FV(t)`，`t R φ ⇒ t R ∀x φ`。 -/
  | f1 {k : Kind} {t φ : Form} {x : Nat} (hx : ¬ FreeIn x t)
      (h : Derivable (Kind.form k t φ)) : Derivable (Kind.form k t (.all x φ))
  /-- **F2** 全称主体：`x ∉ FV(φ)`，`p R φ ⇒ (∀x p) R φ`。 -/
  | f2 {k : Kind} {p φ : Form} {x : Nat} (hx : ¬ FreeIn x φ)
      (h : Derivable (Kind.form k p φ)) : Derivable (Kind.form k (.all x p) φ)
  /-- **F3** 合取主体：`(a R φ) ∧ (b R φ) ⇒ (a ∧ b) R φ`。 -/
  | f3 {k : Kind} {a b φ : Form} (h₁ : Derivable (Kind.form k a φ))
      (h₂ : Derivable (Kind.form k b φ)) : Derivable (Kind.form k (.and a b) φ)
  /-- **F4** 同一主体合取引入：`(t R φ) ∧ (t R ψ) ⇒ t R (φ ∧ ψ)`。 -/
  | f4 {k : Kind} {t φ ψ : Form} (h₁ : Derivable (Kind.form k t φ))
      (h₂ : Derivable (Kind.form k t ψ)) : Derivable (Kind.form k t (.and φ ψ))
  /-- **R1** 否定反驳：`t ⊳ ¬φ ⇒ t ⊲ φ`。 -/
  | r1 {t φ : Form} (h : Derivable (t ⊳ .not φ)) : Derivable (t ⊲ φ)
  /-- **P1** 二元合取推广（`R,S` 各自独立取 `⊳`／`⊲`）。 -/
  | p1 {kR kS : Kind} {a b c d f : Form} (h₁ : Derivable (Kind.form kR a c))
      (h₂ : Derivable (Kind.form kR b d)) (h₃ : Derivable (Kind.form kS (.and c d) f)) :
      Derivable (Kind.form kR (.and a b) (Kind.form kS (.and c d) f))
  /-- **P2** 全称推广（`R,S` 各自独立取 `⊳`／`⊲`）。 -/
  | p2 {kR kS : Kind} {a c f : Form} {x : Nat} (h₁ : Derivable (Kind.form kR a c))
      (h₂ : Derivable (Kind.form kS (.all x c) f)) (hx : ¬ FreeIn x f) :
      Derivable (Kind.form kR (.all x a) (Kind.form kS (.all x c) f))

/-- 系统内可推导的记法：`⊢ᴱ φ`。 -/
scoped notation:25 "⊢ᴱ " φ:25 => Derivable φ

end EvidenceLogic
