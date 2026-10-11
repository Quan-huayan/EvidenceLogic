/-
# `Ev` 的反演与原子支持者的正向刻画（Inversion）
`Ev` 的反演（inversion）引理

本文件**不修改任何已有文件**，只在 `EvidenceLogic` 之上补一批新结论，并把
`Ev : Form → Type`（可消去到 `Prop`／`Type` 的**数据**呈现）用于**正向刻画**。

`Ev.ruleTag : ∀ {φ}, Ev φ → Nat` 已说明"最后一个构造子是哪个"是**可计算数据**；
本文件先把它做成 **`Prop` 值判定子** `Ev.isRule`（按 `Ev` 结构递归，可计算谓词），
再用它做反演，最后给出链式正规形的**规范**与卡点说明。

## 结论一览

| 名称 | 陈述 | 状态 |
|---|---|---|
| `Ev.isRule`／`isE`…`isP2` | "最后一步是第 `n` 条规则"的可计算判定子 | ✅ |
| `Ev.atom_root_restricted` | **原子支持者的最后一步必属于 `{e,s1,s2,f1,f4}`**（标签 `0,1,2,3,6`） | ✅ |
| `Ev.atom_supporter_tag_ne_f2`…`_p2` | 逐条排除：标签 `≠ 4,5,7,8,9`（`f2,f3,r1,p1,p2`） | ✅ |
| `Ev.atom_supporter_cases` | 模去 `s2` 后：标签 `≠ 2` ⇒ 属于 `{0,1,3,6}`（`e,s1,f1,f4`） | ✅ |
| `Ev.atom_supporter_cases_strict` | 再模去 `f1`／`f4` 后：标签 `= 0` 或 `= 1`（`e` 或 `s1`） | ✅ |
| `Ev.atom_supporter_cases'` | 上一行的判定子写法（`isE ∨ isS1 ∨ isF1 ∨ isF4`） | ✅ |
| `Ev.f1_atomic_supporter`／`f4_atomic_supporter` | **反例**：原子支持者可以以 `f1`／`f4` 结尾（原题断言为假） | ✅ |
| `Ev.SNF`／`Ev.SNF.len`／`SNF.len_s2_lt` | 链式正规形的规范 + 可计算链长 + 严格增长 | ✅ 规范与链长；构造见第 5 节卡点 |

## ⚠️ 重要更正（一）：原题主定理为**假**

任务书要求的主定理

```lean
theorem Ev.atom_supporter_cases {i ts b} (h : Ev (Form.atom i ts ⊳ b)) :
    Ev.isE h ∨ Ev.isS1 h ∨ Ev.isS2 h
```

**不是"技巧不够"，而是命题本身为假。** 任务书给出的排除理由对七个构造子成立，
对 `f1`／`f4` **不成立**：

* `f2` 的结论支持者是 `Kind.form k (.all x p) φ`，`.supp` 分支下即 `(∀x p) ⊳ φ`
  ——**支持者**变成 `∀x p`，与 `Form.atom i ts` 构造子冲突；✅ 排除
* `f3` 的结论支持者是 `(a ∧ b) ⊳ φ` —— 支持者变成 `a ∧ b`；✅ 排除
* `r1` 的结论是**反驳** `t ⊲ φ`（`Form.refut`），与 `Form.supp` 构造子冲突；✅ 排除
* `p1` 的结论支持者是 `(a ∧ b) ⊳ ((c ∧ d) S f)`；✅ 排除
* `p2` 的结论支持者是 `(∀x a) ⊳ ((∀x c) S f)`；✅ 排除
* 但 `f1` 的结论是 `Kind.form k t (.all x φ)`：`.supp` 分支下**支持者仍是 `t`**，
  它只把**被支持式**变成 `∀x φ`。取 `t := Form.atom i ts`、`b := Form.all x φ`，
  结论 `Form.atom i ts ⊳ Form.all x φ` **正是**一个原子支持者；❌ **无法排除**
* `f4` 同理（只把被支持式变成 `φ ∧ ψ`，支持者不变）。❌ **无法排除**

任务书表格说 `f1`／`f4` "会改变**被支持式**的外形"——但那**不**与
`Form.atom i ts ⊳ b` 冲突：原子支持者约束的是**支持者**，被支持式可以任意。
真正与原子支持者冲突的是"改变**支持者**外形"的 `f2`／`f3`／`p1`／`p2`
和"改变**关系种类**"的 `r1`。

本文件给出**具体反例项**（已通过类型检查）：

* `Ev.f1_atomic_supporter : Ev (Form.atom 0 [] ⊳ Form.all 0 Form.top)`，其
  `ruleTag` 为 `3`（`f1`）；`Ev.not_e_s1_s2_f1` 证明三个析取项全为 `False`；
* `Ev.f4_atomic_supporter : Ev (Form.atom 0 [] ⊳ Form.and Form.top Form.top)`，其
  `ruleTag` 为 `6`（`f4`）；`Ev.not_e_s1_s2_f4` 同理。

## ⚠️ 重要更正（二）：反演的正确（且**紧**的）形状

排除五个构造子后，剩下的可能性是 `e`、`s1`、`s2`、`f1`、`f4`，而且这五个
**都真的可达**，所以这就是完整的刻画：

* `Ev.atom_root_restricted`：原子支持者的最后一步必属于 `{e,s1,s2,f1,f4}`；
* `Ev.atom_supporter_cases`：若最后一步**不是** `s2`，则属于 `{e,s1,f1,f4}`。
  这是"把根定下来"的**第一步**：`s2` 是唯一"保持支持者、只沿后承前进"的规则，
  其前提 `Ev (t ⊳ p)` 支持者仍是同一个 `t`，因此可以无限叠下去，必须模去它。
* `Ev.atom_supporter_cases_strict`：再模去 `f1`／`f4`（它们只改写被支持式），
  才得到 `e` 或 `s1`。**这一步不能只模去 `s2`**——任务书设想的
  "`¬ isS2 h` ⇒ `isS1 h ∨ isE h`" 被 `f1_atomic_supporter` 直接反驳。

## 反演证明里各构造子的排除方式

`cases h`（`h : Ev (Form.atom i ts ⊳ b)`）之后，每个构造子留下"结论类型 = 目标类型"
的等式。本文件一律**先把指标 `generalize` 成变量**再做 `cases`（否则 Lean 的
dependent elimination 会在 `f1` 等分支上因指标里的 `Kind.form` 匹配式而失败）。随后：

| 构造子 | 标签 | 结论形状（`.supp` 分支） | 排除手段 |
|---|---|---|---|
| `e`   | 0 | `δ`（任意） | — 保留 |
| `s1`  | 1 | `p ⊳ q` | — 保留 |
| `s2`  | 2 | `t ⊳ q` | — 保留（支持者不变） |
| `f1`  | 3 | `t ⊳ ∀x φ` | — **保留**（支持者仍是 `t`）；见反例 |
| `f2`  | 4 | `(∀x p) ⊳ φ` | `Form.supp.inj` 得 `Form.all x p = Form.atom i ts`，`Form.noConfusion` |
| `f3`  | 5 | `(a ∧ b) ⊳ φ` | `Form.supp.inj` 得 `Form.and a b = Form.atom i ts`，`Form.noConfusion` |
| `f4`  | 6 | `t ⊳ (φ ∧ ψ)` | — **保留**（只改被支持式） |
| `r1`  | 7 | `t ⊲ φ` | `Form.refut` 与 `Form.supp` 构造子不同，`Form.noConfusion` |
| `p1`  | 8 | `(a ∧ b) ⊳ ((c ∧ d) S f)` | `Form.supp.inj` 得 `Form.and a b = Form.atom i ts`，`Form.noConfusion` |
| `p2`  | 9 | `(∀x a) ⊳ ((∀x c) S f)` | `Form.supp.inj` 得 `Form.all x a = Form.atom i ts`，`Form.noConfusion` |

要点：**所有**排除都发生在**类型指标**（`Form`）层——用 `Form.supp.inj` 取出构造子
参数的等式，再用 `Form.noConfusion` 击碎"不同构造子相等"。`f2`／`f3`／`p1`／`p2`
的 `Kind` 参数必须先 `cases k`，才能让 `Kind.form` **定义性**地归约到
`Form.supp`／`Form.refut`；本文件把"`Kind` 两分支都要矛盾"打包成辅助引理
（`kind_form_all_ne_supp_atom` 等），在 `Kind` 上 `cases` 后用两条腿同时关掉。

## 技术注记

* `Form` 是嵌套归纳类型（`atom` 的参数含 `List Form`），`induction` 对它不生成可用的
  归纳原理，故一律用 `cases`／`match`。
* `e`（元规则）这一支里 `δ = C.plug ψ` 是任意公式，反演**不需要**撕开 `Ctx`：
  `e` 分支直接保留为"根"。
* **`⊳` 记法与 `Kind.form` 的合一**：`Ev.s1`／`Ev.s2` 的目标类型写作
  `Kind.form k p q`，而 `Form.supp p q` 是它的定义性展开；直接对
  `Ev (p ⊳ q)` 目标写 `Ev.s1`／`Ev.s2` 时 Lean 不做这步展开，**必须显式给出
  `p`／`q`**（本文件在构造反例时显式写 `(p := …) (q := …)`，并用
  `show Ev (Kind.form Kind.supp …) from …` 对齐）。
* **`isS2 h` 与 `ruleTag h = 2` 的转换**：`isS2` 是 `abbrev`，作为**函数**出现在
  `¬ isS2 h` 里时 Lean 4.32 不会把它与 `ruleTag h = 2` 合一；因此
  主反演的假设直接写成 `ruleTag h ≠ 2`（等价形式见 `atom_supporter_cases'`）。
* 本文件无 `sorry`／`axiom`／`admit`，零依赖（不含 Mathlib）。
-/
import EvidenceLogic.Analysis.Evidence

namespace EvidenceLogic

namespace Ev

/-! ## 1) "最后一步是哪条规则"的判定子（递归到 `Prop`，可计算谓词） -/

/-- **判定子**：证据项的"最后一步规则标签"是否为 `n`。

这是 `Ev.ruleTag` 的 `Prop` 值版本，因而是**可计算谓词**（`decide` 可用）；
它按 `Ev` 结构递归，而不是从 `Prop` 值的 `Derivable` 消去。 -/
def isRule : ∀ {φ : Form}, Ev φ → Nat → Prop
  | _, h, n => ruleTag h = n

/-- **E** 是最后一步。 -/
abbrev isE : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 0
/-- **S1** 是最后一步。 -/
abbrev isS1 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 1
/-- **S2** 是最后一步。 -/
abbrev isS2 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 2
/-- **F1** 是最后一步。 -/
abbrev isF1 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 3
/-- **F2** 是最后一步。 -/
abbrev isF2 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 4
/-- **F3** 是最后一步。 -/
abbrev isF3 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 5
/-- **F4** 是最后一步。 -/
abbrev isF4 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 6
/-- **R1** 是最后一步。 -/
abbrev isR1 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 7
/-- **P1** 是最后一步。 -/
abbrev isP1 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 8
/-- **P2** 是最后一步。 -/
abbrev isP2 : ∀ {φ : Form}, Ev φ → Prop := fun h => isRule h 9

/-! ### 判定子的归约事实（全部 `rfl` 级：`ruleTag` 是按构造子定义的数据函数） -/

@[simp] theorem isRule_eq {φ : Form} (h : Ev φ) (n : Nat) : isRule h n = (ruleTag h = n) := rfl

@[simp] theorem ruleTag_e {φ ψ γ δ : Form} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ)
    (hγ : Ev γ) : ruleTag (Ev.e hrep heq hγ) = 0 := rfl

@[simp] theorem ruleTag_s1 {p q : Form} (h : Entails p q) : ruleTag (Ev.s1 h) = 1 := rfl

@[simp] theorem ruleTag_s2 {t p q : Form} (h₁ : Ev (t ⊳ p)) (h : Entails p q) :
    ruleTag (Ev.s2 h₁ h) = 2 := rfl

@[simp] theorem ruleTag_f1 {k : Kind} {t φ : Form} {x : Nat} (hx : ¬ FreeIn x t)
    (h : Ev (Kind.form k t φ)) : ruleTag (Ev.f1 hx h) = 3 := rfl

@[simp] theorem ruleTag_f2 {k : Kind} {p φ : Form} {x : Nat} (hx : ¬ FreeIn x φ)
    (h : Ev (Kind.form k p φ)) : ruleTag (Ev.f2 hx h) = 4 := rfl

@[simp] theorem ruleTag_f3 {k : Kind} {a b φ : Form} (h₁ : Ev (Kind.form k a φ))
    (h₂ : Ev (Kind.form k b φ)) : ruleTag (Ev.f3 h₁ h₂) = 5 := rfl

@[simp] theorem ruleTag_f4 {k : Kind} {t φ ψ : Form} (h₁ : Ev (Kind.form k t φ))
    (h₂ : Ev (Kind.form k t ψ)) : ruleTag (Ev.f4 h₁ h₂) = 6 := rfl

@[simp] theorem ruleTag_r1 {t φ : Form} (h : Ev (t ⊳ .not φ)) : ruleTag (Ev.r1 h) = 7 := rfl

@[simp] theorem ruleTag_p1 {kR kS : Kind} {a b c d f : Form} (h₁ : Ev (Kind.form kR a c))
    (h₂ : Ev (Kind.form kR b d)) (h₃ : Ev (Kind.form kS (.and c d) f)) :
    ruleTag (Ev.p1 h₁ h₂ h₃) = 8 := rfl

@[simp] theorem ruleTag_p2 {kR kS : Kind} {a c f : Form} {x : Nat} (h₁ : Ev (Kind.form kR a c))
    (h₂ : Ev (Kind.form kS (.all x c) f)) (hx : ¬ FreeIn x f) :
    ruleTag (Ev.p2 h₁ h₂ hx) = 9 := rfl

/-- 判定子与标签等式可互换。 -/
theorem isRule_iff {φ : Form} (h : Ev φ) (n : Nat) : isRule h n ↔ ruleTag h = n := Iff.rfl

/-- 由标签等式推出判定子。 -/
theorem isRule_of_eq {φ : Form} (h : Ev φ) {n : Nat} (h' : ruleTag h = n) : isRule h n := h'

/-- 若标签是 `n ≠ 2`，则同时为 `2` 会矛盾。 -/
theorem false_of_tag {φ : Form} {h : Ev φ} {n : Nat} (hne : n ≠ 2) (hn : ruleTag h = n)
    (h2 : ruleTag h = 2) : False :=
  hne (hn.symm.trans h2)

/-- **`isE` 与 `isS2` 互斥**。 -/
theorem not_isE_of_isS2 {φ : Form} {h : Ev φ} (h2 : ruleTag h = 2) : ¬ isE h := by
  intro h0
  exact (fun h20 => nomatch h20) (h2.symm.trans h0)

/-- **`isS1` 与 `isS2` 互斥**。 -/
theorem not_isS1_of_isS2 {φ : Form} {h : Ev φ} (h2 : ruleTag h = 2) : ¬ isS1 h := by
  intro h1
  exact (fun h21 => nomatch h21) (h2.symm.trans h1)

end Ev

/-! ## 2) 形状冲突引理

`Kind.form` 是模式匹配定义，故 `Kind.form .supp a b`／`Kind.form .refut a b` 定义性地
归约为 `a ⊳ b`／`a ⊲ b`（`Kind.form_supp`／`Kind.form_refut`，见 `Syntax.lean`）。
下面把反演里用到的每一次"击碎"打包成引理：它们只依赖 `Form.supp.inj` 与
`Form.noConfusion`，**不依赖任何一致性公理**。 -/

/-- `f2`／`p2` 型冲突：支持者是 `Form.all x p`，与 `Form.atom i ts` 冲突。 -/
theorem kind_form_all_ne_supp_atom {i : Nat} {ts : List Form} {b : Form}
    {k : Kind} {p φ : Form} {x : Nat}
    (he : Kind.form k (Form.all x p) φ = (Form.atom i ts ⊳ b)) : False := by
  cases k
  · exact Form.noConfusion (Form.supp.inj he).1
  · exact Form.noConfusion he

/-- `f3`／`p1` 型冲突：支持者是 `Form.and a c`，与 `Form.atom i ts` 冲突。 -/
theorem kind_form_and_ne_supp_atom {i : Nat} {ts : List Form} {b : Form}
    {k : Kind} {a c φ : Form}
    (he : Kind.form k (Form.and a c) φ = (Form.atom i ts ⊳ b)) : False := by
  cases k
  · exact Form.noConfusion (Form.supp.inj he).1
  · exact Form.noConfusion he

/-- `r1` 型冲突：结论是**反驳** `t ⊲ φ`，与支持 `Form.supp` 构造子不同。 -/
theorem refut_ne_supp_atom {i : Nat} {ts : List Form} {b t φ : Form}
    (he : (t ⊲ φ) = (Form.atom i ts ⊳ b)) : False := by
  exact Form.noConfusion he

/-- `p1` 型冲突：结论支持者是 `Form.and a c`，被支持式是嵌套 `Kind.form`。 -/
theorem kind_form_p1_ne_supp_atom {i : Nat} {ts : List Form} {b : Form}
    {kR kS : Kind} {a c d f : Form}
    (he : Kind.form kR (Form.and a c) (Kind.form kS d f) = (Form.atom i ts ⊳ b)) : False := by
  cases kR
  · exact Form.noConfusion (Form.supp.inj he).1
  · exact Form.noConfusion he

/-- `p2` 型冲突：结论支持者是 `Form.all x a`。 -/
theorem kind_form_p2_ne_supp_atom {i : Nat} {ts : List Form} {b : Form}
    {kR kS : Kind} {a c f : Form} {x : Nat}
    (he : Kind.form kR (Form.all x a) (Kind.form kS c f) = (Form.atom i ts ⊳ b)) : False := by
  cases kR
  · exact Form.noConfusion (Form.supp.inj he).1
  · exact Form.noConfusion he

namespace Ev

/-! ## 3) 原子支持者的反演

技术要点：`cases h` 直接用在 `h : Ev (Form.atom i ts ⊳ b)` 上时，Lean 的 dependent
elimination 会因为指标里的 `Kind.form` 匹配式而在 `f1`／`f3`／`f4`／`p1` 分支失败；
因此**先把指标 `generalize` 成变量**再 `cases`。 -/

/-- **原子支持者反演（主定理，修正版）**：

原子支持者 `Form.atom i ts ⊳ b` 的证据项，最后一步**必属于** `{e, s1, s2, f1, f4}`
（标签 `0, 1, 2, 3, 6`）——即 `f2`、`f3`、`r1`、`p1`、`p2` 被排除。

这个刻画是**紧**的：五个析取项都真的可达（`0/1/2` 见 `atom_top_evidence`，
`3/6` 见第 4 节的反例）。 -/
theorem atom_root_restricted {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) :
    ruleTag h = 0 ∨ ruleTag h = 1 ∨ ruleTag h = 2 ∨ ruleTag h = 3 ∨ ruleTag h = 6 := by
  have hf2 : ∀ {k : Kind} {p φ : Form} {x : Nat}, ¬ FreeIn x φ →
      Kind.form k (Form.all x p) φ = (Form.atom i ts ⊳ b) → False :=
    fun {_ _ _ _} _ he => kind_form_all_ne_supp_atom he
  have hf3 : ∀ {k : Kind} {a c φ : Form},
      Kind.form k (Form.and a c) φ = (Form.atom i ts ⊳ b) → False :=
    fun {_ _ _ _} he => kind_form_and_ne_supp_atom he
  have hr1 : ∀ {t φ : Form}, (t ⊲ φ) = (Form.atom i ts ⊳ b) → False :=
    fun {_ _} he => refut_ne_supp_atom he
  have hp1 : ∀ {kR kS : Kind} {a c d f : Form},
      Kind.form kR (Form.and a c) (Kind.form kS d f) = (Form.atom i ts ⊳ b) → False :=
    fun {_ _ _ _ _ _} he => kind_form_p1_ne_supp_atom he
  have hp2 : ∀ {kR kS : Kind} {a c f : Form} {x : Nat},
      Kind.form kR (Form.all x a) (Kind.form kS c f) = (Form.atom i ts ⊳ b) → False :=
    fun {_ _ _ _ _ _} he => kind_form_p2_ne_supp_atom he
  revert h
  generalize hφ : (Form.atom i ts ⊳ b) = φ
  intro h
  cases h with
  | e hrep heq hγ => exact Or.inl rfl
  | s1 hp => exact Or.inr (Or.inl rfl)
  | s2 h1 hpq => exact Or.inr (Or.inr (Or.inl rfl))
  | f1 hx h => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | f2 hx h => exact False.elim (hf2 hx hφ.symm)
  | f3 ha hb => exact False.elim (hf3 hφ.symm)
  | f4 h1 h2 => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  | r1 h => exact False.elim (hr1 hφ.symm)
  | p1 h1 h2 h3 => exact False.elim (hp1 hφ.symm)
  | p2 h1 h2 hx => exact False.elim (hp2 hφ.symm)

/-- **逐条排除引理**：由"标签属于 `{0,1,2,3,6}`"推出"标签不是给定的 `m`"。

把标签层面的排除从析取式里分离出来，便于下游直接 `exact absurd htag (… )`。 -/
theorem tag_ne_of_mem {φ : Form} {h : Ev φ}
    (hmem : ruleTag h = 0 ∨ ruleTag h = 1 ∨ ruleTag h = 2 ∨ ruleTag h = 3 ∨ ruleTag h = 6)
    {m : Nat} (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hm2 : m ≠ 2) (hm3 : m ≠ 3) (hm6 : m ≠ 6) :
    ruleTag h ≠ m := by
  intro hc
  rcases hmem with h0 | h1 | h2' | h3' | h6'
  · exact hm0 (hc.symm.trans h0)
  · exact hm1 (hc.symm.trans h1)
  · exact hm2 (hc.symm.trans h2')
  · exact hm3 (hc.symm.trans h3')
  · exact hm6 (hc.symm.trans h6')

/-- `f2`（标签 `4`）绝不为原子支持者收尾：它把支持者改成 `∀x p`。 -/
theorem atom_supporter_tag_ne_f2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) : ruleTag h ≠ 4 :=
  tag_ne_of_mem (atom_root_restricted h) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- `f3`（标签 `5`）绝不为原子支持者收尾：它把支持者改成 `a ∧ b`。 -/
theorem atom_supporter_tag_ne_f3 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) : ruleTag h ≠ 5 :=
  tag_ne_of_mem (atom_root_restricted h) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- `r1`（标签 `7`）绝不为原子支持者收尾：它的结论是**反驳** `t ⊲ φ`。 -/
theorem atom_supporter_tag_ne_r1 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) : ruleTag h ≠ 7 :=
  tag_ne_of_mem (atom_root_restricted h) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- `p1`（标签 `8`）绝不为原子支持者收尾：它把支持者改成 `a ∧ b`。 -/
theorem atom_supporter_tag_ne_p1 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) : ruleTag h ≠ 8 :=
  tag_ne_of_mem (atom_root_restricted h) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- `p2`（标签 `9`）绝不为原子支持者收尾：它把支持者改成 `∀x a`。 -/
theorem atom_supporter_tag_ne_p2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) : ruleTag h ≠ 9 :=
  tag_ne_of_mem (atom_root_restricted h) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- **主反演定理（模去 `s2`）**：若最后一步的标签**不是** `2`（`s2`），
则它属于 `{0, 1, 3, 6}`（即 `e`、`s1`、`f1`、`f4`）。

这是"把根定下来"的**第一步**：`s2` 是唯一"保持支持者、只沿后承前进"的规则
（前提 `Ev (t ⊳ p)` 的支持者仍是同一个 `t`），所以它可以无限叠下去，必须模去它。
剩下的 `f1`／`f4` 也保持支持者不变，所以**不能**在这里就去掉。 -/
theorem atom_supporter_cases {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) (h2 : ruleTag h ≠ 2) :
    ruleTag h = 0 ∨ ruleTag h = 1 ∨ ruleTag h = 3 ∨ ruleTag h = 6 := by
  rcases atom_root_restricted h with h0 | h1 | h2' | h3 | h6
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact absurd h2' h2
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h6))

/-- **主反演定理（模去 `s2` 与 `f1`／`f4`）**：若最后一步既不是 `s2`，
也不是把**被支持式**改写成 `∀x φ`／`φ ∧ ψ` 的 `f1`／`f4`，则根只能是
`e`（标签 `0`）或 `s1`（标签 `1`）。

这就是任务书想要的"根定下来"——但**必须**额外排除 `f1`／`f4`：
任务书的 `¬ isS2 h ⇒ isS1 h ∨ isE h` 被 `f1_atomic_supporter` 反驳。 -/
theorem atom_supporter_cases_strict {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) (h2 : ruleTag h ≠ 2) (h3 : ruleTag h ≠ 3)
    (h6 : ruleTag h ≠ 6) : ruleTag h = 0 ∨ ruleTag h = 1 := by
  rcases atom_supporter_cases h h2 with h0 | h1 | h3' | h6'
  · exact Or.inl h0
  · exact Or.inr h1
  · exact absurd h3' h3
  · exact absurd h6' h6

/-- **判定子形式**：`atom_supporter_cases` 换成 `isE`／`isS1`／`isF1`／`isF4` 记法。 -/
theorem atom_supporter_cases' {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) (h2 : ruleTag h ≠ 2) :
    isE h ∨ isS1 h ∨ isF1 h ∨ isF4 h := by
  rcases atom_supporter_cases h h2 with h0 | h1 | h3 | h6
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h6))

/-- **判定子形式的严格版**：`atom_supporter_cases_strict` 的 `isRule` 写法。 -/
theorem atom_supporter_cases_strict' {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) (h2 : ruleTag h ≠ 2) (h3 : ruleTag h ≠ 3)
    (h6 : ruleTag h ≠ 6) : isE h ∨ isS1 h :=
  atom_supporter_cases_strict h h2 h3 h6

/-- **根标签形式**（与 `atom_root_restricted` 同义，保留以对应任务书的命名）。 -/
theorem atom_supporter_root {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) :
    ruleTag h = 0 ∨ ruleTag h = 1 ∨ ruleTag h = 2 ∨ ruleTag h = 3 ∨ ruleTag h = 6 :=
  atom_root_restricted h

/-- `f1` 的标签是 `3`，故它不属于 `{0,1,2}`：反演中把 `f1` 排除出 `{e,s1,s2}` 的依据。 -/
theorem not_tag012_of_f1 {k : Kind} {t φ : Form} {x : Nat} (hx : ¬ FreeIn x t)
    (h : Ev (Kind.form k t φ)) :
    ¬ (ruleTag (Ev.f1 hx h) = 0 ∨ ruleTag (Ev.f1 hx h) = 1 ∨ ruleTag (Ev.f1 hx h) = 2) := by
  intro hc
  rcases hc with h0 | h1 | h2
  · rw [ruleTag_f1 hx h] at h0
    exact absurd h0 (by decide)
  · rw [ruleTag_f1 hx h] at h1
    exact absurd h1 (by decide)
  · rw [ruleTag_f1 hx h] at h2
    exact absurd h2 (by decide)

end Ev

/-! ## 4) 反例：原子支持者**可以**以 `f1`／`f4` 结尾

下面给出原题主定理的具体反例。取 `t := Form.atom 0 []`、`x := 0`。
`f1` 的前提是 `Ev (Form.atom 0 [] ⊳ Form.top)`；它由 `s1` 给出
（`Form.atom 0 [] ⊢ Form.top` 恒真：`Form.top` 的真值定义性地是 `⊤`），
再用 `s2` 沿 `Form.top ⊢ Form.top` 保持。 -/

/-- 任意原子支持者都推出 `Form.top`（后承 `Form.atom i ts ⊢ Form.top`）。 -/
theorem entails_atom_top (i : Nat) (ts : List Form) : Entails (Form.atom i ts) Form.top :=
  fun B ρ => by
    rw [show B.truth Form.top ρ = (⊤ : PSet B.W) from rfl]
    exact PSet.le_top _

namespace Ev

/-- 反例的**基础部分**：`Form.atom 0 [] ⊳ Form.top` 的证据。 -/
def atom_top_evidence : Ev (Form.atom 0 [] ⊳ Form.top) :=
  Ev.s2 (p := Form.top) (q := Form.top)
    (Ev.s1 (p := Form.atom 0 []) (q := Form.top) (entails_atom_top 0 []))
    (fun _ _ => PSet.le_refl _)

/-- **反例本体**：原子支持者 `Form.atom 0 [] ⊳ Form.all 0 Form.top` 的证据项，
最后一步是 `f1`（不是 `e`／`s1`／`s2`）。 -/
def f1_atomic_supporter : Ev (Form.atom 0 [] ⊳ Form.all 0 Form.top) :=
  Ev.f1 (k := Kind.supp) (t := Form.atom 0 []) (φ := Form.top) (x := 0)
    (by simp [FreeIn])
    (show Ev (Kind.supp.form (Form.atom 0 []) Form.top) from atom_top_evidence)

/-- 反例的标签是 `3`（`f1`）。 -/
theorem f1_atomic_supporter_tag : ruleTag f1_atomic_supporter = 3 := rfl

/-- **原题主定理在此反例上失效**：`isE h ∨ isS1 h ∨ isS2 h` 为假。 -/
theorem not_e_s1_s2_f1 : ¬ (isE f1_atomic_supporter ∨ isS1 f1_atomic_supporter ∨
    isS2 f1_atomic_supporter) := by
  intro hc
  rcases hc with h0 | h1 | h2
  · exact absurd (f1_atomic_supporter_tag.symm.trans h0) (by decide)
  · exact absurd (f1_atomic_supporter_tag.symm.trans h1) (by decide)
  · exact absurd (f1_atomic_supporter_tag.symm.trans h2) (by decide)

/-- **`f1` 反例同样反驳 `¬ isS2 h ⇒ isS1 h ∨ isE h`**：它的标签是 `3 ≠ 2`，
但 `isE`／`isS1` 都假。 -/
theorem f1_supporter_refutes_naive_cases :
    ruleTag f1_atomic_supporter ≠ 2 ∧ ¬ (isE f1_atomic_supporter ∨ isS1 f1_atomic_supporter) :=
  ⟨by decide, by
    intro hc
    rcases hc with h0 | h1
    · exact absurd (f1_atomic_supporter_tag.symm.trans h0) (by decide)
    · exact absurd (f1_atomic_supporter_tag.symm.trans h1) (by decide)⟩

/-- **`f4` 也能给原子支持者收尾**（标签 `6`），进一步说明原题断言过强。 -/
def f4_atomic_supporter : Ev (Form.atom 0 [] ⊳ Form.and Form.top Form.top) :=
  Ev.f4 (k := Kind.supp) (t := Form.atom 0 []) (φ := Form.top) (ψ := Form.top)
    (show Ev (Kind.supp.form (Form.atom 0 []) Form.top) from atom_top_evidence)
    (show Ev (Kind.supp.form (Form.atom 0 []) Form.top) from atom_top_evidence)

/-- `f4` 反例的标签是 `6`。 -/
theorem f4_atomic_supporter_tag : ruleTag f4_atomic_supporter = 6 := rfl

/-- `f4` 反例同样使 `e`／`s1`／`s2` 三个析取项全假。 -/
theorem not_e_s1_s2_f4 : ¬ (isE f4_atomic_supporter ∨ isS1 f4_atomic_supporter ∨
    isS2 f4_atomic_supporter) := by
  intro hc
  rcases hc with h0 | h1 | h2
  · exact absurd (f4_atomic_supporter_tag.symm.trans h0) (by decide)
  · exact absurd (f4_atomic_supporter_tag.symm.trans h1) (by decide)
  · exact absurd (f4_atomic_supporter_tag.symm.trans h2) (by decide)

/-- `s2` 确实可达（`atom_top_evidence` 的标签是 `2`），故 `atom_root_restricted`
里 `ruleTag h = 2` 这一支不能删——它正是"必须模去 `s2`"的原因。 -/
theorem atom_top_evidence_tag : ruleTag atom_top_evidence = 2 := rfl

end Ev

/-! ## 5) 链式正规形：规范与卡点

`s1`／`e` 的**根**之上只叠有限个 `s2`，并在每一层用 `f1`／`f4` 改写被支持式——
这正是第 3 节反演的自然加强。下面把"这样的链"写成归纳类型 `Ev.SNF`，
并定义**可计算**的链长 `SNF.len`。

**已证到哪一步**：`Ev.SNF` 的定义、`SNF.len` 的结构递归（链长是可计算数据）、
三条 `rfl` 级链长归约引理（`SNF.len_s1`／`SNF.len_e`／`SNF.len_s2`）以及
"叠一个 `s2` 使链长严格增长"（`SNF.len_s2_lt`）都已通过。

**卡在哪**：把 `h : Ev (Form.atom i ts ⊳ b)` 变成 `SNF i ts b` 的递归函数
`snfOfAtom` 需要**在同一函数体内**既对指标 `Form.atom i ts ⊳ b` 做 dependent
elimination、又对子项 `h₁ : Ev (Form.atom i ts ⊳ p)` 做**结构递归**。Lean 4.32 在
指标含 `Kind.form` 匹配式（`f1`／`f3`／`f4`／`p1`／`p2` 分支）时会以

```
Dependent elimination failed: Failed to solve equation
  (Form.atom i ts ⊳ b) =
    match k, t, Form.all x φ with
    | Kind.supp, a, b => a ⊳ b
    | Kind.refut, a, b => a ⊲ b
```

失败；而先用 `generalize` 把指标抽象成变量（本文件第 3 节与 `atom_root_restricted`
所用的正规手法）虽然能让 `cases` 通过，却使递归调用的**结构递减**不再被终止检查器
看见（递归变量被 `revert`／`intro` 打散）。

三条可行路线（都超出本文件已核验的范围，留作后续）：

1. 用 `WellFounded.fix` 在 `sizeOf h` 上做良基递归，`decreasing_by` 里为 `Ev`
   的子项关系 `sizeOf h₁ < sizeOf (Ev.s2 h₁ h)` 单独建引理；
2. 给 `Ev` 手写一个强化版依赖消去器（motive 里同时携带指标等式），在其上定义
   `snfOfAtom`；
3. 把链式正规形改写为**关系式**（`s2` 的自反传递闭包）并只证存在性
   `∃ h', s2Star h h' ∧ (ruleTag h' = 0 ∨ ruleTag h' = 1)`——存在性陈述可在
   `Prop` 层用 `induction` 完成，从而绕开 `Type` 层构造 `SNF` 的依赖消去难题。

本文件不写 `sorry`，因此**不声称**这三条已完成；`Ev.SNF` 在此只是精确的规范。 -/

namespace Ev

/-- 链式正规形：原子支持者 `Form.atom i ts ⊳ b` 的证据，其根是 `s1`（后承支持）
或 `e`（经典等价替换），其上只叠了有限个 `s2`（后承封闭）。

**注意 `e` 的字段**：`Ev.e hrep heq hγ` 的**结论是 `δ`**（不是 `γ`），而
`Replace φ ψ γ δ` 只说明 `γ`、`δ` 是同一上下文的不同填充，并不把 `γ` 与目标公式联系起来；
因此约束目标的等式必须写成 `δ = (Form.atom i ts ⊳ b)`。
（这一点由 `NormalForm.lean` 的正规形构造过程中暴露并修正。） -/
inductive SNF (i : Nat) (ts : List Form) : Form → Type where
  /-- 根是 **S1**：`p ⊢ q ⇒ p ⊳ q`。 -/
  | s1 (b : Form) (k : Kind) {p q : Form} (h : Entails p q) (hsup : p = Form.atom i ts)
      (hbody : q = b) : SNF i ts b
  /-- 根是 **E**：经典等价替换。 -/
  | e (b : Form) {φ ψ γ δ : Form} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ) (hγ : Ev γ)
      (htgt : δ = (Form.atom i ts ⊳ b)) : SNF i ts b
  /-- 在正规形之上再叠一个 **S2**：`(t ⊳ p) ∧ (p ⊢ q) ⇒ t ⊳ q`，支持者 `t` 不变。 -/
  | s2 (b : Form) {p q : Form} (h₁ : Ev (Form.atom i ts ⊳ p)) (hent : Entails p q)
      (st : SNF i ts p) (hbody : q = b) : SNF i ts b

/-- 正规形的"链长"：叠了多少个 `s2`（根不计入）。这是**可计算**的数据。 -/
def SNF.len {i : Nat} {ts : List Form} {b : Form} (st : SNF i ts b) : Nat :=
  match st with
  | .s1 _ _ _ _ _ => 0
  | .e _ _ _ _ _ => 0
  | .s2 _ _ _ s _ => SNF.len s + 1

/-- 链长为 `0` 的 `s1` 根（定义性）。 -/
@[simp] theorem SNF.len_s1 {i : Nat} {ts : List Form} {b : Form} {k : Kind} {p q : Form}
    (h : Entails p q) (hsup : p = Form.atom i ts) (hbody : q = b) :
    SNF.len (.s1 b k h hsup hbody : SNF i ts b) = 0 := rfl

/-- 链长为 `0` 的 `e` 根（定义性）。 -/
@[simp] theorem SNF.len_e {i : Nat} {ts : List Form} {b : Form} {φ ψ γ δ : Form}
    (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ) (hγ : Ev γ)
    (htgt : δ = (Form.atom i ts ⊳ b)) :
    SNF.len (.e b hrep heq hγ htgt : SNF i ts b) = 0 := rfl

/-- 叠一个 `s2` 使链长加一（定义性）。 -/
@[simp] theorem SNF.len_s2 {i : Nat} {ts : List Form} {b : Form} {p q : Form}
    (h₁ : Ev (Form.atom i ts ⊳ p)) (hent : Entails p q) (st : SNF i ts p)
    (hbody : q = b) :
    SNF.len (.s2 b h₁ hent st hbody : SNF i ts b) = SNF.len st + 1 := rfl

/-- `s2` 之上的链长严格增长：链**有限**这一点的定量形式。 -/
theorem SNF.len_s2_lt {i : Nat} {ts : List Form} {b : Form} {p q : Form}
    (h₁ : Ev (Form.atom i ts ⊳ p)) (hent : Entails p q) (st : SNF i ts p)
    (hbody : q = b) :
    SNF.len st < SNF.len (.s2 b h₁ hent st hbody : SNF i ts b) := by
  simp only [SNF.len_s2]
  exact Nat.lt_succ_self _

end Ev

end EvidenceLogic
