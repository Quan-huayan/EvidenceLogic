/-
# TrackF：原子支持者证据项的 `s2`-正规形（"正向刻画"补完）

本文件**不修改任何已有文件**，只在 `EvidenceLogic.Analysis.Inversion` 的成果之上补一批新结论。
无 `sorry` / `axiom` / `admit`，零依赖（不含 Mathlib），`lake env lean TrackF.lean` 零错误零警告。

## 一、精确陈述（本文件证了什么）

### 1) 关系 `Ev.S2Down`

```lean
inductive S2Down : ∀ {φ ψ : Form}, Ev φ → Ev ψ → Prop
  | refl {φ} (h : Ev φ) : S2Down h h
  | step {t p q ψ} (h : Ev (t ⊳ p)) (he : Entails p q) (h' : Ev ψ)
      (hs : S2Down h h') : S2Down (Ev.s2 h he) h'
```

`S2Down h h'` 读作"`h'` 由 `h` **反复剥掉顶层 `s2` 外壳**得到"（`refl` 剥零层，`step` 剥一层）。

> ⚠️ **两个指标必须分开（异质）**。任务书把 `S2Down` 写成 `∀ {φ}, Ev φ → Ev φ → Prop`（两个指标相同），
> 这**不可满足**：`s2` 的一步把结论 `Ev (t ⊳ q)` 变为前提 `Ev (t ⊳ p)`，**被支持式 `q` 变成了 `p`**，
> 因此剥壳后的证据项**不可能**与原证据项同型。正确的刻画是"**支持者不变、被支持式可变**"，
> 本文件把它写成两个指标 `φ ψ`。（`Inversion.lean` 的 `SNF` 用 `hbody : q = b` 记录同一现象，思路一致。）

### 2) 主引理 `Ev.s2_strip_supp`

```lean
theorem s2_strip_supp {s b : Form} (h : Ev (s ⊳ b)) :
    ∃ (b' : Form) (h' : Ev (s ⊳ b')), S2Down h h' ∧ ruleTag h' ≠ 2 ∧ Entails b' b
```

任意支持者 `s`、任意被支持式 `b`：沿顶层 `s2` 链走到尽头，得到一个
**支持者仍是 `s`**、**根不是 `s2`**（`ruleTag ≠ 2`）的证据项（被支持式变成某个 `b'`），
并且 `b' ⊢ b`——每个被剥掉的 `s2` 都是一次"前提 `p` 走向结论 `q`"的后承步，
所以正规形的被支持式是链条上**最强**的那个。
配套的 `Ev.s2_strip` 是不限定支持者的版本（对任意 `h : Ev φ` 都成立，只断言"剥得动"）。

### 3) 主定理 `Ev.atom_snf_exists`（及其加强版 `atom_snf_exists_entails`）

```lean
theorem atom_snf_exists {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) :
    ∃ (b' : Form) (h' : Ev (Form.atom i ts ⊳ b')),
      S2Down h h' ∧ (ruleTag h' = 0 ∨ ruleTag h' = 1 ∨ ruleTag h' = 3 ∨ ruleTag h' = 6)
```

原子支持者的证据项，把顶层 `s2` 外壳**剥干净**之后，根只能是 `e`／`s1`／`f1`／`f4`（标签 `0/1/3/6`）。
加强版 `atom_snf_exists_entails` 另外给出 `ruleTag h' ≠ 2` 与 `Entails b' b`。

### 4) 正规形的**唯一性**（`S2Down.det`／`S2Down.det_term`／`atom_snf_body_unique`）

剥壳终点不仅存在，而且**唯一**：若 `S2Down h h₁`、`S2Down h h₂` 且两者根都不是 `s2`，则
`h₁`、`h₂` 的**类型相同**（`det`），进而作为项**相等**（`det_term`）。
在原子支持者上即：`b'` 被 `h` 唯一决定（`atom_snf_body_unique`）。
因此"原子支持者的 `s2`-正规形"是**良定义**的（不是"存在某个正规形"）。

## 二、相对 `Ev.atom_root_restricted` 多给了什么

`atom_root_restricted` 只说**最外层**构造子属于 `{e,s1,s2,f1,f4}`（标签 `0,1,2,3,6`）。
其中 `s2` 是**唯一**"保持支持者、只沿后承前进"的壳，可以叠任意多层，所以该结论**没有把根定下来**：
最外层可能只是 `s2` 链条的第一环，链尾才见真章。本文件把这条链**剥干净**：

* `s2_strip_supp`：存在一个 `s2`-自由端点（`ruleTag ≠ 2`），**支持者一路不变**（仍是 `s`），
  且被支持式 `b'` 是原被支持式的前件（`b' ⊢ b`）；
* `atom_snf_exists`：在原子支持者上，再用 `atom_supporter_cases`（`Inversion.lean`）
  把 `≠ 2` 收紧为 `∈ {0,1,3,6}`（加强版 `atom_snf_exists_entails` 同时给出 `b' ⊢ b`）；
* `atom_snf_body_unique`：这个端点（在原子支持者上就是被支持式 `b'`）是**唯一**的。

即把"根是 `s2` **或**是终结根"加强为"（沿 `s2` 链走到底）根**就是**终结根，且**只有一个**"。
`f2`／`f3`／`r1`／`p1`／`p2` 之所以从根里消失，是因为它们要么改支持者形状（`f2`／`f3`／`p1`／`p2`），
要么改关系种类（`r1`），在**原子支持者**下直接矛盾（`atom_root_restricted` 已排除）；
`f1`／`f4` 只改被支持式、不改支持者，仍然可达，所以**不能**从 `{0,1,3,6}` 中删去
（见 `Inversion.lean` 第 4 节的具体反例）。

## 三、方法：路线 2（强化消去器），不需要路线 1 的良基递归

难点（`Inversion.lean` 第 5 节已记录）：对 `h : Ev (Form.atom i ts ⊳ b)` 直接
`cases h`／`induction h` 会在 `f1`／`f2`／`f3`／`f4`／`p1`／`p2` 分支上因指标里的
`Kind.form` 匹配式而报

```
Dependent elimination failed: Failed to solve equation
  (Form.atom i ts ⊳ b) = match k, t, Form.all x φ with
  | Kind.supp, a, b => a ⊳ b
  | Kind.refut, a, b => a ⊲ b
```

而先 `generalize` 把指标抽象成变量虽能消除该错误，却打散递归变量、使终止检查失效。

本文件走**路线 2**：直接调用 `Ev` 的归纳原理 `Ev.rec`，把**指标等式搬进 motive**：

```lean
motive := fun (a : Form) (h : Ev a) =>
    ∀ (s' b' : Form), a = (s' ⊳ b') →
      ∃ (b'' : Form) (h'' : Ev (s' ⊳ b'')), S2Down h h'' ∧ ruleTag h'' ≠ 2 ∧ Entails b'' b'
```

三个要点：

1. **指标是变量 `a`**（不是字面量 `Form.atom i ts ⊳ b`）⇒ 依赖消去不再失败；
2. motive 里的等式 `a = (s' ⊳ b')` 由每个分支自己消去（非 `s2` 分支用 `rw [← he]`，
   `s2` 分支用 `subst` 消去 `s'` 与 `q`），于是**构造子的隐式参数全部可命名**
   （在 case lambda 里绑定），`s2` 分支因此拿得到 `t, p, q`，才能把"支持者仍是 `s`"
   与"后承链加长"（`Entails b' t` 与 `Entails p q` 复合）这两步做实；
3. 递归调用由 `Ev.rec` 的**归纳假设**自动给出（`s2` 分支的 IH 直接作用在前提
   `h₁ : Ev (t ⊳ p)` 上），因此**不需要** `WellFounded.fix`、不需要 `decreasing_by`、
   不需要 `sizeOf` 的递减证明——**路线 1 因而不必动用**。

第 5 节仍附上路线 1 所需的递减引理 `sizeOf_lt_Ev_s2`（本文件主证明并不使用它），
以记录 `sizeOf` 路线在 `decreasing_by` 里到底需要哪些引理。

## 四、技术注记

* `Ev.rec` 的 case 函数**只有递归构造子**带归纳假设：`e, s2, f1, f2, f3, f4, r1, p1, p2` 有，
  **`s1` 没有**（`Entails` 不是递归的）。给 `s1` 多写一个 `_` 会把 motive 的第一个参数吃掉，
  报出很易误导的 `Type mismatch … (p ⊳ q) = (x✝ ⊳ b')`。本文件的 case 元数已与 `Ev.rec` 对齐。
* 标签证明不要用 `decide`：`decide` 在目标含自由变量时报
  `Expected type must not contain free variables … ruleTag … ≠ 2`。
  本文件改用 `simp`（`Inversion.lean` 已有 `@[simp] ruleTag_e/s1/s2/f1/…/p2`）。
* `Inversion.lean` 的 `SNF.e` 构造子要求 `hsup : γ = (Form.atom i ts ⊳ b)`，
  但 `Ev.e hrep heq hγ : Ev δ`（**结论**是 `δ` 而不是 `γ`）：`Ev.e` 的数据里 `γ` 与目标公式
  毫无约束关系（`Replace φ ψ γ δ` 只说明两者由**同一上下文**的不同填充得到），
  所以"`γ = 目标`"这一步**不可由规则数据推出**，`snfOfAtom … → SNF i ts b` 按该规范写不出来。
  正确的字段应是 `δ = (Form.atom i ts ⊳ b)`（这正是本文 `s2_strip_supp` 的 `e` 分支所消去的等式）。
-/
import EvidenceLogic.Analysis.Inversion
import EvidenceLogic.System.Derived

namespace EvidenceLogic

namespace Ev

/-! ## 1) "剥掉顶层 `s2` 外壳"的关系 -/

/-- `S2Down h h'`：`h'` 由 `h` 反复剥掉**顶层 `s2` 外壳**得到。

两个指标 `φ`（起点）与 `ψ`（终点）**必须分开**：`s2` 的一步 `Ev (t ⊳ q) → Ev (t ⊳ p)`
保持支持者 `t`，却把被支持式从 `q` 换成前提里的 `p`，因此终点一般**不同型**。 -/
inductive S2Down : ∀ {φ ψ : Form}, Ev φ → Ev ψ → Prop where
  /-- 剥零层。 -/
  | refl {φ : Form} (h : Ev φ) : S2Down h h
  /-- 剥一层 `s2`（支持者 `t` 不变，被支持式由 `q` 退到 `p`），再继续剥。 -/
  | step {t p q : Form} (h : Ev (t ⊳ p)) (he : Entails p q) {ψ : Form} (h' : Ev ψ)
      (hs : S2Down h h') : S2Down (Ev.s2 h he) h'

/-! ## 2) 剥壳引理：`s2` 链总能剥到 `s2`-自由的根 -/

/-- **主引理（路线 2：强化消去器）**：支持者为 `s` 的证据项，沿顶层 `s2` 链剥到底，
得到一个支持者**仍是 `s`**、根**不是 `s2`** 的证据项，且其被支持式 `b'` **是原被支持式 `b` 的前件**
（`b' ⊢ b`：每个被剥掉的 `s2` 都是一次"从前提 `p` 走向结论 `q`"的后承步）。

证明用 `Ev.rec`，motive 里同时携带指标等式 `a = (s' ⊳ b')`；`s2` 分支用归纳假设作用于前提
`h₁ : Ev (t ⊳ p)`，并用 `Form.supp.inj` 把"支持者不变"（`s' = t`）与后承链的延长做实。 -/
theorem s2_strip_supp {s b : Form} (h : Ev (s ⊳ b)) :
    ∃ (b' : Form) (h' : Ev (s ⊳ b')), S2Down h h' ∧ ruleTag h' ≠ 2 ∧ Entails b' b :=
  Ev.rec
    (motive := fun (a : Form) (h : Ev a) => ∀ (s' b' : Form), a = (s' ⊳ b') →
      ∃ (b'' : Form) (h'' : Ev (s' ⊳ b'')), S2Down h h'' ∧ ruleTag h'' ≠ 2 ∧ Entails b'' b')
    -- E：结论 `Ev δ`，把指标改写回 `δ`，取原项作端点（根 `e`，标签 0）
    (fun {φ ψ γ δ : Form} (hrep : Replace φ ψ γ δ) (heq : φ ⊣⊢ ψ) (hγ : Ev γ) _ =>
      fun (s' b' : Form) (he : δ = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.e hrep heq hγ, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- S1：结论 `Ev (p ⊳ q)`（根 `s1`，标签 1；`s1` 没有归纳假设）
    (fun {p q : Form} (hpq : Entails p q) =>
      fun (s' b' : Form) (he : (p ⊳ q) = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.s1 hpq, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- S2：唯一的递归分支：剥掉这一层，再把支持者 `t` 换回 `s'`
    (fun {t p q : Form} (h₁ : Ev (t ⊳ p)) (hpq : Entails p q) ih =>
      fun (s' b' : Form) (he : (t ⊳ q) = (s' ⊳ b')) => by
        obtain ⟨b'', h'', hs'', htag, hent⟩ := ih t p rfl
        have hst : s' = t := ((Form.supp.inj he).1).symm
        have hqb : q = b' := (Form.supp.inj he).2
        subst s'
        subst q
        exact ⟨b'', h'', S2Down.step h₁ hpq h'' hs'', htag,
          fun B ρ => PSet.le_trans (hent B ρ) (hpq B ρ)⟩)
    -- F1：结论 `Ev (Kind.form k t (.all x φ))`（根 `f1`，标签 3）
    (fun {k : Kind} {t φ : Form} {x : Nat} (hx : ¬ FreeIn x t) (h : Ev (Kind.form k t φ)) _ =>
      fun (s' b' : Form) (he : Kind.form k t (.all x φ) = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.f1 hx h, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- F2：结论 `Ev (Kind.form k (.all x p) φ)`（根 `f2`，标签 4）
    (fun {k : Kind} {p φ : Form} {x : Nat} (hx : ¬ FreeIn x φ) (h : Ev (Kind.form k p φ)) _ =>
      fun (s' b' : Form) (he : Kind.form k (.all x p) φ = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.f2 hx h, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- F3：结论 `Ev (Kind.form k (.and a c) φ)`（根 `f3`，标签 5）
    (fun {k : Kind} {a c φ : Form} (h₁ : Ev (Kind.form k a φ)) (h₂ : Ev (Kind.form k c φ)) _ _ =>
      fun (s' b' : Form) (he : Kind.form k (.and a c) φ = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.f3 h₁ h₂, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- F4：结论 `Ev (Kind.form k t (.and φ ψ))`（根 `f4`，标签 6）
    (fun {k : Kind} {t φ ψ : Form} (h₁ : Ev (Kind.form k t φ)) (h₂ : Ev (Kind.form k t ψ)) _ _ =>
      fun (s' b' : Form) (he : Kind.form k t (.and φ ψ) = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.f4 h₁ h₂, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- R1：结论 `Ev (t ⊲ φ)`（根 `r1`，标签 7）
    (fun {t φ : Form} (h : Ev (t ⊳ .not φ)) _ =>
      fun (s' b' : Form) (he : (t ⊲ φ) = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.r1 h, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- P1：结论 `Ev (Kind.form kR (.and a1 a2) (Kind.form kS (.and c d) f))`（根 `p1`，标签 8）
    (fun {kR kS : Kind} {a1 a2 c d f : Form} (h₁ : Ev (Kind.form kR a1 c))
        (h₂ : Ev (Kind.form kR a2 d)) (h₃ : Ev (Kind.form kS (.and c d) f)) _ _ _ =>
      fun (s' b' : Form)
        (he : Kind.form kR (.and a1 a2) (Kind.form kS (.and c d) f) = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.p1 h₁ h₂ h₃, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    -- P2：结论 `Ev (Kind.form kR (.all x a) (Kind.form kS (.all x c) f))`（根 `p2`，标签 9）
    (fun {kR kS : Kind} {a c f : Form} {x : Nat} (h₁ : Ev (Kind.form kR a c))
        (h₂ : Ev (Kind.form kS (.all x c) f)) (hx : ¬ FreeIn x f) _ _ =>
      fun (s' b' : Form)
        (he : Kind.form kR (.all x a) (Kind.form kS (.all x c) f) = (s' ⊳ b')) =>
        ⟨b', by rw [← he]; exact ⟨Ev.p2 h₁ h₂ hx, S2Down.refl _, by simp, entails_refl b'⟩⟩)
    h s b rfl

/-- **剥壳引理（不限定支持者）**：任意证据项都能沿顶层 `s2` 链剥到 `s2`-自由的根。

这是 `s2_strip_supp` 在**任意指标**上的对应版本：结论不再记录端点类型（也不带 `Entails`），
但覆盖任意 `h : Ev φ`（不必是 `s ⊳ b`）。用 `Ev` 的**结构归纳**直接可得：
指标 `φ` 在定理里是变量，故依赖消去不失败。 -/
theorem s2_strip {φ : Form} (h : Ev φ) :
    ∃ (ψ : Form) (h' : Ev ψ), S2Down h h' ∧ ruleTag h' ≠ 2 := by
  induction h with
  | e hrep heq hγ _ => exact ⟨_, Ev.e hrep heq hγ, S2Down.refl _, by simp⟩
  | s1 hpq => exact ⟨_, Ev.s1 hpq, S2Down.refl _, by simp⟩
  | s2 h₁ hpq ih =>
      obtain ⟨ψ, h', hs, htag⟩ := ih
      exact ⟨ψ, h', S2Down.step h₁ hpq h' hs, htag⟩
  | f1 hx h _ => exact ⟨_, Ev.f1 hx h, S2Down.refl _, by simp⟩
  | f2 hx h _ => exact ⟨_, Ev.f2 hx h, S2Down.refl _, by simp⟩
  | f3 h₁ h₂ _ _ => exact ⟨_, Ev.f3 h₁ h₂, S2Down.refl _, by simp⟩
  | f4 h₁ h₂ _ _ => exact ⟨_, Ev.f4 h₁ h₂, S2Down.refl _, by simp⟩
  | r1 h _ => exact ⟨_, Ev.r1 h, S2Down.refl _, by simp⟩
  | p1 h₁ h₂ h₃ _ _ _ => exact ⟨_, Ev.p1 h₁ h₂ h₃, S2Down.refl _, by simp⟩
  | p2 h₁ h₂ hx _ _ => exact ⟨_, Ev.p2 h₁ h₂ hx, S2Down.refl _, by simp⟩

/-! ## 3) 主定理：原子支持者的根 ∈ {e, s1, f1, f4} -/

/-- **主定理**：原子支持者 `Form.atom i ts ⊳ b` 的证据项，沿顶层 `s2` 链剥到底，
得到的端点（支持者不变）其根属于 `{e, s1, f1, f4}`（标签 `0 / 1 / 3 / 6`）。

与 `Ev.atom_root_restricted` 的区别：后者允许最外层是 `s2`（标签 2），
本定理把 `s2` 链整个剥掉，**根不再是 `s2`**，并且被支持式一般变成了另一个 `b'`。 -/
theorem atom_snf_exists {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) :
    ∃ (b' : Form) (h' : Ev (Form.atom i ts ⊳ b')),
      S2Down h h' ∧ (ruleTag h' = 0 ∨ ruleTag h' = 1 ∨ ruleTag h' = 3 ∨ ruleTag h' = 6) := by
  obtain ⟨b', h', hs, htag, _⟩ := s2_strip_supp h
  exact ⟨b', h', hs, atom_supporter_cases h' htag⟩

/-- 主定理的**加强版**：剥壳端点确实不是 `s2`，而且其被支持式 `b'` 是原被支持式 `b` 的**前件**
（`b' ⊢ b`）——剥掉 `s2` 链只会沿后承链把被支持式**加强**。 -/
theorem atom_snf_exists_entails {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) :
    ∃ (b' : Form) (h' : Ev (Form.atom i ts ⊳ b')),
      S2Down h h' ∧ Entails b' b ∧ ruleTag h' ≠ 2 ∧
        (ruleTag h' = 0 ∨ ruleTag h' = 1 ∨ ruleTag h' = 3 ∨ ruleTag h' = 6) := by
  obtain ⟨b', h', hs, htag, hent⟩ := s2_strip_supp h
  exact ⟨b', h', hs, hent, htag, atom_supporter_cases h' htag⟩

/-! ## 4) 正规形的唯一性（剥壳终点是良定义的） -/

/-- **端点的类型唯一**：若 `h` 沿 `s2` 链可剥到两个 `s2`-自由的端点，
则两端点**同型**。故 `s2` 链不含选择。 -/
theorem S2Down.det {φ ψ ψ' : Form} {h : Ev φ} {h' : Ev ψ} {h'' : Ev ψ'}
    (hs : S2Down h h') (hs' : S2Down h h'')
    (ht : ruleTag h' ≠ 2) (ht' : ruleTag h'' ≠ 2) : ψ = ψ' := by
  induction hs with
  | refl =>
      cases hs' with
      | refl => rfl
      | step h₁ he h₂ hs₁ => exact absurd (by simp) ht
  | step h₁ he h₂ hs₁ ih =>
      cases hs' with
      | refl => exact absurd (by simp) ht'
      | step h₃ he' h₄ hs₂ => exact ih hs₂ ht

/-- **端点的项唯一**：两端点同型时，作为证据项也**相等**（"正规形是函数"）。 -/
theorem S2Down.det_term {φ ψ : Form} {h : Ev φ} {h' h'' : Ev ψ}
    (hs : S2Down h h') (hs' : S2Down h h'')
    (ht : ruleTag h' ≠ 2) (ht' : ruleTag h'' ≠ 2) : h' = h'' := by
  induction hs with
  | refl =>
      cases hs' with
      | refl => rfl
      | step h₁ he h₂ hs₁ => exact absurd (by simp) ht
  | step h₁ he h₂ hs₁ ih =>
      cases hs' with
      | refl => exact absurd (by simp) ht'
      | step h₃ he' h₄ hs₂ => exact ih hs₂ ht ht'

/-- **原子支持者的正规形良定义**：`h` 的 `s2`-自由端点的**被支持式 `b'` 唯一**。 -/
theorem atom_snf_body_unique {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊳ b)) {b₁ b₂ : Form}
    {h₁ : Ev (Form.atom i ts ⊳ b₁)} {h₂ : Ev (Form.atom i ts ⊳ b₂)}
    (hs₁ : S2Down h h₁) (hs₂ : S2Down h h₂)
    (ht₁ : ruleTag h₁ ≠ 2) (ht₂ : ruleTag h₂ ≠ 2) : b₁ = b₂ :=
  (Form.supp.inj (S2Down.det hs₁ hs₂ ht₁ ht₂)).2

/-! ## 5) 附：路线 1（`sizeOf` 良基递归）所需的递减排

本文件主证明走路线 2，**不用**这一节。这里记录：若改走路线 1，`decreasing_by` 里对
`s2` 的前提 `h₁` 与 `Ev.s2 h₁ he` 需证 `sizeOf h₁ < sizeOf (Ev.s2 h₁ he)`。
`simp_wf` 把它归约为纯算术 `0 < 1 + sizeOf t + sizeOf p + sizeOf q`，
用核心的 `Nat.lt_of_lt_of_le`／`Nat.zero_lt_one`／`Nat.le_add_right_of_le`／`Nat.le_add_right`
手写即可（不需要 `omega`）。 -/
theorem sizeOf_lt_Ev_s2 {t p q : Form} (h₁ : Ev (t ⊳ p)) (he : Entails p q) :
    sizeOf h₁ < sizeOf (Ev.s2 h₁ he) := by
  simp_wf
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one
    (Nat.le_add_right_of_le
      (Nat.le_add_right_of_le (Nat.le_add_right 1 (sizeOf t)) (k := sizeOf p))
      (k := sizeOf q))

end Ev

end EvidenceLogic
