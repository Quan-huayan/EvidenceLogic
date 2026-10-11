/-
# TrackG：原子**反驳者**的反演（`Ev (Form.atom i ts ⊲ b)` 的根受限）

本文件**不修改任何已有文件**，只在 `import EvidenceLogic` 之上补一批新结论。

姊妹成果 [`EvidenceLogic/Inversion.lean`](EvidenceLogic/Inversion.lean) 做的是**支持侧**：
原子支持者 `Form.atom i ts ⊳ b` 的证据项，最后一步必属于 `{e, s1, s2, f1, f4}`
（标签 `0, 1, 2, 3, 6`）。本文件做**反驳侧**的对偶问题：

```lean
theorem Ev.atom_refut_root_restricted {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) :
    ruleTag h = 0 ∨ ruleTag h = 7 ∨ ruleTag h = 3 ∨ ruleTag h = 6   -- e, r1, f1, f4
```

## 结论一览

| 名称 | 陈述 | 状态 |
|---|---|---|
| `kind_form_all_ne_refut_atom` 等五条 | 反驳侧的形状冲突引理（`Kind` 两分支同时击碎） | ✅ |
| `Ev.atom_refut_root_restricted` | **主定理**：原子反驳者的最后一步必属于 `{e, r1, f1, f4}`（标签 `0, 7, 3, 6`） | ✅ |
| `Ev.atom_refut_root_restricted'` | 主定理的判定子写法（`isE ∨ isR1 ∨ isF1 ∨ isF4`） | ✅ |
| `Ev.tag_ne_of_mem_refut` | 把标签层面的排除从析取式里分离出来 | ✅ |
| `Ev.atom_refuter_tag_ne_s1`…`_p2` | 逐条排除：标签 `≠ 1, 2, 4, 5, 8, 9`（`s1, s2, f2, f3, p1, p2`） | ✅ |
| `Ev.refut_r1_witness`／`_f1_`／`_f4_`／`_e_` | **紧性**：四个槽位 `7/3/6/0` 都真的可达 | ✅ |
| `Ev.refut_e_witness_gen` | `e` 槽位的**非退化**见证（用 `Ctx.refutR` 真的替换子公式 `⊥ ∧ ⊥ ↦ ⊥`） | ✅ |
| `Ev.atom_refut_root_slots_all_realized` | 四个见证的标签恰为 `0, 7, 3, 6` 且两两不同 | ✅ |

## 推导（先想清楚再让 Lean 确认）

**哪些构造子能产出 `⊲` 结论**：`e`（结论任意 `δ`）、`r1`（结论 `t ⊲ φ`），
以及 `f1/f2/f3/f4/p1/p2` 在 `k = .refut`（或 `kR = .refut`）时。

**哪些保持"支持者是原子"（⇒ 保留）**：

* `e`（标签 `0`）：结论任意，平凡可达；
* `r1`（标签 `7`）：`Ev (t ⊳ ¬φ) ⇒ Ev (t ⊲ φ)`，**支持者 `t` 原样保留**，
  取 `t := Form.atom i ts` 即可；
* `f1`（标签 `3`）：`f1` 的结论是 `Kind.form k t (∀x φ)`；在 `k = .refut` 分支下是
  `t ⊲ ∀x φ`——它只改写**被反驳式**，**支持者仍是 `t`**，取 `t := Form.atom i ts` 即可；
* `f4`（标签 `6`）：同理，`t ⊲ (φ ∧ ψ)` 的**支持者仍是 `t`**。

**哪些破坏"支持者是原子"（⇒ 排除）**：

* `s1`／`s2`（标签 `1`／`2`）：结论是 `p ⊳ q`（`Form.supp`），与 `Form.refut` 构造子冲突；
* `f2`（标签 `4`）：`k = .refut` 时结论是 `(∀x p) ⊲ φ`，**支持者变成 `∀x p`**；
* `f3`（标签 `5`）：`k = .refut` 时结论是 `(a ∧ b) ⊲ φ`，**支持者变成 `a ∧ b`**；
* `p1`（标签 `8`）：`kR = .refut` 时支持者是 `a ∧ b`；
* `p2`（标签 `9`）：`kR = .refut` 时支持者是 `∀x a`。

**注意**：与支持侧的"重要更正"不同，这里 `f1`／`f4` **确实**保留支持者（它们只改写
被反驳式），所以预期答案 `{0, 7, 3, 6}` 是**对的**——本文件已机器验证，且四个槽位都
真的可达（第 4 节的四个见证项）。

## 证明里的各构造子排除方式

`cases h`（`h : Ev (Form.atom i ts ⊲ b)`）会因指标含 `Kind.form k …` 匹配式而在
`f1/f2/f3/f4/p1/p2` 分支报 `Dependent elimination failed`；本文件沿用姊妹文件的
正规手法：**先把指标 `generalize` 成变量**再做 `cases`。随后各分支：

| 构造子 | 标签 | 结论形状 | 排除／保留手段 |
|---|---|---|---|
| `e`   | 0 | `δ`（任意） | — 保留（`Or.inl rfl`） |
| `s1`  | 1 | `p ⊳ q` | `Form.noConfusion`（`Form.supp` vs `Form.refut`） |
| `s2`  | 2 | `t ⊳ q` | 同上 |
| `f1`  | 3 | `Kind.form k t (∀x φ)` | — 保留 |
| `f2`  | 4 | `Kind.form k (∀x p) φ` | `cases k` 后两条腿：`supp` 用 `Form.noConfusion`；`refut` 用 `Form.refut.inj` 取 `∀x p = Form.atom i ts` 再 `Form.noConfusion` |
| `f3`  | 5 | `Kind.form k (a ∧ b) φ` | 同上（`Form.and a b = Form.atom i ts`） |
| `f4`  | 6 | `Kind.form k t (φ ∧ ψ)` | — 保留 |
| `r1`  | 7 | `t ⊲ φ` | — 保留 |
| `p1`  | 8 | `Kind.form kR (a ∧ b) (…)` | `cases kR` 后同 `f3` |
| `p2`  | 9 | `Kind.form kR (∀x a) (…)` | `cases kR` 后同 `f2` |

本文件无 `sorry`／`axiom`／`admit`，零依赖（不含 Mathlib）。未使用的绑定一律写 `_`。
-/
import EvidenceLogic.Analysis.Inversion
import EvidenceLogic.Analysis.Initiality

namespace EvidenceLogic

/-! ## 1) 反驳侧的形状冲突引理

`Kind.form` 是模式匹配定义，故 `Kind.form .supp a b`／`Kind.form .refut a b` 定义性地
归约为 `a ⊳ b`／`a ⊲ b`（`Kind.form_supp`／`Kind.form_refut`）。下面五条是姊妹文件
`kind_form_all_ne_supp_atom` 等的**反驳侧对应物**：目标一律换成更具体的
`Form.atom i ts ⊲ b`（左侧保持具体的冒犯参数，故陈述为真且不可削弱）。 -/

/-- `f2` 型冲突（反驳侧）：支持者是 `Form.all x p`，与 `Form.atom i ts` 冲突。 -/
theorem kind_form_all_ne_refut_atom {i : Nat} {ts : List Form} {b : Form}
    {k : Kind} {p φ : Form} {x : Nat}
    (he : Kind.form k (Form.all x p) φ = (Form.atom i ts ⊲ b)) : False := by
  cases k
  · rw [Kind.form_supp] at he
    exact Form.noConfusion he
  · rw [Kind.form_refut] at he
    exact Form.noConfusion (Form.refut.inj he).1

/-- `f3` 型冲突（反驳侧）：支持者是 `Form.and a c`，与 `Form.atom i ts` 冲突。 -/
theorem kind_form_and_ne_refut_atom {i : Nat} {ts : List Form} {b : Form}
    {k : Kind} {a c φ : Form}
    (he : Kind.form k (Form.and a c) φ = (Form.atom i ts ⊲ b)) : False := by
  cases k
  · rw [Kind.form_supp] at he
    exact Form.noConfusion he
  · rw [Kind.form_refut] at he
    exact Form.noConfusion (Form.refut.inj he).1

/-- `s1`／`s2` 型冲突：结论是**支持** `p ⊳ q`，与 `Form.refut` 构造子冲突。

`Ev.s1`／`Ev.s2` 的目标类型是 `Form.supp p q`，而目标指标是 `Form.refut …`；
两者是**不同构造子**，故直接 `Form.noConfusion`（无需先取分量）。 -/
theorem supp_ne_refut_atom {i : Nat} {ts : List Form} {b : Form} {p q : Form}
    (he : (p ⊳ q) = (Form.atom i ts ⊲ b)) : False := by
  exact Form.noConfusion he

/-- `p1` 型冲突（反驳侧）：结论支持者是 `Form.and a c`，被反驳式是嵌套 `Kind.form`。 -/
theorem kind_form_p1_ne_refut_atom {i : Nat} {ts : List Form} {b : Form}
    {kR kS : Kind} {a c d f : Form}
    (he : Kind.form kR (Form.and a c) (Kind.form kS d f) = (Form.atom i ts ⊲ b)) : False := by
  cases kR
  · rw [Kind.form_supp] at he
    exact Form.noConfusion he
  · rw [Kind.form_refut] at he
    exact Form.noConfusion (Form.refut.inj he).1

/-- `p2` 型冲突（反驳侧）：结论支持者是 `Form.all x a`。 -/
theorem kind_form_p2_ne_refut_atom {i : Nat} {ts : List Form} {b : Form}
    {kR kS : Kind} {a c f : Form} {x : Nat}
    (he : Kind.form kR (Form.all x a) (Kind.form kS c f) = (Form.atom i ts ⊲ b)) : False := by
  cases kR
  · rw [Kind.form_supp] at he
    exact Form.noConfusion he
  · rw [Kind.form_refut] at he
    exact Form.noConfusion (Form.refut.inj he).1

namespace Ev

/-! ## 2) 主反演定理

技术要点与姊妹文件相同：`cases h` 直接用在 `h : Ev (Form.atom i ts ⊲ b)` 上时，
Lean 的 dependent elimination 会因为指标里的 `Kind.form` 匹配式而在
`f1/f2/f3/f4/p1/p2` 分支失败；因此**先把指标 `generalize` 成变量**再 `cases`。 -/

/-- **原子反驳者反演（主定理）**：

原子反驳者 `Form.atom i ts ⊲ b` 的证据项，最后一步**必属于** `{e, r1, f1, f4}`
（标签 `0, 7, 3, 6`）——即 `s1`、`s2`、`f2`、`f3`、`p1`、`p2` 被排除。

这个刻画是**紧**的：四个析取项都真的可达，见第 4 节的
`refut_r1_witness`（`7`）、`refut_f1_witness`（`3`）、`refut_f4_witness`（`6`）、
`refut_e_witness`（`0`）以及 `atom_refut_root_slots_all_realized`。 -/
theorem atom_refut_root_restricted {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) :
    ruleTag h = 0 ∨ ruleTag h = 7 ∨ ruleTag h = 3 ∨ ruleTag h = 6 := by
  revert h
  generalize hφ : (Form.atom i ts ⊲ b) = φ
  intro h
  cases h with
  | e _ _ _ => exact Or.inl rfl
  | s1 _ => exact False.elim (supp_ne_refut_atom hφ.symm)
  | s2 _ _ => exact False.elim (supp_ne_refut_atom hφ.symm)
  | f1 _ _ => exact Or.inr (Or.inr (Or.inl rfl))
  | f2 _ _ => exact False.elim (kind_form_all_ne_refut_atom hφ.symm)
  | f3 _ _ => exact False.elim (kind_form_and_ne_refut_atom hφ.symm)
  | f4 _ _ => exact Or.inr (Or.inr (Or.inr rfl))
  | r1 _ => exact Or.inr (Or.inl rfl)
  | p1 _ _ _ => exact False.elim (kind_form_p1_ne_refut_atom hφ.symm)
  | p2 _ _ _ => exact False.elim (kind_form_p2_ne_refut_atom hφ.symm)

/-- **判定子形式**：`atom_refut_root_restricted` 换成 `isE`／`isR1`／`isF1`／`isF4` 记法。 -/
theorem atom_refut_root_restricted' {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : isE h ∨ isR1 h ∨ isF1 h ∨ isF4 h :=
  atom_refut_root_restricted h

/-! ## 3) 逐条排除引理

把标签层面的排除从析取式里分离出来，便于下游直接
`exact absurd htag (atom_refuter_tag_ne_f2 h)`。 -/

/-- 由"标签属于 `{0, 7, 3, 6}`"推出"标签不是给定的 `m`"。 -/
theorem tag_ne_of_mem_refut {φ : Form} {h : Ev φ}
    (hmem : ruleTag h = 0 ∨ ruleTag h = 7 ∨ ruleTag h = 3 ∨ ruleTag h = 6)
    {m : Nat} (hm0 : m ≠ 0) (hm7 : m ≠ 7) (hm3 : m ≠ 3) (hm6 : m ≠ 6) :
    ruleTag h ≠ m := by
  intro hc
  rcases hmem with h0 | h7 | h3 | h6
  · exact hm0 (hc.symm.trans h0)
  · exact hm7 (hc.symm.trans h7)
  · exact hm3 (hc.symm.trans h3)
  · exact hm6 (hc.symm.trans h6)

/-- `s1`（标签 `1`）绝不为原子反驳者收尾：它的结论是**支持** `p ⊳ q`。 -/
theorem atom_refuter_tag_ne_s1 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ruleTag h ≠ 1 :=
  tag_ne_of_mem_refut (atom_refut_root_restricted h) (by decide) (by decide) (by decide)
    (by decide)

/-- `s2`（标签 `2`）绝不为原子反驳者收尾：它的结论是**支持** `t ⊳ q`。 -/
theorem atom_refuter_tag_ne_s2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ruleTag h ≠ 2 :=
  tag_ne_of_mem_refut (atom_refut_root_restricted h) (by decide) (by decide) (by decide)
    (by decide)

/-- `f2`（标签 `4`）绝不为原子反驳者收尾：它把支持者改成 `∀x p`。 -/
theorem atom_refuter_tag_ne_f2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ruleTag h ≠ 4 :=
  tag_ne_of_mem_refut (atom_refut_root_restricted h) (by decide) (by decide) (by decide)
    (by decide)

/-- `f3`（标签 `5`）绝不为原子反驳者收尾：它把支持者改成 `a ∧ b`。 -/
theorem atom_refuter_tag_ne_f3 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ruleTag h ≠ 5 :=
  tag_ne_of_mem_refut (atom_refut_root_restricted h) (by decide) (by decide) (by decide)
    (by decide)

/-- `p1`（标签 `8`）绝不为原子反驳者收尾：它把支持者改成 `a ∧ b`。 -/
theorem atom_refuter_tag_ne_p1 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ruleTag h ≠ 8 :=
  tag_ne_of_mem_refut (atom_refut_root_restricted h) (by decide) (by decide) (by decide)
    (by decide)

/-- `p2`（标签 `9`）绝不为原子反驳者收尾：它把支持者改成 `∀x a`。 -/
theorem atom_refuter_tag_ne_p2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ruleTag h ≠ 9 :=
  tag_ne_of_mem_refut (atom_refut_root_restricted h) (by decide) (by decide) (by decide)
    (by decide)

/-- 判定子写法的 `s1` 排除。 -/
theorem atom_refuter_not_isS1 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ¬ isS1 h :=
  atom_refuter_tag_ne_s1 h

/-- 判定子写法的 `s2` 排除。 -/
theorem atom_refuter_not_isS2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ¬ isS2 h :=
  atom_refuter_tag_ne_s2 h

/-- 判定子写法的 `f2` 排除。 -/
theorem atom_refuter_not_isF2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ¬ isF2 h :=
  atom_refuter_tag_ne_f2 h

/-- 判定子写法的 `f3` 排除。 -/
theorem atom_refuter_not_isF3 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ¬ isF3 h :=
  atom_refuter_tag_ne_f3 h

/-- 判定子写法的 `p1` 排除。 -/
theorem atom_refuter_not_isP1 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ¬ isP1 h :=
  atom_refuter_tag_ne_p1 h

/-- 判定子写法的 `p2` 排除。 -/
theorem atom_refuter_not_isP2 {i : Nat} {ts : List Form} {b : Form}
    (h : Ev (Form.atom i ts ⊲ b)) : ¬ isP2 h :=
  atom_refuter_tag_ne_p2 h

end Ev

/-! ## 4) 紧性：四个槽位都真的可达

`r1` 的前提是 `Ev (t ⊳ ¬φ)`。取 `t := Form.atom 0 []`、`φ := Form.bot`：
`¬⊥` 有效，故 `s1` 给出 `Ev (Form.atom 0 [] ⊳ ¬⊥)`（后承 `Form.atom 0 [] ⊢ ¬⊥`），
`r1` 再给出 `Ev (Form.atom 0 [] ⊲ Form.bot)`——标签 `7`。
由它分别用 `f1`（⇒ `⊲ ∀x ⊥`，标签 `3`）、`f4`（⇒ `⊲ (⊥ ∧ ⊥)`，标签 `6`）
得到另外两个原子反驳者；`e` 用**洞上下文**（恒等替换）直接给出标签 `0` 的见证，
另有一个**非退化**版本 `refut_e_witness_gen`：以 `f4` 见证为前提、用 `Ctx.refutR`
把真子公式 `⊥ ∧ ⊥` 按 `⊥ ∧ ⊥ ⊣⊢ ⊥` 换成 `⊥`。 -/

/-- 任何原子支持者都推出 `¬⊥`（后承 `Form.atom i ts ⊢ ¬⊥`）：
`⊥` 的真值是 `⊥`，其补是 `⊤`，故左边恒 `≤`。 -/
theorem entails_atom_not_bot (i : Nat) (ts : List Form) :
    Entails (Form.atom i ts) (Form.not Form.bot) :=
  fun B ρ => by
    show B.truth (Form.atom i ts) ρ ≤ B.truth (Form.not Form.bot) ρ
    rw [show B.truth (Form.not Form.bot) ρ = (⊥ : PSet B.W)ᶜ from rfl, PSet.compl_bot]
    exact PSet.le_top _

/-- 经典等价 `⊥ ∧ ⊥ ⊣⊢ ⊥`（供非退化的 `e` 见证使用）：
`⊥ ⊓ ⊥ ≤ ⊥` 是 `⊓` 的左投影，`⊥ ≤ ⊥ ⊓ ⊥` 是 `⊥` 的最小性。 -/
theorem cequiv_bot_and_bot : (Form.and Form.bot Form.bot) ⊣⊢ Form.bot :=
  ⟨fun B ρ => by
     show B.truth (Form.and Form.bot Form.bot) ρ ≤ B.truth Form.bot ρ
     exact PSet.inf_le_left _ _,
   fun B ρ => by
     show B.truth Form.bot ρ ≤ B.truth (Form.and Form.bot Form.bot) ρ
     exact PSet.bot_le _⟩

namespace Ev

/-- **`r1` 见证**：`Ev (Form.atom 0 [] ⊲ Form.bot)`，由 `s1`（`⊢ ¬⊥`）经 `r1` 得到。 -/def refut_r1_witness : Ev (Form.atom 0 [] ⊲ Form.bot) :=
  Ev.r1 (t := Form.atom 0 []) (φ := Form.bot)
    (Ev.s1 (p := Form.atom 0 []) (q := Form.not Form.bot) (entails_atom_not_bot 0 []))

/-- `r1` 见证的标签是 `7`。 -/
theorem refut_r1_witness_tag : ruleTag refut_r1_witness = 7 := rfl

/-- **`f1` 见证**：`Ev (Form.atom 0 [] ⊲ Form.all 0 Form.bot)`——`f1` 只改被反驳式，
支持者仍是 `Form.atom 0 []`，故原子反驳者可以以 `f1` 收尾。 -/
def refut_f1_witness : Ev (Form.atom 0 [] ⊲ Form.all 0 Form.bot) :=
  Ev.f1 (k := Kind.refut) (t := Form.atom 0 []) (φ := Form.bot) (x := 0)
    (by simp [FreeIn])
    (show Ev (Kind.refut.form (Form.atom 0 []) Form.bot) from refut_r1_witness)

/-- `f1` 见证的标签是 `3`。 -/
theorem refut_f1_witness_tag : ruleTag refut_f1_witness = 3 := rfl

/-- **`f4` 见证**：`Ev (Form.atom 0 [] ⊲ Form.and Form.bot Form.bot)`——`f4` 只改被反驳式，
支持者仍是 `Form.atom 0 []`。 -/
def refut_f4_witness : Ev (Form.atom 0 [] ⊲ Form.and Form.bot Form.bot) :=
  Ev.f4 (k := Kind.refut) (t := Form.atom 0 []) (φ := Form.bot) (ψ := Form.bot)
    (show Ev (Kind.refut.form (Form.atom 0 []) Form.bot) from refut_r1_witness)
    (show Ev (Kind.refut.form (Form.atom 0 []) Form.bot) from refut_r1_witness)

/-- `f4` 见证的标签是 `6`。 -/
theorem refut_f4_witness_tag : ruleTag refut_f4_witness = 6 := rfl

/-- **`e` 见证**：`Ev (Form.atom 0 [] ⊲ Form.bot)`，用**洞上下文**（把公式替换成它自己）
即元规则 `e` 的退化用法；`e` 是顶层重写，结论任意，故它确实可达。 -/
def refut_e_witness : Ev (Form.atom 0 [] ⊲ Form.bot) :=
  Ev.e (φ := (Form.atom 0 [] ⊲ Form.bot)) (ψ := (Form.atom 0 [] ⊲ Form.bot))
    (γ := (Form.atom 0 [] ⊲ Form.bot)) (δ := (Form.atom 0 [] ⊲ Form.bot))
    ⟨Ctx.hole, rfl, rfl⟩
    (cequiv_refl (Form.atom 0 [] ⊲ Form.bot))
    refut_r1_witness

/-- `e` 见证的标签是 `0`。 -/
theorem refut_e_witness_tag : ruleTag refut_e_witness = 0 := rfl

/-- **`e` 见证（非退化版）**：用 `Ctx.refutR` 把**真子公式** `⊥ ∧ ⊥` 换成 `⊥`
（经典等价 `⊥ ∧ ⊥ ⊣⊢ ⊥`，前提证据是 `f4` 见证），得到 `Ev (Form.atom 0 [] ⊲ Form.bot)`。
这说明 `e` 的槽位不靠"洞上下文恒等替换"也能满足。 -/
def refut_e_witness_gen : Ev (Form.atom 0 [] ⊲ Form.bot) :=
  Ev.e (φ := Form.and Form.bot Form.bot) (ψ := Form.bot)
    (γ := (Form.atom 0 [] ⊲ Form.and Form.bot Form.bot)) (δ := (Form.atom 0 [] ⊲ Form.bot))
    ⟨Ctx.refutR (Form.atom 0 []) Ctx.hole, rfl, rfl⟩
    cequiv_bot_and_bot
    refut_f4_witness

/-- 非退化 `e` 见证的标签同样是 `0`。 -/
theorem refut_e_witness_gen_tag : ruleTag refut_e_witness_gen = 0 := rfl

/-- **紧性（汇总）**：四个槽位 `0`（`e`）、`7`（`r1`）、`3`（`f1`）、`6`（`f4`）
各有一个原子反驳者见证，且四个标签两两不同——故 `atom_refut_root_restricted`
的四个析取项**一个也不能删**。 -/
theorem atom_refut_root_slots_all_realized :
    ruleTag refut_e_witness = 0 ∧ ruleTag refut_r1_witness = 7 ∧
      ruleTag refut_f1_witness = 3 ∧ ruleTag refut_f4_witness = 6 ∧
      (0 ≠ 7 ∧ 0 ≠ 3 ∧ 0 ≠ 6 ∧ 7 ≠ 3 ∧ 7 ≠ 6 ∧ 3 ≠ 6) :=
  ⟨refut_e_witness_tag, refut_r1_witness_tag, refut_f1_witness_tag, refut_f4_witness_tag,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

/-- `r1` 见证**不是** `e` 根：`0` 这一支不能由它满足。 -/
theorem refut_r1_witness_ne_e : ruleTag refut_r1_witness ≠ 0 := by
  rw [refut_r1_witness_tag]
  decide

/-- `f1` 见证**不是** `r1` 根。 -/
theorem refut_f1_witness_ne_r1 : ruleTag refut_f1_witness ≠ 7 := by
  rw [refut_f1_witness_tag]
  decide

/-- `f4` 见证**不是** `f1` 根。 -/
theorem refut_f4_witness_ne_f1 : ruleTag refut_f4_witness ≠ 3 := by
  rw [refut_f4_witness_tag]
  decide

/-- `e` 见证**不是** `f4` 根。 -/
theorem refut_e_witness_ne_f4 : ruleTag refut_e_witness ≠ 6 := by
  rw [refut_e_witness_tag]
  decide

end Ev

end EvidenceLogic
