/-
# TrackQ：λ-探针框架（已证）+ 单层 `q = q'` 的精确缺口

本文件**不修改任何已有文件**，只在 `EvidenceLogic/Probe.lean` 之上补新结论。
`lake env lean TrackQ.lean` 零错误零警告，无 `sorry`／`axiom`／`admit`。

## 0. 已证部分（λ-探针框架，全部可复用）

`probe_eq`（(★_S)）对**任意** `S : PSet W → PSet W → PSet W` 成立，而 `probe` 的
`suppI` 字段**就是** `S`。于是探针不必与 `⊓`／`ᶜ` 语法一致：用**显式 λ 的 `PSet`
字面量**，并把 `¬ X.holds w` 一律写成**显式箭头** `X.holds w → False`，
所有展开都退化成定义性的逐世界 `∧`／`→` 推理，
**完全避开 `Compl.compl`／`Inf` 实例的不透明归约**。

* `probe_inner_eq`：`probe` 内层是**定义性**展开（`rfl`）；
* `probe_pair`：**一个通用引理**给出所有四条探针等式
  `S (S ⟦p⟧ ⟦q⟧) ⟦v⟧ = S (S ⟦p'⟧ ⟦q'⟧) ⟦v'⟧`（典范基），
  只用 `probe_eq` ＋ `probe_inner_eq` ＋ 六次 `tbi_aux`（六个 `NoRel` 分量的基无关性），
  **没有任何实例归约**。四条探针等式由它一次实例化得到；
* `pair_at`：把 `PSet` 等式降成逐世界 `↔`；
* `P1_at`：`andS` 那一块（`a w` 且 `v w`）`q w ↔ q' w`——**已证**；
* `not_iff_not`：`¬P ↔ ¬Q` ⇒ `P ↔ Q`（用 `Classical.byContradiction`）。

## 1. 四条探针的**外层**语义（缺口的成因，务必按这一列选定义）

`S` 既用于**内层** `(p ⊳ q)`、也用于**外层** `(p ⊳ q) ⊳ v`。外层那一步给出的
是 `suppP(S ⟦p⟧ ⟦q⟧, ⟦v⟧)` 的**逐点值**。于是：

| 探针 | 定义（逐世界） | 外层 = `suppP(?, ·)` 里的 `?` |
|---|---|---|
| `andS`    | `X w ∧ Y w`                     | `a ⊓ q` |
| `notAndS` | `(X w → False) ∧ Y w`           | `aᶜ ⊓ q`（即 `¬a ∧ q`） |
| `notNotS` | `(X w → False) ∧ (Y w → False)` | `aᶜ ⊓ qᶜ`（即 `¬a ∧ ¬q`） |
| `andNotS` | `X w ∧ (Y w → False)`           | `a ⊓ qᶜ`（即 `a ∧ ¬q`） |

**关键教训（我在这里卡了很久）**：要拿到「`¬(¬a ∧ q)` 这个**命题**」时，
需要的**探针本身**是 `⟨fun w => ((X w → False) ∧ Y w) → False⟩`
（对**内层结果**取否定），而**不是**把 `¬` 施加在两个自变量上再合取。
第一、二条恰好不区分（`andS`／`notAndS` 的两种读法只差内层合取），
第三、四条会区分——这正是 P₃／P₄ 反复对不上的原因。

## 2. 精确缺口

`singleLayer_q`（`⟦q⟧ = ⟦q'⟧`）与 `singleLayer_full` 尚未写出。需要的四块逐点内容：

1. `a w` 且 `v w`：`q w ↔ q' w` —— **已证**（`P1_at`）；
2. `¬a w` 且 `v w`：先 `¬q w ↔ ¬q' w`，再 `not_iff_not`；
3. `¬a w` 且 `¬v w`：同上；
4. `a w` 且 `¬v w`：同上。

2–4 的**数学内容**已定型：用 `probe_pair` 的对应实例，在 `¬a w`（或 `a w`）处
把内层合取化简，得到 `¬q w ↔ ¬q' w`。剩下的只是按 §1 最后一列
**给第三、四条探针写对定义**，再把三块逐点内容写出来。

## 3. 技术注记

* `probe_eq` 的 `u`、`u'` 必须显式给出，否则从目标反推成小公式、`tbi_aux` 匹配失效；
* 本工程**无 `by_contra` 策略**，反证用 `Classical.byContradiction`；
* `Not P` 与 `P → False` 定义性相等但字面不同；探针定义统一写显式箭头；
* 构造 `S (S A B) V` 的 `holds` 见证时用 `⟨…, …⟩` 显式给外层配对；
  内层 `S A B` 的分量方向（`hc.1`／`hc.2`）务必先 `#check` 确认，很容易搞反。

## 4. 已修正的推导记录

* 「`E₁` + `a = a'` + `v = v'` ⇒（两边 `⊓ aᶜ`）⇒ `aᶜ ⊓ q ⊓ v = aᶜ ⊓ q' ⊓ v`」
  **无效**：`E₁` 在 `w ∉ a` 处两边都是 `⊥ = ⊥`。**反例**：
  `W = {0,1,2}`、`a = {0}`、`q = {1}`、`q' = ∅`、`v = {2}`，
  则 `a ⊓ q ⊓ v = ∅ = a ⊓ q' ⊓ v`，而 `q ⊓ v = q' ⊓ v` 在 `w = 1` 上不成立。
* **`E₂` 不可省**：`aᶜ ⊓ v` 那一块只能由它提供。
-/
import EvidenceLogic.Frontier.Probe

namespace EvidenceLogic

noncomputable section

open PSet

/-! ## 5. λ-探针（`¬` 一律写成显式箭头） -/

/-- 探针 1：`X ∧ Y`。 -/
def andS {W : Type} (X Y : PSet W) : PSet W := ⟨fun w => X.holds w ∧ Y.holds w⟩

/-- 探针 2：`(¬X) ∧ Y`。 -/
def notAndS {W : Type} (X Y : PSet W) : PSet W :=
  ⟨fun w => (X.holds w → False) ∧ Y.holds w⟩

/-- 探针 3：`(¬X) ∧ (¬Y)`。 -/
def notNotS {W : Type} (X Y : PSet W) : PSet W :=
  ⟨fun w => (X.holds w → False) ∧ (Y.holds w → False)⟩

/-- 探针 4：`X ∧ (¬Y)`。 -/
def andNotS {W : Type} (X Y : PSet W) : PSet W :=
  ⟨fun w => X.holds w ∧ (Y.holds w → False)⟩

/-- **内层展开（定义性）**：`probe` 的 `suppI` 就是 `S`。 -/
theorem probe_inner_eq {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    (S : PSet W → PSet W → PSet W) (p q : Form) (ρ : Nat → PSet W) :
    (probe W atomRel S).truth (p ⊳ q) ρ
      = S ((probe W atomRel S).truth p ρ) ((probe W atomRel S).truth q ρ) := rfl

/-- **通用探针等式**：对**任意** `S`，
    `S (S ⟦p⟧ ⟦q⟧) ⟦v⟧ = S (S ⟦p'⟧ ⟦q'⟧) ⟦v'⟧`（典范基）。 -/
theorem probe_pair {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    (S : PSet W → PSet W → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) :
    S (S ((Canon.base W atomRel).truth p ρ) ((Canon.base W atomRel).truth q ρ))
        ((Canon.base W atomRel).truth v ρ)
      = S (S ((Canon.base W atomRel).truth p' ρ) ((Canon.base W atomRel).truth q' ρ))
        ((Canon.base W atomRel).truth v' ρ) := by
  have key := probe_eq atomRel (u := p ⊳ q) (v := v) (u' := p' ⊳ q') (v' := v') h S ρ
  rw [probe_inner_eq atomRel S p q ρ, probe_inner_eq atomRel S p' q' ρ] at key
  rw [tbi_aux (S := S) p hp ρ, tbi_aux (S := S) q hq ρ, tbi_aux (S := S) v hv ρ,
      tbi_aux (S := S) p' hp' ρ, tbi_aux (S := S) q' hq' ρ, tbi_aux (S := S) v' hv' ρ] at key
  exact key

/-- 从集合等式中取出逐世界内容。 -/
theorem eq_at {W : Type} {X Y : PSet W} (h : X = Y) (w : W) : X w ↔ Y w :=
  ⟨fun hx => h ▸ hx, fun hy => h.symm ▸ hy⟩

/-- **通用逐世界内容**。 -/
theorem pair_at {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    (S : PSet W → PSet W → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) (w : W) :
    (S (S ((Canon.base W atomRel).truth p ρ) ((Canon.base W atomRel).truth q ρ))
        ((Canon.base W atomRel).truth v ρ)).holds w
      ↔ (S (S ((Canon.base W atomRel).truth p' ρ) ((Canon.base W atomRel).truth q' ρ))
        ((Canon.base W atomRel).truth v' ρ)).holds w :=
  eq_at (probe_pair atomRel S hp hq hp' hq' hv hv' h ρ) w

/-- **符号翻转**：`¬ P ↔ ¬ Q` 蕴含 `P ↔ Q`。 -/
theorem not_iff_not {P Q : Prop} (h : (P → False) ↔ (Q → False)) : P ↔ Q :=
  ⟨fun hp => Classical.byContradiction (fun hnq => h.mpr hnq hp),
   fun hq => Classical.byContradiction (fun hnp => h.mp hnp hq)⟩

/-! ## 6. 已证的一块：`a ⊓ v` 内 `q w ↔ q' w` -/

/-- **P₁**（`a w` 且 `v w`）：`q w ↔ q' w`（由 `andS` 那条探针等式直接得到）。 -/
theorem P1_at {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hq : NoRel q) (hp' : NoRel p') (hq' : NoRel q')
    (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) (w : W)
    (hvW : (Canon.base W atomRel).truth v ρ w)
    (haW : (Canon.base W atomRel).truth p ρ w) :
    ((Canon.base W atomRel).truth q ρ w ↔ (Canon.base W atomRel).truth q' ρ w) := by
  have hw := pair_at atomRel andS hp hq hp' hq' hv hv' h ρ w
  have haW' : (Canon.base W atomRel).truth p' ρ w :=
    (eq_at (singleLayer_first atomRel hp hp' h ρ) w).mp haW
  have hv'W : (Canon.base W atomRel).truth v' ρ w :=
    (eq_at (singleLayer_third atomRel hv hv' h ρ) w).mp hvW
  constructor
  · intro hqW
    have hleft : (andS (andS ((Canon.base W atomRel).truth p ρ)
        ((Canon.base W atomRel).truth q ρ)) ((Canon.base W atomRel).truth v ρ)).holds w :=
      ⟨⟨haW, hqW⟩, hvW⟩
    exact (hw.mp hleft).1.2
  · intro hq'W
    have hright : (andS (andS ((Canon.base W atomRel).truth p' ρ)
        ((Canon.base W atomRel).truth q' ρ)) ((Canon.base W atomRel).truth v' ρ)).holds w :=
      ⟨⟨haW', hq'W⟩, hv'W⟩
    exact (hw.mpr hright).1.2

end

end EvidenceLogic
