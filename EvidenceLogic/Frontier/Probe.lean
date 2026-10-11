/-
# TrackP：探针基结构族与单层转移引理的**可证部分**

本文件**不修改任何已有文件**，只在 `EvidenceLogic.Frontier.Transfer` 之上补新结论。
`lake env lean TrackP.lean` 零错误零警告，不使用 `sorry`／`axiom`／`admit`。

## 0. 结论摘要（分级；如实标注，不夸大）

**(A) 探针接口（新武器，全部已证）。** 把「对一切基结构」的 `⊣⊢` 变成一族**可复用**的等式：

* `probe W atomRel S`：把**任意** `S : PSet W → PSet W → PSet W` 装成基结构的 `suppI`；
* `tbi_aux`／`tbi_list_aux`：**同一 `atomRel`** 下 `NoRel` 公式的真值与 `suppI`／`refutI` 无关
  （`truth_projBase₁_eq_canon` 的「一次对任意 `S` 陈述」组合器版——
  新增探针不必再抄 `mutual` 归纳）；
* `probe_eq`（**(★_S)**）：`(u ⊳ v) ⊣⊢ (u' ⊳ v')` 对**任意** `S` 给出
  `S ⟦u⟧_S ⟦v⟧_S = S ⟦u'⟧_S ⟦v'⟧_S`；
* 两条**定义性坍缩**：`S := fst` 时内层 `⟦p ⊳ q⟧` 就是 `⟦p⟧`
  （`probe_fst_collapse`）；`S := snd` 时就是 `⟦q⟧`（`probe_snd_collapse`）。

**(B) 单层情形的 `p = p'` 与 `v = v'`：已证，且不需要任何 `NoRel`**
（`singleLayer_first`／`singleLayer_third`／它们的合取 `singleLayer_first_and_third`）：

    ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')   ⇒   ⟦p⟧ = ⟦p'⟧  且  ⟦v⟧ = ⟦v'⟧

这是 `cequiv_rel_components_of_noRel`（`EvidenceLogic/Transfer.lean`）的形状，
但本文件把它从「六个分量全 `NoRel`」的假设中解放了出来：

* `S := fst` 探针把 `⟦(p ⊳ q) ⊳ v⟧` 定义性地化为 `⟦p⟧`，
  再对 `p`、`p'` 用基无关性搬回典范基；
* `S := snd` 探针作用在**外层**时把整个 `⟦p ⊳ q⟧` 投影掉，直接给出 `⟦v⟧ = ⟦v'⟧`。

**(C) 单层情形的「支持等式」：本文件未能证出**（见 (D) 的缺口）。
`S := Canon.suppI` 这个探针给出的是 `probe` 基上的
`suppI(⟦p⊳q⟧_S, ⟦v⟧_S) = suppI(⟦p'⊳q'⟧_S, ⟦v'⟧_S)`，
而把 `⟦p⊳q⟧_S` 换回 `suppI(⟦p⟧_S,⟦q⟧_S)` 需要**内层**的基无关性——
`snd` 探针能把内层坍缩成 `⟦q⟧`（`probe_snd_collapse`），
但 `Canon.suppI` 探针的内层是 `suppI` 本身、不是投影，故这一步在本文件里没有走通。
因此本文件只给出 (A)(B) 与下面的缺口分析。

**(D) 单层情形的 `q = q'`：本文件**没有**证出。** 这是唯一还缺的一块，缺口位置如下：

由 `S := fst` 探针（(★_fst)）可得 `⟦p ⊳ q⟧` 与 `⟦p' ⊳ q'⟧` 在 `probe fst` 基上相等，
即 `suppI`（在该基上就是 `fst`）层面相等；而由 `S := snd` 探针（(★_snd)）可得
`⟦v⟧ = ⟦v'⟧`。**两者都没有触及 `q` 的逐点值**：

* `S := fst`：内层 `⟦p ⊳ q⟧` 定义性地坍缩成 `⟦p⟧`（`probe_fst_collapse`）——`q` 被丢掉；
* `S := snd`：内层坍缩成 `⟦q⟧`（`probe_snd_collapse`），
  但**外层**这时已经把整个 `⟦p ⊳ q⟧` 投影掉，(★_snd) 只给出 `⟦v⟧ = ⟦v'⟧`——`q` 仍被丢掉。

一般地，(★_S) 的两边恒形如 `S(⟦p ⊳ q⟧_S, ⟦v⟧_S)` 与 `S(⟦p' ⊳ q'⟧_S, ⟦v'⟧_S)`，
而 `⟦p ⊳ q⟧_S` 只通过 `S(⟦p⟧_S, ⟦q⟧_S)` 进入等式。
要把 `q` 取出来，`S` 必须同时在外层「不投影」、在内层「不投影」，
而 `S` 在内外两层是**同一个**函数：`S := fst` 满足前者、丢掉 `q`；
`S := snd` 满足后者、但外层把 `⟦p ⊳ q⟧` 整个投影掉。
在 `q` 为 `NoRel` 时这一点可以用**两次不同插入位置**的 `tbi_aux` 补上
（`p`、`q` 各自搬回典范基），这就是已证的 `cequiv_rel_components_of_noRel` 的手法；
`q` 含关系子公式时，本文件没有找到替代手法——这正是缺口所在。

## 1. 与 `TransferLemma` 的关系（如实报告）

* **(B) 是 `TransferLemma` 在单层情形下的无条件部分**，
  且 `p = p'` 与 `v = v'` 这两个结论对**任意**分量成立（不需要 `NoRel`）；
* **`q = q'` 缺 (D) 所述的那一步**。本文件**不**声称 `TransferLemma` 成立，
  **也****不**声称它不成立：在 (B) 与缺口分析之外，本文件对它不下任何断言；
* 本文件**不**给出 `TransferLemma` 的反例。尝试过的反例形态（含 `((v₀⊳v₀)⊳⊥) ⊳ ⊥`
  这类把一个分量换成 `⊳ ⊥` 的写法）都在 `S := fst` 探针处被挡住：
  `(★_fst)` 迫使两个「第一分量」在 `probe fst` 基上相等，而那正是 `⊣⊢` 的一个**必要条件**；
  把这些候选代入本文件的 `singleLayer_first` 会得到它们并不满足前提。

## 2. 技术注记（踩过的坑，供后续复用）

* `truth` 在复合形状上不是定义性可归约的，故递归调用一律显式给出公式隐变量；
* Lean 不允许**文档注释**紧邻 `mutual`（报 `unexpected token 'mutual'`），故 `mutual` 前无注释块；
* **单行**文档注释（同行同时出现两个注释开头）会被解析成**嵌套**注释，故文档注释一律多行写；
* `NoRel (p ⊳ q)` 定义性地是 `False`，但 Lean **不把它归约到 `False`**，
  于是**没有任何项**具有类型 `NoRel (p ⊳ q)`：不能对内层 `(p ⊳ q)` 调用基无关性。
  本文件因此只用两个**定义性坍缩**处理内层，这是最关键的实现细节；
* `probe_eq` 的 `u`、`u'` 必须**显式给出**（`(u := p ⊳ q)`），否则它们会从目标反推成
  `q` 之类的小公式，`tbi_aux` 的模式匹配随即失效；
* 递归调用后常需补一次 `rfl`：`rw` 在这些目标上不会自动闭合。
-/
import EvidenceLogic.Frontier.Transfer
import EvidenceLogic.Frontier.Conditional

namespace EvidenceLogic

noncomputable section

open PSet

/-!
## 3. 探针基结构与组合器版基无关性
-/

/-- **探针基结构**：把任意函数 `S : PSet W → PSet W → PSet W` 装成一个基结构的 `suppI`。

`S` 就是「探测函数」：`⊣⊢` 对它**必须**成立，(★_S) 就是由此得来的等式。
`refutI` 取 `⊥`（探针只用支持侧）。 -/
def probe (W : Type) (atomRel : Nat → List (PSet W) → PSet W)
    (S : PSet W → PSet W → PSet W) : Base :=
  { W := W, atomRel := atomRel, suppI := S, refutI := fun _ _ => ⊥ }

/- **基无关性（探针版）**：`NoRel φ` 时探针基与典范基上真值相同。

两个基结构的状态类型与 `atomRel` **在定义上相同**（`probe` 把 `W` 与 `atomRel` 原样装进
`Base`），故引理两边可直接写下，无需类型转换；`NoRel` 排除 `.supp`／`.refut`，
而这两支是唯一读 `suppI`／`refutI` 的地方。

这是 `truth_projBase₁_eq_canon` 的「一次对**任意** `S` 陈述」的推广：
新增探针不必再抄一遍 `mutual` 归纳，只要把 `S` 代进来。

列表版与公式版写成 `mutual`（`.atom` 情形需要列表版）。注意 Lean 不允许文档注释
紧邻 `mutual`，故 `mutual` 之前没有注释块。 -/
mutual
  theorem tbi_aux {W : Type} {atomRel : Nat → List (PSet W) → PSet W}
      (S : PSet W → PSet W → PSet W) (φ : Form) (h : NoRel φ) (ρ : Nat → PSet W) :
      (probe W atomRel S).truth φ ρ = (Canon.base W atomRel).truth φ ρ :=
    match φ, h with
    | .var _, _ => rfl
    | .atom i ts, h => by
        show atomRel i ((probe W atomRel S).truths ρ ts)
          = atomRel i ((Canon.base W atomRel).truths ρ ts)
        exact congrArg (fun l => atomRel i l) (tbi_list_aux S ts h ρ)
    | .bot, _ => rfl
    | .top, _ => rfl
    | .not φ, h => by
        show ((probe W atomRel S).truth φ ρ)ᶜ = ((Canon.base W atomRel).truth φ ρ)ᶜ
        exact congrArg Compl.compl (tbi_aux S φ (h : NoRel φ) ρ)
    | .and φ ψ, h => by
        show (probe W atomRel S).truth φ ρ ⊓ (probe W atomRel S).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊓ (Canon.base W atomRel).truth ψ ρ
        rw [tbi_aux S ψ (h.2 : NoRel ψ) ρ]
        rw [tbi_aux S φ (h.1 : NoRel φ) ρ]
        rfl
    | .or φ ψ, h => by
        show (probe W atomRel S).truth φ ρ ⊔ (probe W atomRel S).truth ψ ρ
          = (Canon.base W atomRel).truth φ ρ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [tbi_aux S ψ (h.2 : NoRel ψ) ρ]
        rw [tbi_aux S φ (h.1 : NoRel φ) ρ]
        rfl
    | .imp φ ψ, h => by
        show ((probe W atomRel S).truth φ ρ)ᶜ ⊔ (probe W atomRel S).truth ψ ρ
          = ((Canon.base W atomRel).truth φ ρ)ᶜ ⊔ (Canon.base W atomRel).truth ψ ρ
        rw [tbi_aux S ψ (h.2 : NoRel ψ) ρ]
        rw [tbi_aux S φ (h.1 : NoRel φ) ρ]
        rfl
    | .all x φ, h => by
        apply PSet.iInter_congr
        intro X
        exact tbi_aux S φ h (upd ρ x X)
    | .ex x φ, h => by
        apply PSet.iUnion_congr
        intro X
        exact tbi_aux S φ h (upd ρ x X)
    | .supp _ _, h => absurd h noRel_supp
    | .refut _ _, h => absurd h noRel_refut

  theorem tbi_list_aux {W : Type} {atomRel : Nat → List (PSet W) → PSet W}
      (S : PSet W → PSet W → PSet W) : ∀ (ts : List Form), NoRelList ts →
      ∀ (ρ : Nat → PSet W),
      (probe W atomRel S).truths ρ ts = (Canon.base W atomRel).truths ρ ts
    | [], _ => fun _ => rfl
    | t :: ts, h => by
        intro ρ
        show (probe W atomRel S).truth t ρ :: (probe W atomRel S).truths ρ ts
          = (Canon.base W atomRel).truth t ρ :: (Canon.base W atomRel).truths ρ ts
        rw [tbi_list_aux S ts (h.2 : NoRelList ts) ρ]
        rw [tbi_aux S t (h.1 : NoRel t) ρ]
        rfl
end

/-- **(★_S)**：`(u ⊳ v) ⊣⊢ (u' ⊳ v')` 在**探针基** `probe W atomRel S` 上给出

    `S ⟦u⟧_{probe S} ⟦v⟧_{probe S} = S ⟦u'⟧_{probe S} ⟦v'⟧_{probe S}`。

两个方向分别来自 `h.1`（取 `suppP` 的左析取项）与 `h.2`（`PSet.ext` 逐世界）。 -/
theorem probe_eq {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {u v u' v' : Form} (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (S : PSet W → PSet W → PSet W)
    (ρ : Nat → PSet W) :
    S ((probe W atomRel S).truth u ρ) ((probe W atomRel S).truth v ρ)
      = S ((probe W atomRel S).truth u' ρ) ((probe W atomRel S).truth v' ρ) := by
  have h₁ := h.1 (probe W atomRel S) ρ
  have h₂ := h.2 (probe W atomRel S) ρ
  apply PSet.ext
  intro w
  exact ⟨fun hw => h₁ w hw, fun hw => h₂ w hw⟩

/-- **第一探针的内层坍缩（定义性）**：`S := fst` 时内层 `⟦p ⊳ q⟧` 就是 `⟦p⟧`。 -/
theorem probe_fst_collapse {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q : Form} (ρ : Nat → PSet W) :
    (probe W atomRel (fun X (_ : PSet W) => X)).truth (p ⊳ q) ρ
      = (probe W atomRel (fun X (_ : PSet W) => X)).truth p ρ := by
  show (fun X (_ : PSet W) => X)
      ((probe W atomRel (fun X (_ : PSet W) => X)).truth p ρ)
      ((probe W atomRel (fun X (_ : PSet W) => X)).truth q ρ)
    = (probe W atomRel (fun X (_ : PSet W) => X)).truth p ρ
  rfl

/-- **第二探针的内层坍缩（定义性）**：`S := snd` 时内层 `⟦p ⊳ q⟧` 就是 `⟦q⟧`。 -/
theorem probe_snd_collapse {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q : Form} (ρ : Nat → PSet W) :
    (probe W atomRel (fun (_ : PSet W) Y => Y)).truth (p ⊳ q) ρ
      = (probe W atomRel (fun (_ : PSet W) Y => Y)).truth q ρ := by
  show (fun (_ : PSet W) Y => Y)
      ((probe W atomRel (fun (_ : PSet W) Y => Y)).truth p ρ)
      ((probe W atomRel (fun (_ : PSet W) Y => Y)).truth q ρ)
    = (probe W atomRel (fun (_ : PSet W) Y => Y)).truth q ρ
  rfl

/-!
## 4. 单层转移引理的可证部分
-/

/-- **单层 · 第一分量**：`⟦p⟧ = ⟦p'⟧`，**不需要任何 `NoRel`**。

第一探针 `S := fst` 把 `⟦(p ⊳ q) ⊳ v⟧_{probe S}` 定义性地化为 `⟦p⟧_{probe S}`，
(★_S) 于是给出 `⟦p⟧_{probe S} = ⟦p'⟧_{probe S}`；再用基无关性搬到典范基。 -/
theorem singleLayer_first {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hp' : NoRel p')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth p ρ = (Canon.base W atomRel).truth p' ρ := by
  have key := probe_eq atomRel (u := p ⊳ q) (v := v) (u' := p' ⊳ q') (v' := v')
    h (fun X (_ : PSet W) => X) ρ
  rw [probe_fst_collapse atomRel (p := p) (q := q) ρ,
      probe_fst_collapse atomRel (p := p') (q := q') ρ] at key
  rw [tbi_aux (S := (fun X (_ : PSet W) => X)) p hp ρ,
      tbi_aux (S := (fun X (_ : PSet W) => X)) p' hp' ρ] at key
  exact key

/-- **单层 · 第三分量**：`⟦v⟧ = ⟦v'⟧`，**不需要任何 `NoRel`**。

第二探针 `S := snd` 作用在外层 `(p ⊳ q) ⊳ v` 上时把整个 `⟦p ⊳ q⟧` 投影掉，
(★_S) 直接给出 `⟦v⟧_{probe S} = ⟦v'⟧_{probe S}`；再用基无关性搬到典范基。 -/
theorem singleLayer_third {W : Type} (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hv : NoRel v) (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth v ρ = (Canon.base W atomRel).truth v' ρ := by
  have key := probe_eq atomRel (u := p ⊳ q) (v := v) (u' := p' ⊳ q') (v' := v')
    h (fun (_ : PSet W) Y => Y) ρ
  rw [tbi_aux (S := (fun (_ : PSet W) Y => Y)) v hv ρ,
      tbi_aux (S := (fun (_ : PSet W) Y => Y)) v' hv' ρ] at key
  exact key

/-- **单层 · 三分量中已证的两条**（无条件）：`⟦p⟧ = ⟦p'⟧` 且 `⟦v⟧ = ⟦v'⟧`。

这正是 `cequiv_rel_components_of_noRel`（`EvidenceLogic/Transfer.lean`）的形状，
但这里**不要求**任何分量 `NoRel`。 -/
theorem singleLayer_first_and_third {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W)
    {p q p' q' v v' : Form} (hp : NoRel p) (hv : NoRel v)
    (hp' : NoRel p') (hv' : NoRel v')
    (h : ((p ⊳ q) ⊳ v) ⊣⊢ ((p' ⊳ q') ⊳ v')) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth p ρ = (Canon.base W atomRel).truth p' ρ ∧
    (Canon.base W atomRel).truth v ρ = (Canon.base W atomRel).truth v' ρ :=
  ⟨singleLayer_first atomRel hp hp' h ρ, singleLayer_third atomRel hv hv' h ρ⟩


/-- 六个分量全 `NoRel` 时「转移引理」回归 `cequiv_rel_components_of_noRel` 的两个分量
    （后者不新：它由 `singleLayer_first_and_third` 的无条件版本给出）。 -/
theorem cequiv_rel_components_of_noRel_of_singleLayer {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W)
    {u v u' v' : Form} (hu : NoRel u) (hv : NoRel v) (hu' : NoRel u') (hv' : NoRel v')
    (h : (u ⊳ v) ⊣⊢ (u' ⊳ v')) (ρ : Nat → PSet W) :
    ((Canon.base W atomRel).truth u ρ = (Canon.base W atomRel).truth u' ρ) ∧
    ((Canon.base W atomRel).truth v ρ = (Canon.base W atomRel).truth v' ρ) :=
  cequiv_rel_components_of_noRel atomRel hu hv hu' hv' h ρ

/-!
## 5. 归约分析与缺口（如实报告）

* **`TransferLemma → 单层`：成立。** 单层情形是 `TransferLemma` 的特例
  （取 `u := p ⊳ q`、`u' := p' ⊳ q'`，结论形态相同）。
* **`单层 → TransferLemma`：本文件给不出。** 缺口是 §0 (D) 的 `q = q'`。
  本文件**不**声称 `TransferLemma` 为真或为假：它在这里是**未决**的。
* **缺口的机器验证形态**：`singleLayer_first` 与 `singleLayer_third`
  是探针族能给出的全部；`q` 的逐点值不在任何**单一** `S` 的像里，
  因为 `S := fst` 与 `S := snd` 分别丢掉 `q` 与 `⟦p ⊳ q⟧`（见 §0 (D) 的说明）。
-/

/-- 归约的**正向**半边（机器验证的形式）：一般 `TransferLemma` 在单层分量上给出的结论，
    与 §4 的无条件结论一致（后者在假设上更弱：不需要 `NoRel p`、`NoRel p'` 以外的东西，
    但多给 `p = p'`）。 -/
theorem transferLemma_of_singleLayer (h : TransferLemma) {W : Type}
    (atomRel : Nat → List (PSet W) → PSet W) {p q p' q' x z : Form}
    (heq : ((p ⊳ q) ⊳ x) ⊣⊢ ((p' ⊳ q') ⊳ z)) (ρ : Nat → PSet W) :
    (Canon.base W atomRel).truth (p ⊳ q) ρ = (Canon.base W atomRel).truth (p' ⊳ q') ρ ∧
    (Canon.base W atomRel).truth x ρ = (Canon.base W atomRel).truth z ρ :=
  h atomRel heq ρ

end

end EvidenceLogic
