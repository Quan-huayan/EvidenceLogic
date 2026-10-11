/-
# 背书逻辑 v1.0：语言（Syntax）

本文件形式化「背书逻辑 v1.0 定稿」第一节（语言）所规定的对象语言。

## 设计要点：公式即项（单排序语法）

定稿规定 `t ⊳ φ` 与 `c ⊲ φ` 中的 `t`, `c` 是**项**，而「公式可编码为项」。
因此支持者既可以是原子项，也可以是复合公式（如 `a ∧ b`、`∀x p(x)`、
乃至嵌套的 `c ⊲ d`）。最忠实的做法是采用**单排序语法**：只有一个语法范畴
`Form`，公式直接充当项。于是：

* `a ∧ b`（F3／P1 中的合取支持者）就是 `Form.and a b`；
* `∀x p`（F2／P2 中的全称支持者）就是 `Form.all x p`；
* `c ⊲ d`（嵌套关系）就是 `Form.refut c d`。

这正好实现了定稿「公式可编码为项」的要求，并让 F1–F4、P1、P2 的
「同一主体」「全称主体」「合取主体」等表述无需额外的编码／解码函数。

## 自由变量、代入与替换

* `FreeIn x φ`：`x` 在 `φ` 中自由出现（F1/F2/P2 的副作用条件 `x ∉ FV(t)`）。
* `Form.subst`：**避免捕获**的代入（在量词下把被约束变量从代入中移除）。
* `FreeFor t x φ`：`t` 对 `x` 在 `φ` 中可代入（标准的自由代入条件）。
* `Replace φ ψ γ δ`：单项上下文替换关系，供元规则 **E** 使用。

## 注

为使形式化自足，此处不依赖 Mathlib：全部定义只用 Lean 4 核心与 `Std`。
-/
import Std

namespace EvidenceLogic

/-- 对象语言公式。单排序：公式同时充当项（定稿「公式可编码为项」）。 -/
inductive Form where
  /-- 变元（也是项） -/
  | var : Nat → Form
  /-- 原子谓词 `P(t₁, …, tₙ)` -/
  | atom : Nat → List Form → Form
  /-- 假 -/
  | bot : Form
  /-- 真 -/
  | top : Form
  /-- 否定 -/
  | not : Form → Form
  /-- 合取 -/
  | and : Form → Form → Form
  /-- 析取 -/
  | or : Form → Form → Form
  /-- 蕴涵 -/
  | imp : Form → Form → Form
  /-- 全称量化 -/
  | all : Nat → Form → Form
  /-- 存在量化 -/
  | ex : Nat → Form → Form
  /-- 支持：`t ⊳ φ` -/
  | supp : Form → Form → Form
  /-- 反驳：`c ⊲ φ` -/
  | refut : Form → Form → Form
  deriving Repr, Inhabited

/-- 支持算子 `⊳`（二元，独立原语）。 -/
infix:24 " ⊳ " => Form.supp
/-- 反驳算子 `⊲`（二元，独立原语，不通过 `⊳` 定义）。 -/
infix:24 " ⊲ " => Form.refut

/-- 二元关系的种类：`R ∈ {⊳, ⊲}`（定稿第四、六节的「设 `R, S ∈ {⊳, ⊲}`」）。 -/
inductive Kind where
  /-- 支持 `⊳` -/
  | supp
  /-- 反驳 `⊲` -/
  | refut
  deriving DecidableEq, Repr

namespace Kind

/-- 由种类与两个公式构造关系公式。 -/
def form : Kind → Form → Form → Form
  | .supp, a, b => a ⊳ b
  | .refut, a, b => a ⊲ b

/-- 种类对应的关系构造子（在语义中使用）。 -/
def relForm (k : Kind) (a b : Form) : Form := form k a b

@[simp] theorem form_supp (a b : Form) : form .supp a b = (a ⊳ b) := rfl
@[simp] theorem form_refut (a b : Form) : form .refut a b = (a ⊲ b) := rfl

end Kind

/-! ## 自由变量 -/

/- `FreeIn x φ`：变元 `x` 在 `φ` 中**自由**出现（`x ∈ FV(φ)`）。 -/
mutual
  def FreeIn (x : Nat) : Form → Prop
    | .var y => x = y
    | .atom _ ts => FreeInList x ts
    | .bot => False
    | .top => False
    | .not φ => FreeIn x φ
    | .and φ ψ => FreeIn x φ ∨ FreeIn x ψ
    | .or φ ψ => FreeIn x φ ∨ FreeIn x ψ
    | .imp φ ψ => FreeIn x φ ∨ FreeIn x ψ
    | .all y φ => x ≠ y ∧ FreeIn x φ
    | .ex y φ => x ≠ y ∧ FreeIn x φ
    | .supp t φ => FreeIn x t ∨ FreeIn x φ
    | .refut t φ => FreeIn x t ∨ FreeIn x φ

  /-- 列表版自由出现。 -/
  def FreeInList (x : Nat) : List Form → Prop
    | [] => False
    | t :: ts => FreeIn x t ∨ FreeInList x ts
end

@[simp] theorem freeIn_var {x y : Nat} : FreeIn x (.var y) ↔ x = y := Iff.rfl
@[simp] theorem freeIn_bot {x : Nat} : ¬ FreeIn x (.bot) := id
@[simp] theorem freeIn_top {x : Nat} : ¬ FreeIn x (.top) := id
@[simp] theorem freeIn_not {x : Nat} {φ : Form} : FreeIn x (.not φ) ↔ FreeIn x φ := Iff.rfl
@[simp] theorem freeIn_and {x : Nat} {φ ψ : Form} :
    FreeIn x (.and φ ψ) ↔ (FreeIn x φ ∨ FreeIn x ψ) := Iff.rfl
@[simp] theorem freeIn_or {x : Nat} {φ ψ : Form} :
    FreeIn x (.or φ ψ) ↔ (FreeIn x φ ∨ FreeIn x ψ) := Iff.rfl
@[simp] theorem freeIn_imp {x : Nat} {φ ψ : Form} :
    FreeIn x (.imp φ ψ) ↔ (FreeIn x φ ∨ FreeIn x ψ) := Iff.rfl
@[simp] theorem freeIn_all {x y : Nat} {φ : Form} :
    FreeIn x (.all y φ) ↔ (x ≠ y ∧ FreeIn x φ) := Iff.rfl
@[simp] theorem freeIn_ex {x y : Nat} {φ : Form} :
    FreeIn x (.ex y φ) ↔ (x ≠ y ∧ FreeIn x φ) := Iff.rfl
@[simp] theorem freeIn_supp {x : Nat} {t φ : Form} :
    FreeIn x (t ⊳ φ) ↔ (FreeIn x t ∨ FreeIn x φ) := Iff.rfl
@[simp] theorem freeIn_refut {x : Nat} {t φ : Form} :
    FreeIn x (t ⊲ φ) ↔ (FreeIn x t ∨ FreeIn x φ) := Iff.rfl
@[simp] theorem freeInList_nil {x : Nat} : ¬ FreeInList x [] := id
@[simp] theorem freeInList_cons {x : Nat} {t : Form} {ts : List Form} :
    FreeInList x (t :: ts) ↔ (FreeIn x t ∨ FreeInList x ts) := Iff.rfl

/-- 列表成员的自由出现蕴含列表的自由出现。 -/
theorem freeInList_of_mem {x : Nat} {s : Form} {ts : List Form} (hm : s ∈ ts)
    (h : FreeIn x s) : FreeInList x ts := by
  induction ts with
  | nil => simp at hm
  | cons t ts ih =>
      rcases List.mem_cons.mp hm with rfl | htail
      · exact Or.inl h
      · exact Or.inr (ih htail)

/-- 变量更新（用于语义中的赋值）。 -/
def upd {W : Type} (ρ : Nat → W) (x : Nat) (v : W) : Nat → W :=
  fun y => if y = x then v else ρ y

@[simp] theorem upd_same {W : Type} (ρ : Nat → W) (x : Nat) (v : W) : upd ρ x v x = v := by
  simp [upd]

theorem upd_noteq {W : Type} (ρ : Nat → W) {x y : Nat} (h : y ≠ x) (v : W) :
    upd ρ x v y = ρ y := by
  simp [upd, h]

/-- 两个不同变量的更新可交换。 -/
theorem upd_upd_comm {W : Type} (ρ : Nat → W) {x y : Nat} (h : x ≠ y) (v w : W) :
    upd (upd ρ x v) y w = upd (upd ρ y w) x v := by
  funext z
  by_cases hzx : z = x
  · subst hzx
    simp [upd, h]
  · by_cases hzy : z = y
    · subst hzy
      simp [upd, hzx]
    · simp [upd, hzx, hzy]

/-- 同一变量的两次更新：后者胜出。 -/
@[simp] theorem upd_upd_same {W : Type} (ρ : Nat → W) (x : Nat) (v w : W) :
    upd (upd ρ x v) x w = upd ρ x w := by
  funext z
  by_cases hz : z = x <;> simp [upd, hz]

/-! ## 代入（避免捕获） -/

/- 避免捕获的同时代入。在量词 `∀y` / `∃y` 之下，把 `y` 从代入中移除，
以免自由变元被该量词捕获。 -/
mutual
  def subst (σ : Nat → Form) : Form → Form
    | .var y => σ y
    | .atom i ts => .atom i (substList σ ts)
    | .bot => .bot
    | .top => .top
    | .not φ => .not (subst σ φ)
    | .and φ ψ => .and (subst σ φ) (subst σ ψ)
    | .or φ ψ => .or (subst σ φ) (subst σ ψ)
    | .imp φ ψ => .imp (subst σ φ) (subst σ ψ)
    | .all y φ => .all y (subst (fun z => if z = y then .var y else σ z) φ)
    | .ex y φ => .ex y (subst (fun z => if z = y then .var y else σ z) φ)
    | .supp t φ => .supp (subst σ t) (subst σ φ)
    | .refut t φ => .refut (subst σ t) (subst σ φ)

  /-- 列表版代入。 -/
  def substList (σ : Nat → Form) : List Form → List Form
    | [] => []
    | t :: ts => subst σ t :: substList σ ts
end

/-- 恒等代入。 -/
def idSubst : Nat → Form := Form.var

@[simp] theorem subst_var (σ : Nat → Form) (y : Nat) : subst σ (.var y) = σ y := rfl
@[simp] theorem subst_bot (σ : Nat → Form) : subst σ (.bot) = .bot := rfl
@[simp] theorem subst_top (σ : Nat → Form) : subst σ (.top) = .top := rfl
@[simp] theorem subst_not (σ : Nat → Form) (φ : Form) :
    subst σ (.not φ) = .not (subst σ φ) := rfl
@[simp] theorem subst_and (σ : Nat → Form) (φ ψ : Form) :
    subst σ (.and φ ψ) = .and (subst σ φ) (subst σ ψ) := rfl
@[simp] theorem subst_or (σ : Nat → Form) (φ ψ : Form) :
    subst σ (.or φ ψ) = .or (subst σ φ) (subst σ ψ) := rfl
@[simp] theorem subst_imp (σ : Nat → Form) (φ ψ : Form) :
    subst σ (.imp φ ψ) = .imp (subst σ φ) (subst σ ψ) := rfl
@[simp] theorem subst_all (σ : Nat → Form) (y : Nat) (φ : Form) :
    subst σ (.all y φ) = .all y (subst (fun z => if z = y then .var y else σ z) φ) := rfl
@[simp] theorem subst_ex (σ : Nat → Form) (y : Nat) (φ : Form) :
    subst σ (.ex y φ) = .ex y (subst (fun z => if z = y then .var y else σ z) φ) := rfl
@[simp] theorem subst_supp (σ : Nat → Form) (t φ : Form) :
    subst σ (t ⊳ φ) = (subst σ t ⊳ subst σ φ) := rfl
@[simp] theorem subst_refut (σ : Nat → Form) (t φ : Form) :
    subst σ (t ⊲ φ) = (subst σ t ⊲ subst σ φ) := rfl

/-- 恒等代入是恒等函数。 -/
@[simp] theorem subst_id : ∀ φ : Form, subst idSubst φ = φ
  | .var _ => rfl
  | .atom i ts => by
      simp only [subst]
      rw [substList_id ts]
  | .bot => rfl
  | .top => rfl
  | .not φ => by simp [subst, subst_id φ]
  | .and φ ψ => by simp [subst, subst_id φ, subst_id ψ]
  | .or φ ψ => by simp [subst, subst_id φ, subst_id ψ]
  | .imp φ ψ => by simp [subst, subst_id φ, subst_id ψ]
  | .all y φ => by
      simp only [subst]
      rw [keep_idSubst y, subst_id φ]
  | .ex y φ => by
      simp only [subst]
      rw [keep_idSubst y, subst_id φ]
  | .supp t φ => by simp [subst, subst_id t, subst_id φ]
  | .refut t φ => by simp [subst, subst_id t, subst_id φ]
where
  substList_id : ∀ ts : List Form, substList idSubst ts = ts
    | [] => rfl
    | t :: ts => by simp [substList, subst_id t, substList_id ts]
  keep_idSubst : ∀ y : Nat, (fun z => if z = y then Form.var y else idSubst z) = idSubst
    | y => by
        funext z
        show (if z = y then Form.var y else Form.var z) = Form.var z
        by_cases h : z = y
        · rw [if_pos h]; exact congrArg Form.var h.symm
        · rw [if_neg h]

/-- 单变元实例化 `φ[x := t]`。 -/
def inst (x : Nat) (t φ : Form) : Form :=
  subst (fun y => if y = x then t else .var y) φ

/- `t` 对 `x` 在 `φ` 中**可代入**（标准自由代入条件）。 -/
mutual
  def FreeFor (t : Form) (x : Nat) : Form → Prop
    | .var _ => True
    | .atom _ ts => FreeForList t x ts
    | .bot => True
    | .top => True
    | .not φ => FreeFor t x φ
    | .and φ ψ => FreeFor t x φ ∧ FreeFor t x ψ
    | .or φ ψ => FreeFor t x φ ∧ FreeFor t x ψ
    | .imp φ ψ => FreeFor t x φ ∧ FreeFor t x ψ
    | .all y φ => y = x ∨ (¬ FreeIn y t ∧ FreeFor t x φ)
    | .ex y φ => y = x ∨ (¬ FreeIn y t ∧ FreeFor t x φ)
    | .supp a φ => FreeFor t x a ∧ FreeFor t x φ
    | .refut a φ => FreeFor t x a ∧ FreeFor t x φ

  /-- 列表版可代入。 -/
  def FreeForList (t : Form) (x : Nat) : List Form → Prop
    | [] => True
    | s :: ss => FreeFor t x s ∧ FreeForList t x ss
end

/-- 列表版可代入的消去。 -/
theorem freeForList_elim {t : Form} {x : Nat} {ts : List Form}
    (h : FreeForList t x ts) {s : Form} (hs : s ∈ ts) : FreeFor t x s := by
  induction ts with
  | nil => simp at hs
  | cons u us ih =>
      rcases List.mem_cons.mp hs with rfl | htail
      · exact h.1
      · exact ih h.2 htail

/- 任何变元对其自身可代入。 -/
mutual
  theorem freeFor_var : ∀ (y : Nat) (φ : Form), FreeFor (.var y) y φ
    | _, .var _ => trivial
    | y, .atom _ ts => freeForList_var y ts
    | _, .bot => trivial
    | _, .top => trivial
    | y, .not φ => freeFor_var y φ
    | y, .and φ ψ => ⟨freeFor_var y φ, freeFor_var y ψ⟩
    | y, .or φ ψ => ⟨freeFor_var y φ, freeFor_var y ψ⟩
    | y, .imp φ ψ => ⟨freeFor_var y φ, freeFor_var y ψ⟩
    | y, .all z φ => by
        by_cases hzy : z = y
        · exact Or.inl hzy
        · exact Or.inr ⟨fun hzy' => hzy hzy', freeFor_var y φ⟩
    | y, .ex z φ => by
        by_cases hzy : z = y
        · exact Or.inl hzy
        · exact Or.inr ⟨fun hzy' => hzy hzy', freeFor_var y φ⟩
    | y, .supp a φ => ⟨freeFor_var y a, freeFor_var y φ⟩
    | y, .refut a φ => ⟨freeFor_var y a, freeFor_var y φ⟩

  /-- 列表版。 -/
  theorem freeForList_var : ∀ (y : Nat) (ts : List Form), FreeForList (.var y) y ts
    | _, [] => trivial
    | y, _ :: ts => ⟨freeFor_var y _, freeForList_var y ts⟩
end

/-! ## 替换关系（元规则 E 的载体） -/

/-- 单项上下文（带一个洞的公式）。元规则 E 允许在**任何**位置替换经典等价的子公式。 -/
inductive Ctx where
  | hole : Ctx
  | atom (i : Nat) (pre : List Form) (c : Ctx) (post : List Form) : Ctx
  | not (c : Ctx) : Ctx
  | andL (c : Ctx) (ψ : Form) : Ctx
  | andR (φ : Form) (c : Ctx) : Ctx
  | orL (c : Ctx) (ψ : Form) : Ctx
  | orR (φ : Form) (c : Ctx) : Ctx
  | impL (c : Ctx) (ψ : Form) : Ctx
  | impR (φ : Form) (c : Ctx) : Ctx
  | all (x : Nat) (c : Ctx) : Ctx
  | ex (x : Nat) (c : Ctx) : Ctx
  | suppL (c : Ctx) (φ : Form) : Ctx
  | suppR (t : Form) (c : Ctx) : Ctx
  | refutL (c : Ctx) (φ : Form) : Ctx
  | refutR (t : Form) (c : Ctx) : Ctx
  deriving Repr, Inhabited

namespace Ctx

/-- 把公式填入上下文的洞中。 -/
def plug : Ctx → Form → Form
  | .hole, φ => φ
  | .atom i pre c post, φ => .atom i (pre ++ plug c φ :: post)
  | .not c, φ => .not (plug c φ)
  | .andL c ψ, φ => .and (plug c φ) ψ
  | .andR ψ c, φ => .and ψ (plug c φ)
  | .orL c ψ, φ => .or (plug c φ) ψ
  | .orR ψ c, φ => .or ψ (plug c φ)
  | .impL c ψ, φ => .imp (plug c φ) ψ
  | .impR ψ c, φ => .imp ψ (plug c φ)
  | .all x c, φ => .all x (plug c φ)
  | .ex x c, φ => .ex x (plug c φ)
  | .suppL c ψ, φ => .supp (plug c φ) ψ
  | .suppR t c, φ => .supp t (plug c φ)
  | .refutL c ψ, φ => .refut (plug c φ) ψ
  | .refutR t c, φ => .refut t (plug c φ)

end Ctx

/-- `Replace φ ψ γ δ`：把 `γ` 中某处子公式 `φ` 替换为 `ψ` 得到 `δ`。
这是元规则 **E**（经典等价替换）的语法前提。 -/
def Replace (φ ψ γ δ : Form) : Prop := ∃ C : Ctx, γ = C.plug φ ∧ δ = C.plug ψ

/-- 替换关系是对称的（上下文相同，只是洞的填充物互换）。 -/
theorem Replace.symm {φ ψ γ δ : Form} (h : Replace φ ψ γ δ) : Replace ψ φ δ γ := by
  obtain ⟨C, h1, h2⟩ := h
  exact ⟨C, h2, h1⟩

/-- 洞填 `γ` 得到 `γ` 本身。 -/
theorem replace_self (γ : Form) : Replace γ γ γ γ := ⟨.hole, rfl, rfl⟩

end EvidenceLogic
