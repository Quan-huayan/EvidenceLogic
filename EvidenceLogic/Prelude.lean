/-
# 自足的前置记号层（Prelude）

Lean 4 核心只提供 `LE` / `≤`；`⊤`、`⊥`、`⊓`、`⊔`、`ᶜ` 及相应类型类属于 Mathlib。
为使本工程**零依赖**（只使用核心与 `Std`），这里自行声明同名类型类与记号，
语义与 Mathlib 中的同名记号一致（完备布尔代数中的运算）。

注意：由于本工程不引入 Mathlib，这些声明不会与之冲突。
-/
namespace EvidenceLogic

/-- 最大元。 -/
class Top (α : Type u) where
  /-- 最大元 -/
  top : α

/-- 最小元。 -/
class Bot (α : Type u) where
  /-- 最小元 -/
  bot : α

/-- 交（下确界）。 -/
class Inf (α : Type u) where
  /-- 交 -/
  inf : α → α → α

/-- 并（上确界）。 -/
class Sup (α : Type u) where
  /-- 并 -/
  sup : α → α → α

/-- 补。 -/
class Compl (α : Type u) where
  /-- 补 -/
  compl : α → α

notation "⊤" => Top.top
notation "⊥" => Bot.bot
infixl:70 " ⊓ " => Inf.inf
infixl:65 " ⊔ " => Sup.sup
postfix:1024 "ᶜ" => Compl.compl

end EvidenceLogic
