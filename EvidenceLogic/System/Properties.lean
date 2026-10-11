/-
# 背书逻辑 v1.0：系统性质（Properties）

本文件把定稿第八节「系统性质」中可形式化的条目写成定理。

* 「支持对经典后承右封闭」——`S2` 的直接表述；
* 「同一支持者内部合取封闭」——`F4` 的直接表述；
* 「同一支持者若同时支持 `φ` 和 `¬φ`，会支持一切」——由 `F4` + `S2` + 爆炸律得到；
* 「系统不蕴涵真」——存在可推导的支持陈述，其被支持命题不有效。

「不同支持者支持相反命题不会自动合取」（非加性）是**不可推导性**陈述，
由 S7 模式的反模型给出，见 `EvidenceLogic.System.NonDerivable`。
-/
import EvidenceLogic.Model.Canonical

namespace EvidenceLogic

/-! ## 支持方面的封闭性 -/

/-- **S2**：支持对经典后承右封闭。 -/
theorem supp_right_closure {t p q : Form} (h : Derivable (t ⊳ p)) (he : Entails p q) :
    Derivable (t ⊳ q) :=
  Derivable.s2 h he

/-- **F4**：同一支持者内部合取封闭。 -/
theorem supp_and_intro {t φ ψ : Form} (h₁ : Derivable (t ⊳ φ))
    (h₂ : Derivable (t ⊳ ψ)) : Derivable (t ⊳ (.and φ ψ)) :=
  Derivable.f4 (k := .supp) h₁ h₂

/-! ## 自相矛盾的支持者 -/

/-- 经典爆炸律：`φ ∧ ¬φ` 后承一切。 -/
theorem entails_explosion (φ ψ : Form) : Entails (.and φ (.not φ)) ψ := by
  intro B ρ w h
  exact absurd h.1 h.2

/-- 定稿第八节：同一支持者若同时支持 `φ` 与 `¬φ`，则支持一切。

（由 F4 合取封闭得到 `t ⊳ (φ ∧ ¬φ)`，再由 S2 与爆炸律得到任意 `ψ`。） -/
theorem supp_explosion {t φ ψ : Form} (h₁ : Derivable (t ⊳ φ))
    (h₂ : Derivable (t ⊳ (.not φ))) : Derivable (t ⊳ ψ) :=
  Derivable.s2 (Derivable.f4 (k := .supp) h₁ h₂) (entails_explosion φ ψ)

/-! ## 不蕴涵真 -/

/-- 空支持者（`⊥`）支持一切：`⊥ ⊢ φ` 对任意 `φ` 成立。 -/
theorem entails_bot (φ : Form) : Entails .bot φ := by
  intro B ρ w h
  exact absurd h (PSet.not_bot w)

/-- 定稿第八节：系统**不蕴涵真**。

存在可推导的支持陈述 `t ⊳ φ`，而 `φ` 本身并非在所有模型中有效：
取 `t := ⊥`、`φ := P`（原子谓词），则 `⊥ ⊳ P` 由 S1 可推导
（`⊥ ⊢ P`），而取原子解释恒为 `⊥` 的典范模型即知 `P` 无效。 -/
theorem support_does_not_imply_truth :
    ∃ t φ : Form, Derivable (t ⊳ φ) ∧ ¬ (∀ M : Frame, IsModel M → M.Valid φ) := by
  refine ⟨.bot, .atom 0 [], Derivable.s1 (entails_bot _), ?_⟩
  intro h
  have hM : IsModel (Canon.frame (Fin 1) (fun _ _ => (⊥ : PSet (Fin 1)))) :=
    Canon.isModel (Fin 1) (fun _ _ => (⊥ : PSet (Fin 1)))
  have hv := h (Canon.frame (Fin 1) (fun _ _ => (⊥ : PSet (Fin 1)))) hM
  have hval : (Canon.frame (Fin 1) (fun _ _ => (⊥ : PSet (Fin 1)))).truth (.atom 0 [])
      (fun _ => (⊥ : PSet (Fin 1))) = ⊥ := rfl
  have hbot : (⊥ : PSet (Fin 1)) = ⊤ := by
    rw [← hval]
    exact hv (fun _ => (⊥ : PSet (Fin 1)))
  exact PSet.not_bot (0 : Fin 1) (by rw [hbot]; trivial)

end EvidenceLogic
