/-
# 初始性：可靠性 = 折叠，Lindenbaum 商与解释下降（Initiality）

本文件**新增**（不改动仓库任何已有文件），只 `import EvidenceLogic`。目标：

1. `⊣⊢`（`EvidenceLogic.CEquiv`）是 `Form` 上的等价关系；
2. **解释下降**：真值 `φ ↦ M.truth φ ρ` 穿过 `⊣⊢` 商（Lindenbaum 商 `FormQuot`），
   良定义性由 `Derivable.truth_eq_of_cequiv`（即 `IsModel.classical`）给出；
3. **可靠性就是折叠**：`Derivable.soundness` 的证明重写为**显式的 `Derivable.rec` 应用**，
   即从初始代数（语法 `Derivable`）到任意模型真值代数的**唯一同态**；
4. 说明性结论（注释；另附一个只作陈述、不作证明的 `Prop` 定义）。

第 4 点的关键一句：`truthLift` 的**单射性**是完备性（`M.Valid φ → Derivable φ`）的
代数形式，它**在本系统中不可证**，归约到 `docs/讨论与局限.md` 第 2 节的公开问题
（Lindenbaum 代数缺少所需的无穷交）。本文件**不试图证明它**，见文末。

依赖（均有现成证明）：`Derivable.soundness`、`Derivable.rec`、`Derivable.truth_eq_of_cequiv`、
`Frame.plug_congr`、`IsModel`。本文件全部证明完成，不引入新公理，不含未完成证明占位符。
-/
import EvidenceLogic.Model.Soundness

namespace EvidenceLogic

/-! ## 1) `⊣⊢` 是等价关系 -/

/-- 自反：`φ ⊣⊢ φ`。（两侧的后承都是 `≤` 的自反性。） -/
theorem cequiv_refl (φ : Form) : φ ⊣⊢ φ :=
  ⟨fun B ρ => PSet.le_refl (B.truth φ ρ), fun B ρ => PSet.le_refl (B.truth φ ρ)⟩

/-- 对称：交换两个方向。 -/
theorem cequiv_symm {φ ψ : Form} (h : φ ⊣⊢ ψ) : ψ ⊣⊢ φ :=
  ⟨h.2, h.1⟩

/-- 传递：两侧分别用 `≤` 的传递性。 -/
theorem cequiv_trans {φ ψ χ : Form} (h₁ : φ ⊣⊢ ψ) (h₂ : ψ ⊣⊢ χ) : φ ⊣⊢ χ :=
  ⟨fun B ρ => PSet.le_trans (h₁.1 B ρ) (h₂.1 B ρ),
   fun B ρ => PSet.le_trans (h₂.2 B ρ) (h₁.2 B ρ)⟩

/-- 打包：`CEquiv` 满足等价关系的三条公理（可直接用作 `Setoid` 的关系）。 -/
theorem cequiv_equivalence : Equivalence CEquiv :=
  ⟨cequiv_refl, fun h => cequiv_symm h, fun h₁ h₂ => cequiv_trans h₁ h₂⟩

/-! ## 2) 解释下降：真值穿过 `⊣⊢` 商 -/

/-- 公式模 `⊣⊢` 的商（Lindenbaum 商）：公式的「经典等价类」。 -/
def FormQuot : Type := Quot (fun φ ψ : Form => φ ⊣⊢ ψ)

/-- **真值经商下降**：`Quot.lift` 把 `φ ↦ M.truth φ ρ` 送到商上；
良定义性（对 `⊣⊢` 不变）恰由 `Derivable.truth_eq_of_cequiv` 给出，
而后者不过是 `IsModel.classical` 的两个方向的组合。 -/
def truthLift (M : Frame) (hM : IsModel M) (ρ : Nat → PSet M.W) :
    FormQuot → PSet M.W :=
  Quot.lift (fun φ => M.truth φ ρ)
    (fun _ _ h => Derivable.truth_eq_of_cequiv hM h ρ)

/-- 下降映射在代表元上就是原来的解释：这是 `Quot.lift` 的计算规则（`rfl`）。 -/
theorem truthLift_mk (M : Frame) (hM : IsModel M) (ρ : Nat → PSet M.W) (φ : Form) :
    truthLift M hM ρ (Quot.mk _ φ) = M.truth φ ρ :=
  rfl

/-- 显式形式：直接用 `⊣⊢` 说明等价类相等在下降后仍成立（`Quot.sound` 的那一步）。 -/
theorem truthLift_eq_of_cequiv (M : Frame) (hM : IsModel M) (ρ : Nat → PSet M.W)
    {φ ψ : Form} (h : φ ⊣⊢ ψ) :
    truthLift M hM ρ (Quot.mk _ φ) = truthLift M hM ρ (Quot.mk _ ψ) := by
  rw [truthLift_mk, truthLift_mk]
  exact Derivable.truth_eq_of_cequiv hM h ρ

/-- **下降映射的唯一性**：任何在代表元上与 `M.truth · ρ` 一致的 `g` 都等于 `truthLift`。
与 `truthLift_mk`（存在性／计算规则）合起来，`truthLift` 就是
沿 `Quot.mk _` 的**唯一**分解映射——即「初始代数到模型真值代数的唯一同态」在商这一层的说法。 -/
theorem truthLift_unique (M : Frame) (hM : IsModel M) (ρ : Nat → PSet M.W)
    (g : FormQuot → PSet M.W) (hg : ∀ φ : Form, g (Quot.mk _ φ) = M.truth φ ρ) :
    g = truthLift M hM ρ := by
  apply funext
  intro q
  revert q
  exact Quot.ind (fun φ => by rw [hg φ, truthLift_mk])

/-- `⊣⊢` 作为 `Setoid`（由第 1 步的三条定理给出）。 -/
def cequivSetoid : Setoid Form := ⟨CEquiv, cequiv_equivalence⟩

/-- `FormQuot` 恰是 `⊣⊢` 这个 `Setoid` 的商（`Quotient` 在核心中就是 `Quot`）。 -/
theorem formQuot_eq_quotient : FormQuot = Quotient cequivSetoid := rfl

/-! ## 3) 可靠性就是折叠（显式 `Derivable.rec`） -/

/-- **可靠性 = 折叠**：与 `Derivable.soundness` 同陈述，但证明写成**显式的 `Derivable.rec` 应用**。

`Derivable` 是初始代数（语法），`M.Valid` 是任意模型给出的代数；`Derivable.rec`
给出的正是从初始代数出发的**唯一同态**（折叠）。十个分支参数依次对应构造子
`e s1 s2 f1 f2 f3 f4 r1 p1 p2`，每个分支的内容与 `Soundness.lean` 的归纳分支逐字对应；
其中 `E` 那一支用 `Frame.plug_congr`（上下文填入的真值相合性）。 -/
theorem soundness_as_fold (M : Frame) (hM : IsModel M) :
    ∀ {φ : Form}, Derivable φ → M.Valid φ :=
  fun {φ} h =>
    Derivable.rec (motive := fun φ _ => M.Valid φ)
      -- e：经典等价替换
      (fun {φ ψ γ δ} hrep heq hγ ih => by
        obtain ⟨C, hγeq, hδeq⟩ := hrep
        have hφψ : ∀ ρ, M.truth φ ρ = M.truth ψ ρ := Derivable.truth_eq_of_cequiv hM heq
        have hγ' : M.Valid (C.plug φ) := by
          rw [← hγeq]
          exact ih
        rw [hδeq]
        intro ρ
        rw [← Frame.plug_congr M hM C φ ψ hφψ ρ]
        exact hγ' ρ)
      -- s1：后承支持
      (fun {p q} h => fun ρ =>
        Derivable.valid_supp M hM (hM.s1 p q ρ (hM.classical p q h ρ)))
      -- s2：后承封闭
      (fun {t p q} h₁ h ih => fun ρ =>
        Derivable.valid_supp M hM (hM.s2 (M.truth t ρ) p q ρ
          (Derivable.supp_of_valid M hM (ih ρ))
          (hM.classical p q h ρ)))
      -- f1：同一主体全称引入
      (fun {k t φ x} hx h ih => fun ρ =>
        Derivable.valid_rel M hM (hM.f1 k t φ x ρ hx
          (fun X => Derivable.rel_of_valid M hM (ih (upd ρ x X)))))
      -- f2：全称主体
      (fun {k p φ x} hx h ih => fun ρ =>
        Derivable.valid_rel M hM (hM.f2 k p φ x ρ hx
          (fun X => Derivable.rel_of_valid M hM (ih (upd ρ x X)))))
      -- f3：合取主体
      (fun {k a b φ} h₁ h₂ ih₁ ih₂ => fun ρ =>
        Derivable.valid_rel M hM (hM.f3 k (M.truth a ρ) (M.truth b ρ) φ ρ
          (Derivable.rel_of_valid M hM (ih₁ ρ))
          (Derivable.rel_of_valid M hM (ih₂ ρ))))
      -- f4：同一主体合取引入
      (fun {k t φ ψ} h₁ h₂ ih₁ ih₂ => fun ρ =>
        Derivable.valid_rel M hM (hM.f4 k (M.truth t ρ) φ ψ ρ
          (Derivable.rel_of_valid M hM (ih₁ ρ))
          (Derivable.rel_of_valid M hM (ih₂ ρ))))
      -- r1：否定反驳
      (fun {t φ} h ih => fun ρ =>
        Derivable.valid_refut M hM (hM.r1 (M.truth t ρ) φ ρ
          (Derivable.supp_of_valid M hM (ih ρ))))
      -- p1：二元合取推广
      (fun {kR kS a b c d f} h₁ h₂ h₃ ih₁ ih₂ ih₃ => fun ρ =>
        Derivable.valid_rel M hM (hM.p1 kR kS a b c d f ρ
          (Derivable.rel_of_valid M hM (ih₁ ρ))
          (Derivable.rel_of_valid M hM (ih₂ ρ))
          (Derivable.rel_of_valid M hM (ih₃ ρ))))
      -- p2：全称推广
      (fun {kR kS a c f x} h₁ h₂ hx ih₁ ih₂ => fun ρ =>
        Derivable.valid_rel M hM (hM.p2 kR kS a c f x ρ hx
          (fun X => Derivable.rel_of_valid M hM (ih₁ (upd ρ x X)))
          (Derivable.rel_of_valid M hM (ih₂ ρ))))
      h

/-- 折叠与 `Derivable.soundness` 在每一点上**给出同一个证明**（`M.Valid φ` 是命题，
故由证明无关性二者相等）。这把「第 3 步不只是重述」变成可检查的事实。 -/
theorem soundness_as_fold_eq_soundness (M : Frame) (hM : IsModel M)
    {φ : Form} (h : Derivable φ) :
    soundness_as_fold M hM h = Derivable.soundness M hM h :=
  Subsingleton.elim _ _

/-! ## 4) 说明性结论 -/

/-- **「单射性 = 完备性的代数形式」（只作陈述，本文件不证明，也不可证）**。

`truthLift M hM ρ` 穿过 `⊣⊢` 商：Lindenbaum 商 `FormQuot` 是初始代数在
语法侧的商，`PSet M.W` 是模型真值代数。下面的 `Prop` 说这个同态**单射**，
即模型真值把互不等价的公式分开。它是完备性（`M.Valid φ → Derivable φ`）的代数说法，
在本系统中**不可证**：它归约到 `docs/讨论与局限.md` 第 2 节的公开问题
（Lindenbaum 代数缺少所需的无穷交，故无法构造反例所需的自由模型）。

这里只把它写成一个 `Prop`（定义，不声称成立），使「缺口在哪里」在代码中可见。 -/
def completeness_as_injectivity (M : Frame) (hM : IsModel M) (ρ : Nat → PSet M.W) :
    Prop :=
  Function.Injective (truthLift M hM ρ)

end EvidenceLogic
