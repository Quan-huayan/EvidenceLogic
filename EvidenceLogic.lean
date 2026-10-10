/-
# 背书逻辑 v1.0 —— Lean 4 形式化（汇总模块）

本模块导入全部内容，便于 `import EvidenceLogic` 一次性使用：

* `EvidenceLogic.Syntax`       —— 语言（单排序：公式即项）
* `EvidenceLogic.Semantics`    —— 两层语义与模型类 `IsModel`
* `EvidenceLogic.Derivable`    —— 公理系统（E、S1、S2、F1–F4、R1、P1、P2）
* `EvidenceLogic.Canonical`    —— 典范（自由）模型族与存在性定理
* `EvidenceLogic.Soundness`    —— 可靠性定理
* `EvidenceLogic.Derived`      —— 定稿第九节：可导出结果
* `EvidenceLogic.Properties`   —— 定稿第八节：系统性质
* `EvidenceLogic.NonDerivable` —— 定稿第十节：不可推导性（反模型）

详见 `README.md`。全部模块无 `sorry`、无 `axiom`、零依赖（不含 Mathlib）。
-/
import EvidenceLogic.Prelude
import EvidenceLogic.Syntax
import EvidenceLogic.Semantics
import EvidenceLogic.Derivable
import EvidenceLogic.Canonical
import EvidenceLogic.Soundness
import EvidenceLogic.Derived
import EvidenceLogic.Properties
import EvidenceLogic.NonDerivable
