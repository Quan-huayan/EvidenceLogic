/-
# 背书逻辑 v1.0 —— Lean 4 形式化（汇总模块）

本模块导入全部内容，便于 `import EvidenceLogic` 一次性使用。
导入顺序与目录分层一致：

* `Core/`     —— 语言与基础（自足格运算记号层）
* `Model/`    —— 两层语义、模型类 `IsModel`、典范模型族、可靠性
* `System/`   —— 公理系统（E、S1、S2、F1–F4、R1、P1、P2）与定稿第八／九／十节结果
* `Analysis/` —— 证据语义分析：判据结构、代数画像、证据项与正向刻画、初始性
* `Frontier/` —— 唯一前沿（支持传递／S7）的片段化障碍链与条件化定理

详见 `README.md`；各层的一句话说明见该文件的模块表。
全部模块无 `sorry`、无 `axiom`、零依赖（不含 Mathlib）。
-/

-- Core：语言与基础
import EvidenceLogic.Core.Prelude
import EvidenceLogic.Core.Syntax

-- Model：语义与模型论
import EvidenceLogic.Model.Semantics
import EvidenceLogic.Model.Canonical
import EvidenceLogic.Model.Soundness
import EvidenceLogic.Model.Strict

-- System：证明系统与定稿第八／九／十节
import EvidenceLogic.System.Derivable
import EvidenceLogic.System.Properties
import EvidenceLogic.System.Derived
import EvidenceLogic.System.NonDerivable
import EvidenceLogic.System.NonAdmissible

-- Analysis：证据语义分析
import EvidenceLogic.Analysis.Structure
import EvidenceLogic.Analysis.Disjuncts
import EvidenceLogic.Analysis.Algebra
import EvidenceLogic.Analysis.Evidence
import EvidenceLogic.Analysis.Initiality
import EvidenceLogic.Analysis.Inversion
import EvidenceLogic.Analysis.InversionRefut
import EvidenceLogic.Analysis.NormalForm

-- Frontier：唯一前沿（支持传递／S7）
import EvidenceLogic.Frontier.EFree
import EvidenceLogic.Frontier.RestrictedE
import EvidenceLogic.Frontier.Transfer
import EvidenceLogic.Frontier.Conditional
import EvidenceLogic.Frontier.Probe
import EvidenceLogic.Frontier.Obstruction
import EvidenceLogic.Frontier.SingleLayer
import EvidenceLogic.Frontier.SingleLayerFull
import EvidenceLogic.Frontier.NoRelFragment
