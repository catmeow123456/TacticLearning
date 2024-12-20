# General information about the project
Project title (My formalization project): Tactic Learning
Author (use \and to separate authors if needed) (catmeow123456): Cat in PKU
URL of GitHub repository (https://github.com/catmeow123456/TacticLearning): 
URL of project website (https://catmeow123456.github.io/TacticLearning): 
URL of project API documentation (https://catmeow123456.github.io/TacticLearning/docs)

# TacticLearning

## TODO list

| 进度 | 文件名   | 内容  |
| :--: | :--:    | :--: |
| T | rwneq | 对条件或目标检查是否是任意类型的不等式，如果是，则进行不等式传递的化简 |
| T | assumption |  尝试将所有条件和 goal 匹配 |
| F | neqsimp1 | 自动检查条件中的不等式是否可以通过传递性证明 goal |
| F | apply | 给定 a -> b  和 b，将目标转换成 a |
| T | myExactSymm | Given a statement, try to close the goal with that or with its symm
| T | myAssumption | Given a statement, try to close the goal with some hyps or its symm version
| T | showtype | `Display/Showdecl.lean` 给定一个类型，返回与该类型匹配的所有假设。有用的函数： `ListLocalDeclWithType` 与 `FvarIdsToMessageData`
| T | addhyp `name` : coeff `id` of `poly` | `Poly/ComputeDegree.lean` 添加一个假设，该假设的形式为 `poly.coeff i = ...` 即这个 Tactic 帮我们自动计算了某个具体多项式的某一项系数
| T | continuous | 判断连续函数是否连续的简易 tactic |
| F | continuity/fun_prop | 研究库中已经实现的 Tactic |
| F | differentialat | 判断是否可微分 |
| F | compute_deriv | 计算初等函数（包括其复合）的导数 |
| F | set_minimal | 对于给定集合 s ，求出其最小元素 a，证明 a 是它最小元 |


## Reference

### 一些重要的学习资料

siddhartha-gadgil 在 github 上和 youtube 上发布的 Meta Programming 教程和例子。
https://github.com/siddhartha-gadgil/MetaExamples.git
https://www.youtube.com/watch?v=Ix8zSpsfbDk&list=PL_bVGic_CrGtMw1QVFRLRsZjcymm56mRi

Lean 官网的 Meta Programming 教程：
https://leanprover-community.github.io/lean4-metaprogramming-book/main/01_intro.html

Lean 官网的 Functional Programming 教程（包含一些函数式编程基础概念的应用例子）：
https://leanprover.github.io/functional_programming_in_lean/
