# TacticLearning

## TODO list

| 进度 | 文件名   | 内容  |
| :--: | :--:    | :--: |
| T | rwneq | 对条件或目标检查是否是任意类型的不等式，如果是，则进行不等式传递的化简 | 
| F  | assumption |  尝试将所有条件和 goal 匹配 |
| F | neqsimp1 | 自动检查条件中的不等式是否可以通过传递性证明 goal |
| F | apply | 给定 a -> b  和 b，将目标转换成 a |


## Reference

### 一些重要的学习资料

siddhartha-gadgil 在 github 上和 youtube 上发布的 Meta Programming 教程和例子。
https://github.com/siddhartha-gadgil/MetaExamples.git
https://www.youtube.com/watch?v=Ix8zSpsfbDk&list=PL_bVGic_CrGtMw1QVFRLRsZjcymm56mRi

Lean 官网的 Meta Programming 教程：
https://leanprover-community.github.io/lean4-metaprogramming-book/main/01_intro.html

Lean 官网的 Functional Programming 教程（包含一些函数式编程基础概念的应用例子）：
https://leanprover.github.io/functional_programming_in_lean/