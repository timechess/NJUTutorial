import Mathlib.Tactic

/-!
# 读懂 Lean 代码

在学习证明技巧之前，我们首先需要学会阅读已有的代码，了解 Lean 代码的基本结构，
并掌握常用命令与工具。
-/

/-!
## `#check` 命令

Lean 中的一切表达式均有类型，`#check` 命令可用于检查表达式的类型，其输出信息一般为
`term : type` 的形式，如 `42 : ℕ` 表示 `42` 的类型为 `ℕ`，或 `42` 是类型 `ℕ` 的
一个term。
-/

#check 42
#check 2 + 2
#check (1 : ℚ)
#check true

#check fun x => x + 1
#check fun x => x = 1

#check True
#check 1 + 1 = 2
#check ∀ x : ℕ, x ≥ 0

#check Nat
#check Nat -> Nat
#check Type
#check Prop

#check Nat.add_comm

/-!
我们可以对上面 `#check` 输出的类型进行分类，如 `ℕ`、`ℚ`、`Bool` 等可分为一类。使用 `→`
或 `->` 连接两个类型所构成的新的类型可分为一类，如 `Nat → Nat`、`Nat -> Bool` 等，被
称为函数类型。类型的类型，如 `Type`、`Type 1`、`Prop` 等可分为一类。

我们还可以注意到，所有具体命题的类型均为 `Prop`，而各个具体命题的term即为其证明。

Lean 中的类型可以划分为多个层级，称为 universe，记为 `Sort u`，其中 `u` 为
universe level，为正整数。 `Prop` 即 `Sort 0`，`Type u` 即 `Sort (u+1)`。
-/

#check Sort 0
#check Sort 1
#check Sort 2

/-!
**在任何时候，`t : T` 均表示 `t` 是 `T` 的一个term，或 `t` 具备类型 `T`。**
-/


/-!
## `#eval` 命令

`#eval` 命令可用于计算表达式的值，表达式是否能用 `#eval` 计算主要取决于该表达式是否
可计算，以及计算结果的类型是否能够打印。
-/

#eval 1 + 1
#eval Nat.Prime 7
#eval True ∧ False
-- 使用 `ctrl + /` 可注释/取消注释代码行
-- #eval (1 : ℝ) / 2
-- #eval fun x => x + 1

/-!
## def/theorem 关键词

在以上的例子中，我们实际上只使用了当前环境中已有的常量来构造表达式。我们可以通过使用 `def`
或 `theorem` 等关键词来为环境添加新的常量，步骤一般如下：

1. 决定新常量的名称，需要区别于当前环境中已有的常量。
2. 标记新常量的类型。（不考虑自动类型推断）
3. 构造新常量的值（term）。

语法格式为： `def/theorem 常量名 : 常量类型 := 常量值` 。

若为函数类型，也可把常量类型中的自变量提取到冒号前面，语法格式为：
`def/theorem 常量名 (自变量1 : 类型1) ... (自变量n : 类型n) : 因变量类型 := 因变量值` 。

`def` 与 `theorem` 的唯一区别是，`theorem` 所定义的常量的类型必须是具体命题（类型为 `Prop`），
而 `def` 则没有此限制。

定义后该常量永久存在，通过 `import` 语句可在其他文件中使用该常量。

若使用 `example` 关键词，则无需给定常量名，也无法在其他地方使用该常量，仅可用于测试或展示。
-/

def x : ℕ := 42

#check x
#eval x

def f₁ : ℕ → ℕ := fun n => n + 1

#check f₁
#check f₁ 2

def f₂ (n : ℕ) : ℕ := n + 2

#check f₂
#check f₂ 2

def f₃ : (a b : Nat) → Nat := fun a b => a + b

#check f₃
#check f₃ 2 3

theorem thm₁ : 1 + 1 = 2 := rfl
theorem thm₂ (m n : ℕ) : m + n = n + m := Nat.add_comm m n

#check thm₁
#check thm₂

/-!
**证明一个定理，即构造该定理类型的一个term。**

同一个定理的不同证明在 Lean 中被视为等价的。（重要的是定理类型，而非证明。）

想要查看一个常量的具体定义，可使用 `#print` 命令。
-/

#print f₁
#print f₂
#print thm₂

/-!
`#print` 命令还有更多妙用，在以后的课程会进一步介绍。
-/

/-!
## 参数类型

参数列表中的不同括号意味着不同参数类型，如 `()` 表示显式参数，`{}` 表示隐式参数，`[]` 表示
实例隐式参数。我们这里只介绍显式参数与隐式参数。

使用 `()` 括起的参数表示显式参数，调用时必须显式提供参数值。
-/

def f₄ (a b : ℕ) : ℕ := a + b

#eval f₄ 2 3

/-!
使用 `{}` 括起的参数表示隐式参数，调用时 Lean 会根据上下文自动推断参数值，一般用于提供类型参数。
-/

def f₅ {α : Type} (a : α) : α := a

#eval f₅ 42
#check f₅ 42
#check f₅ (α := ℚ) 42 -- 强制指定隐式参数语法

/-!
我们这里不具体介绍实例隐式参数，但可通过一个简单例子来理解其作用。
-/

-- 此处 `[Add α]` 表示 `α` 具备加法结构，因此类型为 `α` 的元素可使用 `+` 运算符。
def f₆ {α : Type} [Add α] (a b : α) := a + b

#eval f₆ 2 3

-- 反例：若去掉 `[Add α]`，则无法使用 `+` 运算符。
-- def f₆ {α : Type} (a b : α) := a + b

/-!
## section/variable/namespace/open 关键词

以上关键词一般用于项目代码结构组织。

如果在某个文件中的某一段，你需要定义多个有着相同参数变量前缀的函数或定理，可使用
`section` 划分出一节，并在其中使用 `variable` 关键词声明前缀变量。这些变量将只在
该节内有效。如若不使用 `section` 分节，则变量在剩余文件中均有效。

`section` 可跟名称，也可不跟，没有影响。
-/

section MySection
variable (a b : ℕ)

def f : ℕ := a + b
def g : ℕ := a - b

variable (p : a = b)

include p

theorem fg₁ : f a b = 2 * a := by
  rw [f, p, two_mul]

theorem fg₂ : g a b = 0 := by
  rw [g, p, Nat.sub_self]
end MySection

#check f -- 在 section 外依然可用
#check fg₁

/-!
`namespace` 具备 `section` 的所有功能，但必须给定名称。其会给命名空间内所有定义的常量
添加前缀，避免命名冲突。使用 `open` 关键词可打开某个命名空间，从而省略前缀。

使用 `open xxx in` 可在局部打开命名空间 `xxx`，只在 `in` 后的表达式中省略前缀。
-/

namespace MyNamespace

def f : ℕ → ℕ := fun n => n * n

end MyNamespace

#check MyNamespace.f

open MyNamespace in
#check f

#check f


/-!
# 函数类型

函数类型表示从一个类型到另一个类型的映射关系，记为 `A → B`，表示从类型 `A` 到类型 `B` 的函数。
命题也可视为函数，如 `P → Q` 表示可从命题 `P` 的证明构造出命题 `Q` 的证明。在 Lean 中有着大量
函数类型的应用，在本节中将会介绍几个常见的例子。
-/

/-!
## Type Constructor

我们可以基于已有类型构造出新的类型，比如使用 `Prod` 构造笛卡尔积类型，使用 `Sum` 构造
类型的直和，使用 `List` 构造列表类型等。
-/

#check Prod
#check Prod ℕ ℕ
#check ℕ × ℝ

#check Prod.mk 2 3
-- 使用 \< 与 \> 可输入尖括号
#check (⟨2, 3⟩ : ℕ × ℝ)
#check (2, 3, 4)

#check Sum
#check Sum ℕ ℕ
#check ℕ ⊕ ℚ

#check (Sum.inl 2 : Sum ℕ ℕ)
#check (Sum.inr 3 : Sum ℚ ℕ)

#check List
#check List ℕ

#check [1, 2]

/-!
对于命题，合取与析取对应的类型为 `And` 与 `Or`，作用类似于 `Prod` 与 `Sum`。
-/

#check And
#check And True False
#check True ∧ False

#check (And.intro rfl rfl : (1 = 1) ∧ (2 = 2))

#check Or
#check Or True False
#check True ∨ False

#check (Or.inl rfl : (1 = 1) ∨ (2 = 3))


/-!
## Theorem as Function

在 Lean 中，定理被视为从前提到结论的函数。使用定理的方法与使用函数相同，书写定理时也可用
类似函数的技巧。
-/

theorem thm₃ {P Q : Prop} (h₁ : P) (h₂ : P → Q) : Q := h₂ h₁

theorem thm₄ : ∀ {P Q : Prop}, P → (P → Q) → Q :=
  fun h₁ h₂ => h₂ h₁

theorem thm₅ : {P Q : Prop} → P → (P → Q) → Q :=
  fun h₁ h₂ => h₂ h₁

-- 作为比较
def f₇ : {α β : Type} → α → (α → β) → β :=
  fun a b => b a

#eval f₇ 42 (fun _ => "Hello world")

/-!
## Dependent Function

Lean 的理论基础为依赖类型论，因此函数类型也可依赖于自变量的取值，称为依赖函数，记为
`(x : A) → B x`，表示从类型 `A` 的元素 `x` 映射到类型 `B x` 的函数，其中 `B x` 可随
`x` 的取值而变化。
-/

def f₈ : (n : ℕ) → Fin (n + 1) :=
  fun n => ⟨0, Nat.succ_pos n⟩

#check f₈ 4
#check f₈ 10

def f₉ : {α : Type} → (x : α) → (α ⊕ Nat) :=
  fun x => Sum.inl x

#check f₉ "Lean"
#eval f₉ "Lean"
#check f₉ 42
#eval f₉ 42

/-!
命题类型是最典型的依赖函数的例子。
-/

theorem thm₆ : ∀ (n : ℕ), n ≥ 0 :=
  fun n => Nat.zero_le n

/-!
## 例子： Set

在 Lean 中，集合被定义为某类型元素到命题的映射，即 `Set α := α → Prop`。
-/

#print Set

-- 大于 2 的自然数集合
def s₁ : Set ℕ := fun n => n > 2
def s₂ : Set ℕ := { n : ℕ | n > 2 }

theorem thm₇ (n : ℕ) (h : s₁ n) : n ∈ s₂ := h

theorem thm₈ : s₁ 3 := by
  unfold s₁
  norm_num

#print setOf
theorem thm₉ : s₂ 3 := by
  unfold s₂
  -- { n | n > 2 } 实际上是 setOf (fun n => n > 2) 的语法糖
  rw [setOf] -- 展开 setOf定义
  norm_num

/-!
从以上的例子里我们可以看到，Lean 中的 `Set` 本质实际上是函数，但 Mathlib 设计了我们习惯的
符号与定义使其操作起来与我们熟悉的集合几乎没有差异。

但下面的例子可能会比较令人困惑，如若 `s : Set α` 表示 `s` 是一个具体的 `α` 的集合，那么
`a : s` 中的 `a` 实际上是一个类型 `α` 的 `Subtype`，记为 `{ a // a ∈ s}`。若用集合的思维
理解，则 `a` 是 `α` 中满足特殊性质（即属于子集 `s`）的一个元素。然而，此时 `a` 的类型不能
看作 `α`，但可以用 `a.1` 来获取 `a` 中作为 `α` 的term的部分，而 `a.2` 则是 `a.1` 属于 `s`
的性质。

我们会在之后的课程中再次遇到 `Subtype`。
-/
section

variable {α : Type} (s : Set α) (a : s)

-- `↑` 表示发生了隐式类型转换，此时可通过鼠标悬浮查看具体转换过程
#check a
#check a.1
#check a.2

#print Set.Elem

#print Set.Subset
example (t : Set α) (h : s ⊆ t) : a.1 ∈ t := h a.2

end

/-!
# 基本Tactic

在本节中，我们将介绍一些最基本的tactic，为后续的学习做预热。需要注意的是，Lean 中的证明分为
两个模式：**Tactic mode** 与 **Term mode**，区别在于是否使用了 `by`，在上面的例子中我们
两种模式都进行了演示。

回顾先前我们对 Lean 中证明实质的陈述：**证明定理即构造该类型的一个term**，我们可以知道实际上
tactic所做的就是帮我们简化了构造term的过程，且提供了全程可见的proof state。

**代码风格提示**
我们可以用 `have` 将证明目标改为一些自定义的中间结论，在证明完 `have` 出的小命题后将其引入
主定理的proof state。

在证明的部分小步骤中我们可以使用term mode简化代码（一般term proof编译更为高效），但由于term
proof本质上就是函数的应用，故为可读性考虑，尽量避免多个函数嵌套，比如：

`have : xxx := thm₁ (thm₂ x y z) (thm₃ a) (thm₄ (thm₅ b))`

推荐的写法：

```
have h1 := thm₂ x y z
have h2 := thm₃ a
have h3 := thm₅ b
have h4 := thm₄ h3
exact h1 h2 h4
```

总之，不要让一行证明过长。
-/

/-!
## rfl/exact

`rfl` 与 `exact` 可以说是最为简单的两个tactic。事实上，在可以使用 `rfl` 完成证明时，可以不
进入tactic mode，直接写 `rfl`（作为term）。在可以使用 `by exact xxx` 时，大部分情况下
可以省略 `by exact`。

`rfl` 可用于证明 `A = A`，此处的两个 `A` 在字面上可以不相同，但只要 Lean 能够判定其依定义
相等，那么 `rfl` 就可以完成证明。

当你在tactic mode中将proof state修改至可以一步构造出需要的term的时候，你可以用 `exact` 以
term mode的格式完成证明。
-/

example : 1 = 1 := rfl

example : 1 = 1 := by exact rfl

example : 1 + 1 = 2 := by rfl

#check Nat.add_comm
example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

example (P : Prop) (h : P) : P ∧ P := by
  have hp : P := h
  exact And.intro hp h

example (P : Prop) (h : P) : P ∧ P := by
  have hp := h
  exact And.intro hp h


/-!
你可以使用 `show_term` 查看tactic为你构造出的term。如果你使用了高级tactic，那么构造出的
term可读性往往会极差（尽管你知道存在更简洁的证明）。这也是为何使用tactic相比term proof会降低
编译速度。
-/

example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := show_term by
  linarith

example (a b c : Nat) (h1 : a < b) (h2 : b < c) : a < c := show_term by
  exact lt_trans h1 h2

/-!
## rw

`rw` 相比于我们先前介绍的tactic区别在于，它需要额外输入常量，基于已知事实改写当前proof state。
例如，我们先前使用 `rw [setOf]` 展开了 `setOf` 的定义，用 `rw [two_mul]` 将表达式中的
`2 * b` 改写为了 `b + b`。

`rw` 一方面可用于展开定义，另一方面也可基于输入的形如 `A = B` 或者 `P ↔ Q` 的事实对proof state
中的 `A` 或 `P` 进行改写，转为 `B` 或 `Q`。
-/

#print Monotone
example : Monotone (fun n => n + 1) := by
  rw [Monotone]
  intro a b h
  linarith

/-！
虽然 `add_assoc` 等定理的定义中，参数均为显式参数，但 `rw` 时 Lean 会进行自动推断。
如若你不满意其自动推断的结果，则可以正常手动提供全部（或部分）参数。
-/
example (a b c : Nat) : a + b + c = b + c + a := by
  rw [add_assoc, add_comm]

/-!
如若使用的定理形如 `A = B`，但你希望把 `B` 改写为 `A`，则在 `rw` 该定理时，在定理前加 `←`。
输入方法为 `\l`
-/
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  rw [pow_two]
  rw [add_mul, mul_add, mul_add]
  rw [← pow_two, ← pow_two]
  rw [← add_assoc, add_assoc (x ^ 2), mul_comm y x, ← two_mul]
  rw [← mul_assoc]

/-!
**calc 模式**

在使用 `rw` 时，我们可以使用 `calc` 让运算过程更清晰可见。 `calc` 常用于等式与不等式的证明。
-/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  calc
    _ = (x + y) * (x + y) := by rw [pow_two]
    _ = x * x + x * y + (y * x + y * y) := by rw [add_mul, mul_add, mul_add]
    _ = x ^ 2 + x * y + (y * x + y ^ 2) := by rw [← pow_two, ← pow_two]
    _ = x ^ 2 + 2 * (x * y) + y ^ 2 := by
      rw [← add_assoc, add_assoc (x ^ 2), mul_comm y x, ← two_mul]
    _ = _ := by rw [← mul_assoc]



section Exercise

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by sorry

namespace MyRing
variable {R : Type*} [Ring R]

#check neg_add_cancel

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  sorry

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry

theorem mul_zero (a : R) : a * 0 = 0 := by
  sorry

theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry
end MyRing

variable {G : Type*} [Group G]

#check inv_mul_cancel

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

end MyGroup
end Exercise
