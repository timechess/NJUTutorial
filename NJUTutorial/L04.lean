import Mathlib

namespace Class

/-!
# 代数结构

为了澄清“代数结构”这一短语的含义，我们将通过一些例子来说明。
-/

/-
1. 一个偏序集由一个集合 `P` 和一个在 `P` 上的二元关系 `≤` 组成，该关系是传递的和自反的。
   一个群由一个集合 `G` 和一个结合的二元运算、一个单位元 `e` 以及一个为每个 `G` 中元素 `x` 返回逆元的函数组成。
   如果该运算是交换的，则该群是阿贝尔群或交换群。
-/

/-
2. 一个格是一个带有交和并的偏序集。
-/

/-
3. 一个环由一个（加法写作的）阿贝尔群 `R` 连同结合的乘法运算和单位元 `1` 组成，
   使得乘法对加法分配。如果乘法是交换的，则该环是交换环。
-/

/-
4. 一个有序环 `R` 由一个环连同其元素上的偏序组成，
   使得对于 `R` 中的每个 `a`、`b` 和 `c`，`a ≤ b` 意味着 `a + c ≤ b + c`，
   并且 `0 ≤ a` 和 `0 ≤ b` 意味着 `0 ≤ ab`。
-/

/-
5. 一个度量空间由一个集合 `X` 和一个函数 `d : X × X → ℝ` 组成，满足以下条件：
   1. 对于 `X` 中的每个 `x` 和 `y`，`d(x, y) ≥ 0`。
   2. `d(x, y) = 0` 当且仅当 `x = y`。
   3. 对于 `X` 中的每个 `x` 和 `y`，`d(x, y) = d(y, x)`。
   4. 对于 `X` 中的每个 `x`、`y` 和 `z`，`d(x, z) ≤ d(x, y) + d(y, z)`。
-/

/-
6. 一个拓扑空间由一个集合 `X` 和一个 `X` 的子集集合 `τ` 组成，称为 `X` 的开子集，满足以下条件：
   1. 空集和 `X` 是开的。
   2. 两个开集的交是开的。
   3. 任意开集的并是开的。
-/

/-
在这些例子中，结构的元素属于一个集合，即载体集，有时它代表整个结构。
例如，当我们说“设 `G` 是一个群”然后说“设 `x ∈ G`”时，我们使用 `G` 来代表结构和它的载体。
并非每个代数结构都以这种方式与单个载体集相关联。例如，二分图涉及两个集合之间的关系，伽罗瓦对应也是如此。
一个范畴也涉及两个感兴趣的集合，通常称为对象和态射。

这些例子说明了为了支持代数推理需要做的一些事情。
首先，它需要识别结构的具体实例。数系 `ℤ`、`ℚ` 和 `ℝ` 都是有序环，
我们应该能够在这些实例中应用关于有序环的通用定理。
有时，一个具体集合可能以多种方式成为结构的实例。例如，
除了 `ℝ` 上的通常拓扑（构成实分析的基础）之外，
我们还可以考虑 `ℝ` 上的离散拓扑，其中每个集合都是开的。

其次，证明助手需要支持结构上的通用符号。在 Lean 中，符号 `*` 用于所有常见数系中的乘法，
以及通用群和环中的乘法。当我们使用像 `f x * y` 这样的表达式时，
Lean 必须使用关于 `f`、`x` 和 `y` 的类型信息来确定我们所指的是哪种乘法。

第三，它需要处理结构可以以各种方式从其他结构继承定义、定理和符号的事实。
一些结构通过添加更多公理来扩展其他结构。一个交换环仍然是一个环，
因此任何在环中有意义的定义在交换环中也有意义，任何在环中成立的定理在交换环中也成立。
一些结构通过添加更多数据来扩展其他结构。例如，任何环的加法部分是一个加法群。
环结构添加了乘法和单位元，以及管理它们并将它们与加法部分关联的公理。
有时我们可以用一个结构定义另一个结构。任何度量空间都有一个与之相关的规范拓扑，
即度量空间拓扑，并且可以有任何线性序关联的各种拓扑。

最后，重要的是要记住，数学允许我们使用函数和运算来定义结构，就像我们使用函数和运算来定义数字一样。
群的乘积和幂仍然是群。对于每个 `n`，模 `n` 的整数形成一个环，
对于每个 `n`，该环上的多项式矩阵再次形成一个环。因此，我们可以像计算它们的元素一样轻松地计算结构。
这意味着代数结构在数学中具有双重身份，作为对象集合上的信息和作为独立对象。
证明助手必须适应这种双重角色。

当处理具有关联代数结构的类型的元素时，证明助手需要识别结构并找到相关的定义、定理和符号。
所有这些听起来像是很多工作，确实如此。但 Lean 使用一部分基本机制来执行这些任务。
本节的目标是解释这些机制并向您展示如何使用它们。

第一个要素几乎显而易见：正式地说，代数结构是上节中所述的结构。
代数结构是对满足某些公理假设的数据的，我们在第上节中看到，
这正是 `structure` 命令设计用来容纳的。这是天作之合！

给定一个数据类型 `α`，我们可以如下定义 `α` 上的群结构。
-/

structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

/-
这个群的定义类似于 Mathlib 中 `Group` 的定义，我们选择了名称 `Group₁` 以区分我们的版本。
如果您编写 `#check Group` 并按住 `ctrl` 键点击定义，您将看到 Mathlib 版本的 `Group` 被定义为扩展另一个结构；
我们未来将解释如何做到这一点。

让我们构造一个群，即 `Group₁` 类型的一个元素。对于任何类型对 `α` 和 `β`，
Mathlib 定义了类型 `Equiv α β`，表示 `α` 和 `β` 之间的等价关系。
Mathlib 还为此类型定义了符号 `α ≃ β`。元素 `f : α ≃ β` 是 `α` 和 `β` 之间的双射，
由四个组件表示：一个从 `α` 到 `β` 的函数 `f.toFun`，逆函数 `f.invFun` 从 `β` 到 `α`，
以及两个属性，指定这些函数确实是彼此的逆。
-/

variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

/-
要注意，`f.trans g` 需要以相反的顺序组合函数。
Mathlib 已声明从 `Equiv α β` 到函数类型 `α → β` 的强制转换，
因此我们可以省略编写 `.toFun` 并让 Lean 为我们插入它。
-/

example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

/-
Mathlib 还定义了类型 `perm α`，表示 `α` 与自身之间的等价关系。
-/

example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl

/-
显然，`Equiv.Perm α` 在等价关系的复合下形成一个群。
我们将其定向为 `mul f g` 等于 `g.trans f`，其正向函数是 `f ∘ g`。
换句话说，乘法就是我们通常认为的双射的复合。这里我们定义这个群：
-/

def permGroup {α : Type*} : Group₁ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

/-
现在我们知道如何在 Lean 中定义代数结构，并且我们知道如何定义这些结构的实例。
但我们也希望将符号与结构关联起来，以便我们可以在每个实例中使用它。
此外，我们希望安排它，以便我们可以在结构上定义一个操作并在任何特定实例中使用它，
并且我们希望安排它，以便我们可以在结构上证明一个定理并在任何实例中使用它。

事实上，Mathlib 已经设置为对 `Equiv.Perm α` 使用通用群符号、定义和定理。
-/

variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹
#check g ^ n

example : f * g * g⁻¹ = f := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

/-
我们现在的任务是理解幕后发生的魔法，使 `Equiv.Perm α` 的示例如此便于使用。

Lean 需要能够使用我们键入的表达式中找到的信息来找到相关的符号和隐式群结构。
类似地，当我们使用类型为 `ℝ` 的表达式 `x` 和 `y` 编写 `x + y` 时，Lean 需要将 `+` 符号解释为实数上的相关加法函数。
它还必须将类型 `ℝ` 识别为交换环的实例，以便所有交换环的定义和定理都可用。
再举一个例子，连续性在 Lean 中是相对于任何两个拓扑空间定义的。
当我们有 `f : ℝ → ℂ` 并编写 `Continuous f` 时，Lean 必须找到 `ℝ` 和 `ℂ` 上的相关拓扑。

这种魔法是通过三者的结合实现的。

1. **逻辑**。一个应该在任何群中解释的定义将群的类型和群结构作为参数。
   类似地，关于任意群元素的定理以对群的类型和群结构的全称量词开始。

2. **隐式参数**。类型和结构的参数通常被隐式化，因此我们不必编写它们或在 Lean 信息窗口中看到它们。
   Lean 会默默地为我们填充这些信息。

3. **类型类 (type-class) 推断**。也称为类推断，这是一种简单但强大的机制，
   使我们能够注册信息供 Lean 以后使用。当 Lean 被要求填充定义、定理或符号的隐式参数时，
   它可以使用已注册的信息。

虽然注释 `(grp : Group G)` 告诉 Lean 它应该期望显式给出该参数，
注释 `{grp : Group G}` 告诉 Lean 它应该尝试从表达式中的上下文线索中推断出来，
但注释 `[grp : Group G]` 告诉 Lean 应该使用类型类推断来合成相应的参数。
由于使用此类参数的重点是我们通常不需要显式引用它们，Lean 允许我们编写 `[Group G]` 并匿名化名称。
您可能已经注意到，Lean 会自动选择像 `_inst_1` 这样的名称。
当我们使用带有 `variables` 命令的匿名方括号注释时，只要变量仍在范围内，
Lean 会自动将参数 `[Group G]` 添加到任何提到 `G` 的定义或定理中。

我们如何注册 Lean 需要使用的信息以执行搜索？回到我们的群的例子，我们只需要做两个更改。
首先，我们使用关键字 `class` 而不是 `structure` 来定义群结构，以指示它是类推断的候选者。
其次，我们使用关键字 `instance` 而不是 `def` 来注册特定实例。
与类变量的名称一样，我们允许实例定义匿名，因为通常我们希望 Lean 找到它并使用它，而不会用细节困扰我们。
-/

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

/-
以下说明了它们的用法。
-/

#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

/-
`#check` 命令显示 `Group₂.mul` 有一个隐式参数 `[Group₂ α]`，
我们期望通过类推断找到它，其中 `α` 是 `Group₂.mul` 参数的类型。
换句话说，`{α : Type*}` 是群元素类型的隐式参数，而 `[Group₂ α]` 是 `α` 上群结构的隐式参数。
类似地，当我们为 `Group₂` 定义一个通用平方函数 `my_square` 时，
我们使用 `{α : Type*}` 作为元素类型的隐式参数，并使用 `[Group₂ α]` 作为 `Group₂` 结构的隐式参数。

在第一个示例中，当我们编写 `Group₂.mul f g` 时，`f` 和 `g` 的类型告诉 Lean，
在 `Group₂.mul` 的参数 `α` 中必须实例化为 `Equiv.Perm β`。
这意味着 Lean 必须找到一个 `Group₂ (Equiv.Perm β)` 的元素。
之前的实例声明告诉 Lean 如何做到这一点。问题解决了！

这种用于注册信息的简单机制非常有用，以便 Lean 在需要时可以找到它。
以下是它的一种应用方式。在 Lean 的基础中，数据类型 `α` 可能为空。
然而，在许多应用中，知道一个类型至少有一个元素是有用的。
例如，函数 `List.headI` 返回列表的第一个元素，可以在列表为空时返回默认值。
为了实现这一点，Lean 库定义了一个类 `Inhabited α`，它所做的只是存储一个默认值。
我们可以显示 `Point` 类型是一个实例：
-/

structure Point where
  x : ℤ
  y : ℤ
  z : ℤ

def Point.add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

instance : Inhabited Point where
  default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl

/-
类推断机制也用于通用符号。表达式 `x + y` 是 `Add.add x y` 的缩写，
其中`Add α` 是一个类，它存储了 `α` 上的二元函数。编写 `x + y` 告诉 Lean 找到一个已注册的 `[Add.add α]` 实例并使用相应的函数。
下面，我们为 `Point` 注册加法函数。
-/

instance : Add Point where
  add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end

/-
通过这种方式，我们也可以将符号 `+` 分配给其他类型上的二元操作。

但我们还可以做得更好。我们已经看到 `*` 可以在任何群中使用，
`+` 可以在任何加法群中使用，并且两者都可以在任何环中使用。
当我们在 Lean 中定义一个新的环实例时，我们不必为该实例定义 `+` 和 `*`，
因为 Lean 知道这些是为每个环定义的。我们可以使用这种方法为我们的 `Group₂` 类指定符号：
-/

instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end

/-
这种方法之所以有效，是因为 Lean 执行递归搜索。根据我们声明的实例，
Lean 可以通过找到 `Group₂ (Equiv.Perm α)` 的实例来找到 `Mul (Equiv.Perm α)` 的实例，
并且它可以找到 `Group₂ (Equiv.Perm α)` 的实例，因为我们已经提供了一个。
Lean 能够找到这两个事实并将它们链接在一起。

类推断是微妙的，使用时必须小心，因为它无形中控制了我们键入的表达式的解释。
然而，如果明智地使用，类推断是一个强大的工具。它使 Lean 中的代数推理成为可能。
-/

/-
## 练习

证明之前定义的2*2矩阵, 构成一个环. 以下代码已经写好可供使用. 你可能需要添加更多引理作为准备.
-/

@[ext]
structure Vec2D where
  x : ℝ
  y : ℝ

namespace Vec2D

@[simp] def smul (n : ℝ) (v : Vec2D) : Vec2D := ⟨n * v.x, n * v.y⟩

instance : Add Vec2D where
  add := fun v1 v2 => ⟨v1.1 + v2.1, v1.2 + v2.2⟩

instance : Zero Vec2D where
  zero := ⟨0, 0⟩

instance : Neg Vec2D where
  neg := fun v => ⟨-v.1, -v.2⟩

@[simp] lemma add_def (v1 v2 : Vec2D) : v1 + v2 = ⟨v1.1 + v2.1, v1.2 + v2.2⟩ := rfl
@[simp] lemma zero_def : (0 : Vec2D) = ⟨0, 0⟩ := rfl
@[simp] lemma neg_def (v : Vec2D) : -v = ⟨-v.1, -v.2⟩ := rfl

theorem add_comm (v1 v2 : Vec2D) : v1 + v2 = v2 + v1 := by
  ext <;> simp <;> linarith

theorem add_assoc (v1 v2 v3 : Vec2D) : (v1 + v2) + v3 = v1 + (v2 + v3) := by
  ext <;> simp <;> linarith

instance : AddCommGroup Vec2D where
  add_comm := add_comm
  add_assoc := add_assoc
  zero_add := fun v => by ext <;> simp
  add_zero := fun v => by ext <;> simp
  neg_add_cancel := fun v => by ext <;> simp
  nsmul := fun n v => ⟨n * v.1, n * v.2⟩
  zsmul := fun z v => ⟨z * v.1, z * v.2⟩
  nsmul_zero := fun v => by ext <;> simp
  nsmul_succ := fun n v => by ext <;> dsimp <;> push_cast <;> linarith
  zsmul_zero' := fun v => by ext <;> simp
  zsmul_succ' := fun n v => by ext <;> dsimp <;> push_cast <;> linarith
  zsmul_neg' := fun n v => by ext <;> dsimp <;> push_cast <;> linarith

end Vec2D

@[ext]
structure Mat2D where
  fstc : Vec2D
  sndc : Vec2D

namespace Mat2D

@[simp] def zero : Mat2D := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
@[simp] def one : Mat2D := ⟨⟨1, 0⟩, ⟨0, 1⟩⟩
@[simp] def add (m1 m2 : Mat2D) : Mat2D where
  fstc := ⟨m1.fstc.x + m2.fstc.x, m1.fstc.y + m2.fstc.y⟩
  sndc := ⟨m1.sndc.x + m2.sndc.x, m1.sndc.y + m2.sndc.y⟩
@[simp] def mul (m1 m2 : Mat2D) : Mat2D where
  fstc := {
    x := m1.fstc.x * m2.fstc.x + m1.sndc.x * m2.fstc.y
    y := m1.fstc.y * m2.fstc.x + m1.sndc.y * m2.fstc.y
  }
  sndc := {
    x := m1.fstc.x * m2.sndc.x + m1.sndc.x * m2.sndc.y
    y := m1.fstc.y * m2.sndc.x + m1.sndc.y * m2.sndc.y
  }
@[simp] def mul_vec (m : Mat2D) (v : Vec2D) : Vec2D where
  x := m.fstc.x * v.x + m.sndc.x * v.y
  y := m.fstc.y * v.x + m.sndc.y * v.y

theorem mul_assoc (m1 m2 m3 : Mat2D) : (m1.mul m2).mul m3 = m1.mul (m2.mul m3) := by
  ext <;> simp <;> linarith

theorem add_comm (m1 m2 : Mat2D) : m1.add m2 = m2.add m1 := by
  ext <;> simp <;> linarith

theorem add_assoc (m1 m2 m3 : Mat2D) : (m1.add m2).add m3 = m1.add (m2.add m3) := by
  ext <;> simp <;> linarith

theorem zero_mul (m : Mat2D) : zero.mul m = zero := by ext <;> simp

theorem mul_zero (m : Mat2D) : m.mul zero = zero := by ext <;> simp

theorem mul_one (m : Mat2D) : m.mul one = m := by ext <;> simp

theorem one_mul (m : Mat2D) : one.mul m = m := by ext <;> simp

theorem zero_add (m : Mat2D) : zero.add m = m := by ext <;> simp

theorem add_zero (m : Mat2D) : m.add zero = m := by ext <;> simp

instance : Zero Mat2D where
  zero := zero

instance : Add Mat2D where
  add := Mat2D.add

instance : Neg Mat2D where
  neg m := {
    fstc := -m.fstc
    sndc := -m.sndc
  }

instance : Ring Mat2D where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  add_comm := sorry
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  sub := sorry
  sub_eq_add_neg := sorry
  zsmul := zsmulRec
  neg_add_cancel := sorry
  intCast := sorry
  intCast_ofNat := sorry
  intCast_negSucc := sorry

end Mat2D

end Class

namespace Hierarchies

/-
# Hierarchies
-/

/-
At the very bottom of all hierarchies in Lean, we find
data-carrying classes. The following class records that the given
type α is endowed with a distinguished element called one. At this
stage, it has no property at all.
-/
class One₁ (α : Type) where
  /-- The element one -/
  one : α

#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

example (α : Type) [One₁ α] : α := One₁.one

/-
Our next task is to assign a notation to One₁.one. Since we don’t
want collisions with the builtin notation for 1, we will use 𝟙.
This is achieved by the following command where the first line
tells Lean to use the documentation of One₁.one as documentation
for the symbol 𝟙.
-/

@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl

/-
We now want a data-carrying class recording a binary operation. We
don’t want to choose between addition and multiplication for now
so we’ll use diamond.
-/

class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia

/-
Let us now define the class of semigroup structures where the
operation is denoted by ⋄. For now, we define it by hand as a
structure with two fields, a Dia₁ instance and some Prop-valued
field dia_assoc asserting associativity of ⋄.
-/
class Semigroup₀ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

/-
Note that while stating dia_assoc, the previously defined field
toDia₁ is in the local context hence can be used when Lean
searches for an instance of Dia₁ α to make sense of a ⋄ b. However
this toDia₁ field does not become part of the type class instances
database. Hence doing example {α : Type} [Semigroup₁ α] (a b : α)
: α := a ⋄ b would fail with error message failed to synthesize
instance Dia₁ α.
-/

attribute [instance] Semigroup₀.toDia₁

example {α : Type} [Semigroup₀ α] (a b : α) : α := a ⋄ b

/-
Before building up, we need to use a different syntax to add this
toDia₁ field, to tell Lean that Dia₁ α should be treated as if its
fields were fields of Semigroup₁ itself. This also conveniently
adds the toDia₁ instance automatically. The class command supports
this using the extends syntax as in:
-/
class Semigroup₁ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

/-
Let us now try to combine a diamond operation and a distinguished
one element with axioms saying this element is neutral on both
sides.
-/

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙

/-
Note that we don’t need to include extra fields where combining
existing classes. Hence we can define monoids as:
-/

class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α

/-
While the above definition seems straightforward, it hides an
important subtlety. Both Semigroup₁ α and DiaOneClass₁ α extend
Dia₁ α, so one could fear that having a Monoid₁ α instance gives
two unrelated diamond operations on α, one coming from a field
Monoid₁.toSemigroup₁ and one coming from a field Monoid₁.
toDiaOneClass₁.

Indeed if we try to build a monoid class by hand using:

-/

class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

/-
then we get two completely unrelated diamond operations
Monoid₂.toSemigroup₁.toDia₁.dia and Monoid₂.toDiaOneClass₁.toDia₁.dia.

The version generated using the extends syntax does not have this defect.
-/

example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α)
(toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α]
(one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁

/-
We are now very close to defining groups. We could add to the
monoid structure a field asserting the existence of an inverse for
every element. But then we would need to work to access these
inverses. In practice it is more convenient to add it as data. To
optimize reusability, we define a new data-carrying class, and
then give it some notation.
-/
class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]


export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)

example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]

/-
It is now your turn to prove things about our algebraic structures.
-/

lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
  sorry

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
  sorry


/-
At this stage we would like to move on to define rings, but there
is a serious issue. A ring structure on a type contains both an
additive group structure and a multiplicative monoid structure,
and some properties about their interaction. But so far we
hard-coded a notation ⋄ for all our operations. More
fundamentally, the type class system assumes every type has only
one instance of each type class. There are various ways to solve
this issue. Surprisingly Mathlib uses the naive idea to duplicate
everything for additive and multiplicative theories with the help
of some code-generating attribute. Structures and classes are
defined in both additive and multiplicative notation with an
attribute to_additive linking them.
-/

class AddSemigroup₃ (α : Type) extends Add α where
  /-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
  /-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1

attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

/-
# Exercises
As an exercise you can now set up a simple hierarchy for order
relations, including a class for ordered commutative monoids,
which have both a partial order and a commutative monoid structure
such that ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b. Of course you
need to add fields and maybe extends clauses to the following
classes.
-/

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)

class PartialOrder₁ (α : Type)

class OrderedCommMonoid₁ (α : Type)

instance : OrderedCommMonoid₁ ℕ where

end Hierarchies
