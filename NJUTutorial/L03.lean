import Mathlib.Tactic
namespace L03
/-!
# structure关键词

## 基本用法

在之前的课程中，我们已经学习了认识 Lean 中基本的类型，并能够使用一些基础的tactic进行简单
的定理证明。下面，我们要开始学习如何定义新的类型，从而能够用 Lean 实现数学中的各种结构。

我们从简单的 ℝ² 中的点开始，这一类型的值应当具备两个属性，即其 x 轴与 y 轴的坐标。使用
structure关键词，我们可以这样定义：
-/
@[ext]
structure Point where
  x : ℝ
  y : ℝ

#check Point

/-
structure L03.Point : Type
number of parameters: 0
fields:
  L03.Point.x : ℝ
  L03.Point.y : ℝ
constructor:
  L03.Point.mk (x y : ℝ) : Point
-/
#print Point

/-!
`#print` 命令能够告诉我们许多与该structure有关的信息，比如该结构中包含哪些属性，如何构造
该类型的值等。其中constructor与我们知道的tactic `constructor` 同名，实际上含义也相同，
一个类型的constructor就是它的值的构造方法，此处为 `Point.mk`。

我们可以修改这一constructor的命名，使用如下的语法将其改为 `Point.new`：

```lean4
structure Point where
new ::
  x : ℝ
  y : ℝ
```

structure命令还帮我们生成了以下函数：
-/

#check Point.mk
#check Point.x
#check Point.y

/-!
先前我们在structure上标注的 `@[ext]` 实际上为我们额外生成了如下函数，同时也让我们能够对
`Point` 结构使用 `ext` 这个tactic。

这些函数本质上是在说，要证明两个 `Point` 的实例相等，等价于证明其属性相等。
-/
#check Point.mk.injEq -- 没有 `@[ext]` 也存在该函数
#check Point.ext
#check Point.ext_iff

example (p q : Point) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  ext <;> assumption

/-!
我们有许多种构造 `Point` 类型的值的方法。
-/

-- 1. 使用 `⟨·, ·⟩` 这一记号，Lean会调用你正在构造的值的类型的构造函数
def p1 : Point := ⟨1, 1⟩

-- 2. 直接使用构造函数
def p2 : Point := Point.mk 1 1

-- 3. 使用 `where`
def p3 : Point where
  x := 1
  y := 1

-- 4. 使用 `{}` 记号
def p4 : Point := {
  x := 1, y := 1
}

-- 5. 使用tactic mode与constructor （不推荐）
def p5 : Point := show_term by
  constructor
  · exact 1
  · exact 1

/-!
**本质上constructor就是使用了要构造的值的类型的第一个构造函数**
-/

#print And
section
variable {p q : Prop} (hp : p) (hq : q)

example : p ∧ q := ⟨hp, hq⟩
example : p ∧ q := And.intro hp hq
example : p ∧ q where
  left := hp
  right := hq
example : p ∧ q := {
  left := hp, right := hq
}
example : p ∧ q := by
  constructor <;> assumption
end

/-!
我们也可以用structure定义函数类型，实际上是定义了一族类型。
-/
structure GeneralPoint (α : Type) where
  x : α
  y : α

#check GeneralPoint
#print GeneralPoint

#print Prod

/-!
structure中的属性也可以是命题类型。你还可以指定属性的默认值，在构造时不给出对应位置的属性
则采用默认值。
-/
structure SpecialNumber where
  val : ℕ
  property : Nat.Prime val := by decide

#print SpecialNumber
def sn₁ : SpecialNumber := SpecialNumber.mk 2
def sn₂ : SpecialNumber := ⟨2, by decide⟩ -- 使用 `⟨·, ·⟩` 时默认值不生效，必须给出
def sn₃ : SpecialNumber where
  val := 3

-- 看看有理数是怎么定义的
#print Rat

/-!
你也可以定义命题类型。
-/
structure IsSpecialPoint (p : GeneralPoint ℕ) : Prop where
  x_prime : Nat.Prime p.x := by decide
  y_prime : Nat.Prime p.y := by decide

example : IsSpecialPoint ⟨2, 3⟩ where

/-!
你还可以把某个结构具体需要满足的性质写成predicate，用类型对性质进行编码。
-/
structure SpecialPoint (prop : Point → Prop) where
  point : Point
  property : prop point

#print SpecialPoint

def sp₁ : SpecialPoint (fun p => Odd p.x ∧ Odd p.y) where
  point := ⟨1, 3⟩
  property := by
    constructor <;> norm_num

/-!
此时我们可以回顾我们之前讲Set时碰到的Subtype了，这是典型的structure的例子，同时使用了
我们上面所述的技巧。
-/
#print Subtype

#check Subtype (fun (p : Point) => Odd p.x)
#check { p : Point // Odd p.x }

/-!
当你想要使用某个structure的term中的具体属性时，既可以使用属性名访问，也可以用 `.1` `.2`
访问，Lean 默认按顺序提取其中的值。
-/

#check p1.1
#check p1.2

/-!
在下面的例子中，我们看到 `⟨·, ·⟩` 可以嵌套使用，并且我们在构造具体值时随时可以通过 `by`
进入tactic mode。
-/
def sp₂ : { p : Point // Odd p.x } := ⟨⟨1, 3⟩, by norm_num⟩

section

variable {α : Type} (s : Set α) (a : s)

-- `↑` 表示发生了隐式类型转换，此时可通过鼠标悬浮查看具体转换过程
#check a
#check a.1
#check a.2

#print Set.Elem

#print Set.Subset
example (t : Set α) (h : s ⊆ t) : a.1 ∈ t := by
  apply h
  exact a.2

end

/-!
属性当然也可以是函数。
-/
structure SpecialFunction (α β : Type) (prop : (α → β) → Prop) where
  f : α → β
  property : prop f

/-!
**思考题**：现在你有多少种方法来表达如下数学概念？
1. 小于等于10的自然数。
2. ℝ²中与原点距离为某一给定值的点。
3. 等价关系。
-/


/-!
## Dot Notation

下面我们来定义 `Point` 有关的一些运算，同时介绍 Lean 中一个便利的语法糖 Dot Notation。
在开始前，我们先创建 `Point` 命名空间，使得所有在该命名空间中的函数均具有前缀 `Point`。
-/

namespace Point

def add (p1 p2 : Point) : Point := ⟨p1.x + p2.x, p1.y + p2.y⟩
def sub (p1 p2 : Point) : Point := ⟨p1.x - p2.x, p1.y - p2.y⟩
def mul (p1 p2 : Point) : Point := ⟨p1.x * p2.x, p1.y * p2.y⟩

#check add p1 p2
#check sub p1 p2
#check mul p1 p2

/-!
除上述标准的函数调用写法外，我们还可以把第一个参数前置。
-/

#check p1.add p2
#check p1.sub p2
#check p1.mul p2

/-!
这一用法与上面的标准用法等价。

实际上，当你写出 `a.func` 时，如果 `a` 的类型为 `A`，且上下文中存在函数名为 `A.func`，
并且 `A.func` 的第一个参数类型为 `A`，那么 Lean 就能够将该表达式解析为 `A.func a`。
这种记法在 Lean 中被称为 Dot Notation。
-/

#check p1.add

/-!
Dot Notation把函数应用从前缀变为了我们习惯的中缀，而我们还可以更进一步，将其绑定到一个
运算符上。使用 `infixl:{priority} "{operator}" => func` 语法，我们就可以实现这一效果。
-/

infixl:42 " +ₚ " => add

#check p1 +ₚ p2

/-!
相应的，还有前缀与后缀的定义，分别为 `prefix` 与 `postfix`，典型的例子有 `¬` 与 `⁻¹`。

这时我们自然想到，一般的运算符如 `+` `*` 等是不是也绑定到了某个函数上，答案是肯定的。
事实上，你可以用如下的写法来查看某个记号所对应的函数。而之所以这些运算符能够支持各种
不同类型的值之间的运算，而不支持该运算的结构也无法使用这些运算符，便要归功于 Lean 的
Typeclass系统，我们将在后面的课程中具体介绍。
-/

#check (· + ·)
#check (·⁻¹)
#check (¬·)

/-!
除了运算符以外，我们还会意识到，如 `1` 和 `0` 这样具备特殊意义的数值，在不同类型中实际
对应了不同的具体常量。我们可以通过 `notation` 命令把常量绑定到符号上，但依然是靠Typeclass
才能实现上述的效果。
-/

notation "P₁" => p1

#check P₁

#check Nat.totient

/-!
为了便利，我们在这里把 `Point` 上的加法和乘法绑定到 `+` 和 `*` 上，并绑定 `1` 与 `0`。
你目前不需要理解下面代码的意思。
-/

instance : Add Point where
  add := add

instance : Mul Point where
  mul := mul

instance : Zero Point where
  zero := ⟨0, 0⟩

instance : One Point where
  one := ⟨1, 1⟩

/-!
此时我们就可以写 `p1 + p2` 了，但也带来一个问题，即你无法使用 `rw [Point.add]` 这样的
方式将加法定义展开了。此时我们需要手动添加如下引理。
-/

@[simp] theorem add_def (p1 p2 : Point) : p1 + p2 = ⟨p1.x + p2.x, p1.y + p2.y⟩ :=
  rfl
@[simp] theorem mul_def (p1 p2 : Point) : p1 * p2 = ⟨p1.x * p2.x, p1.y * p2.y⟩ :=
  rfl
@[simp] theorem zero_def : (0 : Point) = ⟨0, 0⟩ := rfl
@[simp] theorem one_def : (1 : Point) = ⟨1, 1⟩ := rfl

/-!
此处引理前的 `@[simp]` 标记涉及到 Lean 中一个非常强大的tactic，即 `simp`。有时候我们面对
的表达式会非常复杂，此时手动化简会让证明过程变得非常繁琐，而 `simp` 提供了一套强大的搜索
与改写系统，可以自动从环境中能访问到的用上述标记标记为 `simp` 引理的定理对当前表达式进行
改写。

注意，`simp` 只能根据引理把等号左边改写到右边，故需保证等号右边一定比等号左边简单，否则
无法成为 `simp` 引理。

`simp` 还有多种变体，比如 `dsimp`，其只会调用能通过 `rfl` 证明的引理，比如上面两条。

`simp?` 可查看具体使用了哪些引理，并可将代码改写为 `simp only [...]`，即只使用给定的
引理进行化简。

`simp` 将是你们后续最常用的tactic，在任何步骤都可以使用一下，或许会有惊喜。
-/
#help tactic simp

/-!
**练习**
证明以下定理，注意使用 `ext` `simp` 等tactic。

请把证明控制在一行。
-/

theorem add_comm (p1 p2 : Point) : p1 + p2 = p2 + p1 := by
  ext <;> simp <;> linarith

theorem add_assoc (p1 p2 p3 : Point) : p1 + p2 + p3 = p1 + (p2 + p3) := by
  ext <;> simp <;> linarith

theorem mul_comm (p1 p2 : Point) : p1 * p2 = p2 * p1 := by ext <;> simp <;> linarith

theorem mul_assoc (p1 p2 p3 : Point) : p1 * p2 * p3 = p1 * (p2 * p3) := by ext <;> simp <;> linarith

theorem mul_add (p1 p2 p3 : Point) : p1 * (p2 + p3) = p1 * p2 + p1 * p3 := by
ext <;> simp <;> linarith

theorem add_mul (p1 p2 p3 : Point) : (p1 + p2) * p3 = p1 * p3 + p2 * p3 := by
ext <;> simp <;> linarith

theorem zero_add (p : Point) : 0 + p = p := by ext <;> simp

theorem add_zero (p : Point) : p + 0 = p := by ext <;> simp

theorem one_mul (p : Point) : 1 * p = p := by ext <;> simp

theorem mul_one (p : Point) : p * 1 = p := by ext <;> simp

/-!
完成上述练习，你大概就会理解 `simp` 的强大。
-/
end Point

/-!
## 继承

数学中常常出现，在已有的代数结构上添加一些性质或运算，就得到了新的结构，同时还能使用先前
结构上的结论。在 Lean 中，我们也可以从一个structure出发，通过继承机制不断创造新的子类。

下面的例子中，`deriving Repr` 是让 Lean 能够在 InfoView中展示该structure的值。
-/

structure A where
  x : Nat
deriving Repr

structure B extends A where
  y : Nat
deriving Repr

structure C extends A where
  z : Nat
deriving Repr

structure D extends B, C
deriving Repr

#print A
#print B
#print C
#print D

#check D.toB
#check D.toC

def d : D := ⟨⟨⟨1⟩, 2⟩, 3⟩
#eval d

def d' : D where
  toC := ⟨⟨1⟩, 2⟩
  y := 3

#eval d.x
#eval d.y
#eval d.z
#eval d
#eval d'

/-!
可以看到，在上述例子中，D 实际上的属性为 `toB` 与 `z`，同时也可以是 `toC` 与 `y`。不要
理解成 D 的值里有个 B 或者 C，而是 D 从 B 和 C 处继承了对应的属性，D 有着自己的 `x` `y`
`z`，`toB` 与 `toC` 不是从值里取出一个父类的对象，而是用自己的属性构造出父类的值。

不要与Python等语言混淆，此处的 `toB` 与 `toC` 依然是纯函数，是用 D 的一个值计算出对应的
B、C 的值。

虽然没有自动生成一个 `D.toA`，但这只是因为我们没有 `extends A`，下面的定义得到的结构与
D 数学意义上是一样的，但有 `toA`，构造函数也略有不同。
-/

structure D' extends A, B, C where

#print D'

def d'' : D' := ⟨⟨1⟩, 2, 3⟩

inductive Color
  | red
  | green
  | yellow

#print Nat

inductive MyNat where
  | succ : MyNat → MyNat
  | zero : MyNat

#print MyNat
#check MyNat.zero
#check MyNat.succ MyNat.zero

#print List

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

#check MyList.nil
#check MyList.cons 2 MyList.nil

inductive Point' where
  | mk (x : ℝ) (y : ℝ) : Point'

#check Point.x

#check Point'.mk 1 2

def Point'.x (p : Point') : ℝ :=
  match p with
  | mk (x : ℝ) (y : ℝ) => by exact x

#print Option

example : MyNat := show_term by
  constructor
  exact MyNat.zero

/-!
## 例子：二维矩阵

下面我们定义 ℝ 上的二维矩阵，以及其运算。
-/

@[ext]
structure Vec2D where
  x : ℝ
  y : ℝ

namespace Vec2D

@[simp] def add (v1 v2 : Vec2D) : Vec2D := ⟨v1.x + v2.x, v1.y + v2.y⟩
@[simp] def zero : Vec2D := ⟨0, 0⟩
@[simp] def neg (v : Vec2D) : Vec2D := ⟨-v.x, -v.y⟩
@[simp] def smul (n : ℝ) (v : Vec2D) : Vec2D := ⟨n * v.x, n * v.y⟩

@[simp] def mul (v1 v2 : Vec2D) : ℝ := v1.x * v2.x + v1.y * v2.y

theorem add_comm (v1 v2 : Vec2D) : v1.add v2 = v2.add v1 := by
  ext <;> simp <;> linarith

theorem add_assoc (v1 v2 v3 : Vec2D) : (v1.add v2).add v3 = v1.add (v2.add v3) := by
  ext <;> simp <;> linarith

theorem zero_add (v : Vec2D) : zero.add v = v := by ext <;> simp

theorem add_zero (v : Vec2D) : v.add zero = v := by ext <;> simp

theorem neg_add_cancel (v : Vec2D) : (neg v).add v = zero := by
  ext <;> simp

end Vec2D

@[ext]
structure Mat2D where
  fstc : Vec2D
  sndc : Vec2D

namespace Mat2D

@[simp] def zero : Mat2D := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
@[simp] def one : Mat2D := ⟨⟨1, 0⟩, ⟨0, 1⟩⟩

@[simp] def add (m1 m2 : Mat2D) : Mat2D where
  fstc := m1.fstc.add m2.fstc
  sndc := m1.sndc.add m2.sndc

@[simp] def fstr (m : Mat2D) : Vec2D := ⟨m.fstc.x, m.sndc.x⟩
@[simp] def sndr (m : Mat2D) : Vec2D := ⟨m.fstc.y, m.sndc.y⟩

@[simp] def mul (m1 m2 : Mat2D) : Mat2D where
  fstc := ⟨m1.fstr.mul m2.fstc, m1.sndr.mul m2.fstc⟩
  sndc := ⟨m1.fstr.mul m2.sndc, m1.sndr.mul m2.sndc⟩

@[simp] def mul_vec (m : Mat2D) (v : Vec2D) : Vec2D where
  x := m.fstr.mul v
  y := m.sndr.mul v

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
end Mat2D

/-!
在上面的例子里我们仅定义了矩阵的基本运算并证明了其最简单的性质，后续我们学习Typeclass后
将对以上定义进行改写。
-/

#print Complex
/-!
**习题**

今天的习题不会直接给出题目，请根据以下自然语言描述自行定义structure并证明相关定理。

1. 定义 `MyComplex` 类型，即复数，包含实部与虚部，并定义其上的加法、乘法、取负，以及
复数的0和1，然后证明其具有交换环结构，参考以下定理，顺序不限。然后，证明不存在平方为-1
的实数，但存在平方为-1的 `MyComplex`。
-/
#check add_assoc
#check add_comm
#check zero_add
#check add_zero
#check left_distrib
#check right_distrib
#check zero_mul
#check mul_zero
#check mul_assoc
#check one_mul
#check mul_one
#check neg_add_cancel
#check mul_comm


/-!
2. 定义 `MyGaussian` 类型，即把 `MyComplex` 中实部与虚部限定在整数上。将上面对 `MyComplex`
做的工作重新做一遍，然后定义 `MyGaussian → ℤ` 的函数 `norm` (norm (a, b) = a² + b²)。证明
以下定理：
- norm (x * y) = norm x * norm y
- 0 ≤ norm x
-/

/-!
3. 基于上面给出的 `Vec2D` 和 `Mat2D` 的定义，尝试定义线性无关与行列式，思考如何定义
矩阵可逆，并尝试证明矩阵的左逆等于右逆。
-/

end L03
