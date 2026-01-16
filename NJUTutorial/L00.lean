/-
This file is intended for Lean beginners. The goal is to demonstrate what it feels like to prove
things using Lean and mathlib. Complicated definitions and theory building are not covered.
Everything is covered again more slowly and with exercises in the next files.
-/
-- We want real numbers and their basic properties
import Mathlib.Data.Real.Basic
-- We want to be able to use Lean's built-in "help" functionality
import Mathlib.Tactic



/-!

## Introduction of basic usage

Lean community website:
https://leanprover-community.github.io/

The online version of Lean:
https://live.lean-lang.org/

Mathlib documentation page:
https://leanprover-community.github.io/mathlib4_docs/
-/

open Nat

-- These are pieces of data.
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f

-- These are propositions, of type `Prop`.
#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem

-- These are proofs of propositions.
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard


/-!
## What is a proof in Lean?
-/

/-
1. Everything in Lean has a type.
Here are some examples of types.
`#check <expression>` in a Lean file shows the type of `<expression>`.
`a : A` means "the type of `a` is `A`" or "`a` is an element of type `A`".
This is not a statement you can prove or disprove inside Lean, it's a fact that is
true or not.
-/

-- a specific natural number
#check 42

-- the type of natural numbers
#check Nat
#check ℕ


-- a specific function
#check succ

-- a specific function
#check fun x : ℕ ↦ x + 3

#check succ 42
#eval succ 42

#check (fun x : ℕ ↦ x + 3) 42
#eval (fun x : ℕ ↦ x + 3) 42

-- the type of functions from Nat to Nat
#check Nat → Nat

#check 1 < 3

#check Prop

#check Type

#check ℚ

#check ℝ

#check IsRefl

/-
2. Terms of type `Prop` are propositions.
When we try to prove or disprove mathematical statements, the targets are propositions.
-/
#check True

#check False

#check 2 + 2 = 5

#check ∃ x : ℕ, x > 5

#check True = False

/-
3. Terms of propositions are proofs.
When we prove a proposition `P`, we construct a term of type `P`.
-/

#check trivial

-- There is no term of type False, but we have:
#check False.elim

theorem something_right : 2 + 2 = 4 := by
  rfl

theorem something_wrong : 2 + 2 = 5 := sorry

#check something_wrong

-- We use variables to add assumptions to our context.
-- Here `P` and `Q` are arbitrary propositions.
-- `hp : P` is an assumption that `P` is true, i.e., we have a proof of `P`.
-- `f : P → Q` is an assumption that `P` implies `Q`, i.e., we have a proof of `P → Q`.
variable (P Q : Prop) (hp : P) (f : P → Q)

#check hp

#check P → Q

-- A proof of `P → Q` is a function that turns a proof of `P` into a proof of `Q`.
#check f hp

/-
One can use `show_term` to see the proof term of a theorem.
-/
theorem induction_ex (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.succ_add, ih]

/-!
## Some examples of proofs in Lean
-/

-- We want to be able to define functions using the law of excluded middle
noncomputable section


/-
Our first goal is to define the set of upper bounds of a set of real numbers.
This is already defined in mathlib (in a more general context), but we repeat
it for the sake of exposition. Right-click "upperBounds" below to get offered
to jump to mathlib's version
-/
#check upperBounds

/-- The set of upper bounds of a set of real numbers ℝ -/
def upBounds (A : Set ℝ) :=
  { x : ℝ | ∀ a ∈ A, a ≤ x }

/-- Predicate `is_maximum a A` means `a` is a maximum of `A` -/
def IsMaximum (a : ℝ) (A : Set ℝ) :=
  a ∈ A ∧ a ∈ upBounds A

/-
In the above definition, the symbol `∧` means "and". We also see the most
visible difference between set theoretic foundations and type theoretic ones
(used by almost all proof assistants). In set theory, everything is a set, and the
only relation you get from foundations are `=` and `∈`. In type theory, there is
a meta-theoretic relation of "typing": `a : ℝ` reads "`a` is a real number" or,
more precisely, "the type of `a` is `ℝ`". Here "meta-theoretic" means this is not a
statement you can prove or disprove inside the theory, it's a fact that is true or
not. Here we impose this fact, in other circumstances, it would be checked by the
Lean kernel.
By contrast, `a ∈ A` is a statement inside the theory. Here it's part of the
definition, in other circumstances it could be something proven inside Lean.
-/
/- For illustrative purposes, we now define an infix version of the above predicate.
It will allow us to write `a is_a_max_of A`, which is closer to a sentence.
-/
infixl:55 " is_a_max_of " => IsMaximum

/-
Let's prove something now! A set of real numbers has at most one maximum. Here
everything left of the final `:` is introducing the objects and assumption. The equality
`x = y` right of the colon is the conclusion.
-/
theorem unique_max (A : Set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y := by
  -- We first break our assumptions in their two constituent pieces.
  -- We are free to choose the name following `with`
  rcases hx with ⟨x_in, x_up⟩
  rcases hy with ⟨y_in, y_up⟩
  -- Assumption `x_up` means x isn't less than elements of A, let's apply this to y
  specialize x_up y
  -- Assumption `x_up` now needs the information that `y` is indeed in `A`.
  specialize x_up y_in
  -- Let's do this quicker with roles swapped
  specialize y_up x x_in
  -- We explained to Lean the idea of this proof.
  -- Now we know `x ≤ y` and `y ≤ x`, and Lean shouldn't need more help.
  -- `linarith` proves equalities and inequalities that follow linearly from
  -- the assumption we have.
  linarith

/-
The above proof is too long, even if you remove comments. We don't really need the
unpacking steps at the beginning; we can access both parts of the assumption
`hx : x is_a_max_of A` using shortcuts `hx.1` and `hx.2`. We can also improve
readability without assistance from the tactic state display, clearly announcing
intermediate goals using `have`. This way we get to the following version of the
same proof.
-/
example (A : Set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y := by
  have : x ≤ y := hy.2 x hx.1
  have : y ≤ x := hx.2 y hy.1
  linarith

/-
Notice how mathematics based on type theory treats the assumption
`∀ a ∈ A, a ≤ y` as a function turning an element `a` of `A` into the statement
`a ≤ y`. More precisely, this assumption is the abbreviation of
`∀ a : ℝ, a ∈ A → a ≤ y`. The expression `hy.2 x` appearing in the above proof
is then the statement `x ∈ A → x ≤ y`, which itself is a function turning a
statement `x ∈ A` into `x ≤ y` so that the full expression `hy.2 x hx.1` is
indeed a proof of `x ≤ y`.

One could argue a three-line-long proof of this lemma is still two lines too long.
This is debatable, but mathlib's style is to write very short proofs for trivial
lemmas. Those proofs are not easy to read but they are meant to indicate that the
proof is probably not worth reading.

In order to reach this stage, we need to know what `linarith` did for us. It invoked
the lemma `le_antisymm` which says: `x ≤ y → y ≤ x → x = y`. This arrow, which
is used both for function and implication, is right associative. So the statement is
`x ≤ y → (y ≤ x → x = y)` which reads: I will send a proof `p` of `x ≤ y` to a function
sending a proof `q'` of `y ≤ x` to a proof of `x = y`. Hence `le_antisymm p q'` is a
proof of `x = y`.

Using this we can get our one-line proof:
-/
example (A : Set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y :=
  le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)

/-
Such a proof is called a proof term (or a "term mode" proof). Notice it has no `by`.
It is directly the kind of low level proof that the Lean kernel is
consuming. Commands like `rcases`, `specialize` or `linarith` are called tactics, they
help users constructing proof terms that could be very tedious to write directly.
The most efficient proof style combines tactics with proof terms like our previous
`have : x ≤ y := hy.2 x hx.1` where `hy.2 x hx.1` is a proof term embeded inside
a tactic mode proof.

In the remaining of this file, we'll be characterizing infima of sets of real numbers
in term of sequences.
-/
/-- The set of lower bounds of a set of real numbers ℝ -/
def lowBounds (A : Set ℝ) :=
  { x : ℝ | ∀ a ∈ A, x ≤ a }

/-
We now define `a` is an infimum of `A`. Again there is already a more general version
in mathlib.
-/
def IsInf (x : ℝ) (A : Set ℝ) :=
  x is_a_max_of lowBounds A

-- Let's define it also as an infix operator
infixl:55 " is_an_inf_of " => IsInf

/-
We need to prove that any number which is greater than the infimum of A is greater
than some element of A.
-/
theorem inf_lt {A : Set ℝ} {x : ℝ} (hx : x is_an_inf_of A) : ∀ y, x < y → ∃ a ∈ A, a < y := by
  -- Let `y` be any real number.
  intro y
  -- Let's prove the contrapositive
  contrapose
  -- The symbol `¬` means negation. Let's ask Lean to rewrite the goal without negation,
  -- pushing negation through quantifiers and inequalities
  push_neg
  -- Let's assume the premise, calling the assumption `h`
  intro h
  -- `h` is exactly saying `y` is a lower bound of `A` so the second part of
  -- the infimum assumption `hx` applied to `y` and `h` is exactly what we want.
  exact hx.2 y h


/-!
## Lean Basics and Tactics: rfl, exact, rw
-/

/-
### How to read a theorem/definition
-/
theorem /-name-/ first_example /-parameters-/ (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : /-conclusion (type)-/ a * (b * e) = c * (d * f) := by /-proof-/
  rw [h']
  rw [← mul_assoc]
  rw [h]
  exact mul_assoc c d f

def /-name-/ g /-parameters-/ (x : ℕ) : /-type (optional)-/ ℕ := /-construction-/
  x + 3

/-
### Implicit and explicit parameters
1. curly braces represent implicit parameters, while parentheses represent explicit parameters.
2. The function needs to fill in parameters to return a conclusion.
3. Implicit parameters do not need to be filled in, explicit parameters need to be filled in.
-/
section
theorem my_lt_trans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by
  sorry

#check (my_lt_trans : ∀ {a b c : ℕ}, a < b → b < c → a < c)

theorem one_lt_two' : 1 < 2 := by sorry
theorem two_lt_three' : 2 < 3 := by sorry

#check lt_trans one_lt_two' two_lt_three'
--lt_trans one_lt_two' two_lt_three' : 1 < 3

--example : 1 < 3 := lt_trans one_lt_two' two_lt_three'
end


/-
### exact & rfl
1. exact prove a goal that is completely consistent with the conclusion of a theorem by using it
2. rfl can prove equations where both sides are equal
-/

#check mul_assoc
example (a b c : ℝ) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (x y : ℝ) : x + 37 * y = x + 37 * y := by rfl

def h (x y : ℝ) := x + 37 * y

example (x y : ℝ) : h x y = x + 37 * y := by rfl

/-
### rw
One of the earliest kind of proofs one encounters while learning mathematics is proving by
a calculation. It may not sound like a proof, but this is actually using lemmas expressing
properties of operations on numbers. It also uses the fundamental property of equality: if two
mathematical objects A and B are equal then, in any statement involving A, one can replace A
by B. This operation is called rewriting, and the Lean "tactic" for this is `rw`.

In the following exercises, we will use the following two lemmas:
  `mul_assoc a b c : a * b * c = a * (b * c)`
  `mul_comm a b : a*b = b*a`

Hence the command
  `rw [mul_assoc a b c]`,
will replace `a*b*c` by `a*(b*c)` in the current goal.

In order to replace backward, we use
  `rw [← mul_assoc a b c]`,
replacing `a*(b*c)` by `a*b*c` in the current goal.

Of course we don't want to constantly invoke those lemmas, and we will eventually introduce
more powerful solutions.
-/

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- 0001
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

-- 0002
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

/-
Now let's return to the preceding example to experiment with what happens
if we don't give arguments to mul_assoc or mul_comm.
For instance, you can start the next proof with
  `rw [← mul_assoc]`,
Try to figure out what happens.
-/
-- 0003
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

/-
We can also perform rewriting in an assumption of the local context, using for instance
  `rw [mul_comm a b] at hyp`,
in order to replace a*b by b*a in assumption hyp.

The next example will use a third lemma:
  `two_mul a : 2*a = a + a`

Also we use the `exact` tactic, which allows to provide a direct proof term.
-/
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- Our assumption hyp is now exactly what we have to prove
/-
And the next one can use:
  `sub_self x : x - x = 0`
-/
-- 0004
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

/-
What is written in the two preceding example is very far away from what we would write on
paper. Let's now see how to get a more natural layout.
Inside each pair of curly braces below, the goal is to prove equality with the preceding line.
-/
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  calc
    c = d * a + b := by rw [hyp]
    _ = d * a + a * d := by rw [hyp']
    _ = a * d + a * d := by rw [mul_comm d a]
    _ = 2 * (a * d) := by rw [two_mul]
    _ = 2 * a * d := by rw [mul_assoc]


/-
From a practical point of view, when writing such a proof, it is convenient to:
* pause the tactic state view update in VScode by clicking the Pause icon button
  in the top right corner of the Lean Goal buffer
* write the full calculation, ending each line with ":= by {}"
* resume tactic state update by clicking the Play icon button and fill in proofs between
  curly braces.

Let's return to the other example using this method.
-/
-- 0005
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry

/-
The preceding proofs have exhausted our supply of "mul_comm" patience. Now it's time
to get the computer to work harder. The `ring` tactic will prove any goal that follows by
applying only the axioms of commutative (semi-)rings, in particular commutativity and
associativity of addition and multiplication, as well as distributivity.
-/
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  calc
    c = d * a + b := by rw [hyp]
    _ = d * a + a * d := by rw [hyp']
    _ = 2 * a * d := by ring


/-
Of course we can use `ring` outside of `calc`. Let's do the next one in one line.
-/
-- 0006
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry

/-
This is too much fun. Let's do it again.
-/
-- 0007
example (a b : ℝ) : a + b + a = 2 * a + b := by
  sorry

/-
Maybe this is cheating. Let's try to do the next computation without ring.
We could use:
`pow_two x : x^2 = x*x`
`mul_sub a b c : a*(b-c) = a*b - a*c`
`add_mul a b c : (a+b)*c = a*c + b*c`
`add_sub a b c : a + (b - c) = (a + b) - c`
`sub_sub a b c : a - b - c = a - (b + c)`
`add_zero a : a + 0 = a`
-/
-- 0008
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

/-
## Exercise Time
Fill the remaining sorries in this file and finish exercises in mathematics_in_lean/MIL/C02_Basics/S01_Calculating.lean
-/
