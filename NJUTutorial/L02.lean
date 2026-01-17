import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
In the previous file, we saw how to rewrite using equalities.
The analogue operation with mathematical statements is rewriting using
equivalences. This is also done using the `rw` tactic.
Lean uses `↔` to denote equivalence instead of `⇔` (increase font size if you don't see a difference).

In the following exercises we will use the lemma:

  `sub_nonneg {x y : ℝ} : 0 ≤ y - x ↔ x ≤ y`

The curly braces around x and y instead of parentheses mean Lean will always try to figure out what
`x` and `y` are from context, unless we really insist on telling it (we'll see how to insist much later).
Let's not worry about that for now.

In order to announce an intermediate statement we use:

  `have my_name : my statement := by`

This triggers the apparition of a new goal: proving the statement. After this is done,
the statement becomes available under the name `my_name`.
-/

example {a b c : ℝ} (hab : a ≤ b) : c + a ≤ c + b := by
  rw [← sub_nonneg]
  have key : c + b - (c + a) = b - a := by-- Here we introduce an intermediate statement named key
    -- and prove it in an idented code block (or on the same line if the proof is very short)
    ring
  -- we can now use the key statement
  rw [key]
  rw [sub_nonneg]
  exact hab

/-
Of course the previous lemma is already in the core library, named `add_le_add_left`, so we can use it below.

Let's prove a variation (without invoking commutativity of addition to reduce to the previous statement
since this would spoil our fun).
-/
-- 0009
example {a b : ℝ} (hab : a ≤ b) (c : ℝ) : a + c ≤ b + c := by
  sorry

/-
Let's see how we could use this lemma. It is already in the core library, under the name `add_le_add_right`:

  `add_le_add_right {a b : ℝ} (hab : a ≤ b) (c : ℝ) : a + c ≤ b + c`

This can be read as: "add_le_add_right is a function that will take as input real numbers `a` and `b`, an
assumption `hab` claiming `a ≤ b` and `a` real number `c`, and will output a proof of `a + c ≤ b + c`".

In addition, recall that curly braces around `a b` mean Lean will figure out those arguments unless we
insist to help. This is because they can be deduced from the next argument `hab`.
So it will be sufficient to feed `hab` and `c` to this function.
-/
example {a b : ℝ} (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact add_le_add_right ha b


/-
In the second line of the above proof, we need to prove `0 + b ≤ a + b`.
The proof after the colon says: this is exactly lemma `add_le_add_right` applied to `ha` and `b`.
Actually the `calc` block expects proof terms, and the `by` keyword is used to tell Lean we will use tactics
to build such a proof term. But since the only tactic used in this block is `exact`, we can skip
tactics entirely, and write:
-/
example (a b : ℝ) (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := add_le_add_right ha b


-- Let's do a variant.
-- 0010
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  sorry

/-
The two preceding examples are in the core library :

  `le_add_of_nonneg_left  {a b : ℝ} (ha : 0 ≤ a) : b ≤ a + b`
  `le_add_of_nonneg_right {a b : ℝ} (hb : 0 ≤ b) : a ≤ a + b`

Again, there won't be any need to memorize those names, we will
soon see how to get rid of such goals automatically.
But we can already try to understand how their names are built:
"le_add" describe the conclusion "less than or equal to some addition"
It comes first because we are focussed on proving stuff, and
auto-completion works by looking at the beginning of words.
"of" introduces assumptions. "nonneg" is Lean's abbreviation for non-negative.
"left" or "right" disambiguates between the two variations.

Let's use those lemmas by hand for now.

Note that you can have several inequalities steps in a `calc` block,
transitivity of inequalities will be used automatically to assemble
the pieces.
-/
-- 0011
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  sorry

-- And let's combine with our earlier lemmas.
-- 0012
example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  sorry

/-
In the examples above, we prepared proofs of assumptions of our lemmas beforehand, so
that we could feed them to the lemmas. This is called forward reasoning.
The `calc` proofs also belong to this category.

We can also announce the use of a lemma, and provide proofs after the fact, using
the `apply` tactic. This is called backward reasoning because we get the conclusion
first, and provide proofs later. Using `rw` on the goal (rather than on an assumption
from the local context) is also backward reasoning.

Let's do that using the lemma

  `mul_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y`
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  rw [← sub_nonneg]
  have key : b * c - a * c = (b - a) * c := by ring
  rw [key]
  apply mul_nonneg
  -- Here we don't provide proofs for the lemma's assumptions
  -- Now we need to provide the proofs.
  -- There are now two things to prove. We use the center dot (typed using `\.`) to
  -- focus on the current first goal.
  · rw [sub_nonneg]
    exact hab
  · exact hc

/-
Let's prove the same statement using only forward reasoning: announcing stuff,
proving it by working with known facts, moving forward.
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  have hab' : 0 ≤ b - a := by
    rw [← sub_nonneg] at hab
    exact hab
  have h₁ : 0 ≤ (b - a) * c := mul_nonneg hab' hc
  have h₂ : (b - a) * c = b * c - a * c := by ring
  have h₃ : 0 ≤ b * c - a * c := by
    rw [h₂] at h₁
    exact h₁
  rw [sub_nonneg] at h₃
  exact h₃

/-
One reason why the backward reasoning proof is shorter is because Lean can
infer of lot of things by comparing the goal and the lemma statement. Indeed
in the `apply mul_nonneg` line, we didn't need to tell Lean that `x = b - a`
and `y = c` in the lemma. It was infered by "unification" between the lemma
statement and the goal.

To be fair to the forward reasoning version, we should introduce a convenient
variation on `rw`. The `rwa` tactic performs rewrite and then looks for an
assumption matching the goal. We can use it to rewrite our latest proof as:
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  have hab' : 0 ≤ b - a := by rwa [← sub_nonneg] at hab
  have h₁ : 0 ≤ (b - a) * c := mul_nonneg hab' hc
  have h₂ : (b - a) * c = b * c - a * c := by ring
  have h₃ : 0 ≤ b * c - a * c := by rwa [h₂] at h₁
  rwa [sub_nonneg] at h₃

/-
Let's now combine forward and backward reasoning, to get our most
efficient proof of this statement. Note in particular how unification is used
to know what to prove inside the parentheses in the `mul_nonneg` arguments.
-/
example (a b c : ℝ) (hc : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c := by
  rw [← sub_nonneg]
  calc
    0 ≤ (b - a) * c := mul_nonneg (by rwa [sub_nonneg]) hc
    _ = b * c - a * c := by ring


/-
Let's now practice all three styles using:

  `mul_nonneg_of_nonpos_of_nonpos {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b`

  `sub_nonpos {a b : α} : a - b ≤ 0 ↔ a ≤ b`
-/
-- First using mostly backward reasoning
-- 0013
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  sorry

-- Using forward reasoning
-- 0014
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  sorry

-- 0015
/-- Using a combination of both, with a `calc` block -/
example (a b c : ℝ) (hc : c ≤ 0) (hab : a ≤ b) : b * c ≤ a * c := by
  sorry

/-
Let's now move to proving implications. Lean denotes implications using
a simple arrow `→`, the same it uses for functions (say denoting the type of functions
from `ℕ` to `ℕ` by `ℕ → ℕ`). This is because it sees a proof of `P ⇒ Q` as a function turning
a proof of `P` into a proof `Q`.

Many of the examples that we already met are implications under the hood. For instance we proved

  `le_add_of_nonneg_left (a b : ℝ) (ha : 0 ≤ a) : b ≤ a + b`

But this can be rephrased as

  `le_add_of_nonneg_left (a b : ℝ) : 0 ≤ a → b ≤ a + b`

In order to prove `P → Q`, we use the tactic `intro`, followed by an assumption name.
This creates an assumption with that name asserting that `P` holds, and turns the goal into `Q`.

Let's check we can go from our old version of `le_add_of_nonneg_left` to the new one.

-/
example (a b : ℝ) : 0 ≤ a → b ≤ a + b := by
  intro ha
  exact le_add_of_nonneg_left ha

/-
Actually Lean doesn't make any difference between those two versions. It is also happy with
-/
example (a b : ℝ) : 0 ≤ a → b ≤ a + b :=
  le_add_of_nonneg_left

/- No tactic state is shown in the above line because we don't even need to enter
tactic mode using `by`.

Let's practise using `intro`. -/
-- 0016
example (a b : ℝ) : 0 ≤ b → a ≤ a + b := by
  sorry

/-
What about lemmas having more than one assumption? For instance:

  `add_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b`

A natural idea is to use the conjunction operator (logical AND), which Lean denotes
by `∧`. Assumptions built using this operator can be decomposed by the `rcases` tactic,
which is a very general assumption-decomposing tactic.
-/
example {a b : ℝ} : 0 ≤ a ∧ 0 ≤ b → 0 ≤ a + b := by
  intro hyp
  rcases hyp with ⟨ha, hb⟩
  exact add_nonneg ha hb

/-
Needing that intermediate line invoking `rcases` shows this formulation is not what is used by
Lean. It rather sees `add_nonneg` as two nested implications:
if `a` is non-negative then (if `b` is non-negative then `a + b` is non-negative).
It reads funny, but it is much more convenient to use in practice.
-/
example {a b : ℝ} : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
  add_nonneg

/-
The pattern above is so common that implications are defined as **right-associative** operators,
hence parentheses are not needed above.

Let's prove that the naive conjunction version implies the funny Lean version. For this we need
to know how to prove a conjunction. The `constructor` tactic creates two goals from a conjunction goal.
It can also be used to create two implication goals from an equivalence goal.
-/
example {a b : ℝ} (H : 0 ≤ a ∧ 0 ≤ b → 0 ≤ a + b) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  intro ha
  intro hb
  apply H
  constructor
  · exact ha
  · exact hb

/-
Let's practice `rcases` and `constructor`. In the next exercise, `P`, `Q` and `R` denote
unspecified mathematical statements.
-/
-- 0017
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

/-
Of course using `constructor` only to be able to use `exact` twice in a row feels silly. One can
also use the anonymous constructor syntax: ⟨ ⟩
Beware those are not parentheses but angle brackets. This is a generic way of providing
compound objects to Lean when Lean already has a very clear idea of what it is waiting for.

So we could have replaced the last three lines by:
  exact ⟨hQ, hP⟩

We can also combine the `intro` steps. We can now compress our earlier proof to:
-/
example {a b : ℝ} (H : 0 ≤ a ∧ 0 ≤ b → 0 ≤ a + b) : 0 ≤ a → 0 ≤ b → 0 ≤ a + b := by
  intro ha hb
  exact H ⟨ha, hb⟩

/-
The anonymous contructor trick actually also works in `intro`. So we can replace
```
  intro h
  rcases h with ⟨h₁, h₂⟩
```
by
```
  intro ⟨h₁, h₂⟩
```
Now redo the previous exercise using all those compressing techniques, in exactly two lines. -/
-- 0018
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

/-
We are ready to come back to the equivalence between the different formulations of
lemmas having two assumptions. Remember the `constructor` tactic can be used to split
an equivalence into two implications.
-/
-- 0019
example (P Q R : Prop) : P ∧ Q → R ↔ P → Q → R := by
  sorry

/-
If you used more than five lines in the above exercise then try to compress things
(without simply removing line ends).

One last compression technique: given a proof `h` of a conjunction `P ∧ Q`, one can get
a proof of `P` using `h.left` and a proof of `Q` using `h.right`, without using `rcases`.
One can also use the more generic (but less legible) names `h.1` and `h.2`.

Similarly, given a proof `h` of `P ↔ Q`, one can get a proof of `P → Q` using `h.mp`
and a proof of `Q → P` using `h.mpr` (or the generic `h.1` and `h.2` that are even less legible
in this case).

Before the final exercise in this file, let's make sure we'll be able to leave
without learning 10 lemma names. The `linarith` tactic will prove any equality or
inequality or contradiction that follows by linear combinations of assumptions from the
context (with constant coefficients).
-/
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Now let's enjoy this for a while.
-/
-- 0020
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  sorry

-- And let's combine with our earlier lemmas.
-- 0021
example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  sorry

/-
Final exercise

In the last exercise of this file, we will use the divisibility relation on ℕ,
denoted by `∣` (beware this is a unicode divisibility bar, not the ASCII pipe character),
and the `gcd` function.

The definitions are the usual ones, but our goal is to avoid using these definitions and
only use the following three lemmas:

  `dvd_refl (a : ℕ) : a ∣ a`

  `dvd_antisymm {a b : ℕ} : a ∣ b → b ∣ a → a = b :=`

  `dvd_gcd_iff {a b c : ℕ} : c ∣ gcd a b ↔ c ∣ a ∧ c ∣ b`
-/
-- All functions and lemmas below are about natural numbers.
namespace Nat
-- 0022
example (a b : ℕ) : a ∣ b ↔ gcd a b = a := by
  sorry

end Nat
/-
In this file, we'll learn about the `∀` quantifier, and the disjunction
operator `∨` (logical OR).

 # The universal quantifier

Let `P` be a predicate on a type `X`. This means for every mathematical
object `x` with type `X`, we get a mathematical statement `P x`.
In Lean, `P x` has type `Prop`.

Lean sees a proof `h` of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`.
This already explains the main way to use an assumption or lemma which
starts with a `∀`.

In order to prove `∀ x, P x`, we use `intro x` to fix an arbitrary object
with type `X`, and call it `x`.

Note also we don't need to give the type of `x` in the expression `∀ x, P x`
as long as the type of `P` is clear to Lean, which can then infer the type of `x`.

Let's consider two predicates to play with `∀`.

`EvenFun (f : ℝ → ℝ) : ∀ x, f (-x) = f x`

`OddFun (f : ℝ → ℝ) :  ∀ x, f (-x) = -f x`.

-/

def EvenFun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

def OddFun (f : ℝ → ℝ) :=  ∀ x, f (-x) = -f x

/-
In the next proof, we also take the opportunity to introduce the
`unfold` tactic, which simply unfolds definitions. Here this is purely
for didactic reason, Lean doesn't need those `unfold` invocations.
We will also use `rfl` which is a term proving equalities that are true
by definition (in a very strong sense to be discussed later).
-/
example (f g : ℝ → ℝ) : EvenFun f → EvenFun g → EvenFun (f + g) := by
  -- Assume f is even
  intro hf
  -- which means ∀ x, f (-x) = f x
  unfold EvenFun at hf
  -- and the same for g
  intro hg
  unfold EvenFun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold EvenFun
  -- Let x be any real number
  intro x
  -- and let's compute
  calc
    (f + g) (-x) = f (-x) + g (-x) := rfl
    _ = f x + g (-x) := by rw [hf x]
    _ = f x + g x := by rw [hg x]
    _ = (f + g) x := rfl


/-
In the preceding proof, all `unfold` lines are purely for
psychological comfort.

Sometimes unfolding is necessary because we want to apply a tactic
that operates purely on the syntactical level.
The main such tactic is `rw`.

The same property of `rw` explain why the first computation line
is necessary, although its proof is simply `rfl`.
Before that line, `rw [hf x]` won't find anything like `f (-x)` hence
will give up.
The last line is not necessary however, since it only proves
something that is true by definition, and is not followed by
a `rw`.

Also, Lean doesn't need to be told that `hf` should be specialized to
`x` before rewriting.
We can also gather several rewrites using a list of expressions.

One last trick is that `rw` can take a list of expressions to use for
rewriting. For instance `rw [h₁, h₂, h₃]` is equivalent to three
lines `rw [h₁]`, `rw [h₂]` and `rw [h₃]`. Note that you can inspect the tactic
state between those rewrites when reading a proof using this syntax. You
simply need to move the cursor inside the list.

Hence we can compress the above proof to:
-/
example (f g : ℝ → ℝ) : EvenFun f → EvenFun g → EvenFun (f + g) := by
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x) := rfl
    _ = f x + g x := by rw [hf, hg]

/-
Now let's practice. If you need to learn how to type a unicode symbol,
you can put your mouse cursor above the symbol and wait for one second.
-/
-- 0023
example (f g : ℝ → ℝ) : EvenFun f → EvenFun (g ∘ f) := by
  sorry

-- 0024
example (f g : ℝ → ℝ) : OddFun f → OddFun g → OddFun (g ∘ f) := by
  sorry

/-
Let's have more quantifiers, and play with forward and backward reasoning.

In the next definitions, note how `∀ x₁, ∀ x₂` is abreviated to `∀ x₁ x₂`.

`NonDecreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂`

`NonIncreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂`

-/

def NonDecreasing (f : ℝ → ℝ) :=
  ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def NonIncreasing (f : ℝ → ℝ) :=
  ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

-- Let's be very explicit and use forward reasoning first.
example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonDecreasing g) : NonDecreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- Since f is non-decreasing, f x₁ ≤ f x₂.
  have step₁ : f x₁ ≤ f x₂ := hf x₁ x₂ h
  -- Since g is non-decreasing, we then get g (f x₁) ≤ g (f x₂).
  exact hg (f x₁) (f x₂) step₁

/-
In the proof above, note how inconvenient it is to specify `x₁` and `x₂` in `hf x₁ x₂ h` since
they could be inferred from the type of `h`.
We could have written `hf _ _ h` and Lean would have filled the holes denoted by `_`.

Even better we could have written the definition
of `NonDecreasing` as: ∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≤ f x₂, with curly braces to denote
implicit arguments.

But let's leave that aside for now. One possible variation on the proof above is to
use the `specialize` tactic to replace `hf` with its specialization to the relevant value.
 -/
example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonDecreasing g) : NonDecreasing (g ∘ f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf

/-
This `specialize` tactic is mostly useful for exploration, or in preparation for rewriting
in the assumption. One can very often replace its use by using more complicated expressions
directly involving the original assumption, as in the next variation:
-/
example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonDecreasing g) : NonDecreasing (g ∘ f) := by
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)

/-
Since the proof above uses only `intro` and `exact`, we could very easily replace it by the
raw proof term:
-/
example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonDecreasing g) : NonDecreasing (g ∘ f) :=
  fun x₁ x₂ h ↦ hg (f x₁) (f x₂) (hf x₁ x₂ h)

/-
Of course the above proof is difficult to decipher. The principle in mathlib is to use
such a proof when the result is obvious and you don't want to read the proof anyway.

Instead of pursuing this style, let's see how backward reasoning would look like here.
As usual with this style, we use `apply` and enjoy Lean specializing assumptions for us
using unification.
-/
example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonDecreasing g) : NonDecreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- We need to prove (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Since g is non-decreasing, it suffices to prove f x₁ ≤ f x₂
  apply hg
  -- which follows from our assumption on f
  apply hf
  -- and on x₁ and x₂
  exact h

-- 0025
example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonIncreasing g) : NonIncreasing (g ∘ f) := by
  sorry

/- # Disjunctions

Let's switch to disjunctions now. Lean denotes by `∨` the
logical OR operator.

In order to make use of an assumption
  `hyp : P ∨ Q`
we use the cases tactic:
  `rcases hyp with hP | hQ`
which creates two proof branches: one branch assuming `hP : P`,
and one branch assuming `hQ : Q`.

In order to directly prove a goal `P ∨ Q`,
we use either the `left` tactic and prove `P` or the `right`
tactic and prove `Q`.

In the next proof we use `ring` and `linarith` to get rid of
easy computations or inequalities, as well as one lemma:

  `mul_eq_zero : a*b = 0 ↔ a = 0 ∨ b = 0`
-/
example (a b : ℝ) : a = a * b → a = 0 ∨ b = 1 := by
  intro hyp
  have H : a * (1 - b) = 0 := by
    calc
      a * (1 - b) = a - a * b := by ring
      _ = 0 := by linarith

  rw [mul_eq_zero] at H
  rcases H with Ha | Hb
  · left
    exact Ha
  · right
    linarith

-- 0026
example (x y : ℝ) : x ^ 2 = y ^ 2 → x = y ∨ x = -y := by
  sorry

/-
In the next exercise, we can use:
  `eq_or_lt_of_le : x ≤ y → x = y ∨ x < y`
-/
-- 0027
example (f : ℝ → ℝ) : NonDecreasing f ↔ ∀ x y, x < y → f x ≤ f y := by
  sorry

/-
In the next exercise, we can use:
  `le_total x y : x ≤ y ∨ y ≤ x`
-/
-- 0028
example (f : ℝ → ℝ) (h : NonDecreasing f) (h' : ∀ x, f (f x) = x) : ∀ x, f x = x := by
  sorry

/- # Existential quantifiers

In this file, we learn how to handle the ∃ quantifier.

In order to prove `∃ x, P x`, we give some `x₀` using tactic `use x₀` and
then prove `P x₀`. This `x₀` can be an object from the local context
or a more complicated expression.

In the example below, `P x₀` is `8 = 2*4` which is true by definition so
Lean does not ask for a proof.
-/

example : ∃ n : ℕ, 8 = 2 * n := by
  use 4

/-
In order to use `h : ∃ x, P x`, we use the `rcases` tactic to fix
one `x₀` that works.

Again `h` can come straight from the local context or can be a more
complicated expression.
-/
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  -- Let's fix k₀ such that n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- It now suffices to prove k₀ + 1 > 0.
  rw [hk₀]
  -- and we have a lemma about this
  exact Nat.succ_pos k₀

/-
The next exercises use divisibility in ℤ (beware the ∣ symbol which is
not ASCII).

By definition, a ∣ b ↔ ∃ k, b = a*k, so you can prove a ∣ b using the
`use` tactic.
-/
-- Until the end of this file, a, b and c will denote integers, unless
-- explicitly stated otherwise
variable (a b c : ℤ)

-- 0029
example (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  sorry

/-
A very common pattern is to have an assumption or lemma asserting
  `h : ∃ x, y = ...`
and this is used through the combo:
  rcases h with ⟨x, hx⟩
  rw hx at ...
The tactic `rcases` allows us to simplify the above combo when the
name `hx` is replaced by the special name `rfl`, as in the following example.
-/
example (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := by
  rcases h1 with ⟨k, rfl⟩
  rcases h2 with ⟨l, rfl⟩
  use k + l
  ring

/-
You can use the same `rfl` trick with the `rintro` tactic which
is a power powerful variant of `intro`.
-/
example : a ∣ b → a ∣ c → a ∣ b + c := by
  rintro ⟨k, rfl⟩ ⟨l, rfl⟩
  use k + l
  ring

-- 0030
example : 0 ∣ a ↔ a = 0 := by
  sorry

/-
We can now start combining quantifiers, using the definition

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`

-/
open Function

-- In the remaining of this file, f and g will denote functions from
-- ℝ to ℝ.
variable (f g : ℝ → ℝ)

-- 0031
example (h : Surjective (g ∘ f)) : Surjective g := by
  sorry

/-
The above exercise can be done in three lines. Try to do the
next exercise in four lines.
-/
-- 0032
example (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  sorry

/-
Negations, proof by contradiction and contraposition.

This file introduces the logical rules and tactics related to negation:
exfalso, by_contra, contrapose, by_cases and push_neg.

There is a special statement denoted by `False` which, by definition,
has no proof.

So `False` implies everything. Indeed `False → P` means any proof of
`False` could be turned into a proof of P.
This fact is known by its latin name
"ex falso quod libet" (from False follows whatever you want).
Hence Lean's tactic to invoke this is called `exfalso`.
-/
example : False → 0 = 1 := by
  intro h
  exfalso
  exact h

/-
The preceding example suggests that this definition of `False` isn't very useful.
But actually it allows us to define the negation of a statement P as
"P implies False" that we can read as "if P were true, we would get
a contradiction". Lean denotes this by `¬ P`.

One can prove that (¬ P) ↔ (P ↔ False). But in practice we directly
use the definition of `¬ P`.
-/
example {x : ℝ} : ¬x < x := by
  intro hyp
  rw [lt_iff_le_and_ne] at hyp
  rcases hyp with ⟨hyp_inf, hyp_non⟩
  clear hyp_inf -- we won't use that one, so let's discard it
  change x = x → False at hyp_non -- Lean doesn't need this psychological line
  apply hyp_non
  rfl

open Int

-- 0045
example (n : ℤ) (h_even : Even n) (h_not_even : ¬Even n) : 0 = 1 := by
  sorry

-- 0046
example (P Q : Prop) (h₁ : P ∨ Q) (h₂ : ¬(P ∧ Q)) : ¬P ↔ Q := by
  sorry

/-
The definition of negation easily implies that, for every statement P,
`P → ¬ ¬ P`.

The excluded middle axiom, which asserts `P ∨ ¬ P` allows us to
prove the converse implication.

Together those two implications form the principle of double negation elimination.
  `not_not {P : Prop} : (¬ ¬ P) ↔ P`

The implication `¬ ¬ P → P` is the basis for proofs by contradiction:
in order to prove `P`, it suffices to prove `¬ ¬ P`, ie `¬ P → False`.

Of course there is no need to keep explaining all this. The tactic
`by_contra Hyp` will transform any goal `P` into `False` and
add `Hyp : ¬ P` to the local context.

An incarnation of the excluded middle axiom is the principle of
contraposition: in order to prove P ⇒ Q, it suffices to prove
not Q ⇒ not P.
-/

-- Using a proof by contradiction, let's prove the contraposition principle
-- 0047
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  sorry

/-
Again Lean doesn't need this principle explained to it. We can use the
`contrapose` tactic.
-/
example (P Q : Prop) (h : ¬Q → ¬P) : P → Q := by
  contrapose
  exact h

/-
In the next exercise, we'll use
 Odd n : ∃ k, n = 2*k + 1
 Int.odd_iff_not_even {n : ℤ} : odd n ↔ ¬ even n
-/
-- 0048
example (n : ℤ) : Even (n ^ 2) ↔ Even n := by
  sorry

/-
As a last step on our law of the excluded middle tour, let's notice that, especially
in pure logic exercises, it can sometimes be useful to use the
excluded middle axiom in its original form:
  `Classical.em : ∀ P, P ∨ ¬ P`

Instead of applying this lemma and then using the `rcases` tactic, we
have the shortcut
 `by_cases h : P`

combining both steps to create two proof branches: one assuming
`h : P`, and the other assuming `h : ¬ P`.

For instance, let's prove a reformulation of this implication relation,
which is sometimes used as a definition in other logical foundations,
especially those based on truth tables (hence very strongly using
excluded middle from the very beginning).
-/
variable (P Q : Prop)

example : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      exact h hP
    · left
      exact hP
  · intro h hP
    rcases h with hnP | hQ
    · exfalso
      exact hnP hP
    · exact hQ

-- 0049
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry

/-
It is crucial to understand negation of quantifiers.
Let's do it by hand for a little while.
In the first exercise, only the definition of negation is needed.
-/
-- 0050
example (n : ℤ) : (¬∃ k, n = 2 * k) ↔ ∀ k, n ≠ 2 * k := by
  sorry

/-
Contrary to negation of the existential quantifier, negation of the
universal quantifier requires excluded middle for the first implication.
In order to prove this, we can use either
* a double proof by contradiction
* a contraposition, `not_not : (¬ ¬ P) ↔ P` and a proof by contradiction.

Recall we have
`EvenFun (f : ℝ → ℝ) := ∀ x, f (-x) = f x`

-/

-- 0051
example (f : ℝ → ℝ) : ¬EvenFun f ↔ ∃ x, f (-x) ≠ f x := by
  sorry

/-
Of course we can't keep repeating the above proofs, especially the second one.
So we use the `push_neg` tactic.
-/
example : ¬EvenFun fun x => 2 * x := by
  unfold EvenFun
  -- Here unfolding is important because push_neg won't do it.
  push_neg
  use 42
  linarith

-- 0052
example (f : ℝ → ℝ) : ¬EvenFun f ↔ ∃ x, f (-x) ≠ f x := by
  sorry

def BoundedAbove (f : ℝ → ℝ) :=
  ∃ M, ∀ x, f x ≤ M

example : ¬BoundedAbove fun x => x := by
  unfold BoundedAbove
  push_neg
  intro M
  use M + 1
  linarith

-- Let's contrapose
-- 0053
example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  sorry

/-
The "contrapose, push_neg" combo is so common that we can abreviate it to
`contrapose!`

Let's use this trick, together with:
  `eq_or_lt_of_le : a ≤ b → a = b ∨ a < b`
-/
-- 0054
example (f : ℝ → ℝ) : (∀ x y, x < y → f x < f y) ↔ ∀ x y, x ≤ y ↔ f x ≤ f y := by
  sorry

open Classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations. It comes after the file `07FirstNegations`.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contra` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/
section NegationProp

variable (P Q : Prop)

-- 0055
example : P → Q ↔ ¬Q → ¬P := by
  sorry

-- 0056
theorem non_imp (P Q : Prop) : ¬(P → Q) ↔ P ∧ ¬Q := by
  sorry

-- In the next one, let's use the axiom
-- `propext {P Q : Prop} : (P ↔ Q) → P = Q`
-- 0057
example (P : Prop) : ¬P ↔ P = False := by
  sorry

end NegationProp

section NegationQuantifiers

variable (X : Type) (P : X → Prop)

-- 0058
example : (¬∀ x, P x) ↔ ∃ x, ¬P x := by
  sorry

-- 0059
example : (¬∃ x, P x) ↔ ∀ x, ¬P x := by
  sorry

-- 0060
example (P : ℝ → Prop) : (¬∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬P ε := by
  sorry

-- 0061
example (P : ℝ → Prop) : (¬∀ x > 0, P x) ↔ ∃ x > 0, ¬P x := by
  sorry

end NegationQuantifiers

-- 00062 Special Exercise
example (P Q : ℝ → Prop) : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

-- 0063 Special Exercise, Very Hard
example (P : ℝ → Prop) (Q : Prop) : (∃ x > 0, P x → Q) ↔ (∀ x > 0, P x) → Q := by
  sorry

/- # Cheat Sheet

| Logic symbol        | In Goals                   |                    | In Assumptions (name h)   |                             |
| :------------------ | :------------------------- | :----------------- | :------------------------ | :-------------------------- |
|                     | **term**                   | **tactic**         | **term**                  | **tactic**                  |
| `P → Q`             | `fun hp => ...`            | `intro hp`         | `h ...`                   | `apply h (at ...)`          |
| `True`              | `trivial`                  | `trivial`          | CAN'T BE USED             | CAN'T BE USED               |
| `False`             | CAN'T BE USED              | CAN'T BE USED      | `False.elim h`            | `exfalso; exact h`          |
| `¬P`                | `fun hp => ...`            | `intro hp`         | `h ...`                   | `apply h` (when `⊢ False`)  |
| `P ∧ Q`             | `And.intro .../⟨ , ⟩`      | `constructor`      | `h.left`/`h.right`        | `rcases h with ⟨hp, hq⟩`    |
| `P ↔ Q`             | `Iff.intro .../⟨ , ⟩`      | `constructor`      | `h.mp`/`h.mpr`            | `rcases h with ⟨hpq, hqp⟩`  |
| `P ∨ Q`             | `Or.inl`/`Or.inr ...`      | `left`/`right`     | `Or.elim h ...`           | `rcases h with hp | hq`     |
| `∀ (a : X), ...`    | `fun x => ...`             | `intro x`          | `h ...`                   | `(exact) h ...`             |
| `∃ (a : X), ...`    | `Exists.intro x .../⟨ , ⟩` | `use x`/`exists x` | `Classical.choose...`     | `rcases h with ⟨x, hx⟩`     |
-/
