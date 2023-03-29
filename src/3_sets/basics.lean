import tactic           -- import all the tactics
import data.nat.prime_norm_num   -- import ℕ natural numbers 
import data.real.basic  -- import ℝ real numbers
import data.real.irrational  -- allows us to talk about irrational numbers

variables (α β: Type)        
variables (A B C D: set α)
variables (a x y: α)
open set nat

/- 
A set in Lean can only contain elements of the same type.

So for any type `α : Type` there is a type of `set α : Type`

The terms of this type are sets containing elements of type α

So if `S : set ℕ` then `S` is a set containing only natural numbers.

Suppose we also have a set `T : set ℝ`, containing only real numbers. 

As mathematicians we could happily form their intersection `S ∩ T` 
but this doesn't work in Lean! -/

variable (S : set ℕ)
variable (T : set ℝ) 

--#check S ∩ T    -- type mismatch at application `S ∩ T` term `T` has
                  /- type `set ℝ` but is expected to have type `set ℕ` 

Another obvious difference between sets in Lean and in maths is that 
we would usually call S a subset of ℕ and write `S ⊆ ℕ`

Unfortunately this also doesn't work in Lean: `ℕ` is a Type not a set. -/

--#check S ⊆ ℕ -- type mismatch at application S ⊆ ℕ term ℕ has type Type : Type 1
                /- but is expected to have type set ℕ : Type

A `predicate` on a type α is a function `α → Prop`

For example `nat.prime: ℕ → Prop` is the predicate telling us whether 
or not `n : ℕ` is `prime`.

Given any set A whose elements all have type α there is a predicate on α
given by `x ∈ A`.

In Lean `A : set α`  is defined to be this predicate.

Sets can be written in standard set-builder notation

For example `{p : ℕ | nat.prime p}` is the set of primes

Here are some more examples:

`{n : ℕ | n ≤ 10}`  the set ℕ containing all nats ≤ 10
`{x : ℝ | irrational x}`  the set ℝ containing all irrational numbers

Note that in each case the elements of each set are of `a fixed type`. -/

--#check {p : ℕ | nat.prime p} -- : set ℕ
--#check {n : ℕ | n ≤ 10}      -- : set ℕ  
--#check {x : ℝ | irrational x} -- : set ℝ

variable (Pr : α → Prop)  -- a predicate on α
-- The set defined by a predicate equals the predicate

-- 01
example : {a : α | Pr a} = Pr :=
begin
  refl,
end

-- 02
example : {p : ℕ | nat.prime p} = nat.prime :=
begin
  sorry,
end

/-  
The way we refer to membership of a set is with `∈` (type `\in`)
For any  `x : α`  we have  `x ∈ A` iff `Pr x` -/
-- 03
example : x ∈ { a | Pr a} ↔ Pr x:=
begin
   sorry, 
end

-- Asking Lean whether a term of type `β` belongs to a `set α` is problematic
variable (b : β) -- UNCOMMENT next line to see full error
--#check (b ∈ A) -- failed to synthesize type class instance for... ⊢ has_mem β (set α)

/- This error message can be read as saying:
"I don't know how to make sense of the question of whether a term of type β
is a member of a set α"  
  
(Trying to make sense of Infoview output is all part of learning Lean.) -/

/- 
# New tactic: `change` 

When we have a goal `⊢ H1` and we know that it is definitionally equal to `H2`
then we can do `change H2` and our goal changes to `⊢ H2`

It can also be used on local hypotheses: eg if we had 
if `h : H1` then we could do `change H2 at h` to get `h : H2` -/
 
section mem
-- 04
example : 2 ∈ {n : ℕ | even n}:=
begin
  dsimp,    -- simplifies our goal to `⊢ even 2` which is definitionally the same.
  change ∃x, 2 = x + x, --if you check `even k` is defined to be `∃ x, k = x + x`
  use 1, -- provides the required `x` and then closes the remaining goal `2 = 1 + 1`
end

/-
You can check that both `dsimp` and `change` are not needed in our previous proof
(comment out the 1st two lines). They are still useful as we write the proof since they
help to clarify the goal. -/
-- 05
example : 2 ∈ ({1,2,3}: set ℕ):=
begin
  dsimp, -- goal becomes  `⊢ 3 = 1 ∨ 3 = 2 ∨ 3 = 3` 
  right,left,refl,
end

-- 06
example : 3 ∈ {n:ℕ | n ≤ 10}  :=
begin
  sorry,
end

-- 07
example : 1 ∈ { x : ℕ | ∀ (k:ℕ), 1 ≤ k+1} :=
begin
  sorry,
end

--Not in `∉` is `\nin`
-- 08
example : x ∉ A ↔ ¬ (x ∈ A):=
begin
  refl,
end

-- 09
example : 4 ∉ {n : ℕ| 5 < n} ∧ 6 ∉ {n : ℕ | nat.prime n}:=
begin
  sorry,
end

end mem

section subsets

/-  `Subsets`: `⊆` (type \ss) 
If `A B : set α` then `A ⊆ B` iff every element of A is also an element of B -/
-- 10
example : (A ⊆ B) ↔ (∀x, x ∈ A → x ∈ B):=
begin
  refl,
end

--the next proof is easy, but can you explain why `refl` works in this case?
-- 11
example (A : set α) : A ⊆ A:=
begin
  sorry,
end

/- If we have `(h : A ⊆ B)` and `(hx : x ∈ A)` then `h hx` is a proof that `x ∈ B`
So `h` takes a proof that `x ∈ A` and returns a proof that `x ∈ B`-/
-- 12
example (hx: x ∈ A)  (h: A ⊆ B) :  x ∈ B:=
begin
  apply h, -- Goal `⊢ x ∈ B` changes to `⊢ x ∈ A`
  exact hx,
end

-- Since `A ⊆ C` is `∀x, x ∈ A → x ∈ C` you can start with `intro x`,
-- 13
example  (hAB: A ⊆ B) (hBC: B ⊆ C) : A ⊆ C:=
begin
  sorry,
end

-- `dsimp at *` will simplify definitions in local context and in the goal.
-- 14
example : ({1,3} : set ℕ) ⊆ {n | n ≤ 5} :=
begin
  sorry,
end


end subsets

section ops

/- `Operations on sets`

We have all the usual methods of building new sets from old.

They are defined exactly as you would imagine.

Most of the next examples can be proved using `refl`

e.g. intersection `∩` (type \cap ) is `and` -/
-- 15
example : x ∈ A ∩ B ↔ (x ∈ A) ∧ (x ∈ B):=
begin
  refl,
end

-- union `∪` (type \un) is `or`
-- 16
example : x ∈ A ∪ B ↔ (x ∈ A) ∨ (x ∈ B):=
begin
  sorry,
end

-- Set `diff`erence `\` (type \\) is `(in A)  and (not in B)` (for `∉` type `\nin`)
-- 17
example : x ∈ A \ B ↔   x ∈ A ∧ x ∉ B :=
begin
  sorry,
end

-- Complement `ᶜ` (type \^c) is `not in`
-- 18
example : x ∈ Aᶜ ↔ ¬ (x ∈ A):=
begin
  sorry,
end

-- Complement and ∉ are the same
-- 19
example : x ∈ Aᶜ ↔ x ∉ A :=
begin
  sorry,
end

-- 20
example : A ∩ B ⊆ B:=
begin
  sorry,
end

-- 21
example : A ∩ B ⊆ B ∩ A :=
begin
  sorry,
end

-- 22
example  : A ∩ B ⊆ A ∪ B:=
begin
  sorry,
end

-- 23
example (hAB : A ⊆ B) (hCD: C ⊆ D) : A ∩ C ⊆ B ∩ D :=
begin
  sorry,
end

-- 24
example (hAB : A ∪ B ⊆ C) : A ⊆ C ∧ B ⊆ C:=
begin
  sorry,
end
end ops


section univ_empty
/-There are two special sets for any type α

     `univ = {a:α | true}`

     `∅ = {a:α | false}`

Note that `(univ : set α)` and `(∅ : set α)` so each type has
its own universal set and empty set. -/

-- open the namespace `set` to use univ otherwise we would have to use `set.univ`  
open set 
-- 25
example : x ∈ (univ : set α) ↔ true:=
begin
  refl,
end

--26
example  (A : set α) : A ⊆ A ∩ univ  :=
begin
  sorry,
end

/- Although `(univ : set α)` is the set containing every element of type `α`
   it is not equal to `α`, and Lean won't let you consider this -/

-- #check (univ : set α) = α
-- 27
example : x ∈ (∅ : set α) ↔ false:=
begin
  refl,
end

-- Note: if you have `h : x ∈ ∅` then `cases h` will let you consider all the cases..
-- 28
example (A : set α) : ∅ ∪  A ⊆ A   :=
begin
  sorry,
end
end univ_empty