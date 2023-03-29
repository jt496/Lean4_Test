import tactic
import data.complex.basic
import data.real.basic
import data.real.irrational
import data.nat.prime_norm_num
import algebra.group.ext
variables (α β γ R : Type)
variables (A B C : set α)
variables (a x y: α)
open_locale classical polynomial 
variables [ring R] {p q : R[X]}

open set complex
section ext

/-
# New tactic: ext

`Extensionality` says that two sets are equal iff they have the same elements.

In Lean we can use the `ext` tactic to prove equality between sets. 

We can also use it to prove equality of functions and many, many other objects 
see the end of this file for some examples.

 -/
-- 01
example : A ∩ B = B ∩ A:=
begin
  ext,
  split,
  intro hx, exact ⟨hx.2,hx.1⟩,
  intro hx, exact ⟨hx.2,hx.1⟩,
end

-- 02
example :  A ∩ univ = A:=
begin
  ext a, 
  sorry,
end

-- 03
example : A ∩ B ∪ C = C ∪ B ∩ A :=
begin
  ext,
  sorry,
end

-- 04
example : A ∪ Aᶜ = univ:=
begin
  sorry,
end

-- 05
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C):=
begin
  sorry,
end


/- Using `ext` with functions is identical. -/
-- 06
example (f g : α → β) (h :∀ x:α, f x = g x) : f = g:=
begin
  ext,
  sorry,
end

-- Lets define two functions that are obviously equal.

def fun1 : ℕ → ℕ := λ n , (n+1)^2   -- this is just CS notation for  `n ↦ (n + 1)²`

def fun2 : ℕ → ℕ:= λ n, n^2 + 2*n + 1     -- and `n ↦ n² + 2n + 1`

-- We can use ext to prove that `fun1 = fun2` 
-- 07 
example  : fun1 = fun2 :=
begin
  ext n,
  unfold fun1 fun2, 
  linarith, 
end

/-
# have 

In our next example it is useful to prove an intermediate result. 
To do this we use the tactic: `have`. 

The general form of this tactic is as follows:
If we want to prove a proposition `P` we do the following: 

have h : P,
{
  proof of P,
},
-- now have `h : P` in the local context

-/
-- 07
example : A ∪ B ⊆ B ∪ C → A \ B ⊆ C :=
begin
  intros h x hab,
  cases hab with ha hnb,
  have h2 : x ∈ A ∪ B,
  {
    sorry,
  },
  sorry,
end

/- # New tactic : by_cases 

If we have a proposition `P` then we can do a cases split on `P ∨ ¬ P`
using `by_cases P` -/

-- 08 If f and g agree on A and agree on Aᶜ then they are equal.
example  (f g : α → β) (A : set α) (hA: ∀ x, x ∈ A → f x = g x) (hAc: ∀ x, x ∈ Aᶜ → f x = g x):
f = g:=
begin
  ext,
  by_cases (x ∈ A),
  {
    sorry,
  },
  {
    sorry,
  },
end

/- 
# New tactic: rintro 

`rintro` allows us to do cases/intros recursively and quickly introduce 
and breakup complicated expressions.

If the goal is `⊢ (P ∧ Q) → R` then `rintro ⟨hP,hQ⟩` will introduce two
terms `hP : P` and `hQ : Q` and change the goal to `⊢ R` 
(So equivalent to `intro h` followed by `cases h with hP hQ`)

If the goal is `⊢ (P ∨ Q) → R` then `rintro (hP | hQ)` will split the goal into two
goals both `⊢ R`. In the 1st local context  you have `hP : P` and in the 2nd `hQ : Q`
(So equivalent to `intro h` followed by `cases h with hP hQ`)

If you have `⊢ (P ∧ Q ∧ (A ∨ B)) → C` then `rintro ⟨hP ,hQ, (hA | hB)⟩` will do what you need.

The easiest way to learn its syntax is to use `rintro?` which will then suggest a way 
to use it (although you will probably want to change the variable names it introduces).



# New tactic: refine

`refine` is like exact but with the advantage that you can put `_` as placeholders
 for terms that you can't immediately fill-in.   -/
-- 09
example : (A \ B) ∪ (B \ A) = (A ∪ B) \ (A ∩ B) :=
begin
  ext, 
  refine ⟨_,_⟩, -- equivalent to split, 
  { 
    rintro (⟨hA, hnB⟩ | ⟨hB, hnA⟩),
    split,
    left,
    exact hA,
    intro hAB,
    exact hnB hAB.2,
    sorry,
  },
  {
    rintro ⟨ha | hb, hnab⟩,
    {
      left, 
      refine ⟨ha, _⟩, -- recall `x ∈ A \ B` is `x ∈ A ∧ x ∉ B` 
      sorry
    },
    {
      sorry
    },
  },
end

-- 10
example :  A ∩ univ = A:=
begin
  sorry,
end

-- 11 At some point you might want to start looking in mathlib for one-line proofs..
example : (A ∪ B) ∪ C = A ∪ (B ∪ C):=
begin 
  sorry,
end

-- 12
example : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C):=
begin
  sorry,
end

-- Another way of proving that two sets are equal is to use anti-symmetry of ⊆
-- i.e. A ⊆ B → B ⊆ A →  A = B
-- 13
example : A ∪ B = B ∪ A:=
begin 
  apply subset_antisymm,
  {
    sorry
  },
  {
    sorry
  },
end

-- 14
example : (A ∪ B ) ∩ (A ∪ C) = A ∪ (B ∩ C)  :=
begin
  symmetry, -- useful if  you'd prefer to prove `x = y` rather than `y = x`
  apply subset_antisymm,
  {
    rintro x (ha | ⟨hb,hc⟩),
    refine ⟨_,_⟩; {left, exact ha},
    refine ⟨_,_⟩; right, exact hb, exact hc,
  },
  {
    sorry
  },
end

/-
Some other uses of `ext` are given below
-/


-- two complex numbers are equal iff ...
example (z w : ℂ) : z = w :=
begin
  ext,
  sorry,
  sorry,
end


-- two rational numbers are equal iff ... 
example (a b : ℚ ) : a = b :=
begin
  ext,
  sorry,
  sorry,
end


-- two terms in a product type are equal iff... 
example (x y : α × β ) : x = y :=
begin
  ext,
  sorry,
  sorry,
end

-- polynomials in X over a ring R are equal iff all their coefficients agree
example (p q : R[X]) : p = q:=
begin
  ext,
  sorry,
end

-- two vectors in ℝ^5 agree iff.. 
example (v w : vector ℝ 5) : v = w:=
begin
  ext,
  sorry,
end

variables (m n : ℕ) 
-- Two m x n matrices are equal iff..
example (M1 M2 : matrix (fin m) (fin n) α) : M1 = M2 :=
begin
  ext,
  sorry,
end

-- ext for finite sets is the same as for sets
example (s t : finset α) : s = t:=
begin
  ext,
  sorry,
end

-- two multisets with elements of type α are equal iff they contain the same number
-- of each term of α
example (M N : multiset α) : M = N:=
begin
  ext a, 
  sorry,
end

-- two lists are equal iff they agree in all positions
example (l1 l2 : list α) : l1 = l2:=
begin
  ext n a,  
sorry,
end

-- an equivalence relation  on α bundled with a proof that it is an equiv rel is called a setoid 
example (r s : setoid α) : r = s:=
begin 
  ext,
  sorry,
end

-- Two group structures on the same type α are equal iff their definitions of multiplication agree
example (G H : group α) : G = H :=
begin
  ext a b, 
  sorry
end

-- A filters is a family of sets closed under taking super-sets and finite intersections
example (F G : filter α) : F = G:=
begin 
  ext,
  sorry,
end



/- ETC...-/

end ext