import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime
variable (P Q  : Prop)
variable (α β : Type)
variable (R S: ℕ → Prop)
open Function Nat

/-
# Quantifiers 

# Existential ∃ tactics: use / cases

If our goal is `⊢ ∃(x:A), P` (where P may dep on x) and we know that `a : A` is a term
with the required property, then we can tell Lean to `use a` and our goal will change to `⊢ P`.  
In fact if we can prove `P` using `refl` then Lean will do this automatically.

If we have `h : ∃(x:A), P` in the local context then  `cases h with x hx` 
will give us `x : A` and `hx : P` in our local context.

[Notice how similar this is to how we used `cases h with hp hq` with `h : P ∧ Q`]

# Universal ∀ tactics: intro, apply, specialize  

If we have a goal `⊢ ∀(n:ℕ), P n` then we can use `intro n` and the our goal will
change to `⊢ P n`. (For Lean a `∀` statement is basically a function.)

If we have `(h : ∀(x:A), P x)` and we want to use this hypotesis for a particular choice 
of `x` then we can use `specialize h x` or (if goal is `⊢ P x`) just `apply h`

# New tactics for numerical/arithmetic proofs: norm_num and linarith

`norm_num` can prove results involving actual numerical expressions such as `4*3^2 < 50`

`linarith` can prove results involving linear arithmetic including inequalities. 

# New tactics to help us make sense of definitions: unfold and dsimp

`unfold blah` will unfold a definition of `blah`in the goal. 
Use unfold when you're not sure what a definition means.

`dsimp` will simplify the goal using definitions. 
Use dsimp if the goal looks unreadable.  -/

-- 01
example : ∃(n:ℕ), n = 20 :=by
  use 20 


-- 02
example : ∃(n:ℕ), 200 < n:=by
  use 201 
  norm_num



-- 03 
example : ∃(P:Prop), P:=by
use True
trivial


-- 04
example : ∃ (P:Prop), ¬ P → P:=by
use True
intro _
trivial 


-- 05 
example (h: ∃(n:ℕ), n.Prime ∧ 10 < n) : ∃(k:ℕ), k.Prime ∧ 7 < k :=by
obtain ⟨n,hn1,hn2⟩:= h
use n
apply And.intro hn1
linarith


-- 06 Hint : `Even n` is defined to be `∃(r:ℕ), n = r + r`
example (n : ℕ) : Even (4 * n):=by
  rw  [Even]
  use (2*n) 
  rw [← two_mul,←mul_assoc ]
  rfl
  
-- 07 
example (h: ∃(n:ℕ), Even n ∧ Even (n+1)) : ∃(k:ℕ), Even (2*k + 1) :=by
rcases h with ⟨n,hn1,hn2⟩
use n
rw [Even] at *
rcases hn1 with ⟨r,hr⟩
rcases hn2 with ⟨s,hs⟩
use (r+s)
rw [two_mul, ← add_assoc, add_comm, add_assoc,add_assoc, add_comm s,←add_assoc,←add_assoc,←add_assoc]
rw[← hr,add_assoc,add_assoc,← hs,add_comm,add_assoc]



-- 08
example : ∀ (n:ℕ), ∃ (k:ℕ), n < k:=by
intro n
use n.succ
exact lt_succ_self n

-- 09
example : ∀(n:ℕ), R n ∧ S n → ∃(k:ℕ), S k:=by
intro n hn
exact ⟨n,hn.2⟩



-- 10
example (f: ℕ → ℕ) (k : ℕ): Surjective f → ∃(n:ℕ), f n = 2023^k := by
intro hf
apply hf 


-- 11 Hint: if we have `h : ∀ (n : ℕ), f n = g n` then `rw (h n)` will replace `f n` by `g n` in the goal. 
example (f g: ℕ → ℕ) (h : ∀ n, f n = g n):  Injective f → Injective g:=by
intro hf
intro a b hab
apply hf
rwa [h a,h b]


-- 12
example (f : ℕ → ℕ) (m n : ℕ): Bijective f → f m = f n → m = n:=by
intro hf heq
apply hf.1
exact heq




/-
If (a b: ℕ) then `a ∣ b` means `a divides b`, ie. `∃(c:ℕ), b = a*c`
Note that this symbol is `\|` not `|` which is obviously not the same...-/

-- 13  
example (h : ∀n:ℕ, 3 ≤ n → 2 ∣ n → ¬n.Prime ) :∀(k:ℕ), Even k → 3 ≤ k → ¬ k.Prime :=by 
  intro k hk1 hk2 
  apply h
  exact hk2
  cases' hk1 with r hr
  use r
  rwa [two_mul]
  


-- We can use `⟨n,h⟩` notation for `∃ n, h`
-- 14 
example (n : ℕ)(h : n.Prime) : ∃ (k : ℕ), k.Prime:=by
  exact ⟨n,h⟩


-- 15 what if we don't have the hypothesis `n.Prime`
example  : ∃ (k : ℕ), k.Prime:=by
  refine' ⟨2,Nat.prime_two⟩

-- 16 To complete the next proof we need to show 2027 is Prime. Luckily `norm_num` will do it.
example  : ∃ (k : ℕ), 2026 < k ∧ k.Prime:=by
  refine'  ⟨2027,by norm_num,_⟩
  --norm_num -- the primality proving part of norm_num does not seem to exist in Lean4
  norm_num 
  sorry


-- /-
-- # New tactic: push_neg

-- Given a proposition with quantifiers involving a negation  `push_neg` will push the negation inside 
-- the expression as far as possible 

-- Like `rw` we can also use it to simplify terms in the local context eg `push_neg at h`  -/

-- 17
example : ¬ ∃ (n:ℕ), ∀ (k:ℕ), k < n:=by
  push_neg
  intro n
  use n


-- 18 Hint: If m,n ∈ ℕ then `max m n` is their maximum, `norm_num` may be useful again here
example : ∀ (m: ℕ), ∀ (n: ℕ), ∃ (k:ℕ), m ≤ k ∧ n ≤ k:=by
intro m n
refine' ⟨m+n,_,_⟩
apply Nat.le_add_right m
apply Nat.le_add_left n


variable (pr : α → Prop) 
/- A function from a type to Prop is usually called a `predicate` 
   For example `nat.Prime: ℕ → Prop` -/

-- 19 
example : (∀ (a:α), pr a) ↔ ¬ ∃ (b:α), ¬ pr b:=by
apply Iff.intro
· intro h
  push_neg
  exact h
· intro h
  push_neg at h  
  exact h

/-
In the previous example we had a `split` and the two parts used almost the same 
code. One way to do such proofs is to use the `try {code}` tactic, which tries the
`code` but doesn't complain if it fails. 
-/
-- 20 
-- example : (∀ (a:α), pr a) ↔ ¬ ∃ b:α, ¬ pr b:=by
-- apply Iff.intro
-- repeat 
--   intro h
--   try {push_neg}  -- this succeeds the 1st time but silently fails the 2nd time
--   try {push_neg at h}  --this succeeds the 2nd time but silently fails the 1st time
--   exact h




-- 21 
example : ∃ (n: ℕ), n + 2 = 5 ∧ 2 * n = 6:=by
use 3
norm_num

-- 22 beware the divides `∣` symbol is not `|` but `\|` 
example : ¬(∀ n: ℕ, n.Prime ∨ (2 ∣ n)):=by
intro hf
contrapose hf
push_neg
use 9
norm_num
intro h2

sorry


-- -- 23 Hint: Even n := ∃(r:ℕ), n = r + r
-- example : ∀ (n m:ℕ), Even n ∧ Even m → Even (n+m):=
-- by
--  admit


-- -- A relation r on ℕ
-- variable (r : ℕ → ℕ → Prop)
-- -- 24
-- example:  reflexive r → r 17 17:=
-- by
--   unfold reflexive,
--   admit


-- -- 25
-- example : symmetric r →  r 13 2 → r 2 13:=
-- by
--   unfold symmetric,
--   admit


-- -- 26
-- example (a b c : ℕ) : equivalence r → r a b →  r b c →  r a c:=
-- by
--   unfold equivalence transitive,
--   admit


-- -- 27
-- example (a b c : ℕ) : equivalence r → r a b →  r b c →  r c a:=
-- by
--   admit


-- -- 28
-- example (h1 : symmetric r) (h2: ∃ (a b:ℕ), r a b ∧ a ≠ b) : 
-- (∀ {m n: ℕ}, r m n → r n m → m = n) → false :=
-- by 
--   admit


-- -- 29 Hint: dsimp may be useful here (you'll know when to use it!)
-- example : ∃! (n:ℕ), ∀ (k:ℕ), n ≤ k :=
-- by
--   admit


-- -- 30
-- example : ¬∃ (n:ℕ), ∀ (k:ℕ), k ≤ n :=
-- by
--   admit


-- /- If we want to define a function and then use it we use the `def` keyword 

--  We can define the relation `parity` on the integers ℤ
--  `parity a b` holds iff `a + b` is Even -/
-- def parity : ℤ → ℤ → Prop :=
-- by
--   intros a b, 
--   exact Even (a+b),


-- -- Lets prove this is an equivalence relation
-- -- 31
-- example : equivalence parity :=
-- by
--   split,
--   {
--     admit
--   },
--   split,
--   {
--     admit
--   },
--   {
--     admit
--   },


-- -- The relation `r a b` iff `a = b mod m` iff `m ∣ (b-a)`
-- def mod (m: ℤ) : ℤ → ℤ → Prop :=
-- by
--   intros a b, 
--   exact m ∣ (b-a),


-- -- 32
-- example :∀ (m:ℤ), equivalence (mod m) :=
-- by
--   admit


