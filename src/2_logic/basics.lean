import Mathlib.Data.Real.Basic
variable (P Q R S : Prop)
variable (A B C D : Type)
variable (a b c d k m n x: ℕ)
open Function Set
/-
# Logic

In Lean a `Prop` is any true/false statement. 

For example: `3 = 2`  or `x = 7 → x is prime` or 
`∀ (n:ℕ), 2 ∣ n` or `∃ (k:ℕ), even k ∧ ¬ prime k` -/

--#check 3 = 2
--#check x = 7 → prime x
--#check ∀ (n:ℕ), 2 ∣ n
--#check ∃ (k:ℕ), even k ∧ ¬ prime k

/-
If we have `(P : Prop)` then `P` is a proposition, so it is
a statement that is either true or false. 

So what is `(hp : P)`? It is simply a proof that P is true.
Or equivalently `hp` is the hypothesis that P is true.

# Tactics

We will use the three basic tactics from last time: `exact`, `intro`, `apply`

# exact
If our goal is `⊢ P` and we have a term `hp : P` then 
we can close it with `exact hp`

# intro(s)
If our goal is `⊢ P → Q` then `intro hp` introduces a term `(hp : P)`
into our local context and our goal changes to `⊢ Q`.

# apply
If our goal is `⊢ Q` and we have a term `(hpq : P → Q)` then
`apply hpq` changes our goal to `⊢ P`

(We think of this as : we know `P implies Q`, so if our goal is `Q` it
suffices to prove `P` and then `Q` follows.) 

# New tactic: refl

# refl 
If our goal can be proved by `reflexivity` then `refl` will close it.
For example  `P = P` or `P ↔ P` -/

-- 01 `if and only if` `↔` is reflexive so refl works here
example : P ↔ P :=
by
  rfl


-- 02 Equality is also reflexive so again `refl` will work
example : P = P := 
by
  rfl


/- Unless told otherwise, Lean assumes numerals refer to natural
numbers i.e. ℕ = {0, 1, 2,...} also known as `nats`.

If we do operations such as ` + - / * ^ % ` with nats then the result is
also a nat. -/

-- 03
example : 1 + 1 = 2 :=
by
  rfl

-- 04 
example : 12 * 25 = 300 :=
by
  rfl


-- 05
example : 7 - 3 = 2 ^ 2 :=
by
  rfl


-- 06
example : 2 - 3 = 0 := -- yes 2 - 3 = 0 in Lean
by
  rfl


-- 07  `a % b` is the remainder of `a` after division by `b`.
example : 18 % 7 = 4:=
by
  rfl

-- 08  Remember everything here is a natural number
example (n : ℕ): (12 / 5)^4  = 4^(5 / 2) * n^ (3 - 4) :=
by
  rfl


-- 09 `refl` can also see through definitions 
example  (f : A → B) : Injective f ↔ ∀ (x y : A), f x = f y → x = y :=
by
  rfl


-- 10 
example (f : A → B) : Surjective f ↔ ∀ (b:B), ∃ (a:A), f a = b:=
by
  rfl


/- We give the next example a name because it captures one of the fundmental 
   properties of `Prop` in Lean: 
           `Any two proofs of the same Prop are equal` -/
-- 11 
lemma proof_irrelevance (P : Prop) (h1 : P) (h2 : P) : h1 = h2:=
by
  rfl


/- The same isn't true for most Types. 
   [Qu: what can you say about types for which this is true?] -/
-- 12
example (A : Type) (a1 : A) (a2 : A) : a1 = a2:=
by 
  sorry -- don't try to prove this it isn't true without further assumptions about A!


-- 13 Any proposition implies itself
example  : P → P :=
by
  intro hp -- introduce the hypothesis `hp : P` in the local context
            -- our goal is now `⊢ P` so we can accomplish this with
  exact hp


-- 14 If P is true and P → Q is true then Q is true
example (hp : P) (hpq : P → Q) : Q :=
by
  exact hpq hp



/-  # There is no special `implies` symbol in Lean

As we have just seen we don't have a different symbol for `implies` we just reuse `→` 
that was introduced earlier for functions. 

So if `(A B : Type)` and `(P Q : Prop)` what is the difference between
 `f : A → B` and `hpq : P → Q` ?

`f` is a function mapping terms of type `A` to terms of type `B`, while `hpq` is a 
function mapping terms of type `P` to terms of type `Q`. 

The crucial difference is that `A` and `B` have type `Type` while `P` and `Q` have 
type `Prop`

Interpreting a term of type `P` as a proof of `P` then we can think of `hpq : P → Q` as 
a function mapping proofs of P to proofs of Q. -/


-- 15
example : P → Q → P :=
by
  intro hp _
  exact hp


-- 16
example : P → (P → Q) → (Q → R) → R :=
by
  intro p pq qr
  apply qr
  apply pq 
  exact p


-- 17
example  : (P → Q → R) → (Q → R → P) → (R → Q → P) :=
by
  intro _ qrp r q
  apply qrp 
  exact q
  exact r


/-
# New tactic: rw

# rw
rw is short for rewrite, it allows us to rewrite using equations and equivalences.

For example if we have `h : a = b` and our goal is `⊢ a + c = b + c` then `rw h` will replace
`a` by `b` in the goal so it becomes `⊢ b + c = b + c`  (which we can then close with `refl`) 

We can tell `rw` to do the rewrite on a term in our local context.
For example if we have `h1 : a = b` and `h2 : a = c` we can use `rw h1 at h2` to convert h2
into `h2 : b = c`

rw works from left to right, so given `h : a = b`, `rw h` will replace each `a` in the goal by `b`.
If we want to instead replace each `b` by `a` we can use `rw ← h` to rewrite from right to left.  -/

-- 18 We can do this be rewriting 
example (h1 : a = b) (h2 : b = c) (h3: c = d) : a = d:=
by
  rwa [h1,h2]


-- 19 We start with a rewrite in the local context
example (h1 : a = b) (h2 : b = c) (h3: c = d) : a = d :=
by
  rw [h1] 
  rwa [h3] at h2


-- 20 We can start by rewriting from right to left using `hqr : Q ↔ R`
example  (hpq : P ↔ Q) (hqr : Q ↔ R) : P ↔ R:=
by
  rwa [hpq]
 


-- 21
example  (f g : A → B) (hfg : Injective f ↔ Injective g) 
(hg : ∀ (x y: A), g x = g y → x = y)  : Injective f:=
by
   rw [hfg]
   intro a b h
   apply hg
   assumption


-- 22 -- symmetry may be useful here..
example (f: A → ℕ) (x y : A) (hf : f x = f y → x = y) 
(hfx: f x = n) (hfy: f y = m) (heq: m = n) : x = y:=
by  
  apply hf
  rw [hfx,hfy]
  exact heq.symm



