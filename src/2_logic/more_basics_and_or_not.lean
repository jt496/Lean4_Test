variable (P Q R S : Prop)

/- 
Lean has the logical connectives  `and`, `or`, `not` built-in.

Lean has special tactics to help us deal with them. 

New tactics: `cases'`, `split`, `left` and `right`

# And (conjunction)

 `P and Q` is written  `P ∧ Q`. This is True iff P and Q are both True.

# cases 

 Given `h : P ∧ Q` in the local context we can use `cases h with hp hq` 
 to get the two parts so `hp : P` and `hq : Q` replace `h : P ∧ Q` -/ 

-- 01
example (h : P ∧ Q) : P:=
by
  exact h.1


/- If our goal is `⊢ P ∧ Q` then we can use `split` to create two new goals
one `⊢ P` and the other `⊢ Q` -/

-- 02
example (hp : P) (hq : Q) : P ∧ Q := by 
apply And.intro 
exact hp
exact hq



/- 
Dot notation: if we have `(hpq : P ∧ Q)` then `hpq.1 : P` and `hpq.2 : Q`

(This `dot` notation is very common in Lean.)

Conversely if we have `(hp : P)` and `(hq : Q)` then `⟨hp,hq⟩ : P ∧ Q` 
i.e. `⟨hp,hq⟩` is a term of type `P ∧ Q`. 

The angled brackets are typed `\<` and `\>` -/
-- 03
example (hpq : P ∧ Q) : Q ∧ P :=by
apply And.intro  
exact hpq.2
exact hpq.1
  -- or more simply `exact ⟨hpq.2,hpq.1⟩,`


-- Having introduced `→` and `∧` we get `iff` (written `↔`) for free
-- `P ↔ Q` is:  `P → Q` and `Q → P`
-- 04
example : P ∧ Q ↔ Q ∧ P := by
apply Iff.intro
· intro pq
  exact ⟨pq.2,pq.1⟩
· intro qp
  apply And.intro
  exact qp.2
  exact qp.1






-- 05 
example : P ∧ Q → Q :=by
  intro h
  exact h.2


-- in Lean `P ∧ Q ∧ R` means `P ∧ (Q ∧ R)` (∧ is right-associative)
-- Find a single line `exact ...` solution to the following.
-- (Hint: what are h.1 and h.2 in this example?)
-- 06
example  (h: P ∧ Q ∧ R ∧ S ) : R :=by
  exact h.2.2.1


-- 07
example : P → Q → P ∧ Q :=by
  intro p q
  exact ⟨p,q⟩


-- 08
example : P ∧ Q → Q ∧ R → P ∧ R :=by
  intro pq qr
  exact ⟨pq.1,qr.2⟩

-- 09
example :  P ∧ R ∧ Q → Q ∧ P ∧ R :=by
  intro pqr
  exact ⟨pqr.2.2,pqr.1,pqr.2.1⟩
  

/-
   # Or (disjunction)

The proposition `P or Q` is written  `P ∨ Q`. 
 
 `P ∨ Q` is True iff P is True or Q is True.

If our goal is `⊢ P ∨ Q` then we can accomplish this by either giving a term
of type `P` or a term of type `Q`. We indicate which by using `left` for `P`
and `right` for Q.
 -/

-- 10
example (hp : P) : Q ∨ P :=by
exact Or.inr hp


/-
Given `(hpq : P ∨ Q)` in the local context we can use `cases hpq with hp hq` 
to split our goal into two subgoals, one in which `hp : P` and the other
in which `hq : Q`
-/
-- 11
example (hpq : P ∨ Q) : Q ∨ P :=by
cases hpq with
| inl hp => exact Or.inr hp
| inr hq => exact Or.inl hq

-- 12 
example : (P ∨ Q) ∧ (P → Q) → Q :=by
  intro ⟨hporq,hpq⟩
  cases hporq with
  | inl hp => apply hpq hp
  | inr hq => exact hq


-- 13 
example : (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R):=by 
intro ⟨pq,pr⟩
cases pq with
| inl p => exact Or.inl p
| inr q => cases pr with
          | inl p => exact Or.inl p
          | inr r=>  exact Or.inr ⟨q,r⟩
  


-- 14 
example : (P ∨ Q) ∧ (R ∨ S) → (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S):=by
intro ⟨pq,rs⟩
cases pq with
| inl p => cases rs with
          | inl r => exact Or.inl ⟨p,r⟩
          | inr s => apply Or.inr $ Or.inl ⟨p,s⟩
| inr q => cases rs with
          | inl r => exact Or.inr $ Or.inr $ Or.inl ⟨q,r⟩
          | inr s => apply Or.inr $ Or.inr $ Or.inr ⟨q,s⟩
          

example  (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
apply Iff.intro
· intro ⟨hp,hqr⟩
  cases hqr with
  |inl hq => exact Or.inl ⟨hp,hq⟩
  |inr hr => exact Or.inr ⟨hp,hr⟩
· intro hpqpr 
  cases hpqpr with
  |inl hpq => exact ⟨hpq.1,Or.inl hpq.2⟩
  |inr hpr => exact ⟨hpr.1,Or.inr hpr.2⟩


/-
There are two special propositions : `False` and `True`

To prove `True` we use `triv`

You shouldn't be able to prove `False`.

If you have `False` in the local context then you have a `contradiction`
-/
#check True
-- 15
example : True :=by trivial





-- 16
example: P → True :=by
intro _ 
trivial


-- 17
example : False → P:=by
intro f
contradiction


-- 18
example : False → True:=by
intro _
trivial


-- 19 
example : True → False → True → False → True :=by
intro _ _ _ _
trivial



/- 
# Negation

If `P : Prop` then `not P` is denoted `¬ P` this is defined to be `P → False`  -/
-- 20
example : ¬P ↔ (P → False):=by 
apply Iff.intro
· intro hnp hp
  contradiction
· intro hpf hnp
  exact hpf hnp

  
-- 21
example : ¬ True → False :=by
intro nt
apply nt
trivial

-- 22
example : ¬ False → True :=by
intro _ 
trivial


-- 23
example : P → ¬¬P :=by
intro hp
intro nnp 
contradiction

-- 24
example (hp : P) (hnp : ¬ P) : Q ∧ R → ¬ Q  :=by
intro _ _
contradiction

-- Can you explain how the following proof works?
-- 25
example (hp : P) (hnp : ¬ P) : Q :=by
cases (hnp hp) -- Hint: what is `(hnp hp)`?


