import Mathlib.Data.Nat.Basic


namespace Nat
/-
In Lean the natural numbers `ℕ` are defined as follows:

inductive nat
| zero : nat
| succ (n : nat) : nat

This means that there are two ways to construct a natural number `n:ℕ`
Either `n` is `zero` or it is the successor of a previously constructed 
natural number `succ n`. -/

--#check zero
--#reduce succ 3
--#check succ (succ zero)
--#check zero.succ


#check Nat.zero_add
/-
Addition is defined inductively in Lean:

def add : ℕ → ℕ → ℕ
| a  zero     := a                    --  a + 0 := a
| a  (succ b) := succ (add a b)       --  a + (b + 1) := (a + b) + 1

-/

-- We will use the `dot` notation for the successor function.
/--  n + 1 = n.succ -/
lemma Succ_eq_add_one (n : ℕ) :  n.succ = n + 1  :=
by rfl


/- 
We are now proving lemmas/theorems that already exist in `mathlib`.

To avoid clashes we will use the same names as `mathlib` but they will be Capitalised.

We won't use high level tactics such as `norm_num` or `linarith` but we will 
need to use earlier results as we progress (mainly with `rw` and `apply` tactics).   

For a much more complete tour of the natural numbers check out the Natural Numbers Game:

https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/

-/

lemma Add_zero (n : ℕ) : n + 0 = n :=
by rfl



/-- a + (b + 1) = (a + b) + 1 -/
lemma Add_succ (a b : ℕ) : a + b.succ = (a + b).succ:=
by rfl
 


/-
# New tactic for ℕ: induction 

If we want to prove `∀ (n:ℕ), P n` then we can use 
`induction n` which requires us to prove two things: 
`P 0` and `P n →  P n.succ`

# New tactic for structured proofs: have 

Sometimes we want to prove intermediate results within a proof.

We can do this using the `have` tactic. 

If we need to prove `h : P` (ie a proof that the proposition P is true)
then we can do this as follows:

.... middle of a proof
have h : P, 
{
  proof of P,
},
.... continue proof

We now have `h : P` in the local context.

# Variant of rw : rwa 

If we have term in the local context `h1 : P` and after `rw h2` our goal becomes `⊢ P`
then `rwa h2` will do the `rw h2, exact h1` in one step. 

(The `a` in `rwa` stands for `assumption` which is yet another tactic that will work whenever 
our goal is closed by a term in the local context.) -/

lemma Zero_add  :∀ n:ℕ, 0 + n = n 
  | zero => rfl
  | n+1 => congrArg succ (Zero_add n) 


lemma Succ_add (a b : ℕ) : a.succ + b = (a + b).succ:= by
cases b with
| zero => rfl
| succ b =>  exact congrArg succ (Succ_add a b)  



/- Digression: how do we know that 0 ≠ 1? 
This is one of the axioms of the natural numbers (Peano arithmetic)
and it is built into Lean's model of ℕ.  -/

theorem Succ_ne_zero (n : ℕ) : n.succ ≠ 0 :=by 
  intro hn 
  contradiction

-- Lean also knows that the successor function is injective (by definition)
theorem Succ.inj (n m : ℕ) : n.succ = m.succ → n = m :=by
  exact Nat.succ.inj


/- Our next result says that `+` is `associative`

In Lean `a + b + c` is defined as `(a + b) + c` so whenever you see an expression such as `a + b + c + d`
you need to remember how this is read by Lean: `((a + b) + c) + d`

We know that the brackets aren't required, but in Lean you need to prove this.
-/
--#check 1 + (2 + 4) -- brackets
--#check (1 + 2) + 4 -- no brackets

lemma Add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c):=by
  induction' c with n ih
  rfl
  rw [Add_succ,ih,Add_succ,Add_succ]

lemma Add_comm (a b : ℕ) : a + b = b + a :=by
  induction' b with b ib
  rw [Zero_add,Add_zero]
  rw [Succ_add,Add_succ,ib]

-- /-
-- Multiplication is also defined inductively in Lean.

-- def mul : ℕ → ℕ → ℕ
-- | a 0     := 0                      --  a * 0 := 0
-- | a (b + 1) := (mul a b) + a        --  a * (b + 1) = (a * b) + a  -/

lemma Mul_zero (n : ℕ) : n * 0 = 0:=by
rfl


lemma Mul_succ (m n : ℕ) : m * n.succ = m * n + m:=by
rfl


lemma Succ_mul (m n : ℕ) : m.succ * n = m * n + n:=by
induction' n with n hn
rfl
rw [Mul_succ,hn,Mul_succ,Add_assoc,Add_assoc,Add_succ,Add_succ m,Add_comm n]

lemma Zero_mul (n : ℕ) : 0 * n = 0:=by
induction' n with n hn
rfl
rw [Mul_succ, hn]

lemma Mul_one (n : ℕ) : n * 1 = n:=by
rw [Mul_succ,Mul_zero,Zero_add]


lemma One_mul (n : ℕ) : 1 * n = n:=by
induction' n with n hn
rfl
rw [Mul_succ,hn]


lemma Mul_add (a b c: ℕ) : a*(b + c) = a*b + a*c:=by
induction' a with a ha
rw [Zero_mul,Zero_mul,Zero_mul]
rw [Succ_mul,ha,Succ_mul,Succ_mul,Add_assoc,Add_assoc, Add_comm (a*c),Add_comm (a*c),Add_assoc]


lemma Add_mul (a b c: ℕ) : (b + c)*a = b*a +c*a:=by
induction' a with a ha
rfl
rw [Mul_succ,ha,Mul_succ,Mul_succ,Add_assoc,Add_assoc, Add_comm (c*a),Add_comm (c*a),Add_assoc]



lemma Mul_comm (a b : ℕ) : a * b = b * a :=by
induction' b with b hb
rw [Zero_mul]
rfl
rw [Mul_succ,hb,Succ_mul]

lemma Mul_assoc (a b c : ℕ) : a * b * c = a * (b * c):=by
induction' c with c hc
rw [Mul_zero] 
rfl
rw [Mul_succ,Mul_succ,hc,Mul_add]

lemma Pow_zero (n : ℕ) : n ^ 0 = 1:=by
rfl

lemma Pow_succ (a b : ℕ) : a^b.succ= a^b * a:=by
rfl

lemma Pow_one (n : ℕ) : n ^ 1 = n:=by 
rw [Pow_succ,Pow_zero,One_mul]

-- /-
-- # New use of tactic : cases 

-- We don't need induction to prove our next result, but we do need to consider the cases of zero and 
-- successor separately. The `cases n` tactic does exactly this.   -/

lemma Zero_pow (n : ℕ) (h : n ≠ 0): 0 ^ n = 0:=by
  cases' n with n
  contradiction
  rw [Pow_succ,Mul_zero]



lemma One_pow (n : ℕ) : 1 ^ n = 1:=by
induction' n with n hn
rw [Pow_zero]
rwa [Pow_succ,Mul_one]


lemma Pow_add (a b c: ℕ): a^(b + c)=a^b*a^c:=by
induction' c with c hc
rw [Add_zero,Pow_zero,Mul_one]
rw[Add_succ,Pow_succ,Pow_succ,← Mul_assoc,← hc]


lemma Pow_mul (a b c : ℕ) : a^(b * c) = (a^b)^c :=by
induction' c with c hc
rfl
rw [Pow_succ,Mul_succ,Pow_add,hc]


lemma Two_eq_one_add_one : 2 = 1 + 1:=by
rfl

lemma Two_mul (n : ℕ) : 2*n = n + n:=by
rw [Two_eq_one_add_one,Add_mul,One_mul]


lemma Three_mul (n : ℕ) : 3*n = n + n + n:=
have h3: 3 = 2 + 1:= by rfl
by rw [h3,Add_mul,One_mul,Two_mul]

lemma Pow_two (n : ℕ) : n^2 = n*n:=by
rw [Two_eq_one_add_one,Pow_add,Pow_one]

lemma Add_sq (a b : ℕ) : (a + b)^2 = a^2 + 2*a*b + b^2 :=by
rw [Pow_two,Pow_two,Pow_two,Add_mul,Mul_add,Mul_add,Two_mul,
    Add_mul,Mul_comm b a,Add_assoc,Add_assoc,Add_assoc]

lemma Pow_three (n : ℕ) : n^3 = n*n*n:=by
  have h3: 3 = 2 + 1 := by rfl
  rw [h3,Pow_add,Pow_two,Pow_one]


lemma Add_cube (a b : ℕ) : (a + b)^3 = a^3 + 3*a^2*b + 3*a*b^2 + b^3:=by
simp_rw [Pow_three,Pow_two,Add_mul,Mul_add,Add_mul,Three_mul,
        Add_mul,Add_assoc]
apply congrArg (λ x => a*a*a+x)
rw [Mul_comm, Mul_assoc]
apply congrArg (λ x => a*(a*b)+x)
apply congrArg (λ x => a*(a*b)+x)
simp_rw [←Add_assoc,Add_comm,Mul_comm b,Mul_assoc,Add_assoc]
apply congrArg (λ x => a*(b*b)+x)
apply congrArg (λ x => a*(b*b)+x)
simp_rw [Mul_comm b a,Add_assoc]
apply congrArg (λ x => a*(a*b)+x)
simp_rw [←Mul_assoc, Mul_comm b a]


