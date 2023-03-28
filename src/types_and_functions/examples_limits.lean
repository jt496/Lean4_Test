import Mathlib.Data.Real.Basic

/- 
Lean is a programming language which can be used to prove maths theorems.

Here we will prove a theorem from 1st year analysis: 

  If `xₙ → s` and `yₙ → t` then `xₙ + yₙ → s + t`  

(Don't worry if the code below doesn't mean anything to you, this example is
simply intended to show you what Lean can do.)

-/

def limit (x : ℕ → ℝ) (l : ℝ) : Prop := 
∀ ε > 0, ∃ K, ∀ n, n ≥ K → |x n - l| < ε 


theorem sum_limits (x y : ℕ → ℝ) (s t : ℝ) (hx : limit x s) (hy : limit y t) :
  limit (λ n => x n + y n) (s + t) :=
by
  intros ε hε                    -- Given ε ∈ ℝ satisyfing ε > 0
  dsimp                           -- simplify for the reader
  specialize hx (ε/2)            -- use the hypothesis xₙ → s with ε/2
  specialize hy (ε/2)            -- use the hypothesis yₙ → t with ε/2 
  have : (ε/2) > 0 := half_pos hε -- need to check that ε/2 > 0 
  cases' hx this with A hA         -- obtain A ∈ ℕ using ε/2 > 0 and xₙ → s
  cases' hy this with B hB         -- obtain B ∈ ℕ using ε/2 > 0 and yₙ → t
  clear hx hε hy this             -- clear statements we no longer need
  use max A B                     -- use the max(A,B) as our "K"
  intros n hn                     -- given n ∈ ℕ with n ≥ max(A,B) need to prove..
  -- we can prove intermediate results and use them later
  have AleM : A ≤ max A B := le_max_left A B -- A ≤ max(A,B)
  -- We now have `A ≤ max(A,B)`and `max(A,B) ≤ n` so Lean can deduce `A ≤ n`
  have Alen : A ≤ n := AleM.trans hn
  specialize hA n Alen 
  specialize hB n (le_trans (le_max_right A B) hn) 
  -- Need to rearrange terms -- use the `ring` tactic 
  have rearrange: x n + y n  - (s + t) = (x n - s) + (y n - t) := by ring
  rw [rearrange]  -- rewrite this rearranged expression in the goal
  -- Now apply triangle-inequality
  have tri: |x n  - s + (y n - t)| ≤ |x n - s| + |y n - t| := abs_add _ _
  apply lt_of_le_of_lt tri 
  rw [← add_halves ε]
  apply add_lt_add hA hB

-- #print sum_limits
