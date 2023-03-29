import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic.Tauto

open Finset Nat Classical

/- 

Basic Ramsey theory for graphs

**Main results** 

1). Upper bound (Ramsey's Theorem) R(s+1,t+t) ≤ (s+t).choose s (DONE)

Ramsey (s t : ℕ)  : Ramsey_of ((s + t).choose s) s.succ t.succ :=

2). Lower bound (Erdos prob): if (n.choose s) < 2^((s.choose 2)-1) then n < R(s,s)
(but written without division)

 Ramsey_lower_bound (s n : ℕ) (hn: 2 ≤ s ) :
(n.choose s) * 2 * (2^((n.choose 2) - (s.choose 2) )) < 2^(n.choose 2) → ¬ Ramsey_of n s s 

3). Existence of k-colour 2-graph Ramsey numbers and Schur's theorem
kcol_Ramsey (s: Fin k.succ → ℕ) : ∃ n, kRamsey_of n s

4).  Schur's theorem: for any k, there exists n such that in any k-coloring of ℕ there is
a monochromatic solution to x + y = z with x,y,z < n
Schur' (k:ℕ) : ∃ (n:ℕ), Schur n k


-/
open Finset Nat 

section twocolour

/-- Only two colours for now. We can think of 0 as red and 1 as blue -/
lemma  fin_two_not (a : Fin 2) : ¬ a = 0 ↔ a = 1 :=by
  apply Iff.intro
  · intro hn0
    have h1: (a:ℕ).succ ≤ 2:=a.2
    rw [succ_le_succ_iff] at h1
    rw [← Fin.val_eq_val] at *
    apply le_antisymm h1
    rwa [one_le_iff_ne_zero]
  · intro h1 h0
    rw [h0] at h1 
    exact Fin.zero_ne_one h1



/- flip a colour -/
def not_c (c : Fin 2) : Fin 2:= if (c = 0) then 1 else 0

/-- not not  -/
lemma not_not_c (c : Fin 2) : not_c (not_c c) = c:=
by
  rw [not_c,not_c]
  split_ifs with h
  contradiction
  exact h.symm
  rw [fin_two_not] at h
  exact h.symm
  contradiction

/-- the flipped colouring given by swapping all colours -/
def col_flip (col : Finset ℕ → Fin 2) (A: Finset ℕ) : Fin 2 :=  (not_c (col A))

/-- A col is mono on a set A iff every pair in the set receives the same colour  -/
def mono_c_on (A : Finset ℕ) (col : Finset ℕ → Fin 2) (c :Fin 2) :  Prop:= 
∀ (e : Finset ℕ), e ∈ Finset.powersetLen 2 A → col e = c

/-- Trivially if A is empty or a singleton any colouring is mono on it-/
lemma mono_on_subsingleton {A : Finset ℕ} (h: A.card < 2) (col : Finset ℕ → Fin 2) (c : Fin 2) : mono_c_on A col c:=
by
  intro e he
  apply False.elim 
  rw [powersetLen_empty 2 h] at he  
  contradiction


/-- col is mono on A iff its flipped version is mono -/
lemma mono_flip  {A : Finset ℕ} {col : Finset ℕ → Fin 2} {c : Fin 2} : mono_c_on A col c ↔
mono_c_on A (col_flip col) (not_c c):=
by
  simp_rw [col_flip]
  dsimp
  apply Iff.intro
  intros hm e he
  dsimp
  rw [hm e he] 
  intro hm e he
  have t1:=hm e he
  dsimp at t1
  apply_fun not_c at t1
  simp_rw [not_not_c] at t1
  assumption



/-- A colouring col is a Ramsey_col for N s t if every n-set contains a red s-set or a blue t-set under col -/
def Ramsey_col (col : Finset ℕ → Fin 2) (N s t : ℕ) : Prop := 
∀ {V : Finset ℕ}, N ≤ V.card → (∃ (A : Finset ℕ), A ⊆ V ∧ ((mono_c_on A col 0 ∧ s ≤ A.card) ∨ (mono_c_on A col 1 ∧ t ≤ A.card)))


/-- N is Ramsey for s,t if every colouring is a Ramsey_col for n s t -/
def Ramsey_of (N s t : ℕ): Prop:= ∀ (col : Finset ℕ → Fin 2), Ramsey_col col N s t

/-- if N is Ramsey for s,t and N ≤ M then m is also Ramsey -/
lemma mono_Ramsey_of {N M s t: ℕ} (h : Ramsey_of N s t) (hm: N ≤ M) : Ramsey_of M s t :=
by
  intro col V h2
  exact  h col (hm.trans h2)


/-- given a Finset V and n ∉ V the nbhd_col c is the set of w ∈ V such that col {w, n} = c -/
def nbhd_col {n : ℕ}  (col : Finset ℕ → Fin 2) (c : Fin 2) {V: Finset ℕ}(hV: n ∉ V) : Finset ℕ:= V.filter ( λ w => col (insert w {n}) = c)  

/-- rw lemma for nbhd_col -/
lemma col_nhbd_col {n w: ℕ} {col : Finset ℕ → Fin 2} {c: Fin 2}{V : Finset ℕ}(hV: n ∉ V)  (hw: w ∈ nbhd_col col c hV) : col (insert w {n}) = c:=
by
  exact (mem_filter.1 hw).2


/-- Any vertex in nbhd_col is in the original set V -/
lemma mem_col_nbhd_range {v : ℕ} {n : ℕ} {col : Finset ℕ → Fin 2} {c: Fin 2} {V : Finset ℕ}{hV: n ∉ V} (hv :v ∈ nbhd_col col c hV): v ∈ V:=
by
  exact (mem_filter.1 hv).1


/-- Any subset of nbhd_col is a subset of V -/
lemma col_nbhd_sub_range {n : ℕ} {col : Finset ℕ → Fin 2} {c: Fin 2} 
{A V : Finset ℕ}{hV: n ∉ V} (hA: A ⊆ nbhd_col col c hV) : A ⊆ V:=
by
  intros v hv 
  exact mem_col_nbhd_range (hA hv)


/-- the sets {b,a} and {a,b} are equal (note the proof is not refl)-/
lemma insert_eq' (a b : ℕ)  : (insert a {b}: Finset ℕ)= insert b {a} :=by
ext x
apply Iff.intro
· intro h
  rw [mem_insert,  mem_singleton] at * 
  rwa [or_comm]
· intro h
  rw [mem_insert,  mem_singleton] at * 
  rwa [or_comm]

/-- Given an edge from n to the c-coloured nbhd of n it has colour c-/
lemma mono_nbhr {n : ℕ}{A V e: Finset ℕ} {col: Finset ℕ → Fin 2} {c : Fin 2} {hV: n ∉ V} (hnb: A ⊆ nbhd_col col c hV) 
(he: e ∈ image (insert n) (powersetLen 1 A)): col e = c:=by
  simp_rw [mem_image, mem_powersetLen,card_eq_one] at he
  obtain ⟨B,⟨h1,⟨b,rfl⟩⟩,h3⟩:=he
  rw [←h3,insert_eq']
  exact col_nhbd_col hV ((h1.trans hnb) (mem_singleton_self b))


/-- If A is mono c and contained in the set of c-col nbhrs of n then A ∪ {n} is also mono c-/
lemma mono_c_ext  {n : ℕ}{A V : Finset ℕ} {col: Finset ℕ → Fin 2} {c : Fin 2} {hV: n ∉ V}
 (hm : mono_c_on A col c) (hnb: A ⊆ nbhd_col col c hV) :
mono_c_on (insert n A) col c:=by
  intros e he
  rw [powersetLen_succ_insert,mem_union] at he
  cases' he with he he
  exact hm e he
  exact (mono_nbhr hnb he)
  exact not_mem_mono (col_nbhd_sub_range hnb) hV

/-- red and blue nbhds of n are disjoint-/
lemma  nbhd_col_disj {n : ℕ} {V : Finset ℕ} (col : Finset ℕ → Fin 2)   (hV: n ∉ V): Disjoint (nbhd_col col 0 hV ) (nbhd_col col 1 hV):=by
  unfold nbhd_col 
  intros w hw0 hw1 x hx
  have hx0:=hw0 hx
  have hx1:=hw1 hx
  dsimp at *
  simp_rw [mem_inter,mem_filter] at *
  apply False.elim
  rcases hx0 with ⟨_,hx0⟩
  rcases hx1 with ⟨_,hx1⟩
  rw [hx0] at hx1
  apply Fin.zero_ne_one hx1


/- union of red and blue nbhds of n ∉ V is V-/
lemma  nbhd_col_union_eq {n : ℕ} {V : Finset ℕ} (col : Finset ℕ → Fin 2) (hV: n ∉ V) : (nbhd_col col 0 hV) ∪ (nbhd_col col 1 hV) = V :=by
  unfold nbhd_col
  convert filter_union_filter_neg_eq (λ w => col (insert w {n})  = 0) V
  simp_rw [fin_two_not]


/-- sum of red and blue nbhds is |V| -/
lemma card_col_nbhd {n : ℕ} {V : Finset ℕ} (col : Finset ℕ → Fin 2)   (hV: n ∉ V) :
V.card = (nbhd_col col 0 hV).card + (nbhd_col col 1 hV).card :=by
  have :=card_union_eq (nbhd_col_disj col hV)
  rwa [nbhd_col_union_eq] at this


/-- The inequality we require for the inductive step in Ramsey's theorem -/
lemma nbhd_cards_add_imp {a b c d: ℕ} :  a + b - 1 ≤ c + d  → a ≤ c ∨ b ≤ d:=by
  intros h
  contrapose h
  push_neg at h
  change c.succ ≤ a ∧ d.succ ≤ b at h
  have :=add_lt_add_of_le_of_lt h.1 h.2 
  rw [succ_add] at this
  exact (not_le_of_gt (le_pred_of_lt  this))


/-- Key step  R (s+1,t+1) ≤ R(s,t+1) + R(s+1,t) -/
lemma Ramsey_step {a b s t : ℕ} (hab : 1 ≤ a + b): Ramsey_of a s t.succ → Ramsey_of b s.succ t 
→ Ramsey_of (a+b) s.succ t.succ:=by
  intro ra rb col W hc
  --- Need to show W contains a set of size s+1  that is red or t+1 that is blue
  -- Since 0 < a+b , so W is non-empty and we can find a element n ∈ W. 
  -- We work in the nbhd of n, which is V := W.erase n
  obtain ⟨n,hn⟩:=card_pos.1 (hab.trans hc)
  set V:= W.erase n with hVr
  -- n ∉ V
  have hV:=not_mem_erase n W 
  -- |V| = |W|-1
  have hVc:=card_erase_of_mem hn
  rw [← hVr] at hVc
  have :=pred_le_pred hc 
  rw [← pred_eq_sub_one] at hVc; rw [← hVc] at this
  rw [ card_col_nbhd col hV,pred_eq_sub_one] at  this
  -- Have a + b - 1 ≤ |V0| + |V1| (so we can apply previous lemma to say..)
  cases' nbhd_cards_add_imp this with h h
 --- Case 1) a ≤ |V0| so we use Ramsey_of a s t+1 to get set C ⊆ A such that either 
  rcases ra col h with ⟨C,hC1,⟨hR2,hR3⟩| ⟨hB2,hB3⟩⟩ 
  use (insert n C)
  refine' ⟨insert_subset.2 ⟨hn,(col_nbhd_sub_range hC1).trans (erase_subset n W)⟩,_⟩
  left
  refine' ⟨mono_c_ext hR2 hC1,_⟩
  convert succ_le_succ hR3
  apply card_insert_of_not_mem
  intro hnR; exact  hV (mem_col_nbhd_range (hC1 hnR))
  exact  ⟨C,(col_nbhd_sub_range hC1).trans  (erase_subset n W),Or.inr ⟨hB2,hB3⟩⟩
  rcases rb col h with ⟨C,hC1,⟨hR2,hR3⟩| ⟨hB2,hB3⟩⟩
  exact ⟨C,(col_nbhd_sub_range hC1).trans  (erase_subset n W), Or.inl ⟨hR2,hR3⟩⟩
  use (insert n C)
  refine' ⟨insert_subset.2 ⟨hn,(col_nbhd_sub_range hC1).trans (erase_subset n W)⟩,_⟩
  right
  refine' ⟨mono_c_ext hB2 hC1,_⟩
  convert succ_le_succ hB3
  apply card_insert_of_not_mem
  intro hnR;exact hV (mem_col_nbhd_range (hC1 hnR))
  

/-- Symmetry in (s,t) -/
lemma Ramsey_symm (s t n : ℕ) : Ramsey_of n s t → Ramsey_of n t s:=by
  intros h col V hV
  rcases (h (col_flip col) hV) with ⟨A,hA1,⟨hA2,hA3⟩ | ⟨hA2,hA3⟩⟩
  exact ⟨A,hA1, Or.inr ⟨mono_flip.2 hA2,hA3⟩⟩
  exact ⟨A,hA1,Or.inl ⟨mono_flip.2 hA2,hA3⟩⟩ 


/-- R(0,t) ≤ 0 and R(1,t) ≤ 1 -/
lemma Ramsey_lt_two {s t : ℕ} (h : s < 2): Ramsey_of s s t:=by
  intro col V hV
  obtain ⟨B,hB1,rfl⟩:=exists_smaller_set V s hV
  exact ⟨B,hB1,Or.inl ⟨mono_on_subsingleton h col 0,le_refl _⟩⟩


/-- R(0,t) ≤ 0 -/
lemma Ramsey_zero (t : ℕ): Ramsey_of 0 0 t:=
by
  exact Ramsey_lt_two zero_lt_two


/-- R(1,t) ≤ 1 -/
lemma Ramsey_one (t : ℕ): Ramsey_of 1 1 t:=
by
  exact Ramsey_lt_two one_lt_two


/-- R(s,2) ≤ s -/
lemma Ramsey_theorem_two (s : ℕ) : Ramsey_of s s 2:=
by
  intro col V hV
  by_cases h : ∃(e: Finset ℕ), e ∈ powersetLen 2 V ∧ col e = 1
  obtain ⟨e,he⟩:=h
  refine' ⟨e,(mem_powersetLen.1 he.1).1,Or.inr ⟨_, (mem_powersetLen.1 he.1).2.symm.le⟩⟩
  intros x
  have :=powersetLen_self e
  intros hx 
  rw [(mem_powersetLen.1 he.1).2] at this
  rw [this,mem_singleton] at hx
  convert he.2
  push_neg at h
  refine' ⟨V, le_refl V, _⟩
  left
  refine' ⟨_ ,hV⟩
  intros e he
  have := h e he
  dsimp at this
  rwa [← fin_two_not,not_not] at this



/-- Ramsey's theorem: R(s+1,t+1) ≤ (s+t).choose s -/
theorem Ramsey (s t : ℕ)  : Ramsey_of ((s + t).choose s) s.succ t.succ :=
by
  induction' s with s hs generalizing t
  rw [choose_zero_right] 
  exact Ramsey_one t.succ
  induction' t  with t ht generalizing s
  simp_rw [add_zero, choose_self]
  apply Ramsey_symm
  exact Ramsey_one _
  rw [succ_add,add_succ,choose_succ_succ,← add_succ]
  refine' Ramsey_step _ (hs t.succ) _ 
  change 0 < _ 
  apply add_pos
  refine' choose_pos _
  exact le_add_right (le_refl s)
  refine' choose_pos _
  rw [add_succ] 
  apply succ_le_succ (le_add_right (le_refl s))
  rw [add_succ,← succ_add]
  exact ht s hs


/-- R(3,3) ≤ 6-/
lemma R33 : Ramsey_of 6 3 3:=
by
  exact Ramsey 2 2


/-- R(3,4) ≤ 10 -/
lemma R34 : Ramsey_of 10 3 4:=
by
  exact Ramsey 2 3


/-- R(4,4) ≤ 20 -/
lemma R44 : Ramsey_of 20 4 4:=
by
  exact Ramsey 3 3


/-- R(5,5) ≤ 70 -/
lemma R55 : Ramsey_of 70 5 5:=
by
  exact Ramsey 4 4


/-- R(6,6) ≤ 252 -/
lemma R66 : Ramsey_of 252 6 6:=
by
  exact Ramsey 5 5




-- section lower_bounds


-- /-- If n is Ramsey for s then  for every coloring of range n by red/blue there is a subset
--  A of size at least s and a color c such that all pairs coloured of A colored by c.  -/
-- lemma Ramsey_of_range {n s: ℕ} (hr: Ramsey_of n s s) : ∀ (col: Finset ℕ → Fin 2),  
-- ∃ (A: Finset ℕ), ∃ (c : Fin 2), A ⊆ range n ∧ s ≤ A.card ∧ (∀ {e}, e ∈ powersetLen 2 A → col e = c ) :=
-- by 
--   intro col,
--   obtain ⟨A,hA1,⟨hA2,hA3⟩|⟨hA2,hA3⟩⟩:= hr col (card_range n).symm.le,
--   exact ⟨A,0,hA1,hA3, hA2⟩,
--   exact ⟨A,1,hA1,hA3,hA2⟩,
-- 


-- /-- n is not Ramsey for s if there is a 2-coloring such that for any color c ∈ {0,1}  and any s-subset S ⊆ range n 
-- there is a pair e ⊆ S that is not coloured c -/
-- theorem Ramsey_lb (s n: ℕ) : 
-- (∃ (col : Finset ℕ → Fin 2),∀ (c: Fin 2), ∀ (S ∈ powersetLen s (range n)), ∃ e, e ∈powersetLen 2 S ∧ col e ≠ c)  → ¬ Ramsey_of n s s :=
-- by
--   intros h hr,
--   obtain ⟨col,hc⟩:=h,
--   obtain ⟨A,c,hA1,hA2,hA3⟩:=(Ramsey_of_range hr) col,
--   obtain ⟨B,hB⟩:= exists_smaller_set A s hA2,
--   specialize hc c B, rw mem_powersetLen at hc,
--   obtain ⟨e,he1,he2⟩:=hc ⟨hB.1.trans hA1,hB.2⟩,
--   apply he2,
--   apply hA3,
--   exact powersetLen_mono hB.1 he1,
-- 

-- lemma Finset_fin2 : (univ: Finset (Fin 2)) = ({0}:Finset (Fin 2)) ∪ ({1}:Finset (Fin 2))  ∧ disjoint ({0}:Finset (Fin 2))  ({1}:Finset (Fin 2)):=
-- by
--   split,    
--   ext, simp_rw [mem_union,mem_singleton,mem_univ],
--   split,
--   intro h, by_cases a = 0, left , exact h, right, exact (fin_two_not _).1 h,
--   intro, triv,
--   intros x hx, 
--   simp only [inf_eq_inter, inter_singleton_of_not_mem, mem_singleton, Fin.one_eq_zero_iff, nat.one_ne_zero, not_false_iff,not_mem_empty] at hx,
--   exact hx,
-- 

-- lemma map_fin_eq {n : ℕ} (A: Finset (Fin n)) :Finset.Fin n (A.map Fin.coe_embedding) = A :=
-- by
--   ext, 
--   simp_rw [mem_fin, mem_map,Fin.coe_embedding_apply,  exists_prop,← Fin.ext_iff,exists_eq_right],
-- 

-- lemma map_fin_range {n : ℕ} (S: Finset (Fin n)) : S.map Fin.coe_embedding ⊆range n:=
-- by
--   intros x, 
--   rw [mem_map,mem_range],
--   rintro ⟨a,h1,h2⟩, rw Fin.coe_embedding_apply at h2,
--   subst_vars,
--   exact a.2,
-- 


-- /-- Equiv to show existence of coloring of Fin n with no mono K_s to showing coloring of ℕ -/
-- lemma fin_lb' (s n : ℕ) : (∃ (col : Finset ℕ → Fin 2), ∀(c: Fin 2), ∀ (S ∈ powersetLen s (range n)), ∃ e, e ∈powersetLen 2 S ∧ col e ≠ c)  ↔
-- (∃ (colf : Finset (Fin n) → Fin 2),∀ (c: Fin 2), ∀ (S:Finset (Fin n)), S.card = s →  ∃ e, e ∈ powersetLen 2 S ∧ colf e ≠ c) :=
-- by
--   split,
--   intro h, cases h with col hc,
--   set colf: Finset (Fin n) → Fin 2 :=  (λ s, col (s.map Fin.coe_embedding)),
--   use colf,rintros c S hS,
--   specialize hc c (S.map Fin.coe_embedding),
--   rw mem_powersetLen at hc,
--   rw card_map at hc, 
--   obtain ⟨e,he,hec⟩:=hc ⟨map_fin_range S,hS⟩,
--   simp_rw mem_powersetLen at he ⊢, 
--   rw subset_map_iff at he,
--   obtain ⟨hu,hf⟩:=he,
--   obtain ⟨u,H1,H2⟩:=hu,
--   refine ⟨u,⟨H1,_⟩,_⟩,
--   rwa [H2,card_map] at hf,
--   rw H2 at hec, exact hec, 
--   --
--   intro h, cases h with colf hc,
--   set col: Finset ℕ → Fin 2:=(λ s, if (s ⊆ range n) then (colf (s.Fin n)) else 0) with hcol,
--   use col, rintros c S hS,  rw mem_powersetLen at hS,
--   specialize hc c (S.Fin n),
--   cases hS with hr hc2,
--   have :=@fin_map n S, 
--   rw filter_true_of_mem at this,
--   rw [← this, card_map] at hc2,
--   obtain ⟨e,he,hec⟩:= hc hc2,
--   use (e.map Fin.coe_embedding),
--   rw mem_powersetLen at *, 
--   clear hc, rw card_map,refine ⟨⟨_,he.2⟩,_⟩,
--   cases he with he1 he2,
--   rw ← this, rw subset_map_iff, exact ⟨e,he1,rfl⟩,
--   convert hec, rw hcol,dsimp,split_ifs,
--   congr', exact map_fin_eq e,
--   exfalso, apply h, exact map_fin_range e,
--   intros x hx, exact mem_range.1 (hr hx),
-- 

-- open_locale classical
-- open fintype
-- variables {α β :Type*} [fintype α] [fintype β]

-- noncomputable
-- def equiv_sub_fun {α β :Type*} [fintype α] [fintype β] (p : α → Prop) (b : β): 
-- {f : α → β // ∀x, ¬ p x → f x = b} ≃ Π x:α, p x → β:=
-- { to_fun := λ f x hx, f.val x,
--   inv_fun := by
--     intros h, 
--     set f: α → β :=λ x, if hx: p x then (h x hx) else b with hf,
--     refine ⟨f,_⟩,
--     intros x hx , rw hf,
--     dsimp, simp only [dite_eq_right_iff],
--     intros h1, contradiction,
--   ,
--   left_inv := by
--     intros f,
--     simp only [subtype.val_eq_coe, dite_eq_ite],
--     ext,
--     simp only [subtype.coe_mk, ite_eq_left_iff],
--     intro hx, 
--     have :=f.property x hx, simp_rw ← this,
--     refl,
--   ,
--   right_inv := by
--   intros h, simp only [dite_not] at *,
--   ext, split_ifs, refl,
--   ,  }




-- def equiv_prop_true_fun (P: Prop) (h : P) [fintype β] : (P → β) ≃ β:=
-- { to_fun :=λ f, f h,
--   inv_fun := λ b,λ h1, b,
--   left_inv := by
--     intros h2,dsimp, simp only [eq_self_iff_true],
--   ,
--   right_inv := by
--     intro b, dsimp,refl,
--   , }

-- def equiv_prop_false_fun (P: Prop) (h : ¬P) [fintype β] : (P → β) ≃ unit:=
-- { to_fun :=λ f, punit.star,
--   inv_fun := by
--   intros u h1,exfalso,apply h h1,
--   ,
--   left_inv := by
--     intro f,dsimp, 
--     ext,contradiction, 
--   ,
--   right_inv := by
--   intro u,dsimp, simp only [eq_iff_true_of_subsingleton],
--   , }



-- lemma function_res_card  {α β :Type*} [fintype α] [fintype β] (p: α →Prop) (b : β):    
-- fintype.card  (Π x:α,p x → β) = card β ^(Finset.card (univ.filter (λx, p x))):=
-- by
--   simp only [fintype.card_pi],
--   have : ∀ a:α, (fintype.card (p a → β) = if (p a) then (card β) else 1),{
--     intros a,
--     by_cases p a, simp only [*, if_true] at *,
--     rw card_eq, use equiv_prop_true_fun _ h,
--     simp only [*, if_false] at *,
--     rw ← card_unit,
--     rw card_eq,  use equiv_prop_false_fun  _ h,},
--   simp_rw [this, prod_ite,  prod_const, one_pow, mul_one], 
-- 



-- lemma card_fun_res {α β :Type*} [fintype α] [fintype β] (p: α →Prop ) (b : β):
-- fintype.card ({f:α → β // ∀x, ¬ p x → f x = b}) = card β ^(Finset.card (univ.filter (λx,  p x))):=
-- by
--   rw ← function_res_card p b,
--   apply card_eq.2,  use equiv_sub_fun p b,
-- 

-- --subtype of 2-edge colorings of K_n
-- def twocol (n : ℕ) :Type*:= {A:Finset (Fin n) // A.card = 2} → Fin 2 

-- def flipcol {n : ℕ}: twocol n → twocol n :=
-- λ col e, not_c (col e)



-- def not_sub {n : ℕ} (S: Finset (Fin n)): {A:Finset (Fin n) // A.card = 2} → Prop:=λ e, ¬ ↑e ⊆ S  

-- def twocol_mono_c {n : ℕ} (c : Fin 2) (S: Finset (Fin n))  : twocol n → Prop :=
-- λ col, ∀ e: {A:Finset (Fin n) // A.card = 2}, e.val ⊆ S →  col e = c


-- def twocol_mono {n : ℕ} (S: Finset (Fin n))  : twocol n → Prop :=
-- λ col,  (∀ e: {A:Finset (Fin n) // A.card = 2}, e.val ⊆ S →  col e = 0) ∨ (∀ e: {A:Finset (Fin n) // A.card = 2}, e.val ⊆ S →  col e = 1) 



-- lemma flip_mono {n : ℕ} (c : Fin 2) (S: Finset (Fin n)) (col: twocol n) : twocol_mono_c c S col ↔ twocol_mono_c (not_c c) S (flipcol col):=
-- by
--   unfold twocol_mono_c flipcol, 
--   split,
--   intros h e he, rw h e he,
--   intros h e he, rw ← not_not_c c,
--   rw ←  h e he, rw not_not_c,
-- 


-- instance twocol_fintype (n : ℕ) : fintype (twocol n):=
-- by 
--   unfold twocol,
--   apply_instance,
-- 


-- /-- The number of k-edge colourings of K_n^r is...-/
-- lemma card_cols (n k r: ℕ) : fintype.card ({A:Finset (Fin n) // A.card = r} → Fin k )= k^(n.choose r):=
-- by
--   rw [fintype.card_fun, fintype.card_fin, fintype.card_Finset_len,fintype.card_fin],
-- 

-- lemma card_twocols (n : ℕ): fintype.card (twocol n)= 2^(n.choose 2):=card_cols n 2 2

-- lemma card_filter_powersetLen {n k: ℕ} (S: Finset (Fin n)): 
-- (filter (λ (x : {A: Finset (Fin n) // A.card = k}), ↑x ⊆ S) univ).card = S.card.choose k :=
-- by
--   dsimp, rw [← card_powersetLen k S, Finset.card_congr],
--   intros a h1 , rw mem_filter at h1, rw mem_powersetLen,
--   split, exact h1.2, exact a.property,
--   intros a b ha hb heq, 
--   exact subtype.eq heq,
--   intros b hb, rw mem_powersetLen at hb,
--   refine ⟨⟨b,hb.2⟩,_⟩,
--   rw [mem_filter,exists_prop], 
--   exact ⟨⟨mem_univ _, hb.1 ⟩,rfl⟩,
-- 

-- lemma card_filter_powersetLen_compl {n : ℕ} (k : ℕ) (S: Finset (Fin n)): 
-- (filter (λ (x : {A: Finset (Fin n) // A.card = k}), ¬↑x ⊆ S) univ).card = n.choose k - S.card.choose k :=
-- by
--   have :=@card_Finset_len (Fin n) _ k, 
--   rw fintype.card_Fin at this,
--   rw ← Finset.card_univ at this,
--   rw ← filter_card_add_filter_neg_card_eq_card  (λx : {A:Finset (Fin n)// A.card = k}, ↑x ⊆ S) at this,
--   rw [← this, card_filter_powersetLen S, add_tsub_cancel_left], 
-- 

-- /-- The number of 2-edge colorings of K_n that are mono c on a set S of size s is
--     2^(n.choose 2 - s.choose 2) -/
-- lemma card_mono_cols {n : ℕ} {c : Fin 2} {S: Finset (Fin n)}:  
-- fintype.card ({col: twocol n // twocol_mono_c c S col}) = 2^(n.choose 2 - S.card.choose 2):=
-- by
--   unfold twocol_mono_c,
--   have := @card_fun_res ({A:Finset (Fin n) // A.card = 2}) (Fin 2) _ _ (not_sub S) c,
--   unfold not_sub at this, simp_rw not_not at this,
--   rwa [ fintype.card_fin, card_filter_powersetLen_compl 2 S] at this, 
-- 


-- lemma Ramsey_lb_twocol {s n: ℕ} : 
-- (∃ col: twocol n, ∀ (c: Fin 2), ∀ (S:Finset (Fin n)), S.card = s →  ¬ twocol_mono_c c S col) → ¬ Ramsey_of n s s  :=
-- by
--   intro h, 
--   apply Ramsey_lb, rw (fin_lb' s n),
--   obtain ⟨col,hc⟩:=h,
--   set colf: Finset (Fin n) → Fin 2:= λ x, if hx: x.card = 2 then  col ⟨x,hx⟩ else 0 with hcolf,
--   use colf,intros c S hS,
--   specialize hc c S hS,
--   contrapose hc, rw not_not, push_neg at hc,
--   unfold twocol_mono_c, intros e he,
--   specialize hc ↑e, rw mem_powersetLen at hc,
--   rw hcolf at hc,
--   simp only [eq_self_iff_true, subtype.val_eq_coe, subtype.coe_eta, dite_eq_ite, and_imp] at *,
--   specialize hc he e.property, 
--   split_ifs at hc, exact hc,
--   exfalso, apply h, exact e.property,
-- 

-- open_locale big_operators


-- lemma card_card (Q: α → β → Prop) {a : α}: fintype.card ({b:β//Q a b}) = Finset.card {b: β| Q a b}.to_Finset :=
-- by
--   simp only [set.to_Finset_card, set.coe_set_of],
-- 

-- lemma subtype_pigeon_exist (F: Finset α) (p: α → β  → Prop) :
-- ∑ a in F, fintype.card {b : β // p a b} < fintype.card β → ∃ b, ∀ a, a ∈ F → ¬ p a b:=
-- by
--   simp_rw card_card p,
--   simp_rw Finset.card_eq_sum_ones, --simp,
--   intros hf, by_contra, push_neg at h,
--   rw sum_comm' _ at hf,
--   rotate,
--   exact (univ:Finset β),
--   intro b, exact {a:α| a∈F ∧ p a b}.to_Finset,
--   intros x y, 
--   simp_rw set.mem_to_Finset at *,
--   split,
--   rintros ⟨hx,hy⟩,  exact ⟨⟨hx,hy⟩,mem_univ _⟩,
--   intro h,  exact ⟨h.1.1,h.1.2⟩,
--   simp_rw sum_const at hf,
--   simp only [set.to_Finset_card, set.coe_set_of, smul_one_eq_coe, cast_id] at hf,
--   have c1:∀ b, 1 ≤ card {x//x ∈F ∧ p x b},{
--     intro b, change 0 < _, rw card_pos_iff,
--     obtain ⟨a,ha⟩:=h b, use ⟨a,ha⟩,},
--   rw fintype.card_eq_sum_ones at hf,
--   apply lt_irrefl (∑ b: β,1),
--   apply lt_of_le_of_lt _ hf,
--   apply sum_le_sum, intros b hb, exact c1 b,
-- 


-- /-- The mono two colorings that are red on S are disjoint from those that are blue-/
-- lemma col_mono_disj {n : ℕ} {S: Finset (Fin n)} (hn : 2 ≤ S.card ) :
--  disjoint {col: twocol n | twocol_mono_c 0 S col}.to_Finset {col: twocol n | twocol_mono_c 1 S col}.to_Finset:=
-- by
--   simp only [set.to_Finset_disjoint_iff],
--   have := hn.trans (card_le_univ S), rw fintype.card_Fin at this,
--   intros col hc,
--   obtain ⟨e,he⟩:=exists_smaller_set _ _ hn,
--   simp only [set.inf_eq_inter, set.mem_inter_iff, set.mem_set_of_eq] at hc,
--   have c0:=hc.1 ⟨e,he.2⟩ he.1, have c1:=hc.2 ⟨e,he.2⟩ he.1,
--   rw c0 at c1, rw ← fin_two_not at c1, contradiction,
-- 

-- /-- The mono two colorings on S are either red or blue -/
-- lemma col_mono_union {n : ℕ} {S: Finset (Fin n)}  :  {col: twocol n | twocol_mono_c 0 S col}.to_Finset ∪ {col: twocol n | twocol_mono_c 1 S col}.to_Finset
-- = {col : twocol n | twocol_mono S col}.to_Finset
-- :=
-- by
--   ext, simp only [mem_union, set.mem_to_Finset, set.mem_set_of_eq],--simp only [set.mem_union, set.mem_set_of_eq],
--   unfold twocol_mono_c twocol_mono,
-- 


-- /-- Hence the number of mono colorings that of S is the sum over Fin 2 of mono 0 and mono 1 two-colourings -/
-- lemma sum_cols_mono {n : ℕ} {S: Finset (Fin n)} (hn : 2 ≤ S.card ) : 
-- ∑  c, fintype.card ({col: twocol n // twocol_mono_c c S col})
-- = fintype.card ({col: twocol n // twocol_mono S col}) :=
-- by
--   simp_rw card_card,
--   rw [Finset_fin2.1,sum_union Finset_fin2.2, sum_singleton,sum_singleton],
--   rw ← card_disjoint_union, congr, exact col_mono_union, 
--   exact col_mono_disj hn,
-- 


-- -- All quantities in this inequality are now known to us
-- lemma union_card_mono_le_imp {s n : ℕ} (hn: 2 ≤ s ): 
-- ∑ S in powersetLen s univ, ∑ c: Fin 2, fintype.card({col: twocol n // twocol_mono_c c S col} ) 
--                                     < fintype.card(twocol n) →¬Ramsey_of n s s:=
-- by
--   intro h,
--   apply Ramsey_lb_twocol,
--   have : ∀ S:Finset (Fin n), S ∈  powersetLen s univ →  2 ≤ S.card,{
--     intros S hS, rw mem_powersetLen at hS,rw hS.2, exact hn, apply_instance,
--   },
--   rw Finset.sum_congr at h,
--   rotate, refl,
--   intros S hS, exact sum_cols_mono (this S hS),
--   have :=subtype_pigeon_exist (powersetLen s (univ: Finset (Fin n))) twocol_mono h,
--   obtain ⟨col,h⟩:=this, use col, intros c S,
--   intros hc hf,
--   specialize h S,rw mem_powersetLen_univ_iff at h,
--   specialize h hc, apply h, 
--   unfold twocol_mono,
--   by_cases hc2: c= 0,
--     left, rw hc2 at hf, exact hf,
--     right, rw fin_two_not c at hc2, rw hc2 at hf, exact hf,
-- 


-- -- The classical (easy) probabilistic lower bound for R(s,s)
-- theorem Ramsey_lower_bound (s n : ℕ) (hn: 2 ≤ s ) :
-- (n.choose s) * 2 * (2^((n.choose 2) - (s.choose 2) )) < 2^(n.choose 2) → ¬ Ramsey_of n s s:=
-- by
--   intros h,
--   apply union_card_mono_le_imp hn,
--   simp_rw card_mono_cols, unfold twocol, rw card_cols,
--   simp_rw sum_const, rw card_univ, rw fintype.card_fin,
--   simp_rw [nsmul_eq_mul, cast_id],
--   convert h,  nth_rewrite_rhs 0 ← fintype.card_Fin n,  rw ← card_univ,
--   rw ← card_powersetLen, rw Finset.card_eq_sum_ones,simp_rw sum_mul, rw one_mul,
--   apply Finset.sum_congr, refl,intros S hS,rw mem_powersetLen_univ_iff at hS,
--   rw hS,
-- 

--  lower_bounds

  twocolour


--  /-  k-colour 2-graph Ramsey numbers -/
 
-- section kcolour
-- variable {k : ℕ}


-- /-- A col is mono on a particular set iff every pair in the set receives the same colour  -/
-- def kmono_c_on (A : Finset ℕ) (col : Finset ℕ → Fin k) (c : Fin k)  : Prop:=
-- ∀ (e : Finset ℕ), e ∈ powersetLen 2 A → col e = c


-- /-- A colouring col is Ramsey for n s t if every n-set contains a red s-set or a blue t-set under col -/
-- def kRamsey_col (col : Finset ℕ → Fin k) (n : ℕ) (s : Fin k → ℕ) : Prop:= ∀ {V : Finset ℕ}, n ≤ V.card → 
-- (∃ (A : Finset ℕ), ∃ (i : Fin k), (A ⊆ V ∧ kmono_c_on A col i ∧ (s i) ≤ A.card))

-- /-- n is Ramsey if every colouring is Ramsey for n (with s and t) -/
-- def kRamsey_of (n : ℕ) (s : Fin k → ℕ): Prop:= ∀ (col : Finset ℕ → Fin k), kRamsey_col col n s 

-- /-- if n is Ramsey for s,t and n ≤ m then m is also Ramsey -/ 
-- lemma kmono_Ramsey_of {n m: ℕ} {s: Fin k → ℕ} (h : kRamsey_of n s) (hm: n ≤ m) : kRamsey_of m s  :=
-- by
--   intros col V h2,
--   exact  h col (hm.trans h2),
-- 

-- def kres (s : Fin k.succ → ℕ) : Fin k → ℕ:=λ i, s i 

-- def kto2 (col : Finset ℕ → Fin k.succ) : Finset ℕ → Fin 2:=λ e, if (col e = k) then 1 else 0

-- def rescol {col : Finset ℕ → Fin k.succ} {A : Finset ℕ} (hm: mono_c_on A (kto2 col) 0) (hk : 0 < k): Finset ℕ →  (Fin k) :=
-- by
--   intros e, 
--   by_cases he: e ∈ powersetLen 2 A,
--   have hcol:=hm e he,
--   unfold kto2 at hcol, simp only [ite_eq_right_iff, Fin.one_eq_zero_iff, nat.one_ne_zero] at hcol,
--   refine ⟨col e,_⟩,
--   by_contra,
--   have hk2:=Fin.eq_last_of_not_lt h, apply hcol, rw hk2,
--   exact (Fin.coe_nat_eq_last k).symm,
--   exact ⟨0,hk⟩,
-- 


-- lemma resol_eq_col {col : Finset ℕ → Fin k.succ} {A : Finset ℕ} (hm: mono_c_on A (kto2 col) 0)(hk : 0 < k): 
-- ∀ e ∈ powersetLen 2 A, (rescol hm hk e : ℕ) = (col e):=
-- by
--   intros e he, unfold rescol, split_ifs, refl,
-- 

-- lemma mono_to_kmono_1 {col : Finset ℕ → Fin k.succ} {A : Finset ℕ} (hm: mono_c_on A (kto2 col) 1) : kmono_c_on A col k:=
-- by
--   unfold mono_c_on kto2 at hm,
--   simp only [ite_eq_left_iff, Fin.zero_eq_one_iff, nat.one_ne_zero] at hm,
--   unfold kmono_c_on,
--   intros e he, 
--   specialize hm e he,
--   contrapose hm, push_neg, exact ⟨hm,not_false⟩,
-- 

-- lemma mono_to_kmono_0 {col : Finset ℕ → Fin k.succ} {A : Finset ℕ} {a: ℕ}{s : Fin k.succ → ℕ} 
-- (hm: mono_c_on A (kto2 col) 0) (kra: kRamsey_of a (kres s)) (hA : a ≤ A.card) (hk: 0 < k): 
--  ∃ (i:Fin k), ∃ (B:Finset ℕ), B⊆ A ∧ kmono_c_on B col i ∧ (s i) ≤ B.card:=
-- by
--   specialize kra (rescol hm hk) hA,  
--   obtain ⟨B,i, hB1,hB2,hB3⟩:=kra,
--   refine ⟨i,B,hB1,_, hB3⟩,
--   intros e he, 
--   have h1:=resol_eq_col hm hk e (powersetLen_mono hB1 he),
--   have h2:= hB2 e he, rw h2 at h1,
--   rw Fin.eq_iff_veq,
--   simp only [Fin.val_eq_coe, Fin.coe_eq_cast_succ, Fin.coe_cast_succ],  rw h1,
-- 



-- lemma kRamsey_step {a b : ℕ} (s: Fin k.succ → ℕ) (hk : 0 < k): kRamsey_of a (kres s) → Ramsey_of b a (s k) → kRamsey_of b s:=
-- by
--   intros kra rb col V hcv,
--   specialize rb (kto2 col) hcv,
--   obtain ⟨A,hA1,⟨hA2,hA3⟩|⟨hA2,hA3⟩⟩:=rb,
--   obtain ⟨i,B, hB1, hB2,hB3⟩:=mono_to_kmono_0 hA2 kra hA3 hk,
--   exact ⟨B,i,hB1.trans hA1,hB2,hB3⟩,
--   exact ⟨A,k,hA1,mono_to_kmono_1 hA2,hA3⟩,
-- 

-- lemma kRamsey_one  (s : Fin 1 → ℕ) : kRamsey_of (s 0) s:=
-- by
--   intros col A hA,
--   refine ⟨A,0,subset_refl _,  _ ,hA⟩,
--   intros e he, rw eq_iff_true_of_subsingleton, triv,
-- 


-- lemma kRamsey_of_zero {n : ℕ} (s : Fin k.succ → ℕ) :(s k) = 0 →   kRamsey_of n s:=
-- by
--   intros hk col A hA,
--   refine ⟨∅, k, empty_subset _,_, _⟩,
--   intros e he,  exfalso, 
--   have hec1:=mem_powersetLen.1 he,
--   have hec2:=card_le_of_subset hec1.1,
--   rw [card_empty ,hec1.2]at hec2,
--   exact (not_le_of_gt zero_lt_two) hec2,
--   rw hk, exact zero_le',
-- 


-- -- For any number of colours (k+1) and any clique sizes s0 ,s1,... sk there is an n that will work..
-- theorem kcol_Ramsey (s: Fin k.succ → ℕ) : ∃ n, kRamsey_of n s:=
-- by
--   induction k with k h generalizing s,
--   exact ⟨s 0, kRamsey_one s⟩,
--   obtain ⟨a,ha⟩:= h (kres s),
--   have hk1:=kmono_Ramsey_of  ha (le_succ a),
--   refine ⟨(a + (s k.succ).pred).choose a,_⟩,
--   refine kRamsey_step s (succ_pos k) hk1 _,
--   cases (s k.succ),
--   apply Ramsey_symm, 
--   apply mono_Ramsey_of (Ramsey_zero a.succ)  zero_le',
--   rw pred_succ, exact Ramsey a n,
-- 


--  kcolour


-- section schur

-- variable {k : ℕ}

-- def schur3 (x y z : ℕ) : Prop:= x + y = z ∧ 0 < x ∧ 0 < y ∧ 0 < z

-- lemma schur_of_ordered {a b c : ℕ} (h: a < b ∧ b < c): schur3 (c-b) (b-a) (c-a):=
-- by
--   exact ⟨tsub_add_tsub_cancel h.2.le h.1.le,nat.sub_pos_of_lt h.2, nat.sub_pos_of_lt h.1,nat.sub_pos_of_lt (h.1.trans h.2)⟩,
-- 

-- def scol (ncol : ℕ → Fin k.succ) : Finset ℕ → Fin k.succ:=
-- λ A, if hne : A.nonempty then (ncol (max' A hne - min' A hne)) else 0



-- lemma scol_pair {a b : ℕ} (h : a < b) (ncol : ℕ→ Fin k.succ) :scol ncol {a,b} = ncol (b - a):=
-- by
--   unfold scol,
--   set X:={a,b},
--   have ha: a ∈ X,
--   { rw mem_insert,left,refl,},
--   have hb: b ∈ X,
--   { rw mem_insert,right,exact mem_singleton_self b,},
--   set c:= max' X ⟨a,ha⟩ with hc,
--   set d:= min' X ⟨a,ha⟩ with hd,
--   have : X = insert a {b}:=rfl,
--   dsimp, split_ifs,   congr, 
--   refine le_antisymm _ (le_max' X b hb),
--   apply max'_le, intros y hy, rw [mem_insert,mem_singleton] at hy,
--   cases hy,
--   rw hy, exact h.le, rwa hy, 
--   refine le_antisymm  (min'_le {a,b} a ha) _,
--   apply le_min', intros y hy, rw [mem_insert,mem_singleton] at hy,
--   cases hy,
--   rwa hy, rw hy, exact h.le,  
--   exfalso, apply h_1,
--   exact ⟨a,ha⟩,
-- 


-- /-- Schur n k holds iff n is sufficiently large that in any k-colouring of ℕ, every subsert of size at 
-- least n contains a non-zero monochromatic solution of x + y = z -/
-- def Schur (n k : ℕ):Prop:=
--  ∀ (col : ℕ → Fin k.succ),∀ (V: Finset ℕ),
--   n ≤ V.card →  ∃ (x y z : ℕ), ∃ (c : Fin k.succ), schur3 x y z ∧ col x = c ∧ col y = c ∧ col z = c 


-- lemma card_pred_le_card_erase (S : Finset ℕ) (a : ℕ) : S.card.pred ≤ (S.erase a).card:=
-- by
--   rw card_erase_eq_ite, split_ifs,refl,exact pred_le _,
-- 


-- /-- Any set of 3 nats can be ordered and the pairs are edges of the triangle on B -/
-- lemma card_three_nat {B : Finset ℕ} (h : B.card = 3) : ∃ (a b c : ℕ), a < b ∧ b < c ∧
--  {a,b} ∈ powersetLen 2 B ∧ {a,c} ∈ powersetLen 2 B ∧ {b,c} ∈ powersetLen 2 B:=
-- by
--   obtain ⟨x,y,z,hxy, hxz, hyz,hB⟩:=card_eq_three.1 h,
--   have hbx: x∈ B,{rw [hB,mem_insert],left,refl},
--   have hby: y∈ B,{rw [hB,mem_insert,mem_insert],right,left,refl},
--   have hbz: z∈ B,{rw [hB,mem_insert,mem_insert,mem_singleton],right,right,refl},
--   set a:= min' B ⟨x,hbx⟩,
--   set c:= max' B ⟨x,hbx⟩,
--   have haB: a ∈ B :=min'_mem B ⟨x,hbx⟩,
--   have hcB: c ∈ B :=max'_mem B ⟨x,hbx⟩,
--   have haltc:a < c, 
--     {refine min'_lt_max'_of_card B (_:1<B.card),
--      rw h, exact succ_le_succ one_le_two}, 
--   have hBea:= card_erase_of_mem haB,
--   have :=card_erase_of_mem (mem_erase_of_ne_of_mem (ne_of_gt haltc) hcB),
--   rw [hBea,h] at this,
--   rw (by refl:3-1-1=1) at this,
--   obtain ⟨b,hb⟩:=card_eq_one.1 this,
--   have hbb: b ∈ {b}:=mem_singleton_self b,
--   rw ← hb at hbb, 
--   have  hbB':=mem_of_mem_erase hbb,
--   have  hbB:=mem_of_mem_erase hbB',
--   refine ⟨a,b,c,_,_,_,_,_⟩,
--   have aleb:a≤ b:=min'_le B b hbB,
--   have hnab:a ≠ b := (ne_of_mem_erase hbB').symm,
--   exact lt_of_le_of_ne aleb hnab,
--   have blec:b≤ c:=le_max' B b hbB,
--   have hnbc:b≠c := (ne_of_mem_erase hbb),
--   exact lt_of_le_of_ne  blec hnbc,
--   { 
--      refine mem_powersetLen.2 ⟨_,card_eq_two.2 ⟨a,b,⟨(ne_of_mem_erase hbB').symm,rfl⟩⟩⟩ ,
--      intros x hx1, rw [mem_insert,mem_singleton] at hx1,
--      cases hx1,  {rw hx1, exact haB}, {rw hx1, exact hbB},
--   },
--   { 
--      refine mem_powersetLen.2 ⟨_,card_eq_two.2 ⟨a,c,⟨ne_of_lt haltc,rfl⟩⟩⟩,
--      intros x hx1, rw [mem_insert,mem_singleton] at hx1,
--      cases hx1,  {rw hx1, exact haB}, {rw hx1, exact hcB},
--   },
--   { 
--     refine mem_powersetLen.2 ⟨_,card_eq_two.2 ⟨b,c,⟨(ne_of_mem_erase hbb), rfl⟩⟩⟩,
--      intros x hx1, rw [mem_insert,mem_singleton] at hx1,
--      cases hx1, {rw hx1, exact hbB},  {rw hx1, exact hcB},
--   },
-- 


-- /-- For any k the k-colour Ramsey number for triangles + 1 is sufficient to guarantee
--  mono x + y = z in every n-subset -/
-- theorem Schur' (k:ℕ) : ∃ (n:ℕ), Schur n k:=
-- by
--   set s: Fin k.succ → ℕ:= λ i , 3,
--   obtain ⟨n,hn⟩:=kcol_Ramsey s,
--   use n.succ, intros col V hv,
--   have:= (pred_le_pred hv).trans (card_pred_le_card_erase V 0),
--   rw pred_succ at this,
--   obtain ⟨A,i,hA1,hA2,hA3⟩:=hn (scol col) this,
--   obtain ⟨B,hB⟩:=exists_smaller_set A 3 hA3,
--   obtain ⟨a,b,c,hab,hbc,h1,h2,h3⟩:=card_three_nat hB.2,
--   refine ⟨c-b,b-a,c-a,i,schur_of_ordered ⟨hab,hbc⟩,_⟩,
--   have cab:=hA2 {a,b} (powersetLen_mono hB.1 h1),
--   rw scol_pair hab col at cab,
--   have cac:=hA2 {a,c} (powersetLen_mono hB.1 h2),
--   rw scol_pair (hab.trans hbc) col at cac,
--   have cbc:=hA2 {b,c} (powersetLen_mono hB.1 h3),
--   rw scol_pair hbc col at cbc,
--   exact ⟨cbc,cab,cac⟩,
-- 

--  schur



