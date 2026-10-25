/-
Copyright (c) 2026 AItoBit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Definitions792
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Erdos792

/-- Reflection about the largest member bounds a sum-free subset of [1,n]. -/
theorem interval_sumFree_card_bound (n : ℕ) (S : Finset ℤ)
    (hS : S ⊆ Finset.Icc (1 : ℤ) (n : ℤ)) (hs : SumFree S) :
    2*S.card ≤ n+1 := by
  classical
  rcases S.eq_empty_or_nonempty with he | hn
  · subst S
    simp
  let M := S.max' hn
  have hM : M∈S := Finset.max'_mem S hn
  have hMle : M≤(n : ℤ) := (Finset.mem_Icc.mp (hS hM)).2
  let R := S.image (fun x => M-x)
  have hRcard : R.card=S.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact (Int.sub_right_inj M).mp hxy
  have hd : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hxR
    have hadd : x+y=M := by omega
    apply hs x hx y hy
    rw [hadd]
    exact hM
  have hu : S∪R ⊆ Finset.Icc (0 : ℤ) (n : ℤ) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx' := Finset.mem_Icc.mp (hS hx)
      exact Finset.mem_Icc.mpr ⟨by omega,hx'.2⟩
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hylo := (Finset.mem_Icc.mp (hS hy)).1
      have hym : y≤M := Finset.le_max' S y hy
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hh := Finset.card_le_card hu
  have hc : (Finset.Icc (0 : ℤ) (n : ℤ)).card=n+1 := by
    simp [Int.card_Icc]
  rw [hc,Finset.card_union_of_disjoint hd,hRcard] at hh
  omega

/-- A verified elementary upper bound, rather than the unresolved sharp estimate. -/
theorem fNonzero_elementary_upper (n : ℕ) : 2*fNonzero n ≤ n+1 := by
  obtain ⟨S,hS,hs,hk⟩ := fNonzero_spec n (Finset.Icc 1 (n : ℤ))
    (by simp) (card_positive_interval n)
  have hb := interval_sumFree_card_bound n S hS hs
  omega

/-- With zero allowed, the exact one-element shift gives this upper bound. -/
theorem f_elementary_upper (n : ℕ) : 2*f n ≤ n := by
  cases n with
  | zero => simp [f_zero]
  | succ n => simpa only [f_succ] using fNonzero_elementary_upper n

#print axioms interval_sumFree_card_bound
#print axioms fNonzero_elementary_upper
#print axioms f_elementary_upper
end Erdos792
