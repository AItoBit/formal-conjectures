import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Construction791

def v (t k : ℕ) : Finset ℕ := (Finset.range (t+1)).image (fun i => k*t^2+i)
def h (t k : ℕ) : Finset ℕ := (Finset.range t).image (fun i => k*t^2+t*i)
def s (t k : ℕ) : Finset ℕ := (Finset.range t).image (fun i => k*t^2+(t+1)*i)
def basis (t : ℕ) : Finset ℕ :=
  (({0,6,10} : Finset ℕ).biUnion (v t)) ∪
  (({0,1,2} : Finset ℕ).biUnion (h t)) ∪ s t 3

lemma v_mem {t k i : ℕ} (hk : k ∈ ({0,6,10} : Finset ℕ)) (hi : i ≤ t) :
    k*t^2+i ∈ basis t := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨i,by simp; omega,rfl⟩⟩
lemma h_mem {t k i : ℕ} (hk : k ∈ ({0,1,2} : Finset ℕ)) (hi : i < t) :
    k*t^2+t*i ∈ basis t := by
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨i,by simpa,rfl⟩⟩
lemma s_mem {t i : ℕ} (hi : i < t) : 3*t^2+(t+1)*i ∈ basis t := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i,by simpa,rfl⟩

lemma vh {t n : ℕ} (ht : 0<t) (hn : n<t^2) :
    ∃ i j : ℕ, i ≤ t ∧ j<t ∧ i+t*j=n := by
  refine ⟨n%t,n/t,?_,?_,?_⟩
  · have := Nat.mod_lt n ht; omega
  · exact (Nat.div_lt_iff_lt_mul ht).mpr (by simpa [pow_two] using hn)
  · exact Nat.mod_add_div n t

lemma vs {t n : ℕ} (ht : 0<t) (hn : n<t^2) :
    ∃ i j : ℕ, i ≤ t ∧ j<t ∧ i+(t+1)*j=n := by
  refine ⟨n%(t+1),n/(t+1),?_,?_,?_⟩
  · have := Nat.mod_lt n (by omega : 0<t+1); omega
  · apply (Nat.div_lt_iff_lt_mul (by omega : 0<t+1)).mpr
    nlinarith
  · exact Nat.mod_add_div n (t+1)

lemma hs {t n : ℕ} (ht : 0<t) (hn : n<t^2) :
    ∃ i j d : ℕ, i<t ∧ j<t ∧ d≤1 ∧ t*i+(t+1)*j+d*t^2=t^2+n := by
  have ha : n/t<t := (Nat.div_lt_iff_lt_mul ht).mpr (by simpa [pow_two] using hn)
  have hb := Nat.mod_lt n ht
  have he := Nat.mod_add_div n t
  generalize hqa : n/t = a at *
  generalize hqb : n%t = b at *
  by_cases hh : b ≤ a
  · refine ⟨a-b,b,1,by omega,hb,by omega,?_⟩
    have hd : a-b+b=a := Nat.sub_add_cancel hh
    nlinarith
  · refine ⟨t+a-b,b,0,by omega,hb,by omega,?_⟩
    have hd : t+a-b+b=t+a := Nat.sub_add_cancel (show b ≤ t+a from by omega)
    nlinarith

lemma card_basis (t : ℕ) : (basis t).card ≤ 7*(t+1) := by
  have hv : (({0,6,10} : Finset ℕ).biUnion (v t)).card ≤ 3*(t+1) := by
    have hh := Finset.card_biUnion_le_card_mul ({0,6,10} : Finset ℕ) (v t) (t+1)
    apply le_trans (hh (by intro i hi; simpa [v] using (Finset.card_image_le (s := Finset.range (t+1)) (f := fun j => i*t^2+j))))
    norm_num
  have hh : (({0,1,2} : Finset ℕ).biUnion (h t)).card ≤ 3*t := by
    have hh := Finset.card_biUnion_le_card_mul ({0,1,2} : Finset ℕ) (h t) t
    apply le_trans (hh (by intro i hi; simpa [h] using (Finset.card_image_le (s := Finset.range t) (f := fun j => i*t^2+t*j))))
    norm_num
  have hs : (s t 3).card ≤ t := by simpa [s] using (Finset.card_image_le (s := Finset.range t) (f := fun j => 3*t^2+(t+1)*j))
  have hu := Finset.card_union_le (({0,6,10} : Finset ℕ).biUnion (v t)) (({0,1,2} : Finset ℕ).biUnion (h t))
  have hu' := Finset.card_union_le ((({0,6,10} : Finset ℕ).biUnion (v t)) ∪ (({0,1,2} : Finset ℕ).biUnion (h t))) (s t 3)
  dsimp [basis]
  omega

end Construction791

namespace Construction791
lemma cover_vh {t r k l : ℕ} (ht : 0<t) (hr : r<t^2)
    (hk : k ∈ ({0,6,10} : Finset ℕ)) (hl : l ∈ ({0,1,2} : Finset ℕ)) :
    ∃ a∈basis t, ∃ b∈basis t, a+b=(k+l)*t^2+r := by
  obtain ⟨i,j,hi,hj,he⟩ := vh ht hr
  refine ⟨k*t^2+i,v_mem hk hi,l*t^2+t*j,h_mem hl hj,?_⟩
  nlinarith
lemma cover_vs {t r k : ℕ} (ht : 0<t) (hr : r<t^2)
    (hk : k ∈ ({0,6,10} : Finset ℕ)) :
    ∃ a∈basis t, ∃ b∈basis t, a+b=(k+3)*t^2+r := by
  obtain ⟨i,j,hi,hj,he⟩ := vs ht hr
  refine ⟨k*t^2+i,v_mem hk hi,3*t^2+(t+1)*j,s_mem hj,?_⟩
  nlinarith
lemma cover_hs {t r k : ℕ} (ht : 0<t) (hr : r<t^2) (hk : k≤1) :
    ∃ a∈basis t, ∃ b∈basis t, a+b=(k+4)*t^2+r := by
  obtain ⟨i,j,d,hi,hj,hd,he⟩ := hs ht hr
  have hm : k+d ∈ ({0,1,2} : Finset ℕ) := by simp; omega
  refine ⟨(k+d)*t^2+t*i,h_mem hm hi,3*t^2+(t+1)*j,s_mem hj,?_⟩
  nlinarith

lemma covers {t n : ℕ} (ht : 2≤t) (hn : n<14*t^2) :
    ∃ a∈basis t, ∃ b∈basis t, a+b=n := by
  have ht' : 0<t := by omega
  have hp : 0<t^2 := by positivity
  have hr : n%t^2<t^2 := Nat.mod_lt n hp
  have hq : n/t^2<14 := (Nat.div_lt_iff_lt_mul hp).mpr hn
  have he : n%t^2+t^2*(n/t^2)=n := Nat.mod_add_div n (t^2)
  suffices hh : ∃ a∈basis t, ∃ b∈basis t, a+b=(n/t^2)*t^2+n%t^2 by
    obtain ⟨a,ha,b,hb,hab⟩ := hh
    exact ⟨a,ha,b,hb,hab.trans (by nlinarith [he])⟩
  generalize hqn : n/t^2=q at *
  have hcases : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨
      q=4 ∨ q=5 ∨ q=6 ∨ q=7 ∨ q=8 ∨
      q=9 ∨ q=10 ∨ q=11 ∨ q=12 ∨ q=13 := by omega
  rcases hcases with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;> rw [hq]
  · simpa using cover_vh (k:=0) (l:=0) ht' hr (by simp) (by simp)
  · simpa using cover_vh (k:=0) (l:=1) ht' hr (by simp) (by simp)
  · simpa using cover_vh (k:=0) (l:=2) ht' hr (by simp) (by simp)
  · simpa using cover_vs (k:=0) ht' hr (by simp)
  · simpa using cover_hs (k:=0) ht' hr (by omega)
  · simpa using cover_hs (k:=1) ht' hr (by omega)
  · simpa using cover_vh (k:=6) (l:=0) ht' hr (by simp) (by simp)
  · simpa using cover_vh (k:=6) (l:=1) ht' hr (by simp) (by simp)
  · simpa using cover_vh (k:=6) (l:=2) ht' hr (by simp) (by simp)
  · simpa using cover_vs (k:=6) ht' hr (by simp)
  · simpa using cover_vh (k:=10) (l:=0) ht' hr (by simp) (by simp)
  · simpa using cover_vh (k:=10) (l:=1) ht' hr (by simp) (by simp)
  · simpa using cover_vh (k:=10) (l:=2) ht' hr (by simp) (by simp)
  · simpa using cover_vs (k:=10) ht' hr (by simp)
end Construction791
#print axioms Construction791.covers
#print axioms Construction791.card_basis




