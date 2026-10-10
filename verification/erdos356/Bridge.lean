import ErdosProblems.Erdos356

open scoped BigOperators

namespace Erdos356Verification

def consecutiveSums (k : ℕ) (a : ℕ → ℤ) : Finset ℤ :=
  ((Finset.Icc 1 k ×ˢ Finset.Icc 1 k).filter (fun p => p.1 ≤ p.2)).image
    (fun p => ∑ i ∈ Finset.Icc p.1 p.2, a i)

def IsAdmissible (n k : ℕ) (a : ℕ → ℤ) : Prop :=
  (∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, i < j → a i < a j) ∧
  (∀ i ∈ Finset.Icc 1 k, 1 ≤ a i ∧ a i ≤ n)

def shift {k : ℕ} (a : Fin k → ℕ) (j : ℕ) : ℤ :=
  if h : 1 ≤ j ∧ j ≤ k then (a ⟨j - 1, by omega⟩ : ℤ) else 0

lemma shift_apply {k : ℕ} (a : Fin k → ℕ) (i : Fin k) :
    shift a (i.val + 1) = (a i : ℤ) := by
  simp [shift, i.isLt]

lemma sum_shift {k : ℕ} (a : Fin k → ℕ) (u v : Fin k) :
    (∑ j ∈ Finset.Icc (u.val + 1) (v.val + 1), shift a j) =
      ((∑ i ∈ Finset.Icc u v, a i : ℕ) : ℤ) := by
  rw [Nat.cast_sum]
  symm
  apply Finset.sum_bij (fun i _ => i.val + 1)
  · intro i hi
    simp only [Finset.mem_Icc, Fin.le_def] at hi ⊢
    omega
  · intro i hi j hj hij
    apply Fin.ext
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    have h : j - 1 < k := by omega
    refine ⟨⟨j - 1, h⟩, ?_, ?_⟩
    · simp only [Finset.mem_Icc, Fin.le_def]
      omega
    change j - 1 + 1 = j
    omega
  · intro i hi
    exact (shift_apply a i).symm

lemma sums_shift {k : ℕ} (a : Fin k → ℕ) :
    consecutiveSums k (shift a) = (Erdos356.consecutiveSums a).image (fun x : ℕ => (x : ℤ)) := by
  ext z
  simp only [consecutiveSums, Erdos356.consecutiveSums, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨⟨hu, hv⟩, huv⟩, rfl⟩
    simp only [Finset.mem_Icc] at hu hv
    let U : Fin k := ⟨u - 1, by omega⟩
    let V : Fin k := ⟨v - 1, by omega⟩
    have hU : U.val + 1 = u := by dsimp [U]; omega
    have hV : V.val + 1 = v := by dsimp [V]; omega
    refine ⟨∑ i ∈ Finset.Icc U V, a i, ⟨(U, V), ?_, rfl⟩, ?_⟩
    · refine ⟨by simp, ?_⟩
      change U.val ≤ V.val
      dsimp [U, V]
      omega
    · rw [← sum_shift a U V, hU, hV]
  · rintro ⟨x, ⟨⟨u, v⟩, huv, rfl⟩, rfl⟩
    refine ⟨(u.val + 1, v.val + 1), ⟨?_, ?_⟩, sum_shift a u v⟩
    · simp only [Finset.mem_Icc]
      constructor <;> constructor <;> omega
    · exact Nat.add_le_add_right huv.2 1

lemma card_shift {k : ℕ} (a : Fin k → ℕ) :
    (consecutiveSums k (shift a)).card = (Erdos356.consecutiveSums a).card := by
  rw [sums_shift, Finset.card_image_of_injective _ (Nat.cast_injective : Function.Injective (fun x : ℕ => (x : ℤ)))]

lemma admissible_shift {n k : ℕ} (a : Fin k → ℕ) (ha : StrictMono a)
    (hb : ∀ i, 1 ≤ a i ∧ a i ≤ n) : IsAdmissible n k (shift a) := by
  constructor
  · intro i hi j hj hij
    simp only [Finset.mem_Icc] at hi hj
    simp only [shift, dif_pos hi, dif_pos hj]
    exact_mod_cast ha (show (⟨i - 1, by omega⟩ : Fin k) < (⟨j - 1, by omega⟩ : Fin k) from by
      change i - 1 < j - 1
      omega)
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    simp only [shift, dif_pos hi]
    exact_mod_cast hb ⟨i - 1, by omega⟩

theorem integer_erdos_356 : True ↔
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (k : ℕ) (a : ℕ → ℤ), IsAdmissible n k a ∧
        c * (n : ℝ) ^ 2 ≤ (consecutiveSums k a).card := by
  constructor
  · intro _
    obtain ⟨c, hc, h⟩ := Erdos356.erdos_356
    refine ⟨c, hc, h.mono ?_⟩
    intro n hn
    obtain ⟨k, a, ha, hb, hcard⟩ := hn
    refine ⟨k, shift a, admissible_shift a ha hb, ?_⟩
    simpa only [card_shift] using hcard
  · intro _
    trivial

#print axioms Erdos356.erdos_356
#print axioms sum_shift
#print axioms sums_shift
#print axioms card_shift
#print axioms admissible_shift
#print axioms integer_erdos_356

end Erdos356Verification
