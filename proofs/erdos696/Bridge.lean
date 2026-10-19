module

public import FormalConjecturesForMathlib.Data.Set.Density
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.List.Chain
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
Standalone bridge development using verbatim mathematical definitions copied from
upstream/main Erdős 696 and the pinned external proof. This file does not import
or recompile the large external proof. No final result is assumed here.
-/
namespace Erdos696Bridge
open Filter

namespace Upstream

def ValidChain (n : ℕ) (P : ℕ → Prop) (s : List ℕ) : Prop :=
  s.IsChain (fun a b => a < b ∧ b ≡ 1 [MOD a]) ∧ ∀ d ∈ s, d ∣ n ∧ P d

noncomputable def h (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n Nat.Prime s) n

noncomputable def H (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k => ∃ s : List ℕ, s.length = k ∧ ValidChain n (fun _ => True) s) n
end Upstream
namespace External

def IsPrimeChain (n : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ ps, p.Prime ∧ p ∣ n) ∧
  ps.Pairwise (· < ·) ∧
  (∀ i : Fin ps.length, ∀ hi : i.val + 1 < ps.length,
      ps.get ⟨i.val + 1, hi⟩ % ps.get i = 1)

def IsDivisorChain (n : ℕ) (ds : List ℕ) : Prop :=
  (∀ d ∈ ds, 1 ≤ d ∧ d ∣ n) ∧
  ds.Pairwise (· < ·) ∧
  (∀ i : Fin ds.length, ∀ hi : i.val + 1 < ds.length,
      Nat.ModEq (ds.get i) (ds.get ⟨i.val + 1, hi⟩) 1)

noncomputable def hChain (n : ℕ) : ℕ :=
  sSup {ℓ | ∃ ps : List ℕ, IsPrimeChain n ps ∧ ps.length = ℓ}
noncomputable def HChain (n : ℕ) : ℕ :=
  if n = 1 then 0
  else sSup {u | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u}
def almostAll (P : ℕ → Prop) : Prop :=
  Filter.Tendsto
    (fun x : ℝ => ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℕ) : ℝ) / x)
    Filter.atTop (nhds 0)
end External

/-- An empty list witnesses an attainable chain of length zero. -/
theorem empty_validChain (n : ℕ) (P : ℕ → Prop) :
    Upstream.ValidChain n P [] := by
  simp [Upstream.ValidChain]

/-- The increasing divisor list has at most n entries when n is positive. -/
theorem validChain_length_le {n : ℕ} (hn : n ≠ 0) {P : ℕ → Prop}
    {s : List ℕ} (hs : Upstream.ValidChain n P s) : s.length ≤ n := by
  classical
  have hinc : s.IsChain (fun a b : ℕ => a < b) :=
    hs.1.imp (fun _ _ hab => hab.1)
  have hp : s.Pairwise (fun a b : ℕ => a < b) :=
    List.isChain_iff_pairwise.mp hinc
  rw [← List.toFinset_card_of_nodup hp.nodup]
  have hsub : s.toFinset ⊆ Finset.Icc 1 n := by
    intro d hd
    have hmem : d ∈ s := List.mem_toFinset.mp hd
    have hdvd : d ∣ n := (hs.2 d hmem).1
    have hd0 : d ≠ 0 := by
      intro hzero
      apply hn
      simpa [hzero] using hdvd
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr hd0, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd⟩
  exact (Finset.card_le_card hsub).trans (by simp)

/-- A bounded attained maximum agrees with the natural-number supremum. -/
theorem findGreatest_eq_sSup (P : ℕ → Prop) [DecidablePred P] (n : ℕ)
    (hzero : P 0) (hbound : ∀ k, P k → k ≤ n) :
    Nat.findGreatest P n = sSup {k | P k} := by
  have hbdd : BddAbove {k | P k} := ⟨n, hbound⟩
  apply le_antisymm
  · exact le_csSup hbdd (Nat.findGreatest_spec (Nat.zero_le n) hzero)
  · exact csSup_le ⟨0, hzero⟩ (fun k hk => Nat.le_findGreatest (hbound k hk) hk)

/-- Exact chain-predicate identifications. -/
def ChainPredicatesAgree : Prop :=
  (∀ n s, Upstream.ValidChain n Nat.Prime s ↔ External.IsPrimeChain n s) ∧
  (∀ n, n ≠ 0 → ∀ s,
    Upstream.ValidChain n (fun _ => True) s ↔ External.IsDivisorChain n s)

/-- Indexing convention used by the external source. -/
theorem isChain_iff_get {α : Type*} (R : α → α → Prop) (s : List α) :
    s.IsChain R ↔ ∀ i : Fin s.length, ∀ hi : i.val + 1 < s.length,
      R (s.get i) (s.get ⟨i.val + 1, hi⟩) := by
  rw [List.isChain_iff_getElem]
  constructor
  · intro h i hi
    simpa only [List.get_eq_getElem] using h i.val hi
  · intro h i hi
    simpa only [List.get_eq_getElem] using h ⟨i, by omega⟩ hi

/-- The chain predicates coincide, including the modulus-one convention. -/
theorem chainPredicatesAgree : ChainPredicatesAgree := by
  constructor
  · intro n s
    constructor
    · rintro ⟨hchain, hmem⟩
      refine ⟨fun p hp => ⟨(hmem p hp).2, (hmem p hp).1⟩,
        (hchain.imp (fun _ _ hab => hab.1)).pairwise, ?_⟩
      intro i hi
      have hm := (isChain_iff_get _ s).mp hchain i hi
      have hp := (hmem (s.get i) (List.get_mem s i)).2
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using hm.2
    · rintro ⟨hmem, hinc, hmod⟩
      refine ⟨(isChain_iff_get _ s).mpr ?_,
        fun p hp => ⟨(hmem p hp).2, (hmem p hp).1⟩⟩
      intro i hi
      have hlt := (isChain_iff_get _ s).mp hinc.isChain i hi
      have hp := (hmem (s.get i) (List.get_mem s i)).1
      refine ⟨hlt, ?_⟩
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using hmod i hi
  · intro n hn s
    constructor
    · rintro ⟨hchain, hmem⟩
      refine ⟨?_, (hchain.imp (fun _ _ hab => hab.1)).pairwise, ?_⟩
      · intro d hd
        have hdvd := (hmem d hd).1
        have hd0 : d ≠ 0 := by
          intro hzero
          apply hn
          simpa [hzero] using hdvd
        exact ⟨Nat.one_le_iff_ne_zero.mpr hd0, hdvd⟩
      · intro i hi
        exact ((isChain_iff_get _ s).mp hchain i hi).2
    · rintro ⟨hmem, hinc, hmod⟩
      refine ⟨(isChain_iff_get _ s).mpr ?_, fun d hd => ⟨(hmem d hd).2, trivial⟩⟩
      intro i hi
      exact ⟨(isChain_iff_get _ s).mp hinc.isChain i hi, hmod i hi⟩

/-- Equality of the two extremal-length conventions away from the exceptional inputs. -/
def ChainLengthsAgree : Prop :=
  ∀ n, 2 ≤ n → Upstream.h n = External.hChain n ∧ Upstream.H n = External.HChain n

/-- The maximum bridge reduces to the chain-predicate bridge; no analytic input is used. -/
theorem chainLengthsAgree_of_chainPredicatesAgree
    (hc : ChainPredicatesAgree) : ChainLengthsAgree := by
  classical
  intro n hn
  have hn0 : n ≠ 0 := by omega
  constructor
  · unfold Upstream.h External.hChain
    rw [findGreatest_eq_sSup _ n
      ⟨[], rfl, empty_validChain n Nat.Prime⟩]
    · congr 1
      ext k
      constructor
      · rintro ⟨s, hlen, hs⟩
        exact ⟨s, (hc.1 n s).mp hs, hlen⟩
      · rintro ⟨s, hs, hlen⟩
        exact ⟨s, hlen, (hc.1 n s).mpr hs⟩
    · rintro k ⟨s, rfl, hs⟩
      exact validChain_length_le hn0 hs
  · unfold Upstream.H External.HChain
    rw [if_neg (by omega : n ≠ 1)]
    rw [findGreatest_eq_sSup _ n
      ⟨[], rfl, empty_validChain n (fun _ => True)⟩]
    · congr 1
      ext k
      constructor
      · rintro ⟨s, hlen, hs⟩
        exact ⟨s, (hc.2 n hn0 s).mp hs, hlen⟩
      · rintro ⟨s, hs, hlen⟩
        exact ⟨s, hlen, (hc.2 n hn0 s).mpr hs⟩
    · rintro k ⟨s, rfl, hs⟩
      exact validChain_length_le hn0 hs

/-- Both repository maxima agree with their external counterparts for n at least two. -/
theorem chainLengthsAgree : ChainLengthsAgree :=
  chainLengthsAgree_of_chainPredicatesAgree chainPredicatesAgree

/-- The exact density normalization obligation: real inclusive counts versus natural strict counts. -/
def DensityNormalizationsAgree : Prop :=
  ∀ P : ℕ → Prop, External.almostAll P ↔ {n : ℕ | P n}.HasDensity 1

/-- Extract precisely the ratio conclusion of the external theorem; no estimate is assumed. -/
def ExternalRatioConclusion : Prop :=
  ∀ ε : ℝ, 0 < ε → External.almostAll (fun n => n ≥ 2 →
    |(External.HChain n : ℝ) / (External.hChain n : ℝ) - 2| ≤ ε)

/-- The same ratio conclusion expressed using the repository's definitions. -/
def UpstreamRatioConclusion : Prop :=
  ∀ ε : ℝ, 0 < ε → External.almostAll (fun n => n ≥ 2 →
    |(Upstream.H n : ℝ) / (Upstream.h n : ℝ) - 2| ≤ ε)

/-- Equality of the chain lengths transfers the existing ratio result exactly. -/
theorem upstreamRatioConclusion_of_external
    (hc : ChainLengthsAgree) (hr : ExternalRatioConclusion) : UpstreamRatioConclusion := by
  intro ε hε
  have heq : (fun n => n ≥ 2 →
      |(Upstream.H n : ℝ) / (Upstream.h n : ℝ) - 2| ≤ ε) =
      (fun n => n ≥ 2 →
      |(External.HChain n : ℝ) / (External.hChain n : ℝ) - 2| ≤ ε) := by
    funext n
    apply propext
    constructor
    · intro h hn
      simpa [(hc n hn).1, (hc n hn).2] using h hn
    · intro h hn
      simpa [(hc n hn).1, (hc n hn).2] using h hn
  rw [heq]
  exact hr ε hε

/-- The exact target currently stated in upstream/main Erdős 696. -/
def RepositoryTarget : Prop :=
  ¬ ∀ M : ℝ,
    {n : ℕ | (Upstream.h n : ℝ) > 0 ∧
      (Upstream.H n : ℝ) / (Upstream.h n : ℝ) > M}.HasDensity 1

/-- Remaining purely density-theoretic obligation, including the two exceptional inputs. -/
def RatioConvergenceRefutesDivergence : Prop :=
  UpstreamRatioConclusion → RepositoryTarget

/-- A set incompatible with an almost-all property outside two inputs has density zero. -/
theorem density_zero_of_almostAll_incompatible {P Q : ℕ → Prop}
    (hp : External.almostAll P)
    (hdisjoint : ∀ n, 2 ≤ n → P n → ¬ Q n) :
    {n : ℕ | Q n}.HasDensity 0 := by
  classical
  unfold External.almostAll at hp
  have hnat := hp.comp tendsto_natCast_atTop_atTop
  simp only [Nat.floor_natCast] at hnat
  have htwo : Filter.Tendsto (fun N : ℕ => (2 : ℝ) / N)
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 2
  have hsum := hnat.add htwo
  have hlimit : Filter.Tendsto
      (fun N : ℕ => (({n : ℕ | Q n} ∩ Set.Iio N).ncard : ℝ) / N)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => by positivity)) ?_
      (by simpa only [add_zero] using hsum)
    apply Filter.Eventually.of_forall
    intro N
    let bad : Set ℕ := {n | n ≤ N ∧ ¬ P n}
    have hbfin : bad.Finite :=
      (Set.finite_Iic N).subset (fun _ hn => hn.1)
    have hsub : {n : ℕ | Q n} ∩ Set.Iio N ⊆ bad ∪ Set.Iio 2 := by
      intro n hn
      by_cases hn2 : 2 ≤ n
      · exact Or.inl ⟨hn.2.le, fun hpn => hdisjoint n hn2 hpn hn.1⟩
      · exact Or.inr (by simpa using hn2)
    have hcard : ({n : ℕ | Q n} ∩ Set.Iio N).ncard ≤ bad.ncard + 2 := by
      calc
        _ ≤ (bad ∪ Set.Iio 2).ncard :=
          Set.ncard_le_ncard hsub (hbfin.union (Set.finite_Iio 2))
        _ ≤ bad.ncard + (Set.Iio 2).ncard := Set.ncard_union_le _ _
        _ = bad.ncard + 2 := by rw [Nat.ncard_Iio]
    have hcardR : (({n : ℕ | Q n} ∩ Set.Iio N).ncard : ℝ) ≤
        (Nat.card {n : ℕ | n ≤ N ∧ ¬ P n} : ℝ) + 2 := by
      exact_mod_cast hcard
    exact (div_le_div_of_nonneg_right hcardR (Nat.cast_nonneg N)).trans_eq
      (add_div _ _ _)
  simpa [Set.HasDensity, Set.partialDensity, Nat.ncard_Iio] using hlimit

/-- The ratio limit refutes the repository's divergence statement at threshold three. -/
theorem ratioConvergenceRefutesDivergence : RatioConvergenceRefutesDivergence := by
  intro hr hdiv
  have hzero :
      {n : ℕ | (Upstream.h n : ℝ) > 0 ∧
        (Upstream.H n : ℝ) / (Upstream.h n : ℝ) > 3}.HasDensity 0 := by
    apply density_zero_of_almostAll_incompatible (hr (1 / 2) (by norm_num))
    intro n hn hp hq
    have hbound := (le_abs_self
      ((Upstream.H n : ℝ) / (Upstream.h n : ℝ) - 2)).trans (hp hn)
    linarith [hq.2]
  have hbad : (0 : ℝ) = 1 := tendsto_nhds_unique hzero (hdiv 3)
  norm_num at hbad

/-- An explicit dependency contract for the final repository proof. -/
theorem repositoryTarget_of_bridges
    (hc : ChainPredicatesAgree)
    (hd : RatioConvergenceRefutesDivergence)
    (hr : ExternalRatioConclusion) : RepositoryTarget :=
  hd (upstreamRatioConclusion_of_external
    (chainLengthsAgree_of_chainPredicatesAgree hc) hr)

/-- Only the external analytic ratio conclusion is needed after the definition bridges. -/
theorem repositoryTarget_of_external (hr : ExternalRatioConclusion) : RepositoryTarget :=
  ratioConvergenceRefutesDivergence
    (upstreamRatioConclusion_of_external chainLengthsAgree hr)

#print axioms empty_validChain
#print axioms validChain_length_le
#print axioms findGreatest_eq_sSup
#print axioms chainPredicatesAgree
#print axioms chainLengthsAgree_of_chainPredicatesAgree
#print axioms chainLengthsAgree
#print axioms upstreamRatioConclusion_of_external
#print axioms repositoryTarget_of_bridges
#print axioms density_zero_of_almostAll_incompatible
#print axioms ratioConvergenceRefutesDivergence
#print axioms repositoryTarget_of_external

end Erdos696Bridge

