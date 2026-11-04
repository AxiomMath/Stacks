module

public import Mathlib.RingTheory.LocalProperties.Projective
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic

/-!
# Idempotent decomposition of a finite projective module by its stalk rank

The stalk rank of a finite projective module over a commutative ring is a locally constant
function on the prime spectrum, so each of its fibres is a clopen subset and therefore the
basic open set of an idempotent. Collecting these idempotents decomposes the ring into
finitely many pieces on which the rank is constant.

## Main results

* `Module.exists_idempotent_rankAtStalk_decomposition`: the idempotent decomposition indexed by
  the (finite) range of the stalk rank.
* `Module.rankAtStalk_pos_of_comp_eq_id`: a split copy of the base ring forces every stalk rank
  to be positive.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Module

/-- A finite projective module splits into finitely many idempotent pieces on which its stalk
rank is constant. The indexing type is the range of the stalk rank function, which is finite
because that function is locally constant on a quasi-compact space. -/
theorem exists_idempotent_rankAtStalk_decomposition {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ∃ (ι : Type) (_ : Fintype ι) (rank : ι → ℕ) (e : ι → R),
      (∑ i, e i = 1) ∧ (∀ i, e i * e i = e i) ∧
      (∀ (i : ι) (p : PrimeSpectrum R), e i ∉ p.asIdeal ↔
        Module.rankAtStalk (R := R) (M := M) p = rank i) ∧
      (∀ i : ι, rank i ∈ Set.range (Module.rankAtStalk (R := R) (M := M))) := by
  classical
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  set r : PrimeSpectrum R → ℕ := Module.rankAtStalk M with hr
  have hloc : IsLocallyConstant r := Module.isLocallyConstant_rankAtStalk
  have hrange : Set.range r = r '' Set.univ := by ext n; simp
  have hfinite : (Set.range r).Finite := by
    rw [hrange]
    exact (isCompact_univ.image hloc.continuous).finite
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  let ι := {n // n ∈ Set.range r}
  have : Finite ι := hfinite.to_subtype
  let : Fintype ι := Fintype.ofFinite ι
  let rank : ι → ℕ := fun i ↦ i.1
  choose e he using fun i : ι ↦ PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (hloc.isClopen_fiber (rank i))
  have hmem (i : ι) (p : PrimeSpectrum R) : e i ∉ p.asIdeal ↔ r p = rank i := by
    rw [← PrimeSpectrum.mem_basicOpen (e i) p]
    exact (Set.ext_iff.mp (he i).2 p).symm
  have hid (i : ι) : e i * e i = e i := (he i).1.eq
  have hcross (i j : ι) (hij : i ≠ j) : e i * e j = 0 := by
    have hij' : IsIdempotentElem (e i * e j) := by
      show e i * e j * (e i * e j) = e i * e j
      calc
        e i * e j * (e i * e j) = e i * e i * (e j * e j) := by ring
        _ = e i * e j := by rw [hid, hid]
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem hij'
      IsIdempotentElem.zero ?_
    rw [PrimeSpectrum.basicOpen_zero]
    refine eq_bot_iff.mpr fun p hp ↦ ?_
    rw [PrimeSpectrum.basicOpen_mul] at hp
    exact absurd (Subtype.ext (((hmem i p).mp hp.1).symm.trans ((hmem j p).mp hp.2)) :
      i = j) hij
  have hsumNotMem (p : PrimeSpectrum R) : (∑ i, e i) ∉ p.asIdeal := by
    obtain ⟨i, hi⟩ : ∃ i : ι, r p = rank i := ⟨⟨r p, p, rfl⟩, rfl⟩
    have hother : (∑ j ∈ Finset.univ.erase i, e j) ∈ p.asIdeal :=
      Ideal.sum_mem _ fun j hj ↦ not_not.mp fun hnot ↦
        (Finset.mem_erase.mp hj).1 (Subtype.ext (hi.symm.trans ((hmem j p).mp hnot)).symm)
    intro hcontra
    refine (hmem i p).mpr hi ?_
    have hsub : e i = (∑ j, e j) - ∑ j ∈ Finset.univ.erase i, e j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]; ring
    rw [hsub]
    exact p.asIdeal.sub_mem hcontra hother
  have hsum : ∑ i, e i = 1 := by
    refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem ?_
      IsIdempotentElem.one ?_
    · show (∑ i, e i) * (∑ i, e i) = ∑ i, e i
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i (fun j _ hji ↦ hcross i j hji.symm) (by simp), hid]
    · rw [PrimeSpectrum.basicOpen_one]
      exact eq_top_iff.mpr fun p _ ↦ (PrimeSpectrum.mem_basicOpen _ p).mpr (hsumNotMem p)
  exact ⟨ι, inferInstance, rank, e, hsum, hid, hmem, fun i ↦ i.2⟩

/-- If the base ring is a direct summand of a finite flat module, then every stalk rank of that
module is positive. -/
theorem rankAtStalk_pos_of_comp_eq_id {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (i : R →ₗ[R] M) (s : M →ₗ[R] R)
    (hsi : s.comp i = LinearMap.id) (p : PrimeSpectrum R) :
    0 < Module.rankAtStalk M p := by
  refine (Module.rankAtStalk_pos_iff_mem_support (M := M) p).2 ?_
  have hinj : Function.Injective i := fun x y hxy ↦ by
    simpa using
      (LinearMap.congr_fun hsi x).symm.trans ((congrArg s hxy).trans (LinearMap.congr_fun hsi y))
  refine Module.support_subset_of_injective i hinj ?_
  rw [Module.mem_support_iff']
  refine ⟨1, fun a ha hazero ↦ ha ?_⟩
  rw [smul_eq_mul, mul_one] at hazero
  exact hazero ▸ p.asIdeal.zero_mem

end Module

end
