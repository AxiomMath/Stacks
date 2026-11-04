module

public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.RingTheory.Artinian.Basic

/-!
# Residue degrees of a finite-dimensional algebra

For a finite-dimensional commutative algebra over a field, the sum of the residue degrees at any
finite family of distinct maximal ideals is at most the dimension of the algebra. The reason is
that distinct maximal ideals are pairwise coprime, so the algebra surjects onto the product of
the corresponding residue fields, and a surjection cannot increase dimension.

This is the algebraic input to the bound on the number of points of a fibre of a morphism whose
degree is bounded: each point contributes at least one to the sum of residue degrees.

## Main results

* `Algebra.sum_finrank_residueField_le_finrank`: the sum of the residue degrees at distinct
  maximal ideals is bounded by the dimension of the algebra.

## Implementation notes

The maximal ideals are indexed by `Fin t`; injectivity expresses that the displayed ideals are
distinct. The result is stated for any such family, rather than requiring it to enumerate every
maximal ideal.

## References

* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public section

namespace Algebra

/-- The sum of the residue degrees at finitely many distinct maximal ideals of a
finite-dimensional commutative algebra is at most the dimension of the algebra. -/
public lemma sum_finrank_residueField_le_finrank
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {t : ℕ} (𝔪 : Fin t → MaximalSpectrum A) (h𝔪 : Function.Injective 𝔪) :
    ∑ i, Module.finrank k (𝔪 i).asIdeal.ResidueField ≤ Module.finrank k A := by
  have hpair : Pairwise fun i j => IsCoprime (𝔪 i).asIdeal (𝔪 j).asIdeal :=
    fun i j hij => Ideal.isCoprime_of_isMaximal fun he => hij (h𝔪 (MaximalSpectrum.ext he))
  let f : (i : Fin t) → A →ₗ[k] (𝔪 i).asIdeal.ResidueField :=
    fun i => (Algebra.linearMap A _).restrictScalars k
  have hsurjf : Function.Surjective (LinearMap.pi f) := by
    intro x
    choose y hy using fun i => (𝔪 i).asIdeal.algebraMap_residueField_surjective (x i)
    obtain ⟨a, ha⟩ := Ideal.pi_mkQ_surjective hpair fun i => (𝔪 i).asIdeal.mkQ (y i)
    refine ⟨a, funext fun i => ?_⟩
    show algebraMap A (𝔪 i).asIdeal.ResidueField a = x i
    rw [← hy i, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    exact (Submodule.Quotient.eq _).mp (congr_fun ha i)
  have (i : Fin t) : Module.Finite k (𝔪 i).asIdeal.ResidueField :=
    .of_surjective (f i) (𝔪 i).asIdeal.algebraMap_residueField_surjective
  calc
    ∑ i, Module.finrank k (𝔪 i).asIdeal.ResidueField =
        Module.finrank k (∀ i, (𝔪 i).asIdeal.ResidueField) := (Module.finrank_pi_fintype k).symm
    _ ≤ Module.finrank k A := LinearMap.finrank_le_finrank_of_surjective hsurjf

end Algebra
