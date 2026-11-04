module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# Where the norm of a finite projective algebra vanishes

Let `A` be a commutative `R`-algebra which is finite and projective as an `R`-module, and let
`a : A`. The norm `Algebra.projectiveNorm R a` lies in a prime `p` of `R` exactly when `a` lies
in some prime of `A` lying over `p`. Geometrically: the vanishing locus of the norm of a function
is the set of points of `Spec R` over which the function vanishes somewhere on the fibre.

## Main definitions

No new definitions are introduced.

## Main results

* `Algebra.projectiveNorm_mem_iff_exists_comap_eq` is the equivalence.
* `Algebra.projectiveNorm_notMem_iff_forall` is its negation, which is the form a consumer
  wanting a nonvanishing locus uses.

## Implementation notes

Both directions are read off the fibre algebra `κ(p) ⊗_R A` over the residue field of `p`, using
that the norm commutes with base change (`Algebra.projectiveNorm_baseChange`) and that the
kernel of `R ⟶ κ(p)` is `p` (`Ideal.ker_algebraMap_residueField`).

The direction producing a prime of `A` needs no determinant theory beyond multiplicativity: if
`1 ⊗ a` were a unit in the fibre algebra its norm would be a unit, so a vanishing norm makes
`1 ⊗ a` a nonunit, and a nonunit lies in a maximal ideal. The contraction of that maximal ideal
along `A ⟶ κ(p) ⊗_R A` lies over `p` because a nonzero element of `κ(p)` becomes a unit in the
fibre algebra and so escapes every proper ideal.

The other direction is `Algebra.projectiveNorm_eq_zero_of_field_hom` applied to the residue
fields of the two primes, joined by `Ideal.ResidueField.map`.

## References

* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A nonzero element of the residue field of `p` becomes a unit in the fibre algebra, so it
escapes every proper ideal of it. -/
private theorem notMem_of_ne_zero_algebraMap_tensor (p : PrimeSpectrum R)
    {m : Ideal (p.asIdeal.ResidueField ⊗[R] A)} (hm : m ≠ ⊤) {c : p.asIdeal.ResidueField}
    (hc : c ≠ 0) : algebraMap p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] A) c ∉ m :=
  fun hmem ↦ hm (Ideal.eq_top_of_isUnit_mem m hmem ((isUnit_iff_ne_zero.mpr hc).map _))

/-- **The vanishing locus of a norm.** For a finite projective `R`-algebra `A` and `a : A`, the
norm of `a` lies in a prime `p` of `R` exactly when `a` lies in some prime of `A` lying over
`p`. -/
theorem projectiveNorm_mem_iff_exists_comap_eq [Module.Finite R A] [Module.Projective R A]
    (p : PrimeSpectrum R) (a : A) :
    projectiveNorm R a ∈ p.asIdeal ↔
      ∃ q : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap R A) q = p ∧ a ∈ q.asIdeal := by
  constructor
  · intro hmem
    have hzero : projectiveNorm p.asIdeal.ResidueField
        ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] a) = 0 := by
      rw [projectiveNorm_baseChange R a]
      exact Ideal.algebraMap_residueField_eq_zero.mpr hmem
    have hnotunit : ¬ IsUnit ((1 : p.asIdeal.ResidueField) ⊗ₜ[R] a) := fun hu ↦
      zero_ne_one (isUnit_zero_iff.mp (hzero ▸ hu.map (projectiveNorm _)))
    obtain ⟨m, hmmax, hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {(1 : p.asIdeal.ResidueField) ⊗ₜ[R] a})
      fun h ↦ hnotunit (Ideal.span_singleton_eq_top.mp h)
    have hxm : (1 : p.asIdeal.ResidueField) ⊗ₜ[R] a ∈ m :=
      hle (Ideal.mem_span_singleton_self _)
    have := hmmax.isPrime
    let φ : A →+* p.asIdeal.ResidueField ⊗[R] A :=
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.ResidueField ⊗[R] A).toRingHom
    refine ⟨⟨m.comap φ, inferInstance⟩, PrimeSpectrum.ext ?_, hxm⟩
    rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
    refine Ideal.ext fun r ↦ ?_
    have hφ : (φ.comp (algebraMap R A)) r =
        algebraMap p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] A)
          (algebraMap R p.asIdeal.ResidueField r) := by
      rw [← IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField]
      exact (Algebra.TensorProduct.includeRight :
        A →ₐ[R] p.asIdeal.ResidueField ⊗[R] A).commutes r
    rw [Ideal.mem_comap, hφ]
    constructor
    · intro hmem'
      by_contra hne
      exact notMem_of_ne_zero_algebraMap_tensor p hmmax.ne_top
        (fun h ↦ hne (Ideal.algebraMap_residueField_eq_zero.mp h)) hmem'
    · intro hr
      rw [Ideal.algebraMap_residueField_eq_zero.mpr hr, map_zero]
      exact m.zero_mem
  · rintro ⟨q, hq, ha⟩
    have hcomap : p.asIdeal = q.asIdeal.comap (algebraMap R A) := by rw [← hq]; rfl
    have hsq : (algebraMap A q.asIdeal.ResidueField).comp (algebraMap R A) =
        (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) hcomap).comp
          (algebraMap R p.asIdeal.ResidueField) := by
      refine RingHom.ext fun r ↦ ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
    exact Ideal.algebraMap_residueField_eq_zero.mp
      (projectiveNorm_eq_zero_of_field_hom R (algebraMap R p.asIdeal.ResidueField)
        (algebraMap A q.asIdeal.ResidueField) _ hsq a
        (Ideal.algebraMap_residueField_eq_zero.mpr ha))

/-- **The nonvanishing locus of a norm.** For a finite projective `R`-algebra `A` and `a : A`,
the norm of `a` avoids a prime `p` of `R` exactly when `a` avoids every prime of `A` lying over
`p`. -/
theorem projectiveNorm_notMem_iff_forall [Module.Finite R A] [Module.Projective R A]
    (p : PrimeSpectrum R) (a : A) :
    projectiveNorm R a ∉ p.asIdeal ↔
      ∀ q : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap R A) q = p → a ∉ q.asIdeal := by
  simp only [projectiveNorm_mem_iff_exists_comap_eq, not_exists, not_and]

end Algebra

end
