module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.Algebra.Homology.DerivedCategory.MappingConeApproximation
public import StacksFrontier.Algebra.Homology.Embedding.StupidTruncHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterionGeneral

/-!
# Local strictly perfect approximations with a cone vanishing in the high degrees

Let `(C, O)` be a ringed site and `E` an `m`-pseudo-coherent complex of `O`-modules. Locally,
`E` receives a strictly perfect approximation `α : ℰ ⟶ E|_V` which vanishes below degree `m` and
whose mapping cone has no cohomology in the degrees `≥ m`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_local_strictlyPerfect_approximation_with_cone`: locally,
  an `m`-pseudo-coherent complex receives a strictly perfect approximation which vanishes below
  degree `m` and whose mapping cone has no cohomology in the degrees `≥ m`.

## Implementation notes

The approximation of the definition of
`AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom` is replaced by its stupid truncation
in degrees `≥ m`: that is still strictly perfect
(`Stacks.SheafOfModules.isStrictlyPerfect_stupidTrunc_general`), and its inclusion is invertible
on cohomology above `m` and epic in degree `m`
(`HomologicalComplex.isIso_homologyMap_ιStupidTrunc_embeddingUpIntGE`,
`HomologicalComplex.epi_homologyMap_ιStupidTrunc_embeddingUpIntGE`). The cone vanishing is
`CochainComplex.isZero_homology_mappingCone_of_approximation`.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Locally, an `m`-pseudo-coherent complex of `O`-modules receives a strictly perfect
approximation which vanishes below degree `m` and whose cone has no cohomology in the degrees
`≥ m`.**

Over each arrow `V ⟶ U` of a covering presieve of `U` there are a strictly perfect complex `ℰ`
of `O|_V`-modules with `ℰ^i = 0` for `i < m` and a map `α : ℰ ⟶ E|_V` with `H^j(α)` invertible
for `j > m` and epic for `j = m`, such that `H^i(C(α)) = 0` for every `i ≥ m`. -/
theorem exists_local_strictlyPerfect_approximation_with_cone
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (hE : X.IsPseudoCoherentComplexFrom E m) (U : X.C) :
    ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
          (∀ i : ℤ, i < m → IsZero (P.X i)) ∧
          ∃ α : P ⟶ X.restrictComplex E V,
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
            Epi (HomologicalComplex.homologyMap α m) ∧
            ∀ i : ℤ, m ≤ i → IsZero ((CochainComplex.mappingCone α).homology i) := by
  obtain ⟨S, hS, hdata⟩ := hE U
  refine ⟨S, hS, fun V f hf => ?_⟩
  obtain ⟨P, hP, α, hiso, hepi⟩ := hdata f hf
  let _ := HasDerivedCategory.standard
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))
  have hiso' : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE m) ≫ α) j) := by
    intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := hiso j hj
    have := P.isIso_homologyMap_ιStupidTrunc_embeddingUpIntGE m j hj
    infer_instance
  have hepi' : Epi (HomologicalComplex.homologyMap
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE m) ≫ α) m) := by
    rw [HomologicalComplex.homologyMap_comp]
    have := P.epi_homologyMap_ιStupidTrunc_embeddingUpIntGE m
    infer_instance
  exact ⟨P.stupidTrunc (ComplexShape.embeddingUpIntGE m),
    Stacks.SheafOfModules.isStrictlyPerfect_stupidTrunc_general _
      (ComplexShape.embeddingUpIntGE m) hP,
    fun i hi => P.isZero_X_stupidTrunc_embeddingUpIntGE m i hi,
    P.ιStupidTrunc (ComplexShape.embeddingUpIntGE m) ≫ α, hiso', hepi', fun i hi =>
      CochainComplex.isZero_homology_mappingCone_of_approximation _ m hiso' hepi' i hi⟩

end AlgebraicGeometry.RingedSite

end
