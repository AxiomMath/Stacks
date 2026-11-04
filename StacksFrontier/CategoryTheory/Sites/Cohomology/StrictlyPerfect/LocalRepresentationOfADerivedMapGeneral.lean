module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap

/-!
# Local representation of a derived map, with the site's universes independent

`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/LocalRepresentationOfADerivedMap.lean`
is Stacks 08FR (1) on a ringed site whose objects and morphisms share a universe. This file
states it, and its quasi-isomorphism form, with the object and morphism universes of the site
independent, which is what the small étale site of a scheme (objects in `Type (u + 1)`,
morphisms in `Type u`) needs.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_general`: Stacks 08FR (1).
* `AlgebraicGeometry.RingedSite.exists_coveringSieve_quasiIso_of_derivedIso_general`: an
  isomorphism of `D(O|_U)` out of a strictly perfect complex is, locally, a quasi-isomorphism of
  complexes.

## References

* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

/-- **Stacks 08FR (1), with the object and morphism universes of the site independent.** Let
`(C, O)` be a ringed site and `U` an object of `C`. Let `E`, `F` be
complexes of `O|_U`-modules with `E` strictly perfect. Any morphism `α : E ⟶ F` of `D(O|_U)` is,
after restriction along the arrows of a covering sieve of `U`, the image under the localisation
functor of a morphism of complexes. -/
alias exists_coveringSieve_complexMap_general := exists_coveringSieve_complexMap_independentUniverses

/-- **An isomorphism of `D(O|_U)` out of a strictly perfect complex is, locally, a
quasi-isomorphism of complexes**, with the object and morphism universes of the site independent.
This is `exists_coveringSieve_complexMap_general` together with the exactness of restriction
along an arrow of the site, which lets the localisation functor detect the quasi-isomorphism. -/
theorem exists_coveringSieve_quasiIso_of_derivedIso_general
    (X : RingedSite.{u, v, w}) (U : X.C)
    [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}]
    [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
    {P F : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj F) :
    ∃ S : Sieve U, S ∈ X.J U ∧
      ∀ ⦃W : X.C⦄ (f : W ⟶ U), S f →
        ∃ β : ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
            ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F,
          QuasiIso β := by
  obtain ⟨S, hS, hβ⟩ := exists_coveringSieve_complexMap_general X U hP e.hom
  refine ⟨S, hS, fun W f hf => ?_⟩
  obtain ⟨hsheaf, hlocal, hadd, hlim, hcolim, β, hcomm⟩ := hβ f hf
  let := hsheaf
  let := hlocal
  let : HasDerivedCategory
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    HasDerivedCategory.standard _
  let := hadd
  let := hlim
  let := hcolim
  have hcomp : IsIso
      ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          f).mapDerivedCategory.map e.hom ≫
        (SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          f).mapDerivedCategoryFactors.hom.app F) :=
    inferInstance
  rw [hcomm] at hcomp
  exact ⟨β, (DerivedCategory.isIso_Q_map_iff_quasiIso _ β).mp
    ((isIso_comp_left_iff
      ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        f).mapDerivedCategoryFactors.hom.app P)
      (DerivedCategory.Q.map β)).mp hcomp)⟩

end AlgebraicGeometry.RingedSite

end
