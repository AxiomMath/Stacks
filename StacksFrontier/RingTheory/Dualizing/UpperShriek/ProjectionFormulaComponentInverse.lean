module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaComponent

/-!
# The inverse of the projection formula at a K-flat representative, leg by leg

`Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaComponent` values the component of
the projection formula at the class of a K-flat complex `P` of `A`-modules and the class of an
arbitrary complex `L` of `B`-modules as a composite of eight isomorphisms: the model comparison of
`E` at `P`, the identification of `iStar` with derived restriction of scalars, the five pasted
comparisons of `Dualizing.ProjectionFormula.derivedProjKFlatChain` -- whose only non-elementary
factor is the chain-level projection formula
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` -- and that identification again.

The *inverse* is the direction every consumer of the projection formula in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit` reads it in, and it had no
component formula: `Dualizing.ProjectionFormula.derivedProjNatIso_inv_kFlat` equates the whole
inverse natural transformation at a K-flat class with
`(Dualizing.ProjectionFormula.derivedProjKFlatRep … ).inv` and stops there.  This file supplies
the formula, as the eight legs in reverse order, each inverted.

## Main results

* `CategoryTheory.Iso.inv_eq_of_hom_eq_comp_eight` -- the arity-eight analogue of the repo's
  `CategoryTheory.Iso.inv_eq_of_hom_eq_comp_five`, with its hypothesis grouped exactly as
  `Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q` associates its composite.
* `Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q` -- **the component formula for the
  inverse**.  No rewriting is needed: each leg is supplied as a `CategoryTheory.Functor.mapIso`,
  `CategoryTheory.Iso.app`, `CategoryTheory.Iso.symm` or `CategoryTheory.asIso` packaging whose
  `hom` projection is definitionally the corresponding leg of the forward formula, so the whole
  proof is one application of the helper to `derivedProjNatIso_hom_app_Q` itself.

No `@[stacks]` attribute is placed here: this is a computation of a morphism belonging to
[stacks 0E9L], whose tag sits where the projection formula is consumed.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0E9L](https://stacks.math.columbia.edu/tag/0E9L)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Iso

universe w w'

/-- An isomorphism given as a composite of eight isomorphisms, inverted. -/
theorem inv_eq_of_hom_eq_comp_eight {C : Type w} [Category.{w'} C]
    {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : C} (e : X₁ ≅ X₉)
    (a : X₁ ≅ X₂) (b : X₂ ≅ X₃) (c : X₃ ≅ X₄) (d : X₄ ≅ X₅) (g : X₅ ≅ X₆)
    (k : X₆ ≅ X₇) (m : X₇ ≅ X₈) (n : X₈ ≅ X₉)
    (h : e.hom = a.hom ≫ b.hom ≫ (c.hom ≫ d.hom ≫ g.hom ≫ k.hom ≫ m.hom) ≫ n.hom) :
    e.inv = n.inv ≫ m.inv ≫ k.inv ≫ g.inv ≫ d.inv ≫ c.inv ≫ b.inv ≫ a.inv :=
  inv_ext (by simp [h])

end CategoryTheory.Iso

universe u v

namespace Dualizing.ProjectionFormula

open CochainComplex CochainComplex.DerivedTensor CochainComplex.KFlat.ScalarBaseChange
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The chain-level component formula for the inverse of the projection formula.**  The five
pasted comparisons of `Dualizing.ProjectionFormula.derivedProjKFlatChain`, the identification of
`iStar` with derived restriction of scalars and the model comparison at the K-flat
representative `P`, each inverted and in the reverse order of
`Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q`. -/
theorem derivedProjNatIso_inv_app_Q (φ : A →+* B)
    (E : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, v, u,
      max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (hP : IsKFlat.{u, v} P)
    (L : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (derivedProjNatIso.{u, v} φ E iStar adj (DerivedCategory.Q.obj P)).inv.app
        (DerivedCategory.Q.obj L) =
      (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).map
          ((leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).hom.app
            (DerivedCategory.Q.obj L)) ≫
        (tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).map
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.hom.app L) ≫
          (derivedTensor_comparison.{u, v} A
              ((restrictScalarsLarge.{v, u, u} φ).obj L) P hP).hom ≫
            DerivedCategory.Q.map (baseChange_tensor_iso.{u, u, v} φ P L).inv ≫
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.inv.app
                  ((tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P)).obj L) ≫
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
                    (derivedTensor_comparison.{u, v} B L
                      ((extendScalarsLarge.{v, u, u} φ).obj P)
                      (isKFlat_extendScalarsLarge.{u, v} φ P hP)).inv ≫
                  (leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).inv.app
                      ((tensorRightDerived.{u, v} B
                        (DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P))).obj
                        (DerivedCategory.Q.obj L)) ≫
                    iStar.map
                      (((Functor.curry.obj
                            (derivedHomAdjunctionOverRing.{u, v,
                              max u v + 1} B).tensor).flip.mapIso
                        (@asIso _ _ _ _ (E.comparison.app P)
                          (E.comparison_isIso_of_kFlat P
                            ((isKFlat_iff_kFlat.{u, v} P).mp hP)))).inv.app
                        (DerivedCategory.Q.obj L)) :=
  Iso.inv_eq_of_hom_eq_comp_eight
    ((derivedProjNatIso.{u, v} φ E iStar adj (DerivedCategory.Q.obj P)).app
      (DerivedCategory.Q.obj L))
    (iStar.mapIso
      (((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} B).tensor).flip.mapIso
        (@asIso _ _ _ _ (E.comparison.app P)
          (E.comparison_isIso_of_kFlat P ((isKFlat_iff_kFlat.{u, v} P).mp hP)))).app
        (DerivedCategory.Q.obj L)))
    ((leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).app
      ((tensorRightDerived.{u, v} B
        (DerivedCategory.Q.obj ((extendScalarsLarge.{v, u, u} φ).obj P))).obj
        (DerivedCategory.Q.obj L)))
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.mapIso
      (derivedTensor_comparison.{u, v} B L ((extendScalarsLarge.{v, u, u} φ).obj P)
        (isKFlat_extendScalarsLarge.{u, v} φ P hP)))
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.app
      ((tensorRightLarge.{u, v} ((extendScalarsLarge.{v, u, u} φ).obj P)).obj L))
    (DerivedCategory.Q.mapIso (baseChange_tensor_iso.{u, u, v} φ P L))
    (derivedTensor_comparison.{u, v} A ((restrictScalarsLarge.{v, u, u} φ).obj L) P hP).symm
    ((tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).mapIso
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategoryFactors.app L).symm)
    ((tensorRightDerived.{u, v} A (DerivedCategory.Q.obj P)).mapIso
      ((leftAdjointIsoRestrictScalarsDerived.{u, v} φ iStar adj).app
        (DerivedCategory.Q.obj L)).symm)
    (derivedProjNatIso_hom_app_Q.{u, v} φ E iStar adj P hP L)

end Dualizing.ProjectionFormula

end
