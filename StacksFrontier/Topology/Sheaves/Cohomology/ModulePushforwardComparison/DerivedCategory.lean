module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages

/-!
# Pushing forward and forgetting, on unbounded derived categories

Let `f : X ⟶ Y` be a morphism of ringed spaces whose direct image of sheaves of modules — and
whose direct image of abelian sheaves — is exact, the inclusion of a closed subset being the case
of interest.  Underived, "push forward and forget" *is* "forget and push forward":
`Stacks.Cohomology.ModulePushforwardComparison.modulePushforwardCompToSheafIso` is `Iso.refl`.
This file carries that identity to the unbounded derived categories, where it is no longer an
identity: the four functors involved are descents through `DerivedCategory.Q`, and a composite of
descents is only canonically isomorphic to the descent of the composite.

## Main definitions

* `Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso`:
  `f_*^D ⋙ Φ_Y^D ≅ Φ_X^D ⋙ f_*^{ab,D}`, where `Φ` is the forgetful functor to abelian sheaves
  and the superscript `D` is `CategoryTheory.Functor.mapDerivedCategory`.

## Main results

* `Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_fac`:
  **what pins it down.**  At the image of a cochain complex it is compatible with the three
  factorizations `CategoryTheory.Functor.mapDerivedCategoryFactors` of the functors involved.  The
  statement contains no inverse, so it can be used in either direction.

## Implementation notes

The isomorphism is the composite

`f_*^D ⋙ Φ_Y^D ≅ (f_* ⋙ Φ_Y)^D = (Φ_X ⋙ f_*^{ab})^D ≅ Φ_X^D ⋙ f_*^{ab,D}`,

whose outer two factors are `Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso` and
whose middle factor is `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` applied
to `modulePushforwardCompToSheafIso`.  That middle factor is *not* dropped even though the
underived comparison is `Iso.refl`: the two composite functors, though definitionally equal, carry
different `PreservesFiniteLimits` and `PreservesFiniteColimits` instance terms, and
`CategoryTheory.Functor.mapDerivedCategory` depends on those.

The exactness of the two direct images is taken as hypotheses rather than proved: it fails for a
general morphism of ringed spaces, and the consumers supply it from
`Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits` and its abelian
counterpart.

The two evaluations of those comparisons at the image of a cochain complex,
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q` and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q`, are taken from
`StacksFrontier/Algebra/Homology/DerivedCategory/MapDerivedCategoryComparisons.lean`, beside the
definitions they evaluate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModulePushforwardComparison

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- Collapsing the chain of eleven morphisms that the comparison unfolds to, at an abstract
category: three composable pairs are inverse to each other, one factor is an identity, and what
is left is the two leading morphisms.  It is stated at a variable category and applied with
`exact` because the objects along the chain are definitionally equal in two spellings each —
`f_*` followed by forgetting, and forgetting followed by `f_*` — which `rw` and `simp` refuse to
identify, reporting that the target is not type-correct at their transparency level. -/
private lemma chain_cancel {C₀ : Type*} [Category* C₀] {W Z A A₁ A₂ B B₁ : C₀}
    (p : W ⟶ Z) (r : Z ⟶ A)
    (u₁ : A ⟶ A₁) (u₂ : A₁ ⟶ A) (h₁ : u₁ ≫ u₂ = 𝟙 A)
    (q : A ⟶ A) (hq : q = 𝟙 A)
    (u₃ : A ⟶ A₂) (u₄ : A₂ ⟶ A) (h₂ : u₃ ≫ u₄ = 𝟙 A)
    (i : A ⟶ B) (m₁ : B ⟶ B₁) (m₂ : B₁ ⟶ B) (hm : m₁ ≫ m₂ = 𝟙 B) (j : B ⟶ A)
    (hij : i ≫ j = 𝟙 A) :
    p ≫ r ≫ u₁ ≫ u₂ ≫ q ≫ u₃ ≫ u₄ ≫ i ≫ m₁ ≫ m₂ ≫ j = p ≫ r := by
  rw [hq]
  simp [h₁, h₂, hij, reassoc_of% hm]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

variable [PreservesFiniteLimits (modulePushforward f)]
  [PreservesFiniteColimits (modulePushforward f)]
  [PreservesFiniteColimits (abelianPushforward f)]

/-- **Pushing modules forward and then forgetting is forgetting and then pushing abelian sheaves
forward, on unbounded derived categories.**

Underived the two functors are definitionally equal — `modulePushforwardCompToSheafIso` is
`Iso.refl` — but their descents to the derived categories are composites of descents, and this is
the canonical comparison of such a composite with the descent of the composite, in both places,
with the underived identity in between. -/
def derivedModulePushforwardCompToSheafIso :
    (modulePushforward f).mapDerivedCategory ⋙
        (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategory ⋙
        (abelianPushforward f).mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso (modulePushforward f)
      (_root_.SheafOfModules.toSheaf (structureSheafRing Y))).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (modulePushforwardCompToSheafIso f) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)) (abelianPushforward f)

/-- **What pins the derived comparison down.**  At the image of a cochain complex it intertwines
the canonical factorizations `CategoryTheory.Functor.mapDerivedCategoryFactors` of the four
functors involved: going down the right-hand side of the square and then forgetting degreewise is
going down the left-hand side and then pushing forward degreewise.  No inverse occurs, so the
identity can be used in either direction. -/
theorem derivedModulePushforwardCompToSheafIso_fac
    (P : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (derivedModulePushforwardCompToSheafIso f).hom.app (DerivedCategory.Q.obj P) ≫
        (abelianPushforward f).mapDerivedCategory.map
          ((_root_.SheafOfModules.toSheaf
            (structureSheafRing X)).mapDerivedCategoryFactors.hom.app P) ≫
        (abelianPushforward f).mapDerivedCategoryFactors.hom.app
          (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (show ((modulePushforward f).mapDerivedCategory ⋙
              (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory).obj
                (DerivedCategory.Q.obj P) ⟶
            DerivedCategory.Q.obj
              (((abelianPushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P)) from
        (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategory.map
            ((modulePushforward f).mapDerivedCategoryFactors.hom.app P) ≫
          (_root_.SheafOfModules.toSheaf (structureSheafRing Y)).mapDerivedCategoryFactors.hom.app
            (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have hmid := Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q
    (modulePushforward f ⋙ _root_.SheafOfModules.toSheaf (structureSheafRing Y))
    (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianPushforward f)
    (modulePushforwardCompToSheafIso f) P
  simp only [derivedModulePushforwardCompToSheafIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, hmid,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q]
  refine chain_cancel _ _ _ _ ?_ _ ?_ _ _ ?_ _ _ _ ?_ _ ?_
  · exact Iso.inv_hom_id_app _ _
  · exact DerivedCategory.Q.map_id _
  · exact Iso.inv_hom_id_app _ _
  · exact ((abelianPushforward f).mapDerivedCategory.mapIso
      ((_root_.SheafOfModules.toSheaf
        (structureSheafRing X)).mapDerivedCategoryFactors.app P)).inv_hom_id
  · exact Iso.inv_hom_id_app _ _

end Stacks.Cohomology.ModulePushforwardComparison

end
