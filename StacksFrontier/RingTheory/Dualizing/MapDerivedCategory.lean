module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Exact functors and the derived categories they induce

An exact functor `F` between abelian categories with derived categories induces
`F.mapDerivedCategory`, and this file records how that assignment behaves on isomorphisms,
composites and the identity: isomorphic functors induce isomorphic functors, a composite induces
the composite, and restriction of scalars along the identity induces the identity.

## Main definitions

* `Dualizing.mapDerivedCategoryNatIso`: an isomorphism `F ≅ G` of exact functors induces
  `F.mapDerivedCategory ≅ G.mapDerivedCategory`.
* `Dualizing.mapDerivedCategoryIsoFromNatIso`: the same isomorphism read at a single object.
* `Dualizing.mapDerivedCategoryCompNatIso`: an isomorphism `F ⋙ G ≅ H` induces
  `F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`.
* `Dualizing.mapDerivedCategoryComp`: the special case `H = F ⋙ G`, in the form
  `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`.
* `Dualizing.mapDerivedCategoryIdIso`: restriction of scalars along `RingHom.id B` induces the
  identity of `DerivedCategory (ModuleCat B)`.

## Implementation notes

Each isomorphism is obtained from `CategoryTheory.Localization.liftNatIso`: the functors induced
on derived categories are lifts along `DerivedCategory.Q` of the functors induced on cochain
complexes, so an isomorphism of the latter descends to the former.

The derived-category universes are instance hypotheses rather than inherited from
`HasDerivedCategory.standard`, which is what lets a file working with the standard derived
category use these at its own universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- `comp_preservesFiniteLimits` and `comp_preservesFiniteColimits` are lemmas rather than
-- instances; exactness of the composite is needed to even state `mapDerivedCategoryComp`.
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

namespace Dualizing

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

/-- Isomorphic exact functors induce isomorphic functors on derived categories. -/
def mapDerivedCategoryNatIso (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) : F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory)
    (DerivedCategory.Q ⋙ G.mapDerivedCategory)
    F.mapDerivedCategory G.mapDerivedCategory
    (F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫ G.mapDerivedCategoryFactors.symm)

/-- An isomorphism of exact functors induces, at each object of the derived category, an
isomorphism of the images under the functors induced on derived categories. -/
def mapDerivedCategoryIsoFromNatIso (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory C) :
    F.mapDerivedCategory.obj K ≅ G.mapDerivedCategory.obj K :=
  (mapDerivedCategoryNatIso F G e).app K

/-- An isomorphism `F ⋙ G ≅ H` of exact functors induces an isomorphism between the composite of
the functors induced by `F` and `G` on derived categories and the functor induced by `H`. -/
def mapDerivedCategoryCompNatIso (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (DerivedCategory.Q ⋙ H.mapDerivedCategory) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      H.mapDerivedCategoryFactors.symm)

/-- The functor induced on derived categories by a composite of exact functors is the composite
of the induced functors. -/
def mapDerivedCategoryComp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  (mapDerivedCategoryCompNatIso F G (F ⋙ G) (Iso.refl _)).symm

/-- An exact equivalence of abelian categories induces an equivalence of their derived
categories. -/
def mapDerivedCategoryEquivalenceOfEquivalence (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    [PreservesFiniteLimits e.functor] [PreservesFiniteColimits e.functor]
    [PreservesFiniteLimits e.inverse] [PreservesFiniteColimits e.inverse] :
    DerivedCategory C ≌ DerivedCategory D :=
  let ec := e.mapHomologicalComplex (ComplexShape.up ℤ)
  Localization.equivalence DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
    (e.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    e.functor.mapDerivedCategory
    (e.inverse.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    e.inverse.mapDerivedCategory
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e.inverse.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.unitIso.symm _ ≪≫ Functor.leftUnitor _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.counitIso _ ≪≫ Functor.leftUnitor _)

/-- Restriction of scalars along the identity of `B` induces the identity functor of
`DerivedCategory (ModuleCat B)`. -/
def mapDerivedCategoryIdIso {B : Type u} [CommRing B]
    [HasDerivedCategory.{w₁} (ModuleCat.{u} B)] :
    (ModuleCat.restrictScalars.{u} (RingHom.id B)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u} B)) :=
  let F := 𝟭 (ModuleCat.{u} B)
  let η : DerivedCategory.Q ⋙ F.mapDerivedCategory ≅ DerivedCategory.Q :=
    F.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} B) (ComplexShape.up ℤ))
          DerivedCategory.Q ≪≫
      Functor.leftUnitor DerivedCategory.Q
  let e := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory) DerivedCategory.Q
    F.mapDerivedCategory (𝟭 (DerivedCategory (ModuleCat.{u} B))) η
  mapDerivedCategoryNatIso (ModuleCat.restrictScalars.{u} (RingHom.id B)) F
    (ModuleCat.restrictScalarsId B) ≪≫ e

end Dualizing

end
