module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.DerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom

/-!
# The projection map for the derived direct image on `D(X_étale, Λ)`

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring. The projection map of
Equation 21.50.0.1 of [Stacks, Tag 0B56] for the morphism of constant ringed topoi
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`, read on `D(X_étale, Λ)` and `D(Y_étale, Λ)`, is a map

`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)`

for `E` in `D(X_étale, Λ)` and `K` in `D(Y_étale, Λ)`. [Stacks, Tag 0F0G] asserts that it is an
isomorphism when `f` is proper and `Λ` is torsion.

For a compactification `j : X ⟶ X̄` of `f : X ⟶ Y` with structure morphism `f̄ : X̄ ⟶ Y`, so
that `Rf_! = Rf̄_* ∘ j_!`, this file composes the projection map of `f̄` at `j_!E` with the
identification `j_!E ⊗^L_Λ f̄^{-1}K = j_!(E ⊗^L_Λ f^{-1}K)` of [Stacks, Tag 0GL1] (in the form
`Stacks.EtaleCohomology.etaleDerivedProjectionIso`) to obtain the map

`Rf_!E ⊗^L_Λ K ⟶ Rf_!(E ⊗^L_Λ f^{-1}K)`

of [Stacks, Tag 0GL5], and shows that it is invertible exactly when the projection map of `f̄`
is invertible at `(j_!E, K)`. This is the proof of Tag 0GL5 in the source.

## Main definitions

* `Stacks.EtaleCohomology.etaleDerivedPushforwardTensorMap`: the projection map
  `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)`.
* `Stacks.EtaleCohomology.etaleExtensionByZeroTensorIso`: for an open immersion `j : U ⟶ X` and
  `g : X ⟶ Y`, `j_!E ⊗^L_Λ g^{-1}K ≅ j_!(E ⊗^L_Λ (j ≫ g)^{-1}K)`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedTensorMap`: the map
  `Rf_!E ⊗^L_Λ K ⟶ Rf_!(E ⊗^L_Λ f^{-1}K)`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleDerivedPushforwardTensorMap_iff`: the projection map on
  `D(X_étale, Λ)` is invertible exactly when the one of the constant ringed topoi is.
* `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedTensorMap_iff`: the map for `Rf_!` is
  invertible exactly when the projection map of `f̄` is invertible at `(j_!E, K)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The projection map `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f^{-1}K)` on `D(X_étale, Λ)`**: Equation
21.50.0.1 of [Stacks, Tag 0B56] for the morphism of constant ringed topoi
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`, read through the equivalences
`Stacks.EtaleCohomology.etaleDerivedEquivalence` and the comparisons of derived direct and inverse
images `Stacks.EtaleCohomology.etaleDerivedPushforwardIso` and
`Stacks.EtaleCohomology.etaleRingedDerivedPullbackIso`. -/
def etaleDerivedPushforwardTensorMap (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    ((etaleDerivedTensor.{u, r} Λ Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj E)).obj K ⟶
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
        (((etaleDerivedTensor.{u, r} Λ X).obj E).obj
          ((etaleModuleDerivedInverseImage.{u, r} Λ f).obj K)) :=
  (etaleDerivedEquivalence.{u, r} Λ Y).inverse.map
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (etaleRingedSite.{u, r} Λ Y).O).map
          ((etaleDerivedPushforwardIso.{u, r} Λ f).hom.app E)).app
          ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K) ≫
        Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap
          (etaleRingedToposHom.{u, r} Λ f) ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj E)
          ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K) ≫
        (etaleRingedDerivedPushforward.{u, r} Λ f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
              (etaleRingedSite.{u, r} Λ X).O).obj
              ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj E)).map
              ((etaleRingedDerivedPullbackIso.{u, r} Λ f).hom.app K) ≫
            (etaleDerivedEquivalence.{u, r} Λ X).counitInv.app _) ≫
        (etaleDerivedPushforwardIso.{u, r} Λ f).inv.app _) ≫
    (etaleDerivedEquivalence.{u, r} Λ Y).unitInv.app _

/-- **The projection map on `D(X_étale, Λ)` is invertible exactly when the projection map of
the constant ringed topoi is**, at the transported objects. -/
theorem isIso_etaleDerivedPushforwardTensorMap_iff (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    IsIso (etaleDerivedPushforwardTensorMap.{u, r} Λ f E K) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap
        (etaleRingedToposHom.{u, r} Λ f) ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj E)
        ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj K)) :=
  (isIso_comp_right_iff _ _).trans ((isIso_iff_of_reflects_iso _ _).trans
    ((isIso_comp_left_iff _ _).trans (isIso_comp_right_iff _ _)))

end Pushforward

section ExtensionByZero

variable {U X Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (g : X ⟶ Y)

/-- The derived inverse image `etaleModuleDerivedInverseImage` of sheaves of `Λ`-modules along a
composite of morphisms of schemes is the composite of the derived inverse images. -/
def etaleModuleDerivedInverseImageSchemeCompIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    etaleModuleDerivedInverseImage.{u, r} Λ (a ≫ b) ≅
      etaleModuleDerivedInverseImage.{u, r} Λ b ⋙ etaleModuleDerivedInverseImage.{u, r} Λ a :=
  letI := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ a
  letI := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ a
  letI := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ b
  letI := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ b
  letI := etaleModuleInverseImage_preservesFiniteLimits.{u, r} Λ (a ≫ b)
  letI := etaleModuleInverseImage_preservesFiniteColimits.{u, r} Λ (a ≫ b)
  Dualizing.mapDerivedCategoryNatIso _ _ (etaleModuleInverseImageCompIso.{u, r} Λ a b) ≪≫
    (DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _)

/-- **[Stacks, Tag 0GL1] for an open immersion, against an inverse image**:
`j_!E ⊗^L_Λ g^{-1}K ≅ j_!(E ⊗^L_Λ (j ≫ g)^{-1}K)` for `j : U ⟶ X` an open immersion, `g : X ⟶ Y`,
`E` in `D(U_étale, Λ)` and `K` in `D(Y_étale, Λ)`. -/
def etaleExtensionByZeroTensorIso (E : DerivedCategory (EtaleModules.{u, r} Λ U))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    ((etaleDerivedTensor.{u, r} Λ X).obj
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj E)).obj
        ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj K) ≅
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj
        (((etaleDerivedTensor.{u, r} Λ U).obj E).obj
          ((etaleModuleDerivedInverseImage.{u, r} Λ (j ≫ g)).obj K)) :=
  etaleDerivedTensorBraidingIso.{u, r} Λ X _ _ ≪≫
    (((etaleDerivedProjectionIso.{u, r} Λ j).app
      ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj K)).app E).symm ≪≫
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).mapIso
      (etaleDerivedTensorBraidingIso.{u, r} Λ U _ _ ≪≫
        ((etaleDerivedTensor.{u, r} Λ U).obj E).mapIso
          ((etaleModuleDerivedInverseImageSchemeCompIso.{u, r} Λ j g).app K).symm)

end ExtensionByZero

section LowerShriek

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f))

/-- The derived inverse image along `f` is the one along `j ∘ f̄`, for a compactification `j`. -/
def etaleModuleDerivedInverseImageCompactificationIso :
    etaleModuleDerivedInverseImage.{u, r} Λ (j.immersion ≫ j.toBase) ≅
      etaleModuleDerivedInverseImage.{u, r} Λ f :=
  eqToIso (by rw [CompactificationOf.immersion_toBase])

/-- **The map `Rf_!E ⊗^L_Λ K ⟶ Rf_!(E ⊗^L_Λ f^{-1}K)` of [Stacks, Tag 0GL5]**, for
`Rf_! = Rf̄_* ∘ j_!` computed through a compactification `j : X ⟶ X̄` of `f` with structure
morphism `f̄`: the projection map of `f̄` at `(j_!E, K)`
(`Stacks.EtaleCohomology.etaleDerivedPushforwardTensorMap`), followed by `Rf̄_*` of the
identification `j_!E ⊗^L_Λ f̄^{-1}K ≅ j_!(E ⊗^L_Λ f^{-1}K)` of [Stacks, Tag 0GL1]. -/
def derivedLowerShriekUnboundedTensorMap (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    ((etaleDerivedTensor.{u, r} Λ Y).obj ((derivedLowerShriekUnbounded.{u, r} f j Λ).obj E)).obj
        K ⟶
      (derivedLowerShriekUnbounded.{u, r} f j Λ).obj
        (((etaleDerivedTensor.{u, r} Λ X).obj E).obj
          ((etaleModuleDerivedInverseImage.{u, r} Λ f).obj K)) :=
  etaleDerivedPushforwardTensorMap.{u, r} Λ j.toBase
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj E) K ≫
    ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).mapIso
      (etaleExtensionByZeroTensorIso.{u, r} Λ j.immersion j.toBase E K ≪≫
        (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).mapIso
          (((etaleDerivedTensor.{u, r} Λ X).obj E).mapIso
            ((etaleModuleDerivedInverseImageCompactificationIso.{u, r} Λ j).app K)))).hom

/-- **The map of [Stacks, Tag 0GL5] is invertible exactly when the projection map of `f̄` is**,
at `(j_!E, K)`. -/
theorem isIso_derivedLowerShriekUnboundedTensorMap_iff
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    IsIso (derivedLowerShriekUnboundedTensorMap.{u, r} Λ j E K) ↔
      IsIso (etaleDerivedPushforwardTensorMap.{u, r} Λ j.toBase
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj E) K) :=
  isIso_comp_right_iff _ _

end LowerShriek

end Stacks.EtaleCohomology

end
