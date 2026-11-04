module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackSingleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.UnitLawNaturality

/-!
# The map `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` of Stacks 08IJ

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and `E ∈ D(𝒪_Y)`.  The proof of Stacks 08IJ uses the canonical map

`E ⊗^L_{𝒪_Y} Rf_*𝒪_X ⟶ Rf_*Lf^*E`

adjoint to `Lf^*(E ⊗^L Rf_*𝒪_X) ≅ Lf^*E ⊗^L Lf^*Rf_*𝒪_X ⟶ Lf^*E ⊗^L 𝒪_X = Lf^*E`, built from
the identification of Stacks 07A4, the counit of `Lf^* ⊣ Rf_*` in the second factor and the unit
law of `⊗^L`.  For affine `f` the source is `E ⊗^L f_*𝒪_X`, by Stacks 073H.

## Main definitions

* `AlgebraicGeometry.Space.derivedPushforwardStructureTensorMap`: the map
  `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E`.

## References

* [Stacks Project, Tag 08IJ](https://stacks.math.columbia.edu/tag/08IJ)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)
open scoped CategoryTheory.Prod

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The structure sheaf of an algebraic space, placed in degree `0` of its derived category. -/
abbrev structureDerived (X : AlgebraicSpaces B S hS) :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))

/-- **The map `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E`** of the proof of Stacks 08IJ: the transpose under
`Lf^* ⊣ Rf_*` of the isomorphism of Stacks 07A4 at `(E, Rf_*𝒪_X)`, followed by the counit
`Lf^*Rf_*𝒪_X ⟶ 𝒪_X` in the second factor and the unit law `Lf^*E ⊗^L 𝒪_X ≅ Lf^*E`. -/
def derivedPushforwardStructureTensorMap (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    ((smallEtaleDerivedTensor B S hS Y).obj E).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
          (structureDerived X)) ⟶
      (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj E) :=
  Stacks.ProjectionFormula.adjunctionTensorMapSnd (smallEtaleDerivedModuleAdjunction B S hS f)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleDerivedPullbackTensorIso f).hom E (structureDerived X) ≫
    (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).map
      (((smallEtaleDerivedTensorProduct B S hS X).unitNatIso _).hom.app
        ((smallEtaleDerivedModulePullback B S hS f).obj E))

/-- **The map `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` is natural in `E`.** -/
theorem derivedPushforwardStructureTensorMap_naturality (f : X ⟶ Y)
    {E E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (u : E ⟶ E') :
    ((smallEtaleDerivedTensor B S hS Y).map u).app
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
          (structureDerived X)) ≫ derivedPushforwardStructureTensorMap f E' =
      derivedPushforwardStructureTensorMap f E ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).map
          ((smallEtaleDerivedModulePullback B S hS f).map u) := by
  have h := Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_map_naturality
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso f).hom (structureDerived X)
    (fun W => ((smallEtaleDerivedTensorProduct B S hS X).unitNatIso _).hom.app W)
    (fun {W W'} w => by
      simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id]
      exact ((smallEtaleDerivedTensorProduct B S hS X).unitNatIso _).hom.naturality w) u
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

/-- The map `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` as a natural transformation. -/
def derivedPushforwardStructureTensorNatTrans (f : X ⟶ Y) :
    (smallEtaleDerivedTensor B S hS Y).flip.obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).obj
          (structureDerived X)) ⟶
      smallEtaleDerivedModulePullback B S hS f ⋙
        derivedPushforward (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) where
  app E := derivedPushforwardStructureTensorMap f E
  naturality _ _ u := derivedPushforwardStructureTensorMap_naturality f u

/-- **The map `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` is an isomorphism at a shift of the structure
sheaf**, for every morphism `f`: tensoring with `𝒪_Y[q]` and with `Lf^*𝒪_Y[q] ≅ 𝒪_X[q]` are
autoequivalences, so the map is the mate of an isomorphism along autoequivalences. -/
theorem isIso_derivedPushforwardStructureTensorMap_of_iso (f : X ⟶ Y)
    {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))} (q : ℤ)
    (e : E ≅ DerivedCategory.Q.obj
      (Stacks.SheafOfModules.singleUnitComplex (smallEtaleRingedTopos B S hS Y).O q)) :
    IsIso (derivedPushforwardStructureTensorMap f E) := by
  let L := smallEtaleDerivedModulePullback B S hS f
  have : ((smallEtaleDerivedTensor B S hS Y).obj E).IsEquivalence :=
    (smallEtaleDerivedTensorProduct B S hS Y).isEquivalence_tensor_obj_of_iso q e
  have : ((smallEtaleDerivedTensor B S hS X).obj (L.obj E)).IsEquivalence :=
    (smallEtaleDerivedTensorProduct B S hS X).isEquivalence_tensor_obj_of_iso q
      (L.mapIso e ≪≫ Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso
        (smallEtaleRingedToposHom B S hS f) q)
  have := isEquivalence_curry_uncurry_obj (smallEtaleDerivedTensor B S hS Y) E
  have := isEquivalence_curry_uncurry_obj (smallEtaleDerivedTensor B S hS X) (L.obj E)
  have := Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_of_isEquivalence
    (smallEtaleDerivedModuleAdjunction B S hS f)
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
    (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
    (smallEtaleDerivedPullbackTensorIso f).hom E (structureDerived X)
  exact (asIso (Stacks.ProjectionFormula.adjunctionTensorMapSnd
      (smallEtaleDerivedModuleAdjunction B S hS f)
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS Y))
      (Functor.uncurry.obj (smallEtaleDerivedTensor B S hS X))
      (smallEtaleDerivedPullbackTensorIso f).hom E (structureDerived X)) ≪≫
    (derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f)).mapIso
      (((smallEtaleDerivedTensorProduct B S hS X).unitNatIso _).app (L.obj E))).isIso_hom

end AlgebraicGeometry.Space

end
