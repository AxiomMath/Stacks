module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfectPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackFiniteProjectiveComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfALocallyConstantComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect

/-!
# The modules `𝒪_X ⊗_A M` on the spaces-étale model, and perfect complexes built from them

Let `X` be an algebraic space and `ψ : A ⟶ Γ(X, 𝒪_X)` a ring map. The inverse image along the
morphism `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, A)` of the model
(`AlgebraicGeometry.Space.spacesEtaleModelToPoint`) is a functor `T_ψ : M ↦ 𝒪_X ⊗_A M` from
`A`-modules to modules on the model. It is additive and right exact and carries `A` to `𝒪_X`, so
it carries a bounded complex `C` of finite projective `A`-modules to a strictly perfect complex,
whose image in the derived category is perfect.

For `g : X' ⟶ X`, `ψ' : A' ⟶ Γ(X', 𝒪_{X'})` and `α : A ⟶ A'` with `ψ' ∘ α = g^* ∘ ψ`, the derived
pullback of `T_ψ(C)` is computed termwise (`T_ψ(C)` is a bounded complex of flat modules), and
termwise it is `T_{ψ'}(A' ⊗_A C)` by
`AlgebraicGeometry.Space.spacesEtaleModelToPointPullbackCompIso`:

`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)`.

This is the form in which the affine case of the descent of perfect objects along a limit of
algebraic spaces (Stacks 09RJ) is assembled.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelPointTensor`: the functor `T_ψ`.
* `AlgebraicGeometry.Space.spacesEtaleModelPointTensorObjSelfIso`: `T_ψ(A) ≅ 𝒪_X`.
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIso`: `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_Q_spacesEtaleModelPointTensor`: `T_ψ(C)` is perfect.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (ψ : A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)))

/-- **The functor `M ↦ 𝒪_X ⊗_A M` on the model of the spaces-étale site of `X`**, for a ring map
`ψ : A ⟶ Γ(X, 𝒪_X)`: the inverse image along `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, A)`. -/
abbrev spacesEtaleModelPointTensor :
    ModuleCat.{u} A ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS X).O) :=
  (pointModuleCatEquiv (R := A)).inverse ⋙
    (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).inverse ⋙
      (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).pullbackTopos

/-- `T_ψ` is left adjoint to sections over the terminal object read as `A`-modules. -/
def spacesEtaleModelPointTensorAdjunction :
    spacesEtaleModelPointTensor B S hS ψ ⊣
      (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).pushforwardTopos ⋙
        Stacks.PointRingedSite.ev (CommRingCat.of A) ⋙ (pointModuleCatEquiv (R := A)).functor :=
  (pointModuleCatEquiv (R := A)).symm.toAdjunction.comp
    ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).symm.toAdjunction.comp
      (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).pullbackPushforwardAdjunctionTopos)

/-- `T_ψ` is additive, being a left adjoint. -/
instance additive_spacesEtaleModelPointTensor :
    (spacesEtaleModelPointTensor B S hS ψ).Additive :=
  haveI := (spacesEtaleModelPointTensorAdjunction B S hS ψ).isLeftAdjoint
  haveI : PreservesBinaryBiproducts (spacesEtaleModelPointTensor B S hS ψ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- `T_ψ` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_spacesEtaleModelPointTensor :
    PreservesFiniteColimits (spacesEtaleModelPointTensor B S hS ψ) :=
  haveI := (spacesEtaleModelPointTensorAdjunction B S hS ψ).isLeftAdjoint
  inferInstance

/-- **`T_ψ(A) ≅ 𝒪_X`**: the module `A` corresponds to the unit of the point, and the inverse image
of the unit along `X ⟶ (pt, A)` is the unit, the functor of sites picking out a terminal object
being final. -/
def spacesEtaleModelPointTensorObjSelfIso :
    (spacesEtaleModelPointTensor B S hS ψ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS X).O) :=
  haveI : IsFiltered (pointRingedTopos (CommRingCat.of A)).C :=
    inferInstanceAs (IsFiltered (Discrete PUnit))
  haveI : (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).u.Final :=
    Functor.final_const_of_isTerminal (isTerminal_spacesEtaleModelTerminal B S hS X)
  have hiso : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).fSharpRing) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _
  (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).pullbackTopos.mapIso
      ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).inverse.mapIso
          (Iso.refl ((pointModuleCatEquiv (R := A)).inverse.obj (ModuleCat.of A A)) :
            _ ≅ (Stacks.PointRingedSite.ev (CommRingCat.of A)).obj (SheafOfModules.unit _)) ≪≫
        (Stacks.PointRingedSite.constModuleEvIso (CommRingCat.of A)
          (SheafOfModules.unit _)).symm) ≪≫
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit
      (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ).fSharpRing) hiso

/-- **`T_ψ(C)` is perfect** for a bounded complex `C` of finite projective `A`-modules: the complex
is strictly perfect, `T_ψ` being additive, right exact and carrying `A` to `𝒪_X`. -/
theorem isPerfect_Q_spacesEtaleModelPointTensor (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (hb : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite A (C.X i)) (hproj : ∀ i : ℤ, Module.Projective A (C.X i)) :
    (spacesEtaleModelRingedSite B S hS X).IsPerfect (DerivedCategory.Q.obj
      (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
  RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect (spacesEtaleModelRingedSite B S hS X) _
    (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
      (spacesEtaleModelPointTensor B S hS ψ) (spacesEtaleModelPointTensorObjSelfIso B S hS ψ)
      hb hfin hproj)

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {A' : Type u} [CommRing A']
  (ψ' : A' →+* (SpacesEtale.structurePresheaf B S hS X').obj (op (SpacesEtale.idObj B S hS X')))
  (α : A →+* A') (hψ : ∀ a, globalFunctionsMap B S hS g (ψ a) = ψ' (α a))

include hψ in
/-- **`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)`** for a bounded complex `C` of finite projective
`A`-modules: the derived pullback of the bounded complex of flat modules `T_ψ(C)` is computed
termwise, and termwise `g^* T_ψ ≅ T_{ψ'} ∘ (A' ⊗_A -)`. -/
def derivedPullbackPointTensorIso (C : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    (hb : C.IsStrictlyLE b) (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite A (C.X i)) (hproj : ∀ i : ℤ, Module.Projective A (C.X i)) :
    (derivedPullback (spacesEtaleModelHom B S hS g)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) ≅
      DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS ψ').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) :=
  letI : (ModuleCat.extendScalars.{u, u, u} α).Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj α)
  derivedPullbackObjIsoOfFiniteProjective (spacesEtaleModelHom B S hS g)
      (isMorphismOfSites_spacesEtaleModelHom B S hS g) (spacesEtaleModelPointTensor B S hS ψ)
      (spacesEtaleModelPointTensorObjSelfIso B S hS ψ) C b hb hbd hfin hproj ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (F := spacesEtaleModelPointTensor B S hS ψ)
        (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
        (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
        (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ) (ComplexShape.up ℤ)).app C)

end AlgebraicGeometry.Space

end
