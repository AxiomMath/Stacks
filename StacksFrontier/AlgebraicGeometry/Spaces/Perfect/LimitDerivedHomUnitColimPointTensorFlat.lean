module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTensorPerfect
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness
public import StacksFrontier.CategoryTheory.Sites.Modules.PointRingedSiteTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation

/-!
# Flatness of `𝒪_X ⊗_A M`, and the derived pullback of `𝒪_X ⊗_A C` for a flat complex `C`

Let `X` be an algebraic space and `ψ : A ⟶ Γ(X, 𝒪_X)` a ring map, and let
`T_ψ : M ↦ 𝒪_X ⊗_A M` be the inverse image along `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, A)`
(`AlgebraicGeometry.Space.spacesEtaleModelPointTensor`).

`T_ψ` **carries a flat `A`-module to a flat sheaf of modules**: a module on the punctual ringed
topos whose sections are flat is flat (Stacks 05ND, `Stacks.PointRingedSite.isFlat_of_flat_ev`)
and the inverse image along a morphism of ringed topoi preserves flatness (Stacks 05VD,
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat`).

Consequently, for a complex `C` of flat `A`-modules bounded above, `T_ψ(C)` is a complex of flat
sheaves of modules bounded above, and on such a complex the derived pullback is computed
termwise (Stacks 06YQ and 06YY), by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackObjIsoOfFlat`.  This gives

`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)`

with no finiteness and no projectivity hypothesis on the terms of `C`:
`AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfFlat` is
`AlgebraicGeometry.Space.derivedPullbackPointTensorIso` with its hypotheses `hbd` (finite
support), `hfin` (finite terms) and `hproj` (projective terms) replaced by the single hypothesis
that the terms of `C` are flat — which every term of a bounded above complex of finite projective
modules is, so the earlier statement is a special case.

## Main results

* `AlgebraicGeometry.Space.isFlat_spacesEtaleModelPointTensor_obj`: `T_ψ` carries a flat
  `A`-module to a flat sheaf of modules.
* `AlgebraicGeometry.Space.isFlat_spacesEtaleModelPointTensor_mapHomologicalComplex_X`: the
  terms of `T_ψ(C)` are flat when the terms of `C` are.
* `AlgebraicGeometry.Space.isStrictlyLE_spacesEtaleModelPointTensor_mapHomologicalComplex`:
  `T_ψ(C)` is bounded above when `C` is.
* `AlgebraicGeometry.Space.derivedPullbackPointTensorIsoOfFlat`:
  `Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` for a bounded above complex `C` of flat `A`-modules.

## References

* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
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

/-- **`T_ψ` carries a flat `A`-module to a flat sheaf of modules.**  The `A`-module `M` is the
sections over the point of a module on the punctual ringed topos `(pt, A)`, which is flat by
Stacks 05ND, and `T_ψ` is the inverse image along `X ⟶ (pt, A)`, which preserves flatness by
Stacks 05VD. -/
theorem isFlat_spacesEtaleModelPointTensor_obj (M : ModuleCat.{u} A) (hM : Module.Flat A M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (spacesEtaleModelRingedTopos B S hS X).O)
      ((spacesEtaleModelPointTensor B S hS ψ).obj M) :=
  have hpt : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (pointRingedTopos (CommRingCat.of A)).O)
      ((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of A)).inverse.obj
        ((pointModuleCatEquiv (R := A)).inverse.obj M)) :=
    Stacks.PointRingedSite.isFlat_of_flat_ev (A := A) _ (by exact hM)
  AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat.{u}
    (spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ)
    (isMorphismOfSites_spacesEtaleModelToPoint B S hS (R := CommRingCat.of A) ψ) _ hpt

/-- **The terms of `T_ψ(C)` are flat when the terms of `C` are.**  The term of `T_ψ(C)` in
degree `i` is `T_ψ(C^i)` on the nose, so this is
`AlgebraicGeometry.Space.isFlat_spacesEtaleModelPointTensor_obj` once per degree. -/
theorem isFlat_spacesEtaleModelPointTensor_mapHomologicalComplex_X
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (hflat : ∀ i : ℤ, Module.Flat A (C.X i)) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (spacesEtaleModelRingedTopos B S hS X).O)
      ((((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).X i) :=
  isFlat_spacesEtaleModelPointTensor_obj B S hS ψ (C.X i) (hflat i)

/-- **`T_ψ(C)` is bounded above when `C` is**, `T_ψ` being additive and so carrying a zero
module to a zero module. -/
theorem isStrictlyLE_spacesEtaleModelPointTensor_mapHomologicalComplex
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ) (hb : C.IsStrictlyLE b) :
    CochainComplex.IsStrictlyLE (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (spacesEtaleModelPointTensor B S hS ψ)
    (C.isZero_of_isStrictlyLE b i hi)

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) {A' : Type u} [CommRing A']
  (ψ' : A' →+* (SpacesEtale.structurePresheaf B S hS X').obj (op (SpacesEtale.idObj B S hS X')))
  (α : A →+* A') (hψ : ∀ a, globalFunctionsMap B S hS g (ψ a) = ψ' (α a))

include hψ in
/-- **`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)`** for a bounded above complex `C` of *flat* `A`-modules:
`T_ψ(C)` is then a bounded above complex of flat sheaves of modules, so the derived pullback is
computed termwise (Stacks 06YQ and 06YY), and termwise `g^* T_ψ ≅ T_{ψ'} ∘ (A' ⊗_A -)`.

This is `AlgebraicGeometry.Space.derivedPullbackPointTensorIso` with its hypotheses `hbd`,
`hfin` and `hproj` on the terms of `C` — finite support, finite and projective — replaced by
flatness of the terms, which those three imply. -/
def derivedPullbackPointTensorIsoOfFlat (C : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    (hb : C.IsStrictlyLE b) (hflat : ∀ i : ℤ, Module.Flat A (C.X i)) :
    (derivedPullback (spacesEtaleModelHom B S hS g)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) ≅
      DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS ψ').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) :=
  letI : (ModuleCat.extendScalars.{u, u, u} α).Additive :=
    Adjunction.left_adjoint_additive (ModuleCat.extendRestrictScalarsAdj α)
  derivedPullbackObjIsoOfFlat (spacesEtaleModelHom B S hS g)
      (isMorphismOfSites_spacesEtaleModelHom B S hS g) _ b
      (isStrictlyLE_spacesEtaleModelPointTensor_mapHomologicalComplex B S hS ψ C b hb)
      (isFlat_spacesEtaleModelPointTensor_mapHomologicalComplex_X B S hS ψ C hflat) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (F := spacesEtaleModelPointTensor B S hS ψ)
        (G := (spacesEtaleModelHom B S hS g).pullbackTopos)
        (H := ModuleCat.extendScalars.{u, u, u} α ⋙ spacesEtaleModelPointTensor B S hS ψ')
        (spacesEtaleModelToPointPullbackCompIso B S hS g ψ ψ' α hψ) (ComplexShape.up ℤ)).app C)

end AlgebraicGeometry.Space

end
