module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.Homology.DerivedCategory.StandardModuleCatModel

/-!
# Derived sections over an affine étale chart, read over an affine base

Let `X` be an algebraic space over an affine object `T` of the big fppf site (ring `R`), with
structure morphism `h : X ⟶ h_T`, and let `U` be an affine étale chart of `X`, with chart morphism
`u : h_U ⟶ X` and `g : U ⟶ T` the composite on charts, so that `u ≫ h = h_g`. Then the derived
sections `RΓ(U, K)` over the chart, read as complexes of `R`-modules, are the derived sections over
`T` of the derived direct image along `u ≫ h` of the derived pullback `Lu^*K`:

`RΓ(U, K)|_R ≅ RΓ_R(h_U, Lu^*K)`, naturally in `K ∈ D(𝒪_X)`.

This is the comparison between the chart form of derived sections (`chartDerivedSections`, the
form of [Stacks, Tag 0CSX] (3)) and the form `RΓ_R(V, -)` of the derived sections over a space `V`
over `T` in which the base change maps of [Stacks, Tag 0CX8] are stated.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineDerivedSectionsRestrictIso`:
  `RΓ(h_U, -)|_R ≅ RΓ_R(h_U, -)` along `h_g`.
* `AlgebraicGeometry.Space.chartDerivedSectionsPushforwardIso`: `RΓ(U, -)|_R ≅ RΓ_R(h_U, Lu^* -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasRightDerivedFunctor_chartSections

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Represented

variable {V T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (g : V ⟶ T)
    (f : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (hf : f = representedSpaceMap B S hS g)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
include hf in
/-- If `f = h_g`, then `𝟙 ≫ f = 𝟙 ≫ h_g`. -/
theorem representedAffineDerivedSectionsRestrict_w :
    𝟙 _ ≫ f = 𝟙 _ ≫ representedSpaceMap B S hS g := by
  rw [Category.id_comp, Category.id_comp, hf]

/-- `affineBaseDerivedSectionsPushforwardIso` at the identity of `h_V`. -/
def representedAffineDerivedSectionsRestrictIsoAux :=
  affineBaseDerivedSectionsPushforwardIso B S hS g f (𝟙 _) (𝟙 _)
    (representedAffineDerivedSectionsRestrict_w g f hf)

/-- **`RΓ(h_V, -)|_R ≅ RΓ_R(h_V, -)`** for a morphism `g : V ⟶ T` of affine objects and a
morphism `f : h_V ⟶ h_T` equal to `h_g`: the derived sections over `V`, restricted along the ring
map of `g`, are the derived sections over `T` of the derived direct image along `f`
(`affineBaseDerivedSectionsPushforwardIso` at the identity of `h_V`). -/
def representedAffineDerivedSectionsRestrictIso :
    representedAffineDerivedSections B S hS V ⋙
        StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g).hom ≅
      derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS T :=
  Functor.isoWhiskerRight ((Functor.leftUnitor (representedAffineDerivedSections B S hS V)).symm ≪≫
      Functor.isoWhiskerRight (derivedModulePushforwardIdIso B S hS
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS)).symm
        (representedAffineDerivedSections B S hS V))
      (ModuleCat.restrictScalars
        (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory ≪≫
    (representedAffineDerivedSectionsRestrictIsoAux g f hf).symm ≪≫
    Functor.isoWhiskerRight (derivedModulePushforwardIdIso B S hS
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
      (derivedModulePushforward B S hS f ⋙ representedAffineDerivedSections B S hS T) ≪≫
    Functor.leftUnitor _

end Represented

variable (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U))]
  {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (h : X ⟶ ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
  (g : (SmallEtale.toOver B S hS X.1).obj U ⟶ T)
  (w : representedChartToSpace X U ≫ h = representedSpaceMap B S hS g)

/-- **`RΓ(U, -)|_R ≅ RΓ_R(h_U, Lu^* -)`**: the derived sections over an affine étale chart `U` of a
space `X` over an affine `T`, restricted along the ring map of `g : U ⟶ T`, are the derived
sections over `T` of the derived direct image along `u ≫ h` of the derived pullback along the chart
morphism `u`. -/
def chartDerivedSectionsPushforwardIso :
    Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⋙
      StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g).hom ≅
    smallEtaleDerivedModulePullback B S hS (representedChartToSpace X U) ⋙
      derivedModulePushforward B S hS (representedChartToSpace X U ≫ h) ⋙
        representedAffineDerivedSections B S hS T :=
  Functor.isoWhiskerRight (asIso (chartDerivedSectionsComparison X U)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (smallEtaleDerivedModulePullbackIsoEtale B S hS
      (representedChartToSpace X U) (isEtale_representedChartToSpace X U)).symm _ ≪≫
    Functor.isoWhiskerLeft _ (representedAffineDerivedSectionsRestrictIso g _ w)

end AlgebraicGeometry.Space

end
