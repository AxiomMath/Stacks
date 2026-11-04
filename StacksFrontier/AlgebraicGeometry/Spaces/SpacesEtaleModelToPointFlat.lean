module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointPullback
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi

/-!
# Flat `X ⟶ Spec(R)`: the inverse image to `(pt, R)` is exact, and `Lf^*(M[0]) = (𝒪_X ⊗_R M)[0]`

Let `f : X ⟶ T` be a flat morphism from an algebraic space to an affine object of the big fppf
site, `R = Γ(T, 𝒪_T)`, and read `f` as the morphism of ringed topoi
`AlgebraicGeometry.Space.spacesEtaleModelToBaseRing` from the spaces-étale model of `X` to the
punctual ringed topos `(pt, R)`.  Its inverse image is `M ↦ 𝒪_X ⊗_R M`
(`AlgebraicGeometry.Space.pullbackToBaseRingIso`), which carries injections to monomorphisms when
`f` is flat (`AlgebraicGeometry.Space.mono_baseRingTensorModule_map`); being a left adjoint it is
right exact, so it is exact.  Hence the derived pullback `Lf^*` exists and sends `M[0]` to
`(𝒪_X ⊗_R M)[0]`.  This is the input `Lf^*K = 𝒪_X ⊗_R K` of the projection formula of
Stacks 08IN, at `K = M[0]`, as the proof of Stacks 0D3F uses it.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteLimits_pullbackTopos_toBaseRing`: the inverse image is
  left exact for flat `f`.
* `AlgebraicGeometry.Space.hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing`: the derived
  pullback exists.
* `AlgebraicGeometry.Space.derivedPullbackToBaseRingSingleIso`: `Lf^*(M[0]) ≅ (𝒪_X ⊗_R M)[0]`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}

/-- **For flat `f : X ⟶ T` over an affine `T`, the inverse image along `X ⟶ (pt, Γ(T, 𝒪_T))` is
exact.**  It is right exact as a left adjoint; it is `M ↦ 𝒪_X ⊗_R M`
(`AlgebraicGeometry.Space.pullbackToBaseRingIso`), which carries injections to monomorphisms for
flat `f` (`AlgebraicGeometry.Space.mono_baseRingTensorModule_map`). -/
theorem preservesFiniteLimits_pullbackTopos_toBaseRing (f : X ⟶ schemeSpace T)
    (hflat : IsFlat B S hS f.hom) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    PreservesFiniteLimits
      (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos := by
  let e := (Stacks.PointRingedSite.modulesEquiv (CommRingCat.of (baseRing B S hS T))).trans
    (pointModuleCatEquiv (R := baseRing B S hS T))
  let G₀ := e.inverse ⋙ (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos
  have hpb : PreservesColimitsOfSize.{0, 0} _ := (spacesEtaleModelToBaseRing B S hS X
      (baseRingHomOfMap f)).pullbackPushforwardAdjunctionTopos.leftAdjoint_preservesColimits
  have hei : PreservesColimitsOfSize.{0, 0} _ := e.symm.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits G₀ :=
    @comp_preservesFiniteColimits _ _ _ _ _ _ _ _
      (@PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _ hei)
      (@PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _ hpb)
  have : G₀.Additive := by
    have : PreservesBinaryBiproducts G₀ :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : PreservesFiniteLimits G₀ := by
    rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
    intro Sc hSc
    refine ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1 inferInstance
      Sc hSc).1, ?_⟩
    have : Mono ((spacesEtaleModelModulesEquiv B S hS X).functor.map (G₀.map Sc.f)) :=
      (MorphismProperty.monomorphisms.iff _).1
        (((MorphismProperty.monomorphisms _).arrow_iso_iff
          (Arrow.isoOfNatIso (pullbackToBaseRingIso B S hS X (baseRingHomOfMap f)) Sc.f)).2
          ((MorphismProperty.monomorphisms.iff _).2 (mono_baseRingTensorModule_map f hflat hT Sc.f
            ((ModuleCat.mono_iff_injective Sc.f).1 hSc.mono_f))))
    exact (spacesEtaleModelModulesEquiv B S hS X).functor.mono_of_mono_map this
  have hef : PreservesLimitsOfSize.{0, 0} _ := e.symm.toAdjunction.rightAdjoint_preservesLimits
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    ((Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.unitIso _ :
      _ ≅ e.functor ⋙ G₀).symm
    (@comp_preservesFiniteLimits _ _ _ _ _ _ _ _
      (@PreservesLimitsOfSize.preservesFiniteLimits _ _ _ _ _ hef) this)

/-- The inverse image along `X ⟶ (pt, R)` is right exact, being a left adjoint. -/
theorem preservesFiniteColimits_pullbackTopos_toBaseRing {R : Type u} [CommRing R]
    (φ : R →+* modelGlobalFunctions B S hS X) :
    PreservesFiniteColimits (spacesEtaleModelToBaseRing B S hS X φ).pullbackTopos :=
  @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
    (spacesEtaleModelToBaseRing B S hS X
      φ).pullbackPushforwardAdjunctionTopos.leftAdjoint_preservesColimits

/-- For flat `f : X ⟶ T` over an affine `T`, the derived pullback along `X ⟶ (pt, Γ(T, 𝒪_T))`
exists, the inverse image being exact. -/
theorem hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing
    [HasDerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleModelRingedTopos B S hS X).O))]
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    (pullbackOnHomotopy
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).O)) (.up ℤ)) :=
  have := preservesFiniteLimits_pullbackTopos_toBaseRing f hflat hT
  have := preservesFiniteColimits_pullbackTopos_toBaseRing (B := B) (S := S) (hS := hS) (X := X)
    (baseRingHomOfMap f)
  pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact.{u}
    (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))

attribute [local instance] HasDerivedCategory.standard in
/-- **For flat `f : X ⟶ T` over an affine `T`, `Lf^*(M[0]) = (𝒪_X ⊗_R M)[0]`** for the morphism
`X ⟶ (pt, Γ(T, 𝒪_T))`: the derived pullback along an exact inverse image is the inverse image
placed in degree zero, and the inverse image is `M ↦ 𝒪_X ⊗_R M`. -/
def derivedPullbackToBaseRingSingleIso (f : X ⟶ schemeSpace T)
    (hflat : IsFlat B S hS f.hom) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (M : ModuleCat.{u} (baseRing B S hS T)) :
    letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
    (derivedPullback (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of (baseRing B S hS T))).trans
            (pointModuleCatEquiv (R := baseRing B S hS T))).inverse.obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((spacesEtaleModelModulesEquiv B S hS X).inverse.obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj M)) :=
  letI := hasLeftDerivedFunctor_pullbackOnHomotopy_toBaseRing f hflat hT
  letI := preservesFiniteLimits_pullbackTopos_toBaseRing f hflat hT
  letI := preservesFiniteColimits_pullbackTopos_toBaseRing (B := B) (S := S) (hS := hS) (X := X)
    (baseRingHomOfMap f)
  Stacks.Cohomology.CohomologicalDescent.derivedPullbackSingleFunctorObjIso
      (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))
      (((Stacks.PointRingedSite.modulesEquiv (CommRingCat.of (baseRing B S hS T))).trans
        (pointModuleCatEquiv (R := baseRing B S hS T))).inverse.obj M) ≪≫
    (DerivedCategory.singleFunctor (spacesEtaleModelRingedTopos B S hS X).Modules 0).mapIso
      ((spacesEtaleModelModulesEquiv B S hS X).unitIso.app _ ≪≫
        (spacesEtaleModelModulesEquiv B S hS X).inverse.mapIso
          ((pullbackToBaseRingIso B S hS X (baseRingHomOfMap f)).app M))

end AlgebraicGeometry.Space

end
