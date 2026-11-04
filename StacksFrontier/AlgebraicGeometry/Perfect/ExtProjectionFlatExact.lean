module

public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionFormula
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# `𝒢 ⊗ f^*(-)` on short exact sequences, for `𝒢` with terms flat over the base

Let `f : X ⟶ S` be a morphism of schemes and `𝒢` a complex of `𝒪_X`-modules whose terms are flat
over `S`.  The functor `ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ` of [Stacks, Tag 0A1F], from `𝒪_S`-modules to
complexes of `𝒪_X`-modules, carries short exact sequences to short exact sequences: in each
degree it is `ℱ ↦ 𝒢^p ⊗ f^*ℱ`, which is the exact functor `ℱ ↦ f^*ℱ ⊗ 𝒢^p` of
[Stacks, Tag 0GMU] composed with the symmetry of the tensor product.

## Main results

* `Stacks.Cohomology.ExtProjectionFlatExact.tensorModuleComplex_additive`: `M ↦ 𝒢 ⊗ M` is
  additive.
* `Stacks.Cohomology.ExtProjectionFlatExact.shortExact_map_pullbackTensor`: the short exactness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StrictlyPerfect

universe u

namespace Stacks.Cohomology.ExtProjectionFlatExact

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

open Stacks.Cohomology.ExtProjectionFormula (tensorModuleComplex)

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (G : CochainComplex
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)

/-- **`M ↦ 𝒢 ⊗_{𝒪_X} M` is additive.** -/
instance tensorModuleComplex_additive : (tensorModuleComplex X G).Additive where
  map_add {_ _ _ _} := HomologicalComplex.hom_ext _ _ (fun p =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.toRingedSpace.sheaf).obj (G.X p)).map_add)

/-- **`ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ` is additive.** -/
instance pullbackTensorModuleComplex_additive :
    (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ⋙
      tensorModuleComplex X G).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _ _ (RingedSpaceModuleAdjunction.modulePullback_additive _)
    _ _ _ _ (tensorModuleComplex_additive G)

/-- The degree-`p` term of `ℱ ↦ 𝒢 ⊗ f^*ℱ` is `ℱ ↦ f^*ℱ ⊗ 𝒢^p`, up to the symmetry of the tensor
product. -/
def evalIso (p : ℤ) :
    (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ⋙ tensorModuleComplex X G) ⋙
        HomologicalComplex.eval _ (ComplexShape.up ℤ) p ≅
      Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom (G.X p) :=
  Functor.isoWhiskerLeft (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom)
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.toRingedSpace.sheaf).app (G.X p))

/-- **`ℱ ↦ 𝒢 ⊗_{𝒪_X} f^*ℱ` carries short exact sequences of `𝒪_S`-modules to short exact
sequences of complexes** when every term of `𝒢` is flat over `S`. -/
theorem shortExact_map_pullbackTensor
    (hflat : ∀ q : ℤ, AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom (G.X q))
    (T : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hT : T.ShortExact) :
    (T.map (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ⋙
      tensorModuleComplex X G)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p => ?_
  have hex := Stacks.SheafOfModules.pullbackTensorFunctor_exact f.toLRSHom.toShHom (G.X p)
    (hflat p)
  have h' := (exactFunctor_iff _).1 hex
  have : PreservesFiniteLimits
      (Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom (G.X p)) := h'.1
  have : PreservesFiniteColimits
      (Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom (G.X p)) := h'.2
  have : (Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom
      (G.X p)).PreservesMonomorphisms := inferInstance
  have : (Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom
      (G.X p)).PreservesEpimorphisms := inferInstance
  have := hT.mono_f
  have := hT.epi_g
  have h₁ := hT.map (Stacks.SheafOfModules.pullbackTensorFunctor f.toLRSHom.toShHom (G.X p))
  exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso T (evalIso f G p)).symm h₁

end Stacks.Cohomology.ExtProjectionFlatExact

end
