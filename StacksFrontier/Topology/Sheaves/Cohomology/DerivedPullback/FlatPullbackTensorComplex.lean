module

public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# Tensoring with a complex flat over the base, after pulling back

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `𝒢` be a bounded complex of
`𝒪_X`-modules each of whose terms is flat over `Y`.  For a complex `M` of `𝒪_Y`-modules write

`Ψ(M) = Tot(𝒢 ⊗_{𝒪_X} f^*M)`,

the total complex of the double complex `(p, q) ↦ 𝒢^p ⊗_{𝒪_X} f^*M^q`, with `f^*` the ordinary
pullback applied termwise.  This file proves that `Ψ` carries quasi-isomorphisms to
quasi-isomorphisms, although neither `f^*` nor `𝒢 ⊗_{𝒪_X} -` does so on its own: in each
bidegree `M ↦ 𝒢^p ⊗ f^*M` is exact because `𝒢^p` is flat over `Y` ([Stacks, Tag 0GMU]), and a
bounded complex built from exact pieces is K-flat by the dévissage of [Stacks, Tag 06YQ].

## Main definitions

* `Stacks.Cohomology.FlatPullbackTensor.bifunctor`: `(B, A) ↦ f^*B ⊗_{𝒪_X} A`.
* `Stacks.Cohomology.FlatPullbackTensor.complexFunctor`: `M ↦ Tot(f^*M ⊗_{𝒪_X} 𝒢)` on cochain
  complexes.

## Main results

* `Stacks.Cohomology.FlatPullbackTensor.exact_bifunctor_flip_obj`: `B ↦ f^*B ⊗ A` is exact when
  `A` is flat over `Y`.
* `Stacks.Cohomology.FlatPullbackTensor.kFlat`: a bounded complex with terms flat over `Y` is
  K-flat in the second variable of the bifunctor.
* `Stacks.Cohomology.FlatPullbackTensor.quasiIso_complexFunctor_map`: `Ψ` preserves
  quasi-isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.FlatPullbackTensor

universe u

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The bifunctor `(B, A) ↦ f^*B ⊗_{𝒪_X} A`** from `𝒪_Y`-modules and `𝒪_X`-modules to
`𝒪_X`-modules.  The `𝒪_Y`-module is the *first* variable, so that the shift of the moving complex
below is the sign-free one of `CochainComplex.mapBifunctorShift₁Iso`. -/
def bifunctor :
    SheafOfModules.{u} (structureSheafRing Y) ⥤ Modules X ⥤ Modules X :=
  modulePullback f ⋙ Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf

/-- The bifunctor `bifunctor f` is additive in its first variable. -/
instance bifunctor_additive : (bifunctor f).Additive :=
  @Functor.instAdditiveComp _ _ _ _ _ _ (modulePullback f) (modulePullback_additive f) _ _ _
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_additive X)

/-- For each `𝒪_Y`-module `B`, the functor `A ↦ f^*B ⊗_{𝒪_X} A` is additive. -/
instance bifunctor_obj_additive (B : SheafOfModules.{u} (structureSheafRing Y)) :
    ((bifunctor f).obj B).Additive :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive X _

/-- The total complex of `bifunctor f` applied to two cochain complexes indexed by `ℤ` exists. -/
instance hasMapBifunctor_bifunctor
    (K₁ : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (K₂ : CochainComplex (Modules X) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂ (bifunctor f) (ComplexShape.up ℤ) :=
  inferInstance

/-- `(bifunctor f).flip.obj A` is the functor `B ↦ f^*B ⊗ A` of [Stacks, Tag 0GMU]. -/
theorem bifunctor_flip_obj (A : Modules X) :
    (bifunctor f).flip.obj A = Stacks.SheafOfModules.pullbackTensorFunctor f A :=
  rfl

/-- **`B ↦ f^*B ⊗_{𝒪_X} A` is exact when `A` is flat over `Y`** ([Stacks, Tag 0GMU]). -/
theorem exact_bifunctor_flip_obj (A : Modules X) (hA : AlgebraicGeometry.IsFlatOver f A) :
    exactFunctor _ _ ((bifunctor f).flip.obj A) :=
  Stacks.SheafOfModules.pullbackTensorFunctor_exact f A hA

/-- An exact functor carries acyclic complexes to acyclic complexes. -/
alias acyclic_mapHomologicalComplex_of_exactFunctor :=
  Stacks.SheafOfModules.acyclic_mapHomologicalComplex_of_exactFunctor

variable (G : CochainComplex (Modules X) ℤ)

/-- **A bounded complex whose terms are flat over `Y` is K-flat for `(B, A) ↦ f^*B ⊗ A` in its
second variable**: `Tot(f^*P ⊗ 𝒢)` is acyclic for every acyclic complex `P` of `𝒪_Y`-modules.
Each term of `𝒢`, placed in its own degree, is K-flat because `f^*(-) ⊗ 𝒢^q` is exact
([Stacks, Tag 0GMU]); the dévissage of [Stacks, Tag 06YQ] assembles the bounded complex. -/
theorem kFlat (hflat : ∀ q : ℤ, AlgebraicGeometry.IsFlatOver f (G.X q)) (a b : ℤ)
    [G.IsStrictlyLE b] [G.IsStrictlyGE a] :
    CochainComplex.KFlatBifunctor.KFlat (bifunctor f) G :=
  CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_isStrictlyGE (bifunctor f) G b a
    (fun q => CochainComplex.KFlatBifunctor.kFlat_single_of_exact (bifunctor f) (G.X q) q
      (fun P hP => acyclic_mapHomologicalComplex_of_exactFunctor _
        (exact_bifunctor_flip_obj f (G.X q) (hflat q)) P hP))

/-- **The functor `M ↦ Tot(f^*M ⊗_{𝒪_X} 𝒢)`** on cochain complexes of `𝒪_Y`-modules. -/
abbrev complexFunctor :
    CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ ⥤ CochainComplex (Modules X) ℤ :=
  ((bifunctor f).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).flip.obj G

/-- **`M ↦ Tot(f^*M ⊗_{𝒪_X} 𝒢)` preserves quasi-isomorphisms** when `𝒢` is bounded with terms
flat over `Y`. -/
theorem quasiIso_complexFunctor_map (hflat : ∀ q : ℤ, AlgebraicGeometry.IsFlatOver f (G.X q))
    (a b : ℤ) [G.IsStrictlyLE b] [G.IsStrictlyGE a]
    {M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (φ : M ⟶ M')
    (hφ : QuasiIso φ) : QuasiIso ((complexFunctor f G).map φ) :=
  CochainComplex.KFlatBifunctor.quasiIso_of_kFlat (bifunctor f) G (kFlat f G hflat a b) φ hφ

end Stacks.Cohomology.FlatPullbackTensor

end
