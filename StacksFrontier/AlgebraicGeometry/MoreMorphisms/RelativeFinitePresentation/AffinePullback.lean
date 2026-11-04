module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Relative finite presentation of an affine pullback

Let `B → A` be a ring map and let `G` be a quasi-coherent module on `Spec B` presented as the
sheaf associated to a `B`-module `M`. Pulling `G` back along `Spec (B → A)` gives the sheaf
associated to `A ⊗_B M`, so its global sections are finitely presented relative to a base ring
`R` as soon as `A ⊗_B M` is.

Both the base-change statement (Stacks 09TA) and the pullback statement (Stacks 09TB) for
relative finite presentation reduce to this one affine computation, which is why it is isolated
here.

## Main results

* `AlgebraicGeometry.finitePresentationRel_pullback_specMap_of_baseChange`: relative finite
  presentation of `A ⊗_B M` gives relative finite presentation of the global sections of the
  pullback of `G` along `Spec (B → A)`.

## Implementation notes

The identification of the pullback with the sheaf associated to the extension of scalars is
`AlgebraicGeometry.pullbackTildeIso` (Stacks 01I9), and the comparison between the ambient
tensor product `A ⊗_B M` and the functorial extension of scalars
`ModuleCat.extendScalars` is `TensorProduct.AlgebraTensorModule.congr` against the identity of
`A`, read as a restriction of scalars of `A` along `B → A`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Relative finite presentation of the global sections of the pullback of a quasi-coherent
module along `Spec` of a ring map, given relative finite presentation of the base change of a
module presenting it. -/
theorem finitePresentationRel_pullback_specMap_of_baseChange
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R A] [Algebra B A]
    (G : (Spec (.of B)).Modules) [G.IsQuasicoherent]
    (M : ModuleCat B) (eG : (tilde.functor (R := .of B)).obj M ≅ G)
    (hbase : Module.FinitePresentationRel R A (TensorProduct B A M)) :
    Module.FinitePresentationRel R A
      ((moduleSpecΓFunctor (R := .of A)).obj
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap B A)))).obj G)) := by
  let T : ModuleCat B := (ModuleCat.restrictScalars (algebraMap B A)).obj (ModuleCat.of A A)
  let : IsScalarTower B A T := IsScalarTower.of_algebraMap_smul (by intro b x; rfl)
  let eT : T ≃ₗ[A] A :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let eTensor : TensorProduct B A M ≃ₗ[A]
      (ModuleCat.extendScalars (algebraMap B A)).obj M :=
    TensorProduct.AlgebraTensorModule.congr eT (LinearEquiv.refl B M)
  have hbase' : Module.FinitePresentationRel R A
      ((ModuleCat.extendScalars (algebraMap B A)).obj M) :=
    Module.FinitePresentationRel.of_linearEquiv eTensor hbase
  have : IsIso G.fromTildeΓ := inferInstance
  let eAffine : (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap B A)))).obj
        ((tilde.functor (R := .of B)).obj M) ≅
      (tilde.functor (R := .of A)).obj ((ModuleCat.extendScalars (algebraMap B A)).obj M) :=
    (pullbackTildeIso (.of B) (.of A) (CommRingCat.ofHom (algebraMap B A))).app M
  let e₀ : (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap B A)))).obj G ≅
      (tilde.functor (R := .of A)).obj ((ModuleCat.extendScalars (algebraMap B A)).obj M) :=
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap B A)))).mapIso
      eG.symm) ≪≫ eAffine
  let e₁ : (moduleSpecΓFunctor (R := .of A)).obj
      ((Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap B A)))).obj G) ≅
      (ModuleCat.extendScalars (algebraMap B A)).obj M :=
    (moduleSpecΓFunctor (R := .of A)).mapIso e₀ ≪≫
      ((tilde.toTildeΓNatIso (R := .of A)).app
        ((ModuleCat.extendScalars (algebraMap B A)).obj M)).symm
  exact Module.FinitePresentationRel.of_linearEquiv e₁.symm.toLinearEquiv hbase'

end AlgebraicGeometry
