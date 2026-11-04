module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage

/-!
# The derived pullback along an étale ringed topos morphism is computed degreewise

For a morphism of schemes `g : X ⟶ Y` and a commutative ring `Λ`, pullback of sheaves of modules
along the morphism of constant ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` is exact, so the
canonical comparison `Lg^*(Q K) ⟶ Q(g^* K)` of [Stacks, Tag 06YY] is invertible at *every*
complex `K`, not only at K-flat ones.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleRingedDerivedPullbackComparison_app`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The derived pullback along the morphism of constant ringed topoi exists. -/
local instance :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy.{max (u + 1) r, max (u + 1) r,
      max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
        (etaleRingedToposHom.{u, r} Λ g)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget
        (Y := (etaleRingedSite.{u, r} Λ Y).ringedTopos)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy.{
    max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
    (etaleRingedToposHom.{u, r} Λ g)

/-- **The derived pullback along the morphism of constant ringed topoi of a morphism of schemes is
computed by degreewise pullback at every complex**: the comparison
`Lg^*(Q K) ⟶ Q(g^* K)` of [Stacks, Tag 06YY] is invertible for every complex `K` of sheaves of
`Λ̲`-modules, degreewise pullback being exact. -/
theorem isIso_etaleRingedDerivedPullbackComparison_app
    (K : HomotopyCategory (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ)) :
    IsIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison.{max (u + 1) r,
      max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
        (etaleRingedToposHom.{u, r} Λ g)).app K) := by
  have : (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory.IsLeftDerivedFunctor
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ)) _
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh
  have h := Functor.leftDerivedNatTrans_app (etaleRingedDerivedPullback.{u, r} Λ g)
    (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison.{max (u + 1) r,
      max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
        (etaleRingedToposHom.{u, r} Λ g))
    (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ))
    (𝟙 _) K
  have hiso : IsIso ((Functor.leftDerivedNatTrans (etaleRingedDerivedPullback.{u, r} Λ g)
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison.{max (u + 1) r,
        max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r, max (u + 1) r}
          (etaleRingedToposHom.{u, r} Λ g))
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ))
      (𝟙 _)).app (DerivedCategory.Qh.obj K)) :=
    inferInstanceAs (IsIso ((etaleRingedDerivedPullbackMapIso.{u, r} Λ g).hom.app _))
  rw [NatTrans.id_app, Category.comp_id] at h
  rw [← h]
  infer_instance

end Stacks.EtaleCohomology

end
