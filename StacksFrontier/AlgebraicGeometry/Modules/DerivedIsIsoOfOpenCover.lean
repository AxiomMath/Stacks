module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.BlowupSubscheme
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# Invertibility in the derived category of a scheme is local

Let `Y` be a scheme and let `φ : K ⟶ L` be a morphism in `D(𝒪_Y)`. If `{V_i}` is an open cover
of `Y` and the restriction `φ|_{V_i}` — the derived pullback of `φ` along the inclusion of
`V_i` — is an isomorphism for every `i`, then `φ` is an isomorphism.

A morphism of the derived category is an isomorphism exactly when it induces isomorphisms on all
cohomology sheaves; restriction to an open is exact, so it commutes with taking cohomology
sheaves; and a morphism of sheaves of modules is an isomorphism as soon as its restrictions to
the members of an open cover are.

## Main definitions

* `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackHomologyIso` — for a morphism of
  ringed spaces with exact module pullback, `H^n(Lg^* K) ≅ g^* H^n(K)`, naturally in `K`.

## Main results

* `Stacks.Cohomology.DerivedOpenImmersion.isIso_of_isIso_derivedPullback_ι` — invertibility of a
  morphism of `D(𝒪_Y)` is local on `Y`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.DerivedOpenImmersion

/-- **Cohomology sheaves commute with an exact pullback, naturally**: for a morphism of ringed
spaces `g` whose module pullback is exact, `H^n ∘ Lg^* ≅ g^* ∘ H^n` as functors on `D(𝒪_Y)`. -/
def derivedPullbackHomologyIso {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)
    [PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback g)]
    [PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePullback g)] (n : ℤ) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n ⋙
        RingedSpaceModuleAdjunction.modulePullback g :=
  Functor.isoWhiskerRight (derivedPullbackIsoMapDerivedCategory g) _ ≪≫
    (RingedSpaceModuleAdjunction.modulePullback g).mapDerivedCategoryHomologyIso n

/-- **Invertibility of a morphism of `D(𝒪_Y)` is local on `Y`.** If the derived pullback of
`φ` to every member of an open cover of `Y` is an isomorphism, then `φ` is an isomorphism. -/
theorem isIso_of_isIso_derivedPullback_ι {Y : Scheme.{u}}
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))}
    (φ : K ⟶ L) {I : Type*} (V : I → Y.Opens) (hV : TopologicalSpace.IsOpenCover V)
    (h : ∀ i, IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (V i).ι.toLRSHom.toShHom).map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict
    ((DerivedCategory.homologyFunctor _ n).map φ) V hV fun i => ?_
  have hfl : AlgebraicGeometry.IsFlat (V i).ι.toLRSHom.toShHom := fun y =>
    AlgebraicGeometry.Flat.stalkMap (V i).ι y
  have _ : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (V i).ι.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _ hfl
  have _ : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback (V i).ι.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  have h0 := h i
  have h1 : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (V i).ι.toLRSHom.toShHom ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (V i).toScheme.toRingedSpace)) n).map φ) :=
    Functor.map_isIso (DerivedCategory.homologyFunctor _ n) _
  have h2 := (NatIso.isIso_map_iff (derivedPullbackHomologyIso (V i).ι.toLRSHom.toShHom n) φ).1 h1
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) _).2 h2

end Stacks.Cohomology.DerivedOpenImmersion

end
