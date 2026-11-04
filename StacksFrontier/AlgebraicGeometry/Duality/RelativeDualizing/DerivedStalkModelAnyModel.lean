module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DimensionFunctionScheme
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat

/-!
# The derived stalk of a complex modelled over an affine open

The derived stalk at `x` of a complex `K` of `𝒪_X`-modules is the extension of scalars to
`𝒪_{X,x}` of any model of `K` over an affine open neighbourhood of `x`.

## Main results

* `Stacks.Duality.nonempty_derivedStalkOfComplex_iso_extendScalars_anyModel`: if `K|_U ≅ ω~` for
  an affine open `U ∋ x`, then the derived stalk of `K` at `x` is `ω ⊗ 𝒪_{X,x}`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w w'

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Duality

section OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)

end OpenImmersion

section RingEquiv

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

end RingEquiv

section TildeStalk

variable (R : CommRingCat.{u}) (y : Spec R)

end TildeStalk

section AffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)

end AffineOpen

/-! ### The derived stalk as an extension of scalars -/

section DerivedStalk

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

open Stacks.DerivedCategoryComparisons in
/-- The derived stalk of `K` at `x` is the extension to `𝒪_{X,x}` of any model of `K` over an
affine open neighbourhood of `x`. Let `E` represent `K` and let `ω` over `Γ(X, U)` satisfy
`K|_U ≅ ω~` in `D(𝒪_U)`. Then the degreewise stalk of `E` at `x` is isomorphic, in
`D(𝒪_{X,x})`, to the degreewise extension of scalars of `ω` along
`Stacks.Duality.affineGermRingHom`, which presents `𝒪_{X,x}` as the localization of `Γ(X, U)`
at the prime of `x`. -/
theorem nonempty_derivedStalkOfComplex_iso_extendScalars_anyModel {K : DerivedCategory X.Modules}
    (E : CochainComplex X.Modules ℤ) (hE : Nonempty (DerivedCategory.Q.obj E ≅ K))
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    [HasDerivedCategory.{w'} U.toScheme.Modules]
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hω : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)) :
    letI := (affineGermRingHom hU x hx).toAlgebra
    letI : PreservesFiniteLimits
        (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx)) :=
      haveI := isLocalization_affineGermRingHom hU x hx
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))
    Nonempty (derivedStalkOfComplex x E ≅
      (ModuleCat.extendScalars.{u, u, u}
        (affineGermRingHom hU x hx)).mapDerivedCategory.obj ω) := by
  let := (affineGermRingHom hU x hx).toAlgebra
  have := isLocalization_affineGermRingHom hU x hx
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl))
  let xU : U.toScheme := ⟨x, hx⟩
  let G := modulesStalkFunctor xU ⋙ ModuleCat.restrictScalars.{u} (affineStalkMap x hx).hom
  have hG := mapDerivedCategoryCompIso (Scheme.Modules.restrictFunctor U.ι) G
  have hT := mapDerivedCategoryCompIso
    (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) G
  have hN := mapDerivedCategoryIsoOfNatIso
    ((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙ G)
    (ModuleCat.extendScalars.{u, u, u} (affineGermRingHom hU x hx))
    (affineStalkNatIso hU x hx)
  have hS := mapDerivedCategoryIsoOfNatIso
    (Scheme.Modules.restrictFunctor U.ι ⋙ G)
    (modulesStalkFunctor x) (affineRestrictStalkNatIso x hx)
  exact ⟨((modulesStalkFunctor x).mapDerivedCategoryFactors.app E).symm ≪≫
    (modulesStalkFunctor x).mapDerivedCategory.mapIso hE.some ≪≫
    hS.symm.app K ≪≫ hG.app K ≪≫
    G.mapDerivedCategory.mapIso hω.some ≪≫
    (hT.app ω).symm ≪≫ hN.app ω⟩

end DerivedStalk

end Stacks.Duality
