module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.SupportedPushforwardReflect

/-!
# Direct image preserves vanishing of cohomology supported over an affine open

Let `p : P ⟶ Y` be a morphism of schemes and `U ⊆ P` an open subscheme with `j ≫ p` affine,
`j : U ⟶ P` the inclusion. If `E ∈ D(𝒪_P)` has quasi-coherent cohomology supported on a closed
subset `T ⊆ U`, then `H^i(E) = 0 ⟹ H^i(Rp_*E) = 0`. This is the converse of
`isZero_homology_of_isZero_homology_derivedPushforward_of_supported`, proved the same way:
`Rp_*E ≅ R(j ≫ p)_*(j^*E)` by [Stacks, Tag 08DF] and Leray, and direct image along an affine
morphism preserves vanishing of quasi-coherent cohomology ([Stacks, Tag 08D5]).

For the second projection of `X ×_S Y` with `S` affine, read over an affine open `U₀` of `X`,
this makes the integral transform `N ↦ R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 N)` by a module `𝓕` supported on a
closed subset of `U₀` right t-exact on objects with quasi-coherent cohomology, which is the
bound the construction of [Stacks, Section 0G07] uses.

## Main results

* `isZero_homology_derivedPushforward_of_supported`: direct image preserves vanishing of
  cohomology supported on a closed subset of an open over which the morphism is affine.
* `isZero_homology_derivedPushforward_pullback_snd`: the second projection of `X ×_S Y`, with `S`
  affine, preserves vanishing of cohomology supported on a closed subset of an affine open of `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace Stacks.AlgebraicGeometry.SupportedPushforwardReflect

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedQCoh.jPush_additive

variable {P Y : Scheme.{u}} (p : P ⟶ Y) (U : P.Opens) {T : Set P} (hT : IsClosed T)
  (hTU : T ⊆ U) (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)))
  (hE : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
    (structureSheafRing P.toRingedSpace) T E)

include hT hTU hE in
/-- **Direct image preserves vanishing of cohomology supported over an open over which it is
affine.** -/
theorem isZero_homology_derivedPushforward_of_supported [IsAffineHom (U.ι ≫ p)]
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) i).obj E).IsQuasicoherent) {i : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing P.toRingedSpace)) i).obj E)) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward p.toLRSHom.toShHom).obj E)) := by
  have hres : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing U.toScheme.toRingedSpace)) i).obj
      ((jStar U (structureSheafRing P.toRingedSpace)).mapDerivedCategory.obj E)) :=
    (Functor.map_isZero (jStar U (structureSheafRing P.toRingedSpace)) h).of_iso
      (homologyJStarIso U i E)
  exact (AffinePushforwardTExactness.isZero_homology_derivedPushforward_of_isZero_homology
    (U.ι ≫ p) _ (fun j => isQuasicoherent_homology_jStar U j E (hcoh j)) hres).of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).mapIso
      (derivedPushforwardRestrictCompIso p U hT hTU E hE))

/-- **The second projection of a fibre product preserves vanishing of cohomology supported over
a closed subset of an affine open of the first factor**, for `S` affine. -/
theorem isZero_homology_derivedPushforward_pullback_snd {X S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [IsAffine S] {U : X.Opens} (hU : IsAffineOpen U) {Z : Set X} (hZ : IsClosed Z)
    (hZU : Z ⊆ U)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace)))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace)) i).obj
        E).IsQuasicoherent)
    (hE : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      (structureSheafRing (pullback f g).toRingedSpace) ((pullback.fst f g).base ⁻¹' Z) E) {i : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (pullback f g).toRingedSpace)) i).obj E)) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) i).obj
      ((derivedPushforward (pullback.snd f g).toLRSHom.toShHom).obj E)) :=
  have : IsAffineHom ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g) :=
    isAffineHom_ι_comp_pullback_snd f g hU
  isZero_homology_derivedPushforward_of_supported (pullback.snd f g)
    (pullback.fst f g ⁻¹ᵁ U) (hZ.preimage (pullback.fst f g).base.hom.continuous)
    (Set.preimage_mono hZU) E hE hcoh h

end Stacks.AlgebraicGeometry.SupportedPushforwardReflect
