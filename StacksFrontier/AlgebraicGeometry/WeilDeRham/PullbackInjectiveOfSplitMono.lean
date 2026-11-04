module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge

/-!
# The de Rham pullback is injective when the comparison map splits

Let `g' ≫ f = f' ≫ g` be a commutative square of schemes, with `f : X ⟶ S` and `f' : X' ⟶ S'`,
and let `g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` be the induced morphism of ringed spaces.
The pullback `H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of [Stacks, Tag 0FL6] factors as `H^m(X, -)` of the
canonical map `c : Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` in `D(X, f^{-1}𝒪_S)` followed by the Leray
identification `H^m(X, Rg₀_* -) = H^m(X', -)` (the edge identity of [Stacks, Tag 0FMP],
`Stacks.DeRhamBaseChange.deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback`).
Hence if `c` has a left inverse in `D(X, f^{-1}𝒪_S)`, the pullback is injective in every degree.

This is the step from [Stacks, Proposition 0FUW] (for a blowing up `b : X' ⟶ X` with smooth centre,
`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}` has a splitting) to axiom (A7) of [Stacks, Section 0FID] for de Rham
cohomology (`b^*` is injective), as used in the proof of [Stacks, Proposition 0FWD].

## Main results

* `Stacks.WeilDeRham.deRhamCohomologyPullback_injective_of_isSplitMono`: if the canonical map
  `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` is a split monomorphism, then the de Rham pullback
  `H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` is injective for every `m`.

## Implementation notes

The split-mono hypothesis is written in the derived category `HasDerivedCategory.standard`, with
the instance given explicitly (`@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)`): the
comparison `pushforwardComparisonQ` and the edge identity this file is a corollary of
(`StacksFrontier/AlgebraicGeometry/DeRham/LerayHirsch/RealizationEdge.lean`) are stated in that model
only. No instance is declared in this file. The conclusion, about the de Rham pullback of
[Stacks, Tag 0FL6], does not depend on a model.

## References

* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 0FMP](https://stacks.math.columbia.edu/tag/0FMP)
* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)

universe u

namespace Stacks.WeilDeRham

/-- A functor to modules, after any functor, takes a split monomorphism to an injective map. -/
private theorem injective_map_map_of_isSplitMono {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    {R : Type u} [Ring R] (G : 𝒞 ⥤ 𝒟) (H : 𝒟 ⥤ ModuleCat.{u} R) {K L : 𝒞} (c : K ⟶ L)
    (hc : IsSplitMono c) : Function.Injective (H.map (G.map c)).hom := by
  have := hc
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The de Rham pullback is injective when the comparison map splits.** For a commutative
square `g' ≫ f = f' ≫ g` of schemes, if the canonical map `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` in
`D(X, f^{-1}𝒪_S)` (the canonical map of de Rham complexes followed by `g₀_* ⟶ Rg₀_*`) has a left
inverse, then the pullback `H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of [Stacks, Tag 0FL6] is injective
for every `m`. -/
theorem deRhamCohomologyPullback_injective_of_isSplitMono
    (hc : IsSplitMono
      ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).map
          (deRhamPushforwardInt g' f' f g w) ≫
        pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) (deRhamComplexInt f')))
    (m : ℤ) :
    Function.Injective (Scheme.Hom.deRhamCohomologyPullback g' f f' g w m).hom := by
  intro ξ η h
  have hξ := deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback g' f' f g w m ξ
  have hη := deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback g' f' f g w m η
  rw [h, hη] at hξ
  have h1 := congrArg (lerayCohomologyIso (inverseImageBaseMap g' f' f g w)
    ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj (deRhamCochainComplex f'))
      m).inv hξ
  simp only [Iso.hom_inv_id_apply] at h1
  have hH := injective_map_map_of_isSplitMono (baseSections (inverseImageBase f))
    (@DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) _ _
      (HasDerivedCategory.standard _) m) _ hc
  have h2 := congrArg (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (Scheme.Hom.deRhamAlgebras f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m).inv
    (hH h1)
  simp only [Iso.hom_inv_id_apply] at h2
  exact h2.symm

end Stacks.WeilDeRham

end
