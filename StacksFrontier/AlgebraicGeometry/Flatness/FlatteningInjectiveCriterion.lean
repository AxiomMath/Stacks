module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjectiveStalk

/-!
# Detecting sections of a module by a flat morphism whose image carries the weakly associated
points

Let `g : X' ⟶ X` be a flat morphism of schemes and let `F` be a quasi-coherent `𝒪_X`-module
every weakly associated point of which lies in the image of `g`. Then the canonical map
`F ⟶ g_* g^* F` is injective.

## Main results

* `AlgebraicGeometry.mono_pullbackPushforwardUnit_of_weaklyAssociatedPoints_subset_range`.

## Implementation notes

This is the heart of Stacks tag 05PD, with the tag's hypothesis `Ass_{X/S}(F) ⊂ g(X')` replaced
by the weaker-looking — and for the proof, the only relevant — condition
`WeakAss_X(F) ⊂ g(X')`. The two are joined by the inclusion `WeakAss_X(F) ⊂ Ass_{X/S}(F)` of
Stacks tag 05IJ, valid when `F` is of finite type and flat over a base over which `X` is
locally of finite type; that step is taken in
`StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjective`.

Injectivity of a morphism of sheaves of modules is the categorical predicate
`CategoryTheory.Mono`, and no quasi-coherence of the target `g_* g^* F` is assumed: it would
require `g` to be quasi-compact and quasi-separated, which the source does not ask for.

## References

* [Stacks Project, Tag 05PD](https://stacks.math.columbia.edu/tag/05PD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If `g : X' ⟶ X` is flat and its image contains every weakly associated point of a
quasi-coherent `𝒪_X`-module `F`, then the canonical map `F ⟶ g_* g^* F` is injective.

At a weakly associated point `x = g x'` the stalk of the map is injective by
`AlgebraicGeometry.stalk_pullbackPushforwardUnit_injective_of_flat`, and pointwise injectivity
at the weakly associated points of the source suffices by
`AlgebraicGeometry.mono_of_stalk_injective_on_weaklyAssociatedPoints_of_source_quasicoherent`. -/
theorem mono_pullbackPushforwardUnit_of_weaklyAssociatedPoints_subset_range
    {X' X : Scheme.{u}} (g : X' ⟶ X) [Flat g] (F : X.Modules) [F.IsQuasicoherent]
    (hWA : Stacks.Divisors.weaklyAssociatedPoints F ⊆ Set.range g.base) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F) := by
  let : ((𝟭 X.Modules).obj F).IsQuasicoherent := inferInstanceAs F.IsQuasicoherent
  apply mono_of_stalk_injective_on_weaklyAssociatedPoints_of_source_quasicoherent
  intro x hx
  obtain ⟨x', hx'⟩ := hWA hx
  have hgx := show g x' = x from hx'
  subst hgx
  exact stalk_pullbackPushforwardUnit_injective_of_flat g F x'

end AlgebraicGeometry

end
