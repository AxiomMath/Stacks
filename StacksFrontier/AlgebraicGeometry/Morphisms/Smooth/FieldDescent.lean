module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveFieldDescent.Basic

/-!
# Smoothness over a field descends along a field extension

Let `X` be a scheme over a field `k` and let `K/k` be a field extension. If the base change
`X_K ⟶ Spec K` is smooth then `X ⟶ Spec k` is smooth.

`Spec K ⟶ Spec k` is surjective, flat and quasi-compact
(`Stacks.QuasiProjectiveFieldDescent.faithfullyFlat_extensionMap`), and smoothness descends along
such a morphism by pinned Mathlib's instance
`DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`
(`Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean:41`). Since smoothness is also stable
under base change, the two conditions are equivalent.

## Main results

* `AlgebraicGeometry.smooth_of_smooth_pullback_snd_spec_algebraMap`: smoothness over `k` follows
  from smoothness of the base change over `K`.
* `AlgebraicGeometry.smooth_pullback_snd_spec_algebraMap_iff`: the two are equivalent.

## Implementation notes

This is the step by which the conclusion of [Stacks, Tag 0FD6] over a bigger field returns to the
field one started with: the divisor `H_v` of a vector with coordinates in `K` base-changes, along
an extension `L/K`, to the divisor of the same coordinates read in `L`, so smoothness of the
latter over `L` gives smoothness of the former over `K`. It carries no `@[stacks]` attribute,
being a consequence of flat descent and not a clause of any tag.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- **Smoothness over a field descends along a field extension.** If the base change
`X_K ⟶ Spec K` of `f : X ⟶ Spec k` along a field extension `K/k` is smooth, then so is `f`. -/
theorem smooth_of_smooth_pullback_snd_spec_algebraMap
    (h : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) : Smooth f := by
  refine MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ?_ h
  obtain ⟨hs, hfl, hqc⟩ := Stacks.QuasiProjectiveFieldDescent.faithfullyFlat_extensionMap k K
  exact ⟨⟨hs, hfl⟩, hqc⟩

/-- **Smoothness over a field is unchanged by enlarging the field.** Smoothness is stable under
base change and descends along a field extension, so `X_K ⟶ Spec K` is smooth exactly when
`X ⟶ Spec k` is. -/
theorem smooth_pullback_snd_spec_algebraMap_iff :
    Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ↔ Smooth f := by
  exact ⟨smooth_of_smooth_pullback_snd_spec_algebraMap k K f,
    fun h => have := h; inferInstance⟩

end AlgebraicGeometry

end
