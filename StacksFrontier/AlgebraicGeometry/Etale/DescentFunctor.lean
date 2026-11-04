module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending subsets along a submersive morphism

A morphism of schemes is *submersive* when its underlying map of topological spaces is a
quotient map. This file proves that a subset of the source of a submersive morphism descends
to the target as soon as it is invariant for the two projections of the self fibre product,
and that the descended subset inherits openness and closedness.

## Main results

* `Stacks.Etale.preimage_pullback_fst_eq_preimage_pullback_snd_iff` identifies invariance for
  the two projections of `X ×_S X` with the condition that membership of a point depend only
  on its image in `S`.
* `Stacks.Etale.preimage_image_eq_of_preimage_pullback_eq` says that an invariant subset is
  the inverse image of its image.
* `Stacks.Etale.exists_isOpen_preimage_eq_of_isQuotientMap` and
  `Stacks.Etale.exists_isOpen_isClosed_preimage_eq_of_isQuotientMap` descend an open,
  respectively an open and closed, invariant subset along a submersive morphism.
* `Stacks.Etale.exists_isOpen_preimage_eq_of_etale_baseChange` descends an open invariant subset
  along the base change of a morphism all of whose étale base changes are submersive.

## Implementation notes

Submersiveness is `Topology.IsQuotientMap` on the underlying map. Invariance is stated as the
equality of the two inverse images of the subset under `CategoryTheory.Limits.pullback.fst` and
`CategoryTheory.Limits.pullback.snd` for the self fibre product. That equality is equivalent to
set-theoretic saturation because the map from the points of a fibre product of schemes to the
fibre product of the underlying sets is surjective, by
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

## References

* [Stacks Project, Tag 0BTK](https://stacks.math.columbia.edu/tag/0BTK)
* [Stacks Project, Tag 0406](https://stacks.math.columbia.edu/tag/0406)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

variable {X S : Scheme.{u}}

/-- The two projections of `X ×_S X` pull a subset `W` of `X` back to the same subset exactly
when membership of a point of `X` in `W` depends only on its image in `S`. -/
theorem preimage_pullback_fst_eq_preimage_pullback_snd_iff (f : X ⟶ S) (W : Set X) :
    pullback.fst f f ⁻¹' W = pullback.snd f f ⁻¹' W ↔
      ∀ x y : X, f x = f y → (x ∈ W ↔ y ∈ W) := by
  refine ⟨fun h x y hxy ↦ ?_, fun h ↦ Set.ext fun z ↦ h _ _ ?_⟩
  · obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    exact Set.ext_iff.mp h z
  · simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : pullback f f ⟶ S => k z) (pullback.condition (f := f) (g := f))

/-- A subset of the source of `f` that is invariant for the two projections of the self fibre
product of `f` is the inverse image of its image. -/
theorem preimage_image_eq_of_preimage_pullback_eq (f : X ⟶ S) {W : Set X}
    (hW : pullback.fst f f ⁻¹' W = pullback.snd f f ⁻¹' W) : f ⁻¹' (f '' W) = W := by
  rw [preimage_pullback_fst_eq_preimage_pullback_snd_iff] at hW
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.subset_preimage_image _ _)
  obtain ⟨y, hy, hxy⟩ := hx
  exact (hW x y hxy.symm).mpr hy

/-- The image of an open invariant subset under a submersive morphism is open. -/
theorem isOpen_image_of_isQuotientMap {f : X ⟶ S} (hf : Topology.IsQuotientMap f) {W : Set X}
    (hW : pullback.fst f f ⁻¹' W = pullback.snd f f ⁻¹' W) (hWo : IsOpen W) :
    IsOpen (f '' W) := by
  refine hf.isCoinducing.isOpen_preimage.mp ?_
  rwa [preimage_image_eq_of_preimage_pullback_eq f hW]

/-- The image of a closed invariant subset under a submersive morphism is closed. -/
theorem isClosed_image_of_isQuotientMap {f : X ⟶ S} (hf : Topology.IsQuotientMap f) {W : Set X}
    (hW : pullback.fst f f ⁻¹' W = pullback.snd f f ⁻¹' W) (hWc : IsClosed W) :
    IsClosed (f '' W) := by
  refine hf.isCoinducing.isClosed_preimage.mp ?_
  rwa [preimage_image_eq_of_preimage_pullback_eq f hW]

/-- **Descent of an open subset along a submersive morphism.** An open subset of the source of
a submersive morphism whose two inverse images under the projections of the self fibre product
agree is the inverse image of an open subset of the target. -/
@[sga "1 IX 2.3" "partial"]
theorem exists_isOpen_preimage_eq_of_isQuotientMap {f : X ⟶ S} (hf : Topology.IsQuotientMap f)
    {W : Set X} (hW : pullback.fst f f ⁻¹' W = pullback.snd f f ⁻¹' W) (hWo : IsOpen W) :
    ∃ V : Set S, IsOpen V ∧ f ⁻¹' V = W :=
  ⟨f '' W, isOpen_image_of_isQuotientMap hf hW hWo,
    preimage_image_eq_of_preimage_pullback_eq f hW⟩

/-- **Descent of an open and closed subset along a submersive morphism.** An open and closed
subset of the source of a submersive morphism whose two inverse images under the projections of
the self fibre product agree is the inverse image of an open and closed subset of the target. -/
@[sga "1 IX 2.3" "partial"]
theorem exists_isOpen_isClosed_preimage_eq_of_isQuotientMap {f : X ⟶ S}
    (hf : Topology.IsQuotientMap f) {W : Set X}
    (hW : pullback.fst f f ⁻¹' W = pullback.snd f f ⁻¹' W) (hWo : IsOpen W) (hWc : IsClosed W) :
    ∃ V : Set S, IsOpen V ∧ IsClosed V ∧ f ⁻¹' V = W :=
  ⟨f '' W, isOpen_image_of_isQuotientMap hf hW hWo,
    isClosed_image_of_isQuotientMap hf hW hWc,
    preimage_image_eq_of_preimage_pullback_eq f hW⟩

/-- Descent of an open subset along the base change of a morphism all of whose étale base
changes are submersive: an open subset of `X ×_S U` invariant for the two projections of
`(X ×_S U) ×_U (X ×_S U)` comes from an open subset of `U`. -/
@[sga "1 IX 2.3" "partial"]
theorem exists_isOpen_preimage_eq_of_etale_baseChange {f : X ⟶ S}
    (hbase : ∀ {U : Scheme.{u}} (g : U ⟶ S), Etale g →
      Topology.IsQuotientMap (pullback.snd f g))
    {U : Scheme.{u}} (g : U ⟶ S) (hg : Etale g) {W : Set ↥(pullback f g)}
    (hW : pullback.fst (pullback.snd f g) (pullback.snd f g) ⁻¹' W =
      pullback.snd (pullback.snd f g) (pullback.snd f g) ⁻¹' W) (hWo : IsOpen W) :
    ∃ V : Set U, IsOpen V ∧ pullback.snd f g ⁻¹' V = W :=
  exists_isOpen_preimage_eq_of_isQuotientMap (hbase g hg) hW hWo

end Stacks.Etale

end
