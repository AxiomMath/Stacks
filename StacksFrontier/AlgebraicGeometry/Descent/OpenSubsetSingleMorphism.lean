module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute

/-!
# Descending an open subset along one surjective flat quasi-compact morphism

Let `f : T' ⟶ T` be a surjective, flat, quasi-compact morphism of schemes and let `W' ⊆ T'` be
an open subset whose two preimages in `T' ×_T T'` agree. Then `W'` is the preimage of a unique
open subset of `T`, namely of its image.

## Main results

* `AlgebraicGeometry.existsUnique_isOpen_preimage_eq_of_flat_of_quasiCompact_of_surjective` : the
  descended open subset, with uniqueness.
* `AlgebraicGeometry.existsUnique_opens_preimage_eq_of_flat_of_quasiCompact_of_surjective` : the
  same statement for open subschemes rather than open subsets.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 02JY](https://stacks.math.columbia.edu/tag/02JY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {T' T : Scheme.{u}} (f : T' ⟶ T) [Surjective f] [Flat f] [QuasiCompact f]

omit [Surjective f] [Flat f] [QuasiCompact f] in
/-- The preimage of the image of a subset whose two preimages in the fibre product agree is the
subset itself. -/
theorem preimage_image_eq_of_preimage_fst_eq_preimage_snd {W' : Set T'}
    (hcompat : (pullback.fst f f).base ⁻¹' W' = (pullback.snd f f).base ⁻¹' W') :
    f.base ⁻¹' (f.base '' W') = W' := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro x ⟨y, hy, hfy⟩
  obtain ⟨z, hz₁, hz₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) y x hfy
  have hzmem : z ∈ (pullback.fst f f).base ⁻¹' W' := by
    show (pullback.fst f f).base z ∈ W'
    rw [hz₁]
    exact hy
  rw [hcompat] at hzmem
  change (pullback.snd f f).base z ∈ W' at hzmem
  rwa [hz₂] at hzmem

/-- **An open subset descends along a surjective flat quasi-compact morphism.** Let
`f : T' ⟶ T` be a surjective, flat, quasi-compact morphism of schemes and let `W' ⊆ T'` be open
with `pr₀⁻¹(W') = pr₁⁻¹(W')` in `T' ×_T T'`. Then there is a unique open `W ⊆ T` with
`W' = f⁻¹(W)`. -/
@[stacks 03N0 "covering by a single surjective flat quasi-compact morphism"]
theorem existsUnique_isOpen_preimage_eq_of_flat_of_quasiCompact_of_surjective {W' : Set T'}
    (hW' : IsOpen W')
    (hcompat : (pullback.fst f f).base ⁻¹' W' = (pullback.snd f f).base ⁻¹' W') :
    ∃! W : Set T, IsOpen W ∧ f.base ⁻¹' W = W' := by
  have hpre : f.base ⁻¹' (f.base '' W') = W' :=
    preimage_image_eq_of_preimage_fst_eq_preimage_snd f hcompat
  refine ⟨f.base '' W', ⟨?_, hpre⟩, ?_⟩
  · have hq := Flat.isQuotientMap_of_surjective f
    refine hq.isCoinducing.isOpen_preimage.mp ?_
    rw [hpre]
    exact hW'
  · rintro W ⟨-, hWpre⟩
    rw [← hWpre, Set.image_preimage_eq _ f.surjective]

/-- **An open subscheme descends along a surjective flat quasi-compact morphism.** For
`f : T' ⟶ T` surjective, flat and quasi-compact, an open subscheme `W'` of `T'` whose two
preimages in `T' ×_T T'` agree is the preimage of a unique open subscheme of `T`. -/
@[stacks 03N0 "covering by a single surjective flat quasi-compact morphism, as open subschemes"]
theorem existsUnique_opens_preimage_eq_of_flat_of_quasiCompact_of_surjective (W' : T'.Opens)
    (hcompat : (pullback.fst f f).base ⁻¹' (W' : Set T') =
      (pullback.snd f f).base ⁻¹' (W' : Set T')) :
    ∃! W : T.Opens, f ⁻¹ᵁ W = W' := by
  obtain ⟨W, ⟨hWo, hWpre⟩, hWuniq⟩ :=
    existsUnique_isOpen_preimage_eq_of_flat_of_quasiCompact_of_surjective f W'.2 hcompat
  refine ⟨⟨W, hWo⟩, TopologicalSpace.Opens.ext hWpre, ?_⟩
  intro V hV
  refine TopologicalSpace.Opens.ext (hWuniq (V : Set T) ⟨V.2, ?_⟩)
  exact congrArg (fun U : T'.Opens => (U : Set T')) hV

end AlgebraicGeometry

end
