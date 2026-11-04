module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Properness from a locally finite cover by open and closed subschemes

Chapter 42 of the Stacks Project repeatedly needs that a morphism `f : X ⟶ Y` which is locally of
finite type is **proper** once `X` is covered by subschemes `Z i ⊆ X` that are open *and* closed,
each of which is proper over `Y`, with the two families of ranges locally finite — in `X` for the
`Z i`, and in `Y` for their images. The motivating case is the structure morphism of a coproduct
`\coprod_i Z_i → Y` of schemes proper over `Y`, whose images form a locally finite family.

Properness is separatedness, universal closedness and local finiteness of type, and the first two
are checked separately against the cover.

* **Separated.** The diagonal `Δ_f : X ⟶ X ×_Y X` has range the union of the ranges of the
  `Z i ⟶ X ×_Y X`, each of which is closed because it factors as the diagonal of the proper
  morphism `Z i ⟶ Y` followed by the closed immersion `Z i ×_Y Z i ⟶ X ×_Y X` obtained from the
  closed immersion `Z i ⟶ X`. That union is closed because the family is locally finite, being
  carried by the first projection into the locally finite family of the ranges of the `Z i`.
* **Universally closed.** The property is stable under base change, and the base change of the
  cover is again a cover with locally finite images, so it suffices to know that a map is closed
  as soon as it is covered by closed maps with locally finite images. That is
  `Stacks.Topology.isClosedMap_of_locallyFinite_cover`, a statement about topological spaces
  alone.

Note that both hypotheses of local finiteness are needed, and for different reasons: the family of
ranges in `X` controls the diagonal, and the family of images in `Y` controls closedness of the
image after base change.

## Main results

* `Stacks.Topology.isClosedMap_of_locallyFinite_cover` — a map covered by closed maps whose images
  form a locally finite family is closed.
* `Stacks.Topology.locallyFinite_of_disjoint_open_cover` — a pairwise disjoint open cover is a
  locally finite family.
* `AlgebraicGeometry.isProper_of_locallyFinite_open_closed_cover` — the properness criterion.

## References

* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Topology

/-- The image of a set `E` under `f` is the union of the images of its preimages under the pieces
`j i` of a cover of the source. -/
private theorem image_eq_iUnion_image_comp_of_cover {A B : Type*} {I : Type*} {Z : I → Type*}
    (f : A → B) (j : ∀ i, Z i → A) (hcover : ∀ x, ∃ i, x ∈ Set.range (j i)) (E : Set A) :
    f '' E = ⋃ i, (f ∘ j i) '' (j i ⁻¹' E) := by
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, z, rfl⟩ := hcover x
    exact Set.mem_iUnion.2 ⟨i, z, hx, rfl⟩
  · intro hy
    obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
    exact ⟨j i z, hz, rfl⟩

/-- A continuous map is closed as soon as its source is covered by continuous maps `j i` along
which it becomes closed, provided the images `(f ∘ j i) '' _` form a locally finite family.

The image of a closed set is the union of its images from the pieces, and a locally finite union
of closed sets is closed. -/
theorem isClosedMap_of_locallyFinite_cover {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {I : Type*} {Z : I → Type*} [∀ i, TopologicalSpace (Z i)]
    (f : A → B) (j : ∀ i, Z i → A) (hj : ∀ i, Continuous (j i))
    (hcover : ∀ x, ∃ i, x ∈ Set.range (j i))
    (hclosed : ∀ i, IsClosedMap (f ∘ j i))
    (hfinite : LocallyFinite fun i ↦ Set.range (f ∘ j i)) :
    IsClosedMap f := by
  intro E hE
  rw [image_eq_iUnion_image_comp_of_cover f j hcover]
  refine (hfinite.subset fun i ↦ Set.image_subset_range _ _).isClosed_iUnion fun i ↦ ?_
  exact hclosed i _ (hE.preimage (hj i))

/-- A pairwise disjoint family of open sets covering a topological space is locally finite: the
member containing a point is a neighbourhood of it meeting no other member. -/
theorem locallyFinite_of_disjoint_open_cover {X : Type*} [TopologicalSpace X] {I : Type*}
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hdisjoint : Pairwise fun i j ↦ Disjoint (U i) (U j)) :
    LocallyFinite U := by
  intro x
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨U i, (hopen i).mem_nhds hi, (Set.finite_singleton i).subset ?_⟩
  intro j hj
  by_contra hji
  obtain ⟨y, hyj, hyi⟩ := hj
  exact Set.disjoint_left.1 (hdisjoint hji) hyj hyi

end Stacks.Topology

namespace AlgebraicGeometry

/-- The range of `g ≫ Δ_f` is closed, for `g : Z ⟶ X` a closed immersion with `g ≫ f`
separated: that composite factors as the diagonal of `g ≫ f`, a closed immersion by
separatedness, followed by the closed immersion `Z ×_Y Z ⟶ X ×_Y X` obtained from `g` by base
change and composition.

This is the step that makes the diagonal of `f` closed when `X` is covered by closed subschemes
proper over `Y`; see `AlgebraicGeometry.isProper_of_locallyFinite_open_closed_cover`. -/
theorem isClosed_range_comp_diagonal_of_isClosedImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Z ⟶ X) [IsClosedImmersion g] [IsSeparated (g ≫ f)] :
    IsClosed (Set.range (g ≫ pullback.diagonal f)) := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : IsClosedImmersion (pullback.map (g ≫ f) (g ≫ f) f f g g (𝟙 Y)
      ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u}) inferInstance inferInstance rfl rfl
  have heq : g ≫ pullback.diagonal f =
      pullback.diagonal (g ≫ f) ≫ pullback.map (g ≫ f) (g ≫ f) f f g g (𝟙 Y)
        ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl) := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd,
        pullback.diagonal_fst_assoc, pullback.diagonal_snd_assoc, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id]
  rw [heq]
  exact (Scheme.Hom.isClosedEmbedding _).isClosed_range

/-- **A morphism locally of finite type is proper once it is covered by open and closed
subschemes that are proper over the target**, the two families of ranges — in the source and in
the target — being locally finite.

This is the criterion that makes the structure morphism of a coproduct of schemes proper over the
base proper, which is how chapter 42 of the Stacks Project produces proper morphisms out of
locally finite collections of proper ones. See the module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.Properness` for the shape of the proof. -/
@[ega "II 5.4.5" "special case"]
theorem isProper_of_locallyFinite_open_closed_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {I : Type u} {Z : I → Scheme.{u}} (j : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)] [∀ i, IsProper (j i ≫ f)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (hjfinite : LocallyFinite fun i ↦ Set.range (j i))
    (hfinite : LocallyFinite fun i ↦ Set.range (j i ≫ f)) :
    IsProper f := by
  have hsep : IsSeparated f := by
    constructor
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    have hclosed (i : I) : IsClosed (Set.range (j i ≫ pullback.diagonal f)) :=
      isClosed_range_comp_diagonal_of_isClosedImmersion f (j i)
    have hlocal : LocallyFinite fun i ↦ Set.range (j i ≫ pullback.diagonal f) := by
      refine (hjfinite.preimage_continuous (pullback.fst f f).continuous).subset fun i ↦ ?_
      rintro _ ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc]
      simp
    have heq := Stacks.Topology.image_eq_iUnion_image_comp_of_cover (pullback.diagonal f).base
      (fun i ↦ (j i).base) hcover Set.univ
    simp only [Set.image_univ, Set.preimage_univ] at heq
    exact heq ▸ hlocal.isClosed_iUnion hclosed
  have huc : UniversallyClosed f := by
    constructor
    intro X' Y' a b f' hs
    have hs' (i : I) :
        IsPullback (pullback.snd a (j i)) (pullback.fst a (j i) ≫ f') (j i ≫ f) b :=
      (IsPullback.of_hasPullback a (j i)).flip.paste_vert hs.flip
    have hp (i : I) : IsProper (pullback.fst a (j i) ≫ f') :=
      MorphismProperty.of_isPullback (hs' i) (P := @IsProper) inferInstance
    have hcover' (x : X') : ∃ i, x ∈ Set.range (pullback.fst a (j i)) := by
      obtain ⟨i, y, hy⟩ := hcover (a x)
      obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      exact ⟨i, z, hz⟩
    have hfinite' : LocallyFinite fun i ↦ Set.range (pullback.fst a (j i) ≫ f') := by
      refine (hfinite.preimage_continuous b.continuous).subset fun i ↦ ?_
      rintro _ ⟨z, rfl⟩
      exact ⟨pullback.snd a (j i) z,
        congrArg (fun m : pullback a (j i) ⟶ Y ↦ m z) (hs' i).w⟩
    have hcm (i : I) : IsClosedMap ((pullback.fst a (j i)) ≫ f').base := by
      have := hp i
      exact (pullback.fst a (j i) ≫ f').isClosedMap
    exact Stacks.Topology.isClosedMap_of_locallyFinite_cover f' (fun i ↦ pullback.fst a (j i))
      (fun i ↦ (pullback.fst a (j i)).continuous) hcover' hcm hfinite'
  exact ⟨⟩

end AlgebraicGeometry

end
