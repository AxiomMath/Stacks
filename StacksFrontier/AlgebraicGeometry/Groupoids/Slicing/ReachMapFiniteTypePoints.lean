module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.ReachMapCoproduct
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Surjectivity of the reach map of a family of slices through the finite type points

Step 3 of the proof of [Stacks Project, Tag 0489] forms `U' = ∐_u U'_u`, the coproduct of the
affine slices produced by [Stacks Project, Tag 04N0] over the finite type points of the object
scheme `U`, and needs the reach map of `∐_u g_u` to be *surjective*, so that together with
flatness and local finite presentation it is an fppf covering.

The source's argument for surjectivity is: the image of each `h_u` is open, because `h_u` is
flat and locally of finite presentation; it contains `u`, because the identity section factors
`g_u` through `h_u`; so the union of the images is an open containing every finite type point
of `U`, hence is `U`.

`StacksFrontier/AlgebraicGeometry/Groupoids/Slicing/ReachMapCoproduct.lean` has the last two of
those three ingredients -- `AlgebraicGeometry.exists_section_comp_reachMap_eq` and
`AlgebraicGeometry.Scheme.Opens.eq_top_of_finiteTypePoints_subset` -- and the reduction of
surjectivity of the reach map of a coproduct to a joint covering,
`AlgebraicGeometry.surjective_reachMap_of_jointly_covering`.  What this file adds is the first
ingredient and the assembly.

Openness is Mathlib's: a flat morphism locally of finite presentation is universally open by
`AlgebraicGeometry.UniversallyOpen.of_flat` ([Stacks Project, Tag 01UA]), and a universally
open morphism is an open map on the underlying spaces by
`AlgebraicGeometry.Scheme.Hom.isOpenMap`.

## Main results

* `AlgebraicGeometry.isOpen_range_of_flat_of_locallyOfFinitePresentation`: the image of a flat
  morphism locally of finite presentation is open.
* `AlgebraicGeometry.surjective_reachMap_sigmaDesc_of_finiteTypePoints`: **the covering clause
  of Step 3 of the proof of [Stacks Project, Tag 0489]** -- if every finite type point of the
  object scheme lies in the image of some member of a family `q_i : V_i ⟶ U` whose reach maps
  are flat and locally of finite presentation, then the reach map of `∐_i q_i` is surjective.

## Implementation notes

The hypotheses are stated for the reach map in the fibre-product-of-schemes form
`pullback.snd (q i) G.target.left ≫ G.source.left`, which is the form in which
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite`, the library's
[Stacks Project, Tag 04N0], states the properties of `h_u`, and the form used throughout
`ReachMapCoproduct.lean`.

Only flatness and local finite presentation of the reach maps are used here; local
quasi-finiteness, the third property [Stacks Project, Tag 04N0] produces, plays no role in
surjectivity and is not assumed.

## References

* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 02J4](https://stacks.math.columbia.edu/tag/02J4)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The image of a flat morphism locally of finite presentation is open.

Such a morphism is universally open ([Stacks Project, Tag 01UA], Mathlib's
`AlgebraicGeometry.UniversallyOpen.of_flat`), hence an open map on the underlying spaces. -/
theorem isOpen_range_of_flat_of_locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] : IsOpen (Set.range f.base) :=
  f.isOpenMap.isOpen_range

/-- **The covering clause of Step 3 of the proof of [Stacks Project, Tag 0489].**

Let `G` be a groupoid scheme and let `q i : V i ⟶ U` be a family of morphisms to its object
scheme whose reach maps `h i : V i ×_{q i, U, t} R ⟶ U` are flat and locally of finite
presentation.  If every finite type point of `U` lies in the image of some `q i`, then the
reach map of `∐_i q i` is surjective.

The images of the `h i` are open by
`AlgebraicGeometry.isOpen_range_of_flat_of_locallyOfFinitePresentation` and contain the images
of the `q i` by `AlgebraicGeometry.exists_section_comp_reachMap_eq`, so their union is an open
containing every finite type point of `U`, hence all of `U`
(`AlgebraicGeometry.Scheme.Opens.eq_top_of_finiteTypePoints_subset`); then
`AlgebraicGeometry.surjective_reachMap_of_jointly_covering` applies to the coproduct
injections. -/
theorem surjective_reachMap_sigmaDesc_of_finiteTypePoints (G : GroupoidScheme S) {I : Type u}
    [Small.{u} I] {V : I → Scheme.{u}} (q : ∀ i, V i ⟶ G.objects.left)
    (hflat : ∀ i, Flat (pullback.snd (q i) G.target.left ≫ G.source.left))
    (hlfp : ∀ i, LocallyOfFinitePresentation
      (pullback.snd (q i) G.target.left ≫ G.source.left))
    (hft : ∀ x : G.objects.left, IsFiniteTypePoint x →
      ∃ (i : I) (y : V i), (q i) y = x) :
    Surjective (pullback.snd (Sigma.desc q) G.target.left ≫ G.source.left) := by
  let W : G.objects.left.Opens :=
    ⟨⋃ i, Set.range (pullback.snd (q i) G.target.left ≫ G.source.left).base,
      isOpen_iUnion fun i =>
        @isOpen_range_of_flat_of_locallyOfFinitePresentation _ _ _ (hflat i) (hlfp i)⟩
  have hWtop : W = ⊤ := by
    refine Scheme.Opens.eq_top_of_finiteTypePoints_subset (fun x hx => ?_)
    obtain ⟨i, y, hy⟩ := hft x hx
    obtain ⟨e, he⟩ := exists_section_comp_reachMap_eq G (q i)
    exact Set.mem_iUnion.2 ⟨i, e y, by rw [← Scheme.Hom.comp_apply, he, hy]⟩
  refine surjective_reachMap_of_jointly_covering G (Sigma.desc q) (Sigma.ι V) q
    (fun i => Sigma.ι_desc _ _) (fun x => ?_)
  have hx : x ∈ (W : Set G.objects.left) := by simp [hWtop]
  exact Set.mem_iUnion.1 hx

end AlgebraicGeometry

end
