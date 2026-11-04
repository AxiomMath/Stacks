module

public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.OpenMapFunctor
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # `Opens X` as a subsite of `Opens Y` along an open embedding

Let `f : X ⟶ Y` be a map of topological spaces and let `v = IsOpenMap.functor : Opens X ⥤ Opens Y`,
`U ↦ f(U)`, be the functor of Stacks 00XQ.  This file collects the facts that exhibit `v` as the
inclusion of a *subsite*: it identifies `Opens X` with the full subcategory of `Opens Y` of those
opens contained in the open set `f(X)`, compatibly with the Zariski topologies of Stacks 00VJ on
both sides.

Mathlib already proves the two halves of the statement that `v` is fully faithful: `v` is always
faithful because `Opens Y` is a poset (`IsOpenMap.functor_faithful`), and `v` is full as soon as
`f` is a monomorphism, i.e. injective (`IsOpenMap.functorFullOfMono`), since fullness of a functor
of posets says exactly that `f(U) ⊆ f(U')` implies `U ⊆ U'`.  Mathlib also proves that `v` is
cover-preserving (`IsOpenMap.coverPreserving`).  What is added here is the packaging of these into
a `Functor.FullyFaithful`, the description of the essential image of `v`, and — the point of the
file — the resulting *two-sided* comparison of covering sieves: a sieve on `U` covers `U` if and
only if the sieve it generates on `f(U)` covers `f(U)`.

## Main results

* `StacksOpenMapSite.fullyFaithfulFunctor`: for an open embedding `f`, the functor `v` is fully
  faithful.
* `StacksOpenMapSite.essImage_functor_iff`: for an open map `f`, an open `V ⊆ Y` lies in the
  essential image of `v` exactly when `V ⊆ f(X)`.
* `StacksOpenMapSite.coverPreserving_functor`: `v` is cover-preserving for the Zariski topologies.
* `StacksOpenMapSite.mem_grothendieckTopology_iff_functorPushforward_mem`: for an open embedding
  `f`, a sieve `T` on `U` is covering if and only if `v(T)` is a covering sieve on `f(U)`.
-/

@[expose] public section

namespace StacksOpenMapSite

open CategoryTheory TopologicalSpace

universe u

variable {X Y : TopCat.{u}} {f : X ⟶ Y}

/-! ### Full faithfulness -/

/-- An open embedding of topological spaces is a monomorphism in `TopCat`, because it is
injective.  This is the hypothesis under which Mathlib's `IsOpenMap.functorFullOfMono` makes
`IsOpenMap.functor` full. -/
theorem mono_of_isOpenEmbedding (hf : Topology.IsOpenEmbedding f) : Mono f :=
  (TopCat.mono_iff_injective f).mpr hf.injective

/-- For an open embedding `f : X ⟶ Y` the functor `v : Opens X ⥤ Opens Y`, `U ↦ f(U)`, is full:
if `f(U) ⊆ f(U')` then `U ⊆ U'`, by injectivity of `f`.

This is Mathlib's `IsOpenMap.functorFullOfMono` with the monomorphism hypothesis supplied by
`StacksOpenMapSite.mono_of_isOpenEmbedding`. -/
theorem full_functor (hf : Topology.IsOpenEmbedding f) :
    (IsOpenMap.functor hf.isOpenMap).Full :=
  hf.isOpenMap.functorFullOfMono (H := mono_of_isOpenEmbedding hf)

/-- For an open embedding `f : X ⟶ Y` the functor `v : Opens X ⥤ Opens Y`, `U ↦ f(U)`, is fully
faithful: faithfulness is automatic since `Opens X` and `Opens Y` are posets, and fullness is the
injectivity of `f` on points. -/
noncomputable def fullyFaithfulFunctor (hf : Topology.IsOpenEmbedding f) :
    (IsOpenMap.functor hf.isOpenMap).FullyFaithful :=
  haveI := full_functor hf
  .ofFullyFaithful _

/-! ### The essential image -/

/-- An open `V ⊆ Y` lies in the essential image of `v : Opens X ⥤ Opens Y`, `U ↦ f(U)`, exactly
when `V` is contained in the open set `f(X)`.

Indeed `f(U) ⊆ f(X)` for every `U`, and conversely if `V ⊆ f(X)` then `V = f(f⁻¹(V))`. -/
theorem essImage_functor_iff (hf : IsOpenMap f) (V : Opens Y) :
    (IsOpenMap.functor hf).essImage V ↔ V ≤ ⟨Set.range f, hf.isOpen_range⟩ := by
  constructor
  · rintro ⟨U, ⟨e⟩⟩
    exact e.inv.le.trans (Set.image_subset_range _ _)
  · intro hV
    exact ⟨(Opens.map f).obj V, ⟨eqToIso (Opens.ext (Set.image_preimage_eq_of_subset hV))⟩⟩

/-- The set-level form of `StacksOpenMapSite.essImage_functor_iff`: an open `V ⊆ Y` is in the
essential image of `U ↦ f(U)` exactly when `V` is contained in the range of `f`. -/
theorem essImage_functor_iff_subset_range (hf : IsOpenMap f) (V : Opens Y) :
    (IsOpenMap.functor hf).essImage V ↔ (V : Set Y) ⊆ Set.range f :=
  essImage_functor_iff hf V

/-- Since `Opens Y` is a poset, being in the essential image of `v : Opens X ⥤ Opens Y` is the
same as being *equal* to `f(U)` for some open `U ⊆ X`, not merely isomorphic to one. -/
theorem essImage_functor_iff_exists_eq (hf : IsOpenMap f) (V : Opens Y) :
    (IsOpenMap.functor hf).essImage V ↔ ∃ U : Opens X, (IsOpenMap.functor hf).obj U = V :=
  ⟨fun ⟨U, ⟨e⟩⟩ => ⟨U, le_antisymm e.hom.le e.inv.le⟩,
    fun ⟨U, hU⟩ => hU ▸ Functor.obj_mem_essImage _ U⟩

/-! ### Compatibility with the Zariski topologies -/

/-- For an open map `f : X ⟶ Y` the functor `v : Opens X ⥤ Opens Y`, `U ↦ f(U)`, is
cover-preserving for the Zariski topologies of Stacks 00VJ: the images of the members of an open
covering of `U` form an open covering of `f(U)`.

This is Mathlib's `IsOpenMap.coverPreserving`, restated here in the notation of this file. -/
theorem coverPreserving_functor (hf : IsOpenMap f) :
    CoverPreserving (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      (IsOpenMap.functor hf) :=
  hf.coverPreserving

/-- **The subsite comparison.** For an open embedding `f : X ⟶ Y` and an open `U ⊆ X`, a sieve `T`
on `U` is a covering sieve for the Zariski topology on `X` if and only if the sieve it generates
on `f(U)` is a covering sieve for the Zariski topology on `Y`.

The forward implication is cover-preservation (`StacksOpenMapSite.coverPreserving_functor`).  The
converse is cocontinuity of `v` (Stacks 00XQ, `StacksOpenMapSite.isCocontinuous_isOpenMapFunctor`),
which pulls the covering sieve `v(T)` back to a covering sieve on `U`, combined with the identity
`v⁻¹(v(T)) = T` valid for a fully faithful `v`. -/
theorem mem_grothendieckTopology_iff_functorPushforward_mem (hf : Topology.IsOpenEmbedding f)
    (V : Opens X) (T : Sieve V) :
    T ∈ Opens.grothendieckTopology X V ↔
      T.functorPushforward (IsOpenMap.functor hf.isOpenMap) ∈
        Opens.grothendieckTopology Y ((IsOpenMap.functor hf.isOpenMap).obj V) := by
  have := full_functor hf
  have := isCocontinuous_isOpenMapFunctor hf.isOpenMap
  refine ⟨fun hT => (coverPreserving_functor hf.isOpenMap).cover_preserve hT, fun hT => ?_⟩
  simpa only [Sieve.functorPullback_functorPushforward_eq] using
    Functor.cover_lift (IsOpenMap.functor hf.isOpenMap) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) hT

end StacksOpenMapSite
