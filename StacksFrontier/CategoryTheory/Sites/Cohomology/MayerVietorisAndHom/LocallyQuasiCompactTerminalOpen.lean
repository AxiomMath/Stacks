module

public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.Topology.Compactness.LocallyCompact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite

/-!
# The top open subset is terminal in the Zariski slice site

Let `X` be an object of the locally quasi-compact Zariski site, and let
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice` be the open-subset functor
from the opens of the space of `X` to the slice site over `X`. This file records two facts
about it that the cohomology comparison of Stacks 0DCU needs as input and that are not part of
the construction itself:

* the image of the top open subset is a terminal object of the slice site, so the two sites
  have matching global sections;
* the inclusion of the Zariski site into topological spaces is locally cover dense for the
  topology of open covers.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSlice_top_isTerminal`: the image
  of `⊤` under `opensToSlice` is terminal in the slice site.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSite_toTop_locallyCoverDense`: the
  inclusion of the Zariski site into `TopCat` is locally cover dense.

## Implementation notes

`opensToSlice` is characterised by its underlying maps being open embeddings with prescribed
images, so the structure map of its value at `⊤` is an open embedding whose range is all of the
space; being also injective it is a homeomorphism, hence an isomorphism in `TopCat`, hence an
isomorphism of the site because the inclusion into `TopCat` reflects isomorphisms. An object of
a slice category whose structure map is an isomorphism is terminal.

Local cover density is checked on a covering family by open embeddings: each member is an open
embedding into the space of an object of the site, so its source is again Hausdorff and locally
quasi-compact and injects into that space, hence is small enough to be an object of the bounded
site; the member is then the image of an arrow of the site, because the inclusion into `TopCat`
is fully faithful.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- The image of the top open subset of the space of `X` is a terminal object of the Zariski
site localized at `X`. -/
def opensToSlice_top_isTerminal (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) : IsTerminal ((S.opensToSlice X).1.obj ⊤) := by
  let F := (S.opensToSlice X).1
  have htop := (S.opensToSlice X).2 (⊤ : Opens X.obj)
  have hsurj : Function.Surjective ((F.obj ⊤).hom : ((F.obj ⊤).left).obj → X.obj) := by
    intro x
    have hx : x ∈ Set.range ((F.obj ⊤).hom : ((F.obj ⊤).left).obj → X.obj) := by
      rw [htop.2]
      exact Set.mem_univ x
    exact Set.mem_range.mp hx
  have : IsIso ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map
      (F.obj ⊤).hom) := by
    rw [TopCat.isIso_iff_isHomeomorph]
    exact ⟨htop.1.continuous, htop.1.isOpenMap, htop.1.toIsEmbedding.injective, hsurj⟩
  have : IsIso (F.obj ⊤).hom :=
    isIso_of_reflects_iso (F.obj ⊤).hom
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)
  exact IsTerminal.ofIso Over.mkIdTerminal (Over.isoMk (asIso (F.obj ⊤).hom)).symm

/-- The inclusion of the locally quasi-compact Zariski site into topological spaces is locally
cover dense for the topology of open covers. -/
theorem qcSite_toTop_locallyCoverDense
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) :
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).LocallyCoverDense
      TopCat.grothendieckTopology := by
  classical
  let E := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  constructor
  intro X T
  obtain ⟨P, hP, hPT⟩ :=
    TopCat.precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp T.property
  have : T2Space (E.obj X) := (S.qcSite.inclusion.obj X).property.1
  have : LocallyCompactSpace (E.obj X) := (S.qcSite.inclusion.obj X).property.2
  have hle : P ≤ (T.val.functorPullback E).functorPushforward E := by
    intro W p hp
    have hpOpen : Topology.IsOpenEmbedding p := hP.2 hp
    have : T2Space W := hpOpen.toIsEmbedding.t2Space
    have : LocallyCompactSpace W := hpOpen.locallyCompactSpace
    let Y : LocallyQuasiCompactHausdorff := ⟨W, ⟨inferInstance, inferInstance⟩⟩
    have hsize : lcSize Y < S.qcSite.cutoff := by
      change Cardinal.mk W < S.qcSite.cutoff
      exact (Cardinal.mk_le_of_injective hpOpen.injective).trans_lt X.property
    let Z : S.category := ⟨Y, hsize⟩
    let p' : locallyQuasiCompactHausdorffToTop.obj (S.qcSite.inclusion.obj Z) ⟶
        locallyQuasiCompactHausdorffToTop.obj (S.qcSite.inclusion.obj X) := p
    let fLC : Y ⟶ S.qcSite.inclusion.obj X :=
      locallyQuasiCompactHausdorffToTop.preimage p'
    let f : Z ⟶ X := S.qcSite.inclusion.preimage fLC
    have hmap : E.map f = p := by
      change locallyQuasiCompactHausdorffToTop.map
          (S.qcSite.inclusion.map (S.qcSite.inclusion.preimage
            (locallyQuasiCompactHausdorffToTop.preimage p'))) = p
      rw [S.qcSite.inclusion.map_preimage]
      exact locallyQuasiCompactHausdorffToTop.map_preimage p'
    have hTmap : T.val (E.map f) := by
      rw [hmap]
      exact hPT W p hp
    exact ⟨Z, f, 𝟙 _, hTmap, by simp [hmap]⟩
  exact TopCat.grothendieckTopology.superset_covering (by rwa [Sieve.generate_le_iff])
    (TopCat.precoverage.generate_mem_toGrothendieck hP)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
