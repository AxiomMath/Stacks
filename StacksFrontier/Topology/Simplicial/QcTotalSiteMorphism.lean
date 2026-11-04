module

public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.Topology.Simplicial.QcTotalSiteComparison

/-!
# The upper horizontal arrow of the diagram of Tag 0DAF is a morphism of topoi

Let `S` be a locally quasi-compact Zariski situation and let `U` be a simplicial object of its
quasi-compact site `LC_qc` of **Tag 09X2**. The functor underlying the upper horizontal arrow
of the diagram of **Tag 0DAF** is `Stacks.Topology.Simplicial.qcTotalComparisonFunctor`,
constructed in `StacksFrontier.Topology.Simplicial.QcTotalSiteComparison`; this file supplies the
two clauses of **Tag 00X1** that turn it into a morphism of topoi

`h : Sh((LC_qc/U)_total) ⟶ Sh(U_Zar)`,

together with that morphism of topoi itself. No augmentation, no hypercovering and no
properness hypothesis enters: `h` exists for an arbitrary simplicial object of `LC_qc`.

## The site on the right-hand corner

The topology of `(LC_qc/U)_total` is the one of Situation 09WE case (B): covering families are
those lying in a single simplicial degree, where they are covering for the localized
quasi-compact topology. `CategoryTheory.SimplicialOver.totalTopology` is that topology, but it
is pinned at `Cat.{u, u}` because `CategoryTheory.SimplicialOver.slices` is, and `LC_qc` has
objects in `Type (u + 1)` — the size gap of Tag 09X2. Only the *degreewise* covering families
had to be restated here, as `Stacks.Topology.Simplicial.qcSliceCoverings`:
`CategoryTheory.SimplicialCoverings.totalTopology`, which assembles them, is already
universe-polymorphic. Working in the big model rather than in the small model of
`StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcSmallModel` keeps the
point-set lemmas about open subspaces directly applicable: an object of the small model carries
no underlying space, so "the image of `P` lies in the open `V`" cannot be stated there without
transporting along the comparison equivalence.

## Both clauses come from one fact

`Stacks.Topology.Simplicial.qcTotalComparisonFunctor_representablyFlat` is the whole of the
work. For an object `(n, P/U_n)` of the total site the simplicial opens receiving it form a
cofiltered category: an object of `StructuredArrow (n, P/U_n) h` is a simplex map `α` out of
`n` together with an open of `|U|_m` containing the image of `P`, the fibre component of such a
morphism being unique once `α` is fixed
(`Stacks.Topology.LocallyQuasiCompactZariskiSituation.over_hom_opensToSlice_ext`); two of them
are refined by taking `α` to be the identity and intersecting the two preimages, and a parallel
pair is equalized the same way, a morphism of simplicial opens being determined by its simplex
map.

Flatness then gives both clauses:

* continuity, because a flat functor is compatible-preserving
  (`CategoryTheory.compatiblePreservingOfFlat`), so `CategoryTheory.CoverPreserving` suffices;
* exactness of `u_s`, because a flat functor has a left exact left Kan extension on presheaves
  (`Stacks.Topology.lan_preservesFiniteLimits_of_flat`) and `u_s` is that extension followed by
  sheafification.

Cover-preservation itself is degreewise. A covering sieve of the site of **Tag 09VL** contains a
covering family lying in one simplicial degree, so the cocontinuous inclusion of that degree
(`Stacks.Topology.Simplicial.levelFunctor_isCocontinuous`) pulls it back to an open covering
there; the **Tag 09X3** comparison `opensToSlice` carries that to a covering of the localized
site; and the inclusion of the degree's fibre carries it into the total site.

## Implementation notes

The universe-general `IsMorphismOfSites` of
`StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs` is used rather than the
small-category-only `CategoryTheory.Functor.IsMorphismOfSites` of Tag 00X1, for the reason
recorded in `StacksFrontier.Topology.Simplicial.Morphisms`: the site of Tag 09VL has objects in
`Type u` but morphisms in `Type`, so it is not a `SmallCategory`, and the total site has objects
in `Type (u + 1)` and morphisms in `Type u`, so the two sites share no universe either. The
sections are therefore taken in `Type (u + 1)`, the universe of the total site's objects, and
not in the `Type u` of the small model.

`Stacks.Topology.lan_preservesFiniteLimits_of_flat` is applied with its universes written out.
Left to inference they are solved from the universe arguments of `PreservesFiniteLimits` rather
than from those of `CategoryTheory.Functor.lan`, which leaves the coefficient universe as an
unsolved `max u ?v` against `u + 1`.

## Main definitions

* `Stacks.Topology.Simplicial.qcSliceCoverings`: the covering families of `LC_qc/U_n`.
* `Stacks.Topology.Simplicial.qcTotalTopology`: the topology of `(LC_qc/U)_total`.
* `Stacks.Topology.Simplicial.qcTotalHomMk`: a morphism of the total category into the
  comparison object of an open of its own simplicial degree.
* `Stacks.Topology.Simplicial.qcTotalComparisonMorphismOfTopoi`: the morphism of topoi `h`.

## Main results

* `Stacks.Topology.Simplicial.qcTotalComparisonFunctor_representablyFlat`: the comparison
  functor is representably flat.
* `Stacks.Topology.Simplicial.qcTotalComparisonFunctor_coverPreserving` and
  `Stacks.Topology.Simplicial.qcTotalComparisonFunctor_isContinuous`: it is cover-preserving,
  hence continuous — the first clause of Tag 00X1.
* `Stacks.Topology.Simplicial.qcTotalComparisonFunctor_isMorphismOfSites`: it is a morphism of
  sites, which adds exactness of `u_s` — the second clause of Tag 00X1.

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace Stacks.Topology.Simplicial

open Stacks.Topology

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
  (U : SimplicialObject S.category)

/-- The covering families of `LC_qc/U_n`. -/
def qcSliceCoverings (n : SimplexCategoryᵒᵖ) :
    Covering.{u + 1, u, u + 1} (Over (U.obj n)) → Prop := fun 𝒰 ↦
  Sieve.generate 𝒰.2.presieve₀ ∈ S.qcSite.grothendieckTopology.over (U.obj n) 𝒰.1

/-- The topology of the total site `(LC_qc/U)_total`. -/
def qcTotalTopology :
    GrothendieckTopology (Grothendieck (U ⋙ Over.mapFunctor S.category)) :=
  SimplicialCoverings.totalTopology (U ⋙ Over.mapFunctor S.category) (qcSliceCoverings S U)

/-- A covering family of one degree, included into the total category, is a covering family of
the total site. -/
theorem qcTotalIota_coverPreserving (n : SimplexCategoryᵒᵖ) :
    CoverPreserving (S.qcSite.grothendieckTopology.over (U.obj n)) (qcTotalTopology S U)
      (Grothendieck.ι (U ⋙ Over.mapFunctor S.category) n) := by
  refine ⟨fun {P T} hT => ?_⟩
  have hcov : qcSliceCoverings S U n ⟨P, T.arrows.preZeroHypercover⟩ := by
    show Sieve.generate (T.arrows.preZeroHypercover).presieve₀ ∈ _
    rwa [Presieve.presieve₀_preZeroHypercover, Sieve.generate_sieve]
  have hgen : Sieve.generate ((T.arrows.preZeroHypercover.map
        (Grothendieck.ι (U ⋙ Over.mapFunctor S.category) n)).presieve₀) ∈
      qcTotalTopology S U ((Grothendieck.ι (U ⋙ Over.mapFunctor S.category) n).obj P) :=
    Precoverage.generate_mem_toGrothendieck ⟨_, ⟨_, hcov, rfl⟩, rfl⟩
  refine (qcTotalTopology S U).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  exact Presieve.ofArrows_le_iff.2 fun i => Sieve.image_mem_functorPushforward _ T i.2

/-- The image of a point of the source of a morphism into a comparison object lies in the
open: the structure morphism of an open subspace has that open as its image. -/
theorem qcComparisonObj_hom_mem {n : SimplexCategoryᵒᵖ} {P : Over (U.obj n)}
    {A : SimplicialOpen (qcSimplicialSpace S U)} {α : n ⟶ A.degree}
    (h : (Over.map (U.map α)).obj P ⟶ qcComparisonObj S U A) (p : P.left.obj) :
    ((U.map α) : (U.obj n).obj → (U.obj A.degree).obj)
        ((P.hom : P.left.obj → (U.obj n).obj) p) ∈ A.toOpens := by
  have key : ((qcComparisonObj S U A).hom :
      (qcComparisonObj S U A).left.obj → (U.obj A.degree).obj) (h.left p) =
      ((U.map α) : (U.obj n).obj → (U.obj A.degree).obj)
        ((P.hom : P.left.obj → (U.obj n).obj) p) := by
    rw [← ConcreteCategory.comp_apply, Over.w h]
    exact ConcreteCategory.comp_apply _ _ p
  rw [← key]
  exact S.opensToSlice_hom_mem A.toOpens (h.left p)

/-- A morphism of the total category into the comparison object of an open in its own
simplicial degree, given that the image of the source lies in that open. It is unique, by
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.over_hom_opensToSlice_ext`. -/
def qcTotalHomMk (V : Grothendieck (U ⋙ Over.mapFunctor S.category))
    (W : Opens ((qcSimplicialSpace S U).obj V.base))
    (hW : ∀ p : V.fiber.left.obj,
      (V.fiber.hom : V.fiber.left.obj → (U.obj V.base).obj) p ∈ W) :
    V ⟶ (qcTotalComparisonFunctor S U).obj ⟨V.base, W⟩ where
  base := 𝟙 V.base
  fiber :=
    (S.nonempty_over_hom_opensToSlice
      ((Over.map (U.map (𝟙 V.base))).obj V.fiber) W (by
        intro p
        have h : (((Over.map (U.map (𝟙 V.base))).obj V.fiber).hom :
            V.fiber.left.obj → (U.obj V.base).obj) p =
            (V.fiber.hom : V.fiber.left.obj → (U.obj V.base).obj) p := by
          change ((V.fiber.hom ≫ U.map (𝟙 V.base)) :
            V.fiber.left.obj → (U.obj V.base).obj) p = _
          rw [U.map_id, Category.comp_id]
        rw [h]
        exact hW p)).some

/-- **The comparison functor of Tag 0DAF is representably flat.** For an object `(n, P/U_n)` of
the total site, the simplicial opens receiving it form a cofiltered category: the pair of a
simplex map `α` out of `n` and an open of `|U|_{A.degree}` containing the image of `P` is
cofinally refined by taking `α` to be the identity and intersecting, and a parallel pair of
refinements is equalized the same way, because a morphism of simplicial opens is determined by
its simplex map.

Flatness is what supplies both clauses of Tag 00X1: it gives
`CategoryTheory.compatiblePreservingOfFlat`, hence continuity from cover-preservation alone,
and it gives left exactness of the left Kan extension, hence exactness of `u_s`. -/
theorem qcTotalComparisonFunctor_representablyFlat :
    RepresentablyFlat (qcTotalComparisonFunctor S U) := by
  constructor
  intro V
  refine { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }
  · intro A B
    refine ⟨StructuredArrow.mk (qcTotalHomMk S U V
        ((Opens.map ((qcSimplicialSpace S U).map A.hom.base)).obj A.right.toOpens ⊓
          (Opens.map ((qcSimplicialSpace S U).map B.hom.base)).obj B.right.toOpens)
        (fun p => ⟨qcComparisonObj_hom_mem S U A.hom.fiber p,
          qcComparisonObj_hom_mem S U B.hom.fiber p⟩)),
      StructuredArrow.homMk ⟨A.hom.base, fun _ hx => hx.1⟩ ?_,
      StructuredArrow.homMk ⟨B.hom.base, fun _ hx => hx.2⟩ ?_, trivial⟩ <;>
    exact Grothendieck.ext _ _ (Category.id_comp _) (S.over_hom_opensToSlice_ext _ _)
  · intro A B a b
    refine ⟨StructuredArrow.mk (qcTotalHomMk S U V
        ((Opens.map ((qcSimplicialSpace S U).map A.hom.base)).obj A.right.toOpens)
        (fun p => qcComparisonObj_hom_mem S U A.hom.fiber p)),
      StructuredArrow.homMk ⟨A.hom.base, fun _ hx => hx⟩ ?_, ?_⟩
    · exact Grothendieck.ext _ _ (Category.id_comp _) (S.over_hom_opensToSlice_ext _ _)
    · apply StructuredArrow.hom_ext
      apply SimplicialOpen.Hom.ext
      show A.hom.base ≫ a.right.base = A.hom.base ≫ b.right.base
      exact congrArg Grothendieck.Hom.base
        ((StructuredArrow.w a).trans (StructuredArrow.w b).symm)
  · exact ⟨StructuredArrow.mk (qcTotalHomMk S U V ⊤ (fun _ => trivial))⟩

/-- On an arrow of one simplicial degree the comparison functor is the Tag 09X3 comparison of
that degree followed by the inclusion of the degree's fibre. On objects this is
`Stacks.Topology.Simplicial.qcTotalComparisonFunctor_obj_levelFunctor`; on arrows there is
nothing to check, both sides being morphisms into a comparison object. -/
theorem qcTotalComparisonFunctor_map_levelFunctor (n : SimplexCategoryᵒᵖ)
    {V W : Opens ((qcSimplicialSpace S U).obj n)} (t : V ⟶ W) :
    (qcTotalComparisonFunctor S U).map ((levelFunctor (qcSimplicialSpace S U) n).map t) =
      (Grothendieck.ι (U ⋙ Over.mapFunctor S.category) n).map
        ((S.opensToSlice (U.obj n)).1.map t) :=
  Grothendieck.ext _ _ rfl (S.over_hom_opensToSlice_ext _ _)

/-- The Tag 09X3 comparison of one simplicial degree is cover-preserving for the *quasi-compact*
localized topology, not only the Zariski one: an open covering is a Zariski covering, and the
Zariski topology on a slice is coarser than the quasi-compact one
(`…zariskiTopology_over_le_qc`). -/
theorem opensToSlice_coverPreserving_qc (n : SimplexCategoryᵒᵖ) :
    CoverPreserving (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (S.qcSite.grothendieckTopology.over (U.obj n)) (S.opensToSlice (U.obj n)).1 := by
  have hc : (S.opensToSlice (U.obj n)).1.IsContinuous
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (S.zariskiTopology.over (U.obj n)) := S.opensToSlice_isContinuous (U.obj n)
  refine ⟨fun {_ _} hS => ?_⟩
  exact S.zariskiTopology_over_le_qc (U.obj n) _
    ((CoverPreserving.of_isContinuous (F := (S.opensToSlice (U.obj n)).1)
      (Opens.grothendieckTopology ((qcSimplicialSpace S U).obj n))
      (S.zariskiTopology.over (U.obj n))).cover_preserve hS)

/-- **The comparison functor of Tag 0DAF is cover-preserving**, which is the first clause of
Tag 00X1. A covering sieve of the site of Tag 09VL contains a covering family lying in a single
simplicial degree, so it is detected by the cocontinuous inclusion of that degree
(`…levelFunctor_isCocontinuous`); there it becomes an open covering, which the Tag 09X3
comparison carries to a covering of the localized quasi-compact site, and the inclusion of the
degree's fibre carries that to a covering family of the total site. -/
theorem qcTotalComparisonFunctor_coverPreserving :
    CoverPreserving (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
      (qcTotalTopology S U) (qcTotalComparisonFunctor S U) := by
  refine ⟨fun {A T} hT => ?_⟩
  have := levelFunctor_isCocontinuous (qcSimplicialSpace S U) A.degree
  have hpull : T.functorPullback (levelFunctor (qcSimplicialSpace S U) A.degree) ∈
      Opens.grothendieckTopology ((qcSimplicialSpace S U).obj A.degree) A.toOpens :=
    Functor.cover_lift (levelFunctor (qcSimplicialSpace S U) A.degree) _ _ hT
  have hcomp := (CoverPreserving.comp _ _ (opensToSlice_coverPreserving_qc S U A.degree)
    (qcTotalIota_coverPreserving S U A.degree)).cover_preserve hpull
  refine (qcTotalTopology S U).superset_covering ?_ hcomp
  intro Z f hf
  obtain ⟨Y, g, h, hg, hfac⟩ := hf
  refine ⟨(levelFunctor (qcSimplicialSpace S U) A.degree).obj Y,
    (levelFunctor (qcSimplicialSpace S U) A.degree).map g, h, hg, ?_⟩
  rw [hfac]
  exact congrArg (fun k => h ≫ k)
    (qcTotalComparisonFunctor_map_levelFunctor S U A.degree g).symm

/-- **The comparison functor of Tag 0DAF is continuous**, the first clause of Tag 00X1. It is
cover-preserving and representably flat, so it is compatible-preserving as well
(`CategoryTheory.compatiblePreservingOfFlat`). -/
theorem qcTotalComparisonFunctor_isContinuous :
    (qcTotalComparisonFunctor S U).IsContinuous
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcTotalTopology S U) := by
  have := qcTotalComparisonFunctor_representablyFlat S U
  exact (Functor.isContinuous_iff_coverPreserving
    (F := qcTotalComparisonFunctor S U)
    (J := SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U))
    (K := qcTotalTopology S U)).2 (qcTotalComparisonFunctor_coverPreserving S U)

/-- **The comparison functor of Tag 0DAF is a morphism of sites**, for sections in the universe
in which the total site's objects live.
This is the full content of Tag 00X1 for it: continuity is
`Stacks.Topology.Simplicial.qcTotalComparisonFunctor_isContinuous`, and `u_s` is exact because
the functor is representably flat, so its left Kan extension on presheaves is left exact
(`Stacks.Topology.lan_preservesFiniteLimits_of_flat`) and the chosen `u_s` is that extension
followed by sheafification.

As in `Stacks.Topology.Simplicial.SimplicialOpen.pullback_isMorphismOfSites_large`, the
universe-general `IsMorphismOfSites` is used rather than the small-category-only
`CategoryTheory.Functor.IsMorphismOfSites`: the site of Tag 09VL has objects in `Type u` but
morphisms in `Type`, and `LC_qc/U_n` has objects in `Type (u + 1)` and morphisms in `Type u`, so
neither site is a `SmallCategory` and the two do not share a universe. -/
theorem qcTotalComparisonFunctor_isMorphismOfSites :
    IsMorphismOfSites.{u + 1} (qcTotalComparisonFunctor S U)
      (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcTotalTopology S U) := by
  have := qcTotalComparisonFunctor_representablyFlat S U
  have := qcTotalComparisonFunctor_isContinuous S U
  refine ⟨?_⟩
  refine ⟨Functor.sheafPullbackConstruction.sheafPullback (qcTotalComparisonFunctor S U)
    (Type (u + 1))
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcTotalTopology S U), ?_⟩
  refine ⟨⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (qcTotalComparisonFunctor S U) (Type (u + 1))
    (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (qcTotalTopology S U)⟩, ?_⟩
  have : PreservesFiniteLimits ((qcTotalComparisonFunctor S U).op.lan :
      ((SimplicialOpen (qcSimplicialSpace S U))ᵒᵖ ⥤ Type (u + 1)) ⥤
        ((Grothendieck (U ⋙ Over.mapFunctor S.category))ᵒᵖ ⥤ Type (u + 1))) :=
    Stacks.Topology.lan_preservesFiniteLimits_of_flat.{u + 1, 0, u, u, u + 1, u + 2, u + 1}
      (qcTotalComparisonFunctor S U) (fun _ => inferInstance)
  exact inferInstance

/-- **The upper horizontal arrow of the diagram of Tag 0DAF**, as a morphism of topoi
`h : Sh((LC_qc/U)_total) ⟶ Sh(U_Zar)`.

It exists for an arbitrary simplicial object `U` of `LC_qc`: no augmentation, no hypercovering
and no properness hypothesis enters. Its inverse image `h^{-1} : Sh(U_Zar) ⥤ Sh((LC_qc/U)_total)`
is the canonical `u_s`, by `IsMorphismOfSites.morphismOfTopoi_inverseImage`. -/
def qcTotalComparisonMorphismOfTopoi :
    MorphismOfTopoi (Sheaf (qcTotalTopology S U) (Type (u + 1)))
      (Sheaf (SimplicialOpen.grothendieckTopology (qcSimplicialSpace S U)) (Type (u + 1))) :=
  (qcTotalComparisonFunctor_isMorphismOfSites S U).morphismOfTopoi

end Stacks.Topology.Simplicial

end
