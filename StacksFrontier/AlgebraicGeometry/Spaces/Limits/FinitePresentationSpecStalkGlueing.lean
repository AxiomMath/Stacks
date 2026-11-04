module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsolutelyQuasiSeparatedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationColimitRealised
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SpecStalkGlueingSquares

/-!
# Glueing algebraic spaces of finite presentation along `Spec 𝒪_{S, s}`

`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing` proves the
formal combination behind [Stacks, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90): for an
object `M` of the big fppf category over `S` carrying a cofiltered system of open neighbourhoods
`W i` of the point `s` complementary to `U`, and an object `N` over the system of the `W i ∩ U`,
*such that* base change exhibits `FP_M` as the cofiltered `2`-colimit of the `FP_{W i}` and `FP_N`
as that of the `FP_{W i ∩ U}`, the comparison functor `FP_S ⥤ FP_U ×_{FP_N} FP_M` is an
equivalence.  This file instantiates that at the system of the tag and discharges both colimit
hypotheses, so that the tag holds with no hypothesis beyond its own: `s` is a closed point of `S`
and the inclusion of `U = S ∖ {s}` is quasi-compact.

The system is the affine open neighbourhoods of `s` contained in a fixed one, `W₀`, which is the
index category on which both halves of the data are available — the overlaps `W ∩ U` are opens of
`W₀` and so are only defined relative to a chosen `W₀`; see
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.SpecStalkGlueingData`.  The vertices are
`M = Spec 𝒪_{S, s}` and `N = V`, the preimage of `U` in it, which is the tag's
`V = Spec 𝒪_{S, s} ∖ {s}` by
`AlgebraicGeometry.toScheme_obj_opensSpecStalkSiteObj_eq_compl_closedPoint` — the identification
the tag makes silently when it writes the closed point of `Spec 𝒪_{S, s}` as `s`.

## The four compatibilities

Besides the two cartesian squares and the two colimit identifications, the glueing theorem asks
that the two cones be compatible with the legs of the squares and that the legs be compatible with
the transition morphisms.  All four hold by terminality rather than by a computation: every stage
of either system, and `U` itself, has a monomorphism as its structure morphism to `S`, so it
receives at most one morphism from any object of the site
(`AlgebraicGeometry.BigFppfOver.subsingleton_hom_opensObj` and
`AlgebraicGeometry.subsingleton_hom_affineOpenNhdsSiteDiagram_obj`).

## Main results

* `FinitePresentationSpacesOver.isFinitePresentationColimit_restrictedSpecStalkSiteCone`:
  the `hloc` of the glueing theorem for the *restricted* system of neighbourhoods, which is the
  one the overlaps are indexed by.  It carries no hypothesis.
* `AlgebraicGeometry.toScheme_obj_opensSpecStalkSiteObj_eq_compl_closedPoint`: the vertex of the
  system of overlaps is the tag's `V = Spec 𝒪_{S, s} ∖ {s}`, the complement of the closed point.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_specStalk`:
  **Stacks 0E90**, with both colimit hypotheses discharged.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_closedPoints`:
  the same with `U` taken to be the complement of a closed point, which is the tag's own wording.

## References

* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : S)
  (W₀ : AffineOpenNhds S s) (U : S.Opens)

/-! ### The compatibilities of the two cones with the legs of the squares -/

/-- **The cone on the overlaps is compatible with the morphisms to `U`.**  This is the `hpNU`
hypothesis of Stacks 0E90.  Both sides are morphisms to an open of `S`, of which there is at most
one from any object of the site. -/
theorem opensSpecStalkSiteπ_comp_stageToU (j : Over W₀) :
    (opensSpecStalkSiteCone B S hS s W₀ U).π.app j ≫ opensSpecStalkStageToU B S hS s W₀ U j =
      opensSpecStalkApexToU B S hS s W₀ U :=
  @Subsingleton.elim _ (BigFppfOver.subsingleton_hom_opensObj B S hS _ U) _ _

/-- **The cone on the overlaps is compatible with the morphisms to the neighbourhoods and with the
cone on them.**  This is the `hpNW` hypothesis of Stacks 0E90.  Both sides are morphisms to an open
of `S`. -/
theorem opensSpecStalkSiteπ_comp_stageToW (j : Over W₀) :
    (opensSpecStalkSiteCone B S hS s W₀ U).π.app j ≫ opensSpecStalkStageToW B S hS s W₀ U j =
      opensSpecStalkApexToM B S hS s W₀ U ≫
        (restrictedSpecStalkSiteCone B S hS s W₀).π.app j :=
  @Subsingleton.elim _ (subsingleton_hom_affineOpenNhdsSiteDiagram_obj B S hS s _ j.left) _ _

/-- **The morphisms from the overlaps to `U` are compatible with the transition morphisms of the
system of overlaps.**  This is the `hiUn` hypothesis of Stacks 0E90. -/
theorem opensSpecStalkSiteDiagram_map_comp_stageToU {j k : Over W₀} (e : k ⟶ j) :
    (opensSpecStalkSiteDiagram B S hS s W₀ U).map e ≫ opensSpecStalkStageToU B S hS s W₀ U j =
      opensSpecStalkStageToU B S hS s W₀ U k :=
  @Subsingleton.elim _ (BigFppfOver.subsingleton_hom_opensObj B S hS _ U) _ _

/-- **The morphisms from the overlaps to the neighbourhoods are compatible with the transition
morphisms of the two systems.**  This is the `hiWn` hypothesis of Stacks 0E90. -/
theorem opensSpecStalkSiteDiagram_map_comp_stageToW {j k : Over W₀} (e : k ⟶ j) :
    (opensSpecStalkSiteDiagram B S hS s W₀ U).map e ≫ opensSpecStalkStageToW B S hS s W₀ U j =
      opensSpecStalkStageToW B S hS s W₀ U k ≫
        (restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).map e :=
  @Subsingleton.elim _ (subsingleton_hom_affineOpenNhdsSiteDiagram_obj B S hS s _ j.left) _ _

/-! ### The vertex is the `V` of the tag -/

/-- **The preimage of the complement of `s` in `Spec 𝒪_{S, s}` is the complement of the closed
point.**  The tag writes its `V` as `Spec 𝒪_{S, s} ∖ {s}`, identifying the closed point of
`Spec 𝒪_{S, s}` with `s`; the development builds it as the preimage of `U = S ∖ {s}` along
`AlgebraicGeometry.Scheme.fromSpecStalk`, which is the spelling its proof of the cartesian square
`V = U ×_S Spec 𝒪_{S, s}` uses.  The two agree because `Spec 𝒪_{S, s} ⟶ S` is a preimmersion,
hence injective, and takes the closed point to `s`. -/
theorem coe_opensSpecStalkApexOpen_eq_compl_closedPoint (hUc : (U : Set S) = {s}ᶜ) :
    (opensSpecStalkApexOpen S s W₀ U : Set (Spec (S.presheaf.stalk s))) =
      {IsLocalRing.closedPoint (S.presheaf.stalk s)}ᶜ := by
  have h : (opensSpecStalkApexOpen S s W₀ U : Set (Spec (S.presheaf.stalk s))) =
      ⇑(S.fromSpecStalk s) ⁻¹' (U : Set S) :=
    congrArg (fun V : (Spec (S.presheaf.stalk s)).Opens =>
      (V : Set (Spec (S.presheaf.stalk s)))) (specStalkCone_π_preimage S s W₀ U)
  rw [h, hUc]
  ext p
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact not_congr ((IsPreimmersion.isEmbedding (S.fromSpecStalk s)).injective.eq_iff'
    Scheme.fromSpecStalk_closedPoint)

/-- **The vertex of the glueing is the `V` of Stacks 0E90.**  When `U` is the complement of `s`,
the underlying scheme of the vertex `N` is any open of `Spec 𝒪_{S, s}` whose underlying set is the
complement of the closed point — that is, `V = Spec 𝒪_{S, s} ∖ {s}`. -/
theorem toScheme_obj_opensSpecStalkSiteObj_eq_compl_closedPoint (hUc : (U : Set S) = {s}ᶜ)
    (V : (Spec (S.presheaf.stalk s)).Opens)
    (hV : (V : Set (Spec (S.presheaf.stalk s))) =
      {IsLocalRing.closedPoint (S.presheaf.stalk s)}ᶜ) :
    (BigFppfOver.toScheme B S hS).obj (opensSpecStalkSiteObj B S hS s W₀ U) = V.toScheme := by
  rw [toScheme_obj_opensSpecStalkSiteObj]
  exact congrArg Scheme.Opens.toScheme (TopologicalSpace.Opens.ext
    ((coe_opensSpecStalkApexOpen_eq_compl_closedPoint S s W₀ U hUc).trans hV.symm))

namespace FinitePresentationSpacesOver

/-! ### The colimit identification for the restricted system of neighbourhoods -/

/-- **Base change exhibits the algebraic spaces of finite presentation over `Spec 𝒪_{S, s}` as the
cofiltered `2`-colimit of those over the affine open neighbourhoods of `s` contained in `W₀`.**
This is the `hloc` hypothesis of Stacks 0E90, for the restricted system — the one over which the
overlaps `W ∩ U` are indexed.

It carries no hypothesis.  The companion
`AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_specStalkSiteCone` is
the same statement for the unrestricted system; the restriction is along
`CategoryTheory.Over.forget`, which is initial, so the restricted cone is still a limit of schemes
(`AlgebraicGeometry.isLimitMapConeRestrictedSpecStalkSiteCone`) and the three clauses of
Stacks 07SK apply to it verbatim. -/
theorem isFinitePresentationColimit_restrictedSpecStalkSiteCone :
    IsFinitePresentationColimit B S hS (restrictedAffineOpenNhdsSiteDiagram B S hS s W₀)
      (restrictedSpecStalkSiteCone B S hS s W₀).pt
      (fun j => (restrictedSpecStalkSiteCone B S hS s W₀).π.app j)
      (fun {_ _} e => (restrictedSpecStalkSiteCone B S hS s W₀).w e) :=
  isFinitePresentationColimit_of_isLimitMapCone B S hS
    (fun {_ _} e =>
      isAffineHom_toScheme_map_restrictedAffineOpenNhdsSiteDiagram_map B S hS s W₀ e)
    (isLimitMapConeRestrictedSpecStalkSiteCone B S hS s W₀)
    (fun k => Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _
      (isAffine_toScheme_restrictedAffineOpenNhdsSiteDiagram_obj B S hS s W₀ k))
    (fun k => Space.isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS B.contains_terminal _
      (isAffine_toScheme_restrictedAffineOpenNhdsSiteDiagram_obj B S hS s W₀ k))

/-! ### The equivalence -/

/-- **Stacks 0E90.**  Let `S` be a scheme, let `s` be a point of `S` and let `U` be an open of `S`
whose underlying set is the complement of `s` — so `s` is a closed point of `S` — with
quasi-compact inclusion morphism.  Then for every affine open neighbourhood `W₀` of `s` the
comparison functor
`FP_S ⥤ FP_U ×_{FP_V} FP_{Spec 𝒪_{S, s}}`
is an equivalence, where `FP_T` is the category of algebraic spaces of finite presentation over
`T` and `V` is the vertex of the system of overlaps, whose underlying scheme is the complement of
the closed point of `Spec 𝒪_{S, s}` — the tag's `V` —
by `AlgebraicGeometry.toScheme_obj_opensSpecStalkSiteObj_eq_compl_closedPoint`.

Every input is unconditional.  The two cartesian squares are
`AlgebraicGeometry.isPullback_opensSpecStalkApex` and
`AlgebraicGeometry.isPullback_opensSpecStalkStage`; the four compatibilities hold by terminality;
the colimit identification over the neighbourhoods is
`FinitePresentationSpacesOver.isFinitePresentationColimit_restrictedSpecStalkSiteCone`,
which has no hypothesis, and the one over the overlaps is
`AlgebraicGeometry.FinitePresentationSpacesOver.isFinitePresentationColimit_opensSpecStalkSiteCone`,
whose single hypothesis is retrocompactness of `U` — the form the tag's quasi-compactness of
`U → S` takes, by `AlgebraicGeometry.isRetrocompact_of_quasiCompact_ι`.  Quasi-compactness of
`U → S` is used in that one place, exactly as in the tag's proof. -/
@[stacks 0E90 "the equivalence, unconditionally: for a point `s` of `S` whose complement is an \
open `U` with quasi-compact inclusion — the tag's closed point and quasi-compact `U → S` — the \
comparison functor `FP_S ⥤ FP_U ×_{FP_V} FP_{Spec O_{S,s}}` is an equivalence, with \
`V = Spec O_{S,s} ∖ {s}` the complement of the closed point, which the vertex of the system of \
overlaps is by `toScheme_obj_opensSpecStalkSiteObj_eq_compl_closedPoint`. The two colimit \
identifications that the general \
theorem `isEquivalence_glueingFunctor_of_colimit` carries as hypotheses are discharged here from \
Stacks 07SK and the identification of `Spec O_{S,s}` and of its puncture as the limits of the \
affine open neighbourhoods of `s` and of their intersections with `U`"]
theorem isEquivalence_glueingFunctor_specStalk (hUc : (U : Set S) = {s}ᶜ)
    (hqc : QuasiCompact U.ι) :
    (glueingFunctor B S hS (isPullback_opensSpecStalkApex B S hS s W₀ U).w).IsEquivalence :=
  isEquivalence_glueingFunctor_of_colimit B S hS
    (isPullback_opensSpecStalkApex B S hS s W₀ U)
    (isPullback_opensSpecStalkStage B S hS s W₀ U)
    (opensSpecStalkSiteπ_comp_stageToU B S hS s W₀ U)
    (opensSpecStalkSiteπ_comp_stageToW B S hS s W₀ U)
    (fun {_ _} e => opensSpecStalkSiteDiagram_map_comp_stageToU B S hS s W₀ U e)
    (fun {_ _} e => opensSpecStalkSiteDiagram_map_comp_stageToW B S hS s W₀ U e)
    (isFinitePresentationColimit_restrictedSpecStalkSiteCone B S hS s W₀)
    (isFinitePresentationColimit_opensSpecStalkSiteCone B S hS s W₀ U
      (isRetrocompact_of_quasiCompact_ι U))
    (BigFppfOver.isOpenImmersion_opensObj_hom B S hS U)
    (isOpenImmersion_restrictedAffineOpenNhdsSiteDiagram_obj_hom B S hS s W₀)
    (BigFppfOver.range_opensObj_hom_eq_compl_singleton B S hS U hUc)
    (mem_range_restrictedAffineOpenNhdsSiteDiagram_obj_hom B S hS s W₀)

/-- **Stacks 0E90 in the tag's own wording**: `s` is a closed point of `S` and `U` is taken to be
the open complement `S ∖ {s}`, whose inclusion is assumed quasi-compact.  This is
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_specStalk` at that
`U`; the equation `(U : Set S) = {s}ᶜ` holds by definition there, so nothing is assumed that the
tag does not grant. -/
theorem isEquivalence_glueingFunctor_closedPoints (hs : s ∈ closedPoints S)
    (hqc : QuasiCompact (Scheme.Opens.ι (X := S)
      ⟨{s}ᶜ, isOpen_compl_singleton_of_mem_closedPoints hs⟩)) :
    (glueingFunctor B S hS (isPullback_opensSpecStalkApex B S hS s W₀
      ⟨{s}ᶜ, isOpen_compl_singleton_of_mem_closedPoints hs⟩).w).IsEquivalence :=
  isEquivalence_glueingFunctor_specStalk B S hS s W₀ _ rfl hqc

end FinitePresentationSpacesOver

end AlgebraicGeometry

end
