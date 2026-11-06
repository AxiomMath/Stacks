module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationStabilizerPart
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleQuotientMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stabilizer-supported membership criterion for Stacks 0DTC

Stacks 0DTC is Stacks 03FM with the strong splitting situation of Stacks 04RL replaced by the
splitting situation of Stacks 0DTB and *strongly split* replaced by *split*.  Both proofs run on
an open `Z_u` of the scheme-theoretic fibre `F_u = R ×_{s, U} Spec κ(u)` which is finite over
`κ(u)`, and they differ in which open that is: for Stacks 04RL it is the piece supported on the
arrows with both endpoints at `u`
(`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer`), while for
Stacks 0DTB it is the piece supported on the arrows underlying the points of the stabilizer group
scheme over `u` (`AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer`),
which is in general a proper subset of the former.

This file supplies, for the second open, the two inputs that
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingExistence.lean` have
only for the first.

The first is the **membership criterion**.  It is proved here in a form that does not mention
either support condition: a section of the ambient fibre product `Spec κ(u) ×_{u, U, s} R` over a
scheme of the site factors through the open subspace which an open `W` of `F_u` cuts out exactly
when every point of the test scheme is carried by the arrow to a point of `W`, read in `R`
(`AlgebraicGeometry.Space.exists_lift_fibreOpenPair_iff`).  Specializing the support gives back
the criterion of Stacks 04RL and, for the first time, the criterion for Stacks 0DTB
(`AlgebraicGeometry.Space.exists_lift_stabilizerFibrePair_iff`).

The second is that the **stabilizer-supported open contains the unit**.  In the strong splitting
situation this is immediate, because the unit arrow has target `u` and the open is supported on
the arrows with target `u`.  For the stabilizer-supported open it is not, and the identification
of the unit of the finite part with the Yoneda image of the identity `e : U ⟶ R` of the groupoid
scheme — `Stacks.Groupoids.GroupoidScheme.unit_hom_eq_yoneda_map_identity` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationQuasiSplittingPoint.lean` — is
*not* what settles it.  What settles it is that the unit is a **section**: its source and its
target are both the base point, so `AlgebraicGeometry.exists_stabilizer_lift` factors it through
the stabilizer group scheme on the nose, and the pointwise condition follows.  Only `unit_source`
and `AlgebraicGeometry.Space.FinitePartUniversalOpen.unit_comp_target` are used, exactly as in
the strong case.

With both inputs in hand the étale neighbourhood and the point of Stacks 0DTC are produced:
`Stacks.Groupoids.GroupoidScheme.exists_etale_point_of_splittingSituation` is the exact analogue,
in Situation 0DTB, of `AlgebraicGeometry.Space.exists_etale_point_of_strongSplittingSituation`,
and it proves **three of the four assertions of Stacks 0DTC**.  The fourth, that `R|_{U'}` is
split over `u'`, is not proved here; it is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStabilizerContainment.lean`,
and the implementation notes below say what that file had to do.

## Main results

* `AlgebraicGeometry.exists_lift_of_immersion_of_isReduced`: a morphism out of a reduced scheme
  whose set-theoretic image lies in the image of an immersion factors through it.
* `AlgebraicGeometry.Space.exists_lift_fibreOpenPair_iff`: **the membership criterion for the
  pair `(u, Z_u)`, with no hypothesis on the support of the open**.
* `AlgebraicGeometry.Space.exists_lift_stabilizerFibrePair_iff`: **the membership criterion for
  the stabilizer-supported open of Stacks 0DTB** — a section lies in the open subspace exactly
  when its arrow factors through `AlgebraicGeometry.stabilizerArrow` over `u`, pointwise.
* `AlgebraicGeometry.Space.exists_lift_fibrePair_iff'`: the criterion for the open of Stacks
  04RL, recovered from the neutral form.
* `AlgebraicGeometry.Space.mem_fiberOpen_iff_target_of_isReduced`: **over a reduced scheme the
  stabilizer-supported open of Situation 0DTB is cut out by the target condition of Situation
  04RL** — the two supports, which differ, impose the same condition on reduced sections.
* `AlgebraicGeometry.Space.mem_fiber_of_stabilizer_section`: a section of the arrow scheme whose
  source and target agree lands pointwise in the stabilizer-supported open.
* `AlgebraicGeometry.Space.unitFibrePoint_mem_stabilizer` and
  `AlgebraicGeometry.Space.containsSection_fibreFiniteOpenSubspace_stabilizer`: **the
  stabilizer-supported pair `(u, Z_u)` contains the unit**, which is the condition of Stacks 04RQ
  placing it in `(R_s/U, e)_fin`.
* `AlgebraicGeometry.Space.etaleLocalStabilizerFibrePoint` and
  `AlgebraicGeometry.Space.lies_over_stabilizerFibrePoint`: **the point `u'` of Situation 0DTB**,
  and the fact that it lies over `u`.
* `Stacks.Groupoids.GroupoidScheme.exists_etale_point_of_splittingSituation`: **Stacks 0DTC, the
  étale neighbourhood and the point** — three of its four assertions.

## Implementation notes

### The membership criterion

`AlgebraicGeometry.Space.exists_lift_fibrePair_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationArrowContainment.lean` uses its
support hypothesis `hW` exactly once, in its last line.  Everything before that line is the
descent of the membership question through Yoneda to the site and then to schemes, where it
becomes a containment of set-theoretic images.  That part is transcribed here unchanged, with
the final step left as the containment itself; the statement proved is therefore the same
theorem with the support condition abstracted, and the two specializations are three-line
consequences.

Membership is a purely topological condition because `Z_u` is an *open* subscheme of the fibre,
which is why the criterion is a pointwise one.

Injectivity of the inclusion of the fibre is taken from the homeomorphism
`AlgebraicGeometry.Scheme.Hom.fiberHomeo` onto the set-theoretic preimage, as in
`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer`, rather than from
an embedding instance.

### Why the chain to the point is retranscribed

`AlgebraicGeometry.Space.etaleLocalFibrePoint` and the seven declarations leading to it take the
support hypothesis `hW` of Situation 04RL as an argument, and use it only to produce the
set-theoretic containment `AlgebraicGeometry.Space.unitFibreSection_range_le`.  A different
hypothesis cannot be substituted into a declaration that names `hW` in its type, so the chain
`unitOpenLift`, `unitOpenSection`, `containsSection_fibreFiniteOpenSubspace`,
`mem_finitePartWithSection`, `etaleLocalFibrePoint`, `objectProjection_fibrePoint`,
`lies_over_fibrePoint` is repeated here with the suffix `Stabilizer`, the proofs transcribed
unchanged and only the containment replaced.

### What is not reached here: the splitting condition of Stacks 0DTC

What remains after this file is the `contains_stabilizer` field of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Splitting`: every point of the stabilizer of
`R|_{U'}` over `u'` lies in `Z_univ`.  The arrow containment of Stacks 03FM is obtained in
`EtaleLocalizationArrowContainment.lean` from
`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_toRestriction_eq`, which needs a predicate
`P` on arrows that cuts out the open subspaces named by the relevant sections of `U'`
(`AlgebraicGeometry.Space.FinitePartUniversalOpen.CutsOut`) and **depends on an arrow only through
its target**.  For Situation 0DTB the predicate the criterion above forces is membership in the
set-theoretic image of `AlgebraicGeometry.stabilizerArrow` over `u`, and that predicate is *not*
target-invariant: the image of `stabilizerArrow` is the preimage under `(t, s)` of the image of
the diagonal of `U`, and a point of `U ×_S U` whose two projections are both `u` need not lie on
the diagonal.  So `AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOut` does not
apply, and no choice of target-invariant predicate cuts out the stabilizer-supported open.

`AlgebraicGeometry.Space.mem_fiberOpen_iff_target_of_isReduced` says the obstruction disappears on
*reduced* test objects, where the two predicates agree and the target-invariant one is available.
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStabilizerContainment.lean`
exploits that: it replaces `CutsOut` by the two-argument
`AlgebraicGeometry.Space.FinitePartUniversalOpen.CutsOutRel`, which may see the section of `U'`
as well as the arrow, and reads membership on the spectra of the residue fields of the test
object, which are reduced.  No extensionality principle for
`AlgebraicGeometry.Space.FiniteOpenSubspace` on reduced sections is needed, and
`Stacks.Groupoids.GroupoidScheme.exists_split_of_splittingSituation` there proves all four
assertions of Stacks 0DTC in Situation 0DTB.

*No attribute is attached in this file*; the Stacks 0DTC attribute sits on that theorem.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
* [Stacks Project, Tag 0DTC](https://stacks.math.columbia.edu/tag/0DTC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A morphism out of a reduced scheme whose set-theoretic image lies in the image of an
immersion factors through that immersion.**

An immersion factors as a closed immersion into the open subscheme cut out by the coborder of its
range followed by that open subscheme's inclusion, so the morphism first factors through the open
subscheme, and the base change of the closed immersion along the resulting morphism is a closed
immersion which is surjective by the image hypothesis — hence an isomorphism, because the source
is reduced.

For a general target this fails: a surjective closed immersion need not be an isomorphism.  The
spectrum of a field is reduced, which is the case this is used in. -/
@[ega "I 5.2.2" "more general",
  sga "3 VIB 7.1" "partial",
  sga "3 VIB 7.3.0",
  sga "3 X 8.9" "partial"]
theorem exists_lift_of_immersion_of_isReduced {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]
    (f : Z ⟶ Y) [IsReduced Z] (hrange : Set.range f.base ⊆ Set.range i.base) :
    ∃ l : Z ⟶ X, l ≫ i = f := by
  have hsub : Set.range f.base ⊆ Set.range i.coborderRange.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hrange.trans subset_coborder
  let g := IsOpenImmersion.lift i.coborderRange.ι f hsub
  have hg : g ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  have hgrange : Set.range g.base ⊆ Set.range i.liftCoborder.base := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := hrange ⟨z, rfl⟩
    refine ⟨x, i.coborderRange.ι.isEmbedding.injective ?_⟩
    show (i.liftCoborder ≫ i.coborderRange.ι) x = (g ≫ i.coborderRange.ι) z
    rw [Scheme.Hom.liftCoborder_ι, hg]
    exact hx
  have hsurj : Surjective (pullback.snd i.liftCoborder g) := by
    rw [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun z => hgrange ⟨z, rfl⟩
  have : IsIso (pullback.snd i.liftCoborder g) :=
    isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd i.liftCoborder g) ≫ pullback.fst i.liftCoborder g, ?_⟩
  calc inv (pullback.snd i.liftCoborder g) ≫ pullback.fst i.liftCoborder g ≫ i
      = inv (pullback.snd i.liftCoborder g) ≫
        pullback.fst i.liftCoborder g ≫ i.liftCoborder ≫ i.coborderRange.ι := by
        rw [Scheme.Hom.liftCoborder_ι]
    _ = f := by
        rw [← Category.assoc (pullback.fst _ _) i.liftCoborder, pullback.condition]
        simp [hg]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_etaleLocalizationStabilizerMembership
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_etaleLocalizationStabilizerMembership
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_etaleLocalizationStabilizerMembership.has_limit _

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
  (C : BigFppfSite.{u}) (hS : C.Contains S) (hU : C.Contains G.objects.left)
  (hR : C.Contains G.arrows.left) (u : G.objects.left)
  (hK : C.Contains (Spec (G.objects.left.residueField u)))
  (hP : C.Contains (pullback G.source G.target).left)
  (W : (G.source.left.fiber u).Opens)
  (hWfin : AlgebraicGeometry.IsFinite (W.ι ≫ G.source.left.fiberToSpecResidueField u))

/-- The inclusion of a scheme-theoretic fibre is injective, being the composition of the
homeomorphism onto the set-theoretic preimage with the inclusion of that preimage. -/
theorem injective_fiberι : Function.Injective (G.source.left.fiberι u) := fun _a _b h =>
  (G.source.left.fiberHomeo u).injective (Subtype.ext h)

/-- The point of the fibre determined by a point of the arrow scheme whose source is `u`. -/
theorem exists_fiber_eq_of_source_eq (r : G.arrows.left) (hr : G.source.left r = u) :
    ∃ x : G.source.left.fiber u, G.source.left.fiberι u x = r :=
  ⟨(G.source.left.fiberHomeo u).symm ⟨r, hr⟩,
    Scheme.Hom.fiberι_fiberHomeo_symm G.source.left u ⟨r, hr⟩⟩

/-- The site-level square of a section of the ambient fibre product commutes, as it does after
Yoneda. -/
private theorem comp_eq_of_yoneda_hc (V' : BigFppfOver C S hS)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR)
    (hc : yoneda.map base ≫
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
        yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom) :
    base ≫ residueSiteMap G C hS hU u hK = arr ≫ sourceSiteMap G C hS hU hR :=
  yoneda.map_injective ((yoneda.map_comp _ _).trans
    ((hc : yoneda.map base ≫ yoneda.map (residueSiteMap G C hS hU u hK) =
      yoneda.map arr ≫ yoneda.map (sourceSiteMap G C hS hU hR)).trans
        (yoneda.map_comp _ _).symm))

/-- A point of the fibre scheme lies in the range of the open immersion of `W` exactly when it
goes into `W` under the identification of the fibre. -/
private theorem mem_range_fibreOpenImmersion_iff
    (y : (BigFppfOver.toScheme C S hS).obj (fibreSiteObject G C hS hU hR u hK)) :
    y ∈ Set.range (fibreOpenImmersion G C hS hU hR u hK W).base ↔
      (etaleLocalFibreIso G C hS hU hR u hK).hom y ∈ W := by
  constructor
  · rintro ⟨x, rfl⟩
    have h1 : (etaleLocalFibreIso G C hS hU hR u hK).hom
        ((fibreOpenImmersion G C hS hU hR u hK W) x) = W.ι x := by
      show ((W.ι ≫ (etaleLocalFibreIso G C hS hU hR u hK).inv) ≫
        (etaleLocalFibreIso G C hS hU hR u hK).hom) x = W.ι x
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h1]
    have hx : W.ι x ∈ Set.range W.ι.base := ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι] at hx
  · intro hy
    refine ⟨⟨(etaleLocalFibreIso G C hS hU hR u hK).hom y, hy⟩, ?_⟩
    show (etaleLocalFibreIso G C hS hU hR u hK).inv
      ((etaleLocalFibreIso G C hS hU hR u hK).hom y) = y
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

/-- **The membership criterion for the pair `(u, Z_u)`, with the support of the open left
open.**  A section of the ambient fibre product `Spec κ(u) ×_{u, U, s} R` over a scheme of the
site factors through the open subspace of the pair attached to an open `W` of the fibre `F_u`
exactly when every point of the test scheme is carried by the arrow component into the image
of `W` in the arrow scheme.

This is `AlgebraicGeometry.Space.exists_lift_fibrePair_iff` with its support hypothesis removed:
that theorem uses the hypothesis only to rewrite the final containment of set-theoretic images,
and what is proved here is the containment itself.  Both the open of Stacks 04RL and the
stabilizer-supported open of Stacks 0DTB are instances. -/
theorem exists_lift_fibreOpenPair_iff (V' : BigFppfOver C S hS)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR)
    (hc : yoneda.map base ≫
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
        yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom) :
    (∃ n : yoneda.obj V' ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
        n ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
      ∀ p : (BigFppfOver.toScheme C S hS).obj V',
        ∃ x : G.source.left.fiber u, x ∈ W ∧
          G.source.left.fiberι u x = (BigFppfOver.toScheme C S hS).map arr p := by
  have hmono := mono_fibreOpenPresheafMap G C hS hU hR u hK W
  have hc₀ := comp_eq_of_yoneda_hc G C hS hU hR u hK hP W hWfin V' base arr hc
  have hk₀ : yoneda.map (pullback.lift base arr hc₀) ≫
      (fibreYonedaIso G C hS hU hR u hK).hom =
      pullback.lift (yoneda.map base) (yoneda.map arr) hc := by
    refine pullback.hom_ext ?_ ?_
    · refine Eq.trans ?_ (pullback.lift_fst (yoneda.map base) (yoneda.map arr) hc).symm
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← yoneda.map_comp,
        pullback.lift_fst]
    · refine Eq.trans ?_ (pullback.lift_snd (yoneda.map base) (yoneda.map arr) hc).symm
      rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← yoneda.map_comp,
        pullback.lift_snd]
  have hiso : ∀ l : yoneda.obj V' ⟶ yoneda.obj (fibreOpenSite G C hS hU hR u hK W),
      (l ≫ fibreOpenPresheafMap G C hS hU hR u hK W =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
        l ≫ yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W) =
          yoneda.map (pullback.lift base arr hc₀) := by
    intro l
    rw [← hk₀]
    exact ⟨fun h => (Iso.cancel_iso_hom_right _ _ (fibreYonedaIso G C hS hU hR u hK)).1
        ((Category.assoc l (yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W))
          (fibreYonedaIso G C hS hU hR u hK).hom).trans h),
      fun h => (Category.assoc l (yoneda.map (fibreOpenSiteMap G C hS hU hR u hK W))
          (fibreYonedaIso G C hS hU hR u hK).hom).symm.trans
        (congrArg (fun z => z ≫ (fibreYonedaIso G C hS hU hR u hK).hom) h)⟩
  have step2 : (∃ l : yoneda.obj V' ⟶ yoneda.obj (fibreOpenSite G C hS hU hR u hK W),
        l ≫ fibreOpenPresheafMap G C hS hU hR u hK W =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
      ∃ l₀ : V' ⟶ fibreOpenSite G C hS hU hR u hK W,
        l₀ ≫ fibreOpenSiteMap G C hS hU hR u hK W = pullback.lift base arr hc₀ := by
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨yoneda.preimage l, yoneda.map_injective ?_⟩
      rw [yoneda.map_comp, yoneda.map_preimage]
      exact (hiso l).1 hl
    · rintro ⟨l₀, hl₀⟩
      refine ⟨yoneda.map l₀, (hiso (yoneda.map l₀)).2 ?_⟩
      rw [← yoneda.map_comp, hl₀]
  have htgt : ∀ p : (BigFppfOver.toScheme C S hS).obj V',
      G.source.left.fiberι u ((etaleLocalFibreIso G C hS hU hR u hK).hom
        ((BigFppfOver.toScheme C S hS).map (pullback.lift base arr hc₀) p)) =
        (BigFppfOver.toScheme C S hS).map arr p := by
    intro p
    have h := congrArg (fun k => k ((BigFppfOver.toScheme C S hS).map
        (pullback.lift base arr hc₀) p)) (fibreIso_hom_comp_fiberι G C hS hU hR u hK)
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    have h2 : (BigFppfOver.toScheme C S hS).map (pullback.lift base arr hc₀) ≫
        (BigFppfOver.toScheme C S hS).map
          (pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) =
        (BigFppfOver.toScheme C S hS).map arr := by
      rw [← Functor.map_comp, pullback.lift_snd]
    exact (Scheme.Hom.comp_apply _ _ p).symm.trans (congrArg (fun k => k p) h2)
  refine (exists_lift_range_iff (fibreOpenPresheafMap G C hS hU hR u hK W) _).trans
    (step2.trans
    (((exists_siteOpen_lift_iff (fibreSiteObject G C hS hU hR u hK)
        (fibreOpenImmersion G C hS hU hR u hK W)
        (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W) V'
        (pullback.lift base arr hc₀)).trans
      ((exists_scheme_lift_iff_range_subset _
        (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W) _).trans ?_))))
  rw [Set.range_subset_iff]
  refine forall_congr' fun p =>
    (mem_range_fibreOpenImmersion_iff G C hS hU hR u hK W _).trans ⟨fun hy => ⟨_, hy, htgt p⟩, ?_⟩
  rintro ⟨x, hxW, hx⟩
  exact injective_fiberι G u (hx.trans (htgt p).symm) ▸ hxW

/-- **The membership criterion for the open of Stacks 04RL**, recovered from the neutral form:
for an open whose points are exactly the arrows with target `u`, a section factors through the
open subspace of the pair exactly when the target of its arrow carries every point of the test
scheme to `u`.

This is `AlgebraicGeometry.Space.exists_lift_fibrePair_iff`, proved again as a check that the
neutral form loses nothing. -/
theorem exists_lift_fibrePair_iff'
    (hW : ∀ x : G.source.left.fiber u,
      x ∈ W ↔ G.target.left (G.source.left.fiberι u x) = u)
    (V' : BigFppfOver C S hS)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR)
    (hc : yoneda.map base ≫
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
        yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom) :
    (∃ n : yoneda.obj V' ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
        n ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
      ∀ p : (BigFppfOver.toScheme C S hS).obj V',
        G.target.left ((BigFppfOver.toScheme C S hS).map arr p) = u := by
  refine (exists_lift_fibreOpenPair_iff G C hS hU hR u hK hP W hWfin V' base arr hc).trans
    (forall_congr' fun p => ⟨?_, ?_⟩)
  · rintro ⟨x, hxW, hx⟩
    exact hx ▸ (hW x).1 hxW
  · intro hp
    have hsrc : G.source.left ((BigFppfOver.toScheme C S hS).map arr p) = u := by
      have hc₀ := comp_eq_of_yoneda_hc G C hS hU hR u hK hP W hWfin V' base arr hc
      have hsch := congrArg (BigFppfOver.toScheme C S hS).map hc₀
      rw [Functor.map_comp, Functor.map_comp] at hsch
      have hval := congrArg (fun k => k p) hsch
      simp only [Scheme.Hom.comp_apply] at hval
      exact hval.symm.trans (Scheme.fromSpecResidueField_apply u _)
    obtain ⟨x, hx⟩ := exists_fiber_eq_of_source_eq G u _ hsrc
    exact ⟨x, (hW x).2 (hx ▸ hp), hx⟩

/-! ### The stabilizer-supported open -/

variable (hWstab : ∀ x : G.source.left.fiber u, x ∈ W ↔ ∃ g : (stabilizer G).left,
  (stabilizer G).hom g = u ∧ stabilizerArrow G g = G.source.left.fiberι u x)

include hWstab in
/-- **Membership in the stabilizer-supported open, read on points of the arrow scheme.**  A
point of the arrow scheme lies in the image of the open exactly when it is the arrow underlying
a point of the stabilizer group scheme lying over `u`. -/
theorem mem_fiberOpen_iff_stabilizer (r : G.arrows.left) :
    (∃ x : G.source.left.fiber u, x ∈ W ∧ G.source.left.fiberι u x = r) ↔
      ∃ g : (stabilizer G).left, (stabilizer G).hom g = u ∧ stabilizerArrow G g = r := by
  constructor
  · rintro ⟨x, hxW, rfl⟩
    exact (hWstab x).1 hxW
  · rintro ⟨g, hg, hgr⟩
    obtain ⟨x, hx⟩ := exists_fiber_eq_of_source_eq G u r
      (hgr ▸ (stabilizerArrow_source_apply G g).trans hg)
    exact ⟨x, (hWstab x).2 ⟨g, hg, hgr.trans hx.symm⟩, hx⟩

include hWstab in
/-- **The membership criterion for the stabilizer-supported open of Stacks 0DTB.**  A section of
the ambient fibre product `Spec κ(u) ×_{u, U, s} R` over a scheme of the site factors through the
open subspace of the pair `(u, Z_u)` exactly when its arrow component factors through
`AlgebraicGeometry.stabilizerArrow` over `u`, pointwise.

This is the content of the choice of `Z_u` made by the étale localization of Situation 0DTB, and
it is the replacement for `AlgebraicGeometry.Space.exists_lift_fibrePair_iff`, which describes the
open of Situation 04RL instead.  The two conditions are different: the arrows with both endpoints
at `u` need not lie on the stabilizer, by the remark on
`AlgebraicGeometry.Space.StrongSplittingSituation.toSplittingSituation`. -/
theorem exists_lift_stabilizerFibrePair_iff (V' : BigFppfOver C S hS)
    (base : V' ⟶ schemeSiteObject C hS (X := residueOver G u) hK)
    (arr : V' ⟶ schemeSiteObject C hS (X := G.arrows) hR)
    (hc : yoneda.map base ≫
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).toBase.hom =
        yoneda.map arr ≫ (G.realization C hS hU hR hP).source.hom) :
    (∃ n : yoneda.obj V' ⟶
          (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.toFunctor,
        n ≫ (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin).subspace.ι =
          pullback.lift (yoneda.map base) (yoneda.map arr) hc) ↔
      ∀ p : (BigFppfOver.toScheme C S hS).obj V',
        ∃ g : (stabilizer G).left, (stabilizer G).hom g = u ∧
          stabilizerArrow G g = (BigFppfOver.toScheme C S hS).map arr p :=
  (exists_lift_fibreOpenPair_iff G C hS hU hR u hK hP W hWfin V' base arr hc).trans
    (forall_congr' fun _p => mem_fiberOpen_iff_stabilizer G u W hWstab _)

include hWstab in
/-- **A section of the arrow scheme whose source and target agree lands in the
stabilizer-supported open**, pointwise, provided its source is the canonical morphism
`Spec κ(u) ⟶ U` out of a scheme all of whose points go to `u`.

The stabilizer group scheme is a fibre product formed in the category of schemes over the base,
so a *section* whose source and target agree factors through it on the nose, by
`AlgebraicGeometry.exists_stabilizer_lift`; the pointwise condition is then read off from that
factorization.  This is what replaces, for the stabilizer-supported open, the one-line argument
of the strong splitting situation, where the open is described by the target condition which the
section satisfies by hypothesis. -/
theorem mem_fiber_of_stabilizer_section {T : Scheme.{u}} (r : T ⟶ G.arrows.left)
    (k : T ⟶ Spec (G.objects.left.residueField u))
    (hsrc : r ≫ G.source.left = k ≫ G.objects.left.fromSpecResidueField u)
    (htgt : r ≫ G.target.left = k ≫ G.objects.left.fromSpecResidueField u) (y : T) :
    ∃ x : G.source.left.fiber u, x ∈ W ∧ G.source.left.fiberι u x = r y := by
  obtain ⟨z, hz, hzhom⟩ := exists_stabilizer_lift G r (hsrc.trans htgt.symm)
  refine (mem_fiberOpen_iff_stabilizer G u W hWstab (r y)).2 ⟨z y, ?_, ?_⟩
  · have hval := congrArg (fun m => m y) (hzhom.trans hsrc)
    simp only [Scheme.Hom.comp_apply] at hval
    exact hval.trans (Scheme.fromSpecResidueField_apply u _)
  · exact (Scheme.Hom.comp_apply z (stabilizerArrow G) y).symm.trans
      (congrArg (fun m => m y) hz)

include hWstab in
/-- **Over a reduced scheme the stabilizer-supported open of Situation 0DTB is cut out by the
target condition of Situation 04RL.**  A section of the arrow scheme over a reduced scheme whose
source is the canonical morphism `Spec κ(u) ⟶ U` lands pointwise in the stabilizer-supported open
exactly when its target is that morphism too.

The two implications use the two directions of the comparison between arrows and points of the
stabilizer group scheme.  Pointwise membership says the set-theoretic image of the section lies in
the image of `AlgebraicGeometry.stabilizerArrow`, which is an immersion, so over a reduced scheme
the section factors through the stabilizer and its target agrees with its source
(`AlgebraicGeometry.exists_lift_of_immersion_of_isReduced`).  Conversely a section whose source and
target agree factors through the stabilizer because the stabilizer is a fibre product
(`AlgebraicGeometry.exists_stabilizer_lift`), which is
`AlgebraicGeometry.Space.mem_fiber_of_stabilizer_section`.

This is the reason Stacks 0DTC goes through at all: the open of Situation 0DTB is *not* the open
of Situation 04RL — the arrows with both endpoints at `u` need not lie on the stabilizer — but the
two become the same condition on the field-valued points at which the splitting is tested. -/
theorem mem_fiberOpen_iff_target_of_isReduced {T : Scheme.{u}} [IsReduced T]
    (r : T ⟶ G.arrows.left) (k : T ⟶ Spec (G.objects.left.residueField u))
    (hsrc : r ≫ G.source.left = k ≫ G.objects.left.fromSpecResidueField u) :
    (∀ y : T, ∃ x : G.source.left.fiber u, x ∈ W ∧
        G.source.left.fiberι u x = r y) ↔
      r ≫ G.target.left = k ≫ G.objects.left.fromSpecResidueField u := by
  have himm : _root_.AlgebraicGeometry.IsImmersion (stabilizerArrow G) :=
    stabilizerArrow_isImmersion G
  refine ⟨fun hmem => ?_, mem_fiber_of_stabilizer_section G u W hWstab r k hsrc⟩
  have hrange : Set.range r.base ⊆ Set.range (stabilizerArrow G).base := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨g, _, hg⟩ := (mem_fiberOpen_iff_stabilizer G u W hWstab (r y)).1 (hmem y)
    exact ⟨g, hg⟩
  obtain ⟨z, hz⟩ := exists_lift_of_immersion_of_isReduced (stabilizerArrow G) r hrange
  calc r ≫ G.target.left = z ≫ stabilizerArrow G ≫ G.target.left := by
        rw [← Category.assoc, hz]
    _ = z ≫ stabilizerArrow G ≫ G.source.left := by
        rw [stabilizerArrow_comp_target_etaleLocal,
          stabilizerArrow_comp_source_etaleLocal]
    _ = k ≫ G.objects.left.fromSpecResidueField u := by
        rw [← Category.assoc, hz, hsrc]

/-! ### The unit of the finite part lands in the stabilizer-supported open -/

variable (F : FinitePartUniversalOpen (G.realization C hS hU hR hP))

/-- On schemes, the unit arrow at `u` followed by the source is the canonical morphism
`Spec κ(u) ⟶ U`.  This is the source-side companion of
`AlgebraicGeometry.Space.toScheme_map_unitArrowSite_comp_target`. -/
theorem toScheme_map_unitArrowSite_comp_source :
    (BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F) ≫
        G.source.left = G.objects.left.fromSpecResidueField u := by
  have h : (BigFppfOver.toScheme C S hS).map
      (unitArrowSite G C hS hU hR u hK hP F ≫ sourceSiteMap G C hS hU hR) =
      (BigFppfOver.toScheme C S hS).map (residueSiteMap G C hS hU u hK) :=
    congrArg _ (unitArrowSite_comp_source G C hS hU hR u hK hP F)
  rw [Functor.map_comp] at h
  exact h

include hWstab in
/-- **The point of the fibre carried by the unit section lies in the stabilizer-supported
open.**  The unit arrow at `u` has both its source and its target equal to the canonical
morphism `Spec κ(u) ⟶ U`, so as a *section* it factors through the stabilizer group scheme by
`AlgebraicGeometry.exists_stabilizer_lift`, and every point of `Spec κ(u)` is therefore carried
into the support of the open.

This replaces `AlgebraicGeometry.Space.unitFibrePoint_mem` for the open of Situation 0DTB.  Only
`AlgebraicGeometry.Space.FinitePartUniversalOpen.unit_source` and `unit_comp_target` are used
about the unit, exactly as in the strong splitting situation; in particular the unit is **not**
identified with the Yoneda image of the identity `e : U ⟶ R` of the groupoid scheme, which the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingExistence.lean` record
as the apparent obstruction. -/
theorem unitFibrePoint_mem_stabilizer
    (y : (BigFppfOver.toScheme C S hS).obj
      (schemeSiteObject C hS (X := residueOver G u) hK)) :
    (etaleLocalFibreIso G C hS hU hR u hK).hom
      ((BigFppfOver.toScheme C S hS).map
        (unitFibreSection G C hS hU hR u hK hP F) y) ∈ W := by
  obtain ⟨x, hxW, hx⟩ := mem_fiber_of_stabilizer_section G u W hWstab
    ((BigFppfOver.toScheme C S hS).map (unitArrowSite G C hS hU hR u hK hP F))
    (𝟙 (BigFppfOver.toScheme C S hS).obj (schemeSiteObject C hS (X := residueOver G u) hK))
    ((toScheme_map_unitArrowSite_comp_source G C hS hU hR u hK hP F).trans
      (Category.id_comp _).symm)
    ((toScheme_map_unitArrowSite_comp_target G C hS hU hR u hK hP F).trans
      (Category.id_comp _).symm) y
  have h := congrArg (fun k => k y) (unitFibrePoint_comp_fiberι G C hS hU hR u hK hP F)
  simp only [Scheme.Hom.comp_apply] at h
  rw [← h] at hx
  exact (injective_fiberι G u hx) ▸ hxW

include hWstab in
/-- **The unit section factors through the stabilizer-supported open set-theoretically.**  This
is the hypothesis which the factorization
`AlgebraicGeometry.Space.unitOpenLift` of the strong splitting situation consumes, proved here
for the open of Situation 0DTB. -/
theorem unitFibreSection_range_le_stabilizer :
    Set.range ((BigFppfOver.toScheme C S hS).map
        (unitFibreSection G C hS hU hR u hK hP F)) ⊆
      Set.range (fibreOpenImmersion G C hS hU hR u hK W) := by
  rintro _ ⟨y, rfl⟩
  exact (mem_range_fibreOpenImmersion_iff G C hS hU hR u hK W _).2
    (unitFibrePoint_mem_stabilizer G C hS hU hR u hK hP W hWstab F y)

/-! ### The point `u'` of the finite part in Situation 0DTB -/

include hWstab in
/-- The factorization of the unit section through the stabilizer-supported open, which exists by
the universal property of an open immersion.  This is
`AlgebraicGeometry.Space.unitOpenLift` for the open of Situation 0DTB. -/
def unitOpenLiftStabilizer :
    (BigFppfOver.toScheme C S hS).obj (schemeSiteObject C hS (X := residueOver G u) hK) ⟶
      (BigFppfOver.toScheme C S hS).obj (fibreOpenSite G C hS hU hR u hK W) :=
  AlgebraicGeometry.IsOpenImmersion.lift
    (H := isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W)
    (fibreOpenImmersion G C hS hU hR u hK W)
    ((BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F))
    (unitFibreSection_range_le_stabilizer G C hS hU hR u hK hP W hWstab F)

include hWstab in
/-- That morphism is a factorization of the unit section through the open. -/
theorem unitOpenLiftStabilizer_fac :
    unitOpenLiftStabilizer G C hS hU hR u hK hP W hWstab F ≫
        fibreOpenImmersion G C hS hU hR u hK W =
      (BigFppfOver.toScheme C S hS).map (unitFibreSection G C hS hU hR u hK hP F) :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac
    (H := isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W) _ _ _

include hWstab in
/-- The factorization of the unit section through the stabilizer-supported open, as a morphism of
the site over `S`. -/
def unitOpenSectionStabilizer :
    schemeSiteObject C hS (X := residueOver G u) hK ⟶ fibreOpenSite G C hS hU hR u hK W :=
  Over.homMk (ObjectProperty.homMk
    (unitOpenLiftStabilizer G C hS hU hR u hK hP W hWstab F)) (by
    apply ObjectProperty.hom_ext
    change unitOpenLiftStabilizer G C hS hU hR u hK hP W hWstab F ≫
      (fibreOpenImmersion G C hS hU hR u hK W ≫
        (fibreSiteObject G C hS hU hR u hK).hom.hom) = _
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (fibreSiteObject G C hS hU hR u hK).hom.hom)
        (unitOpenLiftStabilizer_fac G C hS hU hR u hK hP W hWstab F))).trans
      (congrArg (fun k => k.hom) (Over.w (unitFibreSection G C hS hU hR u hK hP F))))

include hWstab in
/-- That morphism of the site is a factorization of the unit section. -/
theorem unitOpenSectionStabilizer_comp :
    unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F ≫
        fibreOpenSiteMap G C hS hU hR u hK W =
      unitFibreSection G C hS hU hR u hK hP F :=
  (BigFppfOver.toScheme C S hS).map_injective
    (((BigFppfOver.toScheme C S hS).map_comp _ _).trans
      ((congrArg (fun k => (BigFppfOver.toScheme C S hS).map
            (unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F) ≫ k)
          (toScheme_map_siteOpenMap C S hS (fibreSiteObject G C hS hU hR u hK)
            (fibreOpenImmersion G C hS hU hR u hK W)
            (isOpenImmersion_fibreOpenImmersion G C hS hU hR u hK W))).trans
        (unitOpenLiftStabilizer_fac G C hS hU hR u hK hP W hWstab F)))

include hWstab in
/-- Composing it with the inclusion of the open and the projection to `Spec κ(u)` is the
identity. -/
theorem unitOpenSectionStabilizer_comp_fst :
    unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F ≫
        (fibreOpenSiteMap G C hS hU hR u hK W ≫
          pullback.fst (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) = 𝟙 _ :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.fst (residueSiteMap G C hS hU u hK)
        (sourceSiteMap G C hS hU hR))
      (unitOpenSectionStabilizer_comp G C hS hU hR u hK hP W hWstab F)).trans
      (unitFibreSection_comp_fst G C hS hU hR u hK hP F))

include hWstab in
/-- Composing it with the inclusion of the open and the projection to `R` is the unit arrow. -/
theorem unitOpenSectionStabilizer_comp_snd :
    unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F ≫
        (fibreOpenSiteMap G C hS hU hR u hK W ≫
          pullback.snd (residueSiteMap G C hS hU u hK) (sourceSiteMap G C hS hU hR)) =
      unitArrowSite G C hS hU hR u hK hP F :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ pullback.snd (residueSiteMap G C hS hU u hK)
        (sourceSiteMap G C hS hU hR))
      (unitOpenSectionStabilizer_comp G C hS hU hR u hK hP W hWstab F)).trans
      (unitFibreSection_comp_snd G C hS hU hR u hK hP F))

include hWstab in
/-- **The pair `(u, Z_u)` of Situation 0DTB contains the unit**, which is the condition of Stacks
04RQ placing it in the finite part with section `(R_s/U, e)_fin`.

This is `AlgebraicGeometry.Space.containsSection_fibreFiniteOpenSubspace` for the
stabilizer-supported open.  Where the strong splitting situation argues that the unit arrow has
target `u` and the open is cut out by that condition, here the unit arrow is factored through the
stabilizer group scheme as a section, by
`AlgebraicGeometry.Space.unitFibrePoint_mem_stabilizer`. -/
theorem containsSection_fibreFiniteOpenSubspace_stabilizer :
    ContainsSection C S hS (G.realization C hS hU hR hP).source F.unit F.unit_source
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin) := by
  refine ⟨yoneda.map (unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F) ≫
    Subfunctor.toRange (fibreOpenPresheafMap G C hS hU hR u hK W), ?_⟩
  refine ((Category.assoc _ _ _).trans
    (congrArg (fun k =>
      yoneda.map (unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F) ≫ k)
      (Subfunctor.toRange_ι (fibreOpenPresheafMap G C hS hU hR u hK W)))).trans
    (pullback.hom_ext ?_ ?_)
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k =>
            yoneda.map (unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F) ≫ k)
          (fibreOpenPresheafMap_comp_fst G C hS hU hR u hK W)).trans
        (((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map
              (unitOpenSectionStabilizer_comp_fst G C hS hU hR u hK hP W hWstab F))).trans
          (yoneda.map_id _)))).trans (pullback.lift_fst _ _ _).symm
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k =>
            yoneda.map (unitOpenSectionStabilizer G C hS hU hR u hK hP W hWstab F) ≫ k)
          (fibreOpenPresheafMap_comp_snd G C hS hU hR u hK W)).trans
        (((yoneda.map_comp _ _).symm.trans
            (congrArg yoneda.map
              (unitOpenSectionStabilizer_comp_snd G C hS hU hR u hK hP W hWstab F))).trans
          (yoneda_map_unitArrowSite G C hS hU hR u hK hP F)))).trans
      (pullback.lift_snd _ _ _).symm

include hWstab in
/-- The section of the finite part which the pair `(u, Z_u)` of Situation 0DTB names lies in the
open subspace `(R_s/U, e)_fin` cut out by containing the unit, by Stacks 04RR. -/
theorem mem_finitePartWithSection_stabilizer :
    fibrePresheafSection G C hS hU hR u hK hP W hWfin ∈
      (finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
        F.unit_source).toSubfunctor.obj
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) := by
  rw [(finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
    F.unit_source).mem_iff]
  refine containsSection_restrict (G.realization C hS hU hR hP).source F.unit F.unit_source
    ((finiteOpenSubspaceEquiv C S hS (G.realization C hS hU hR hP).source
      (schemeSpace (schemeSiteObject C hS (X := residueOver G u) hK))).1.symm
      (fibreFiniteOpenSubspace G C hS hU hR u hK hP W hWfin))
    ?_ (schemeSiteObject C hS (X := residueOver G u) hK)
    (𝟙 (schemeSiteObject C hS (X := residueOver G u) hK))
  rw [Equiv.apply_symm_apply]
  exact containsSection_fibreFiniteOpenSubspace_stabilizer G C hS hU hR u hK hP W hWfin hWstab F

include hWstab in
/-- **The point `u' : Spec κ(u) ⟶ U'` of Situation 0DTB.**  The pair `(u, Z_u)` with `Z_u` the
stabilizer-supported open, read as a `Spec κ(u)`-valued point of the object space of the finite
part of the groupoid.

This is `AlgebraicGeometry.Space.etaleLocalFibrePoint` for the open of Situation 0DTB, and it is
the point which Stacks 0DTC asserts to exist. -/
def etaleLocalStabilizerFibrePoint :
    F.objects.obj.obj (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) :=
  F.objectsEquiv.inv.app _
    ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
      mem_finitePartWithSection_stabilizer G C hS hU hR u hK hP W hWfin hWstab F⟩

include hWstab in
/-- The image of that point under the projection `g : U' ⟶ U` is the canonical morphism
`Spec κ(u) ⟶ U`, read in the site. -/
theorem objectProjection_stabilizerFibrePoint :
    F.objectProjection.hom.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) =
      residueSiteMap G C hS hU u hK := by
  have h1 := congrArg (fun k : F.objects.obj ⟶ (G.realization C hS hU hR hP).objects.obj =>
      k.app (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F))
    F.objectProjection_spec
  have h2 : F.objectsEquiv.hom.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F) =
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_stabilizer G C hS hU hR u hK hP W hWfin hWstab F⟩ :=
    congrArg (fun k => k.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ⟨fibrePresheafSection G C hS hU hR u hK hP W hWfin,
        mem_finitePartWithSection_stabilizer G C hS hU hR u hK hP W hWfin hWstab F⟩)
      F.objectsEquiv.inv_hom_id
  refine h1.trans ((congrArg (fun z =>
    (finiteOpenSubspacePresheaf C S hS (G.realization C hS hU hR hP).source).baseMap.app
      (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
      ((finitePartWithSection C S hS (G.realization C hS hU hR hP).source F.unit
        F.unit_source).toSubfunctor.ι.app
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK)) z)) h2).trans ?_)
  exact baseMap_fibrePresheafSection G C hS hU hR u hK hP W hWfin

include hWstab in
/-- **The point `u'` of Situation 0DTB lies over `u`**: its composition with the étale projection
`g : U' ⟶ U` is the canonical morphism `Spec κ(u) ⟶ U`. -/
theorem lies_over_stabilizerFibrePoint :
    (yonedaSchemePointEquiv C hS hU
        (Opposite.op (schemeSiteObject C hS (X := residueOver G u) hK))
        (F.objectProjection.hom.app _
          (etaleLocalStabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F))).left =
      G.objects.left.fromSpecResidueField u := by
  rw [objectProjection_stabilizerFibrePoint G C hS hU hR u hK hP W hWfin hWstab F]
  exact congrArg Over.Hom.left (siteToOver_map_schemeSiteMap C hS
    (X := residueOver G u) (Y := G.objects) hK hU (residuePoint G u))

end AlgebraicGeometry.Space

/-! ### The étale neighbourhood and the point of Stacks 0DTC -/

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry AlgebraicGeometry.Space

/-- **Stacks Project, Tag 0DTC, weaker: the étale neighbourhood and the point, not the
splitting.**

In the splitting situation of Stacks 0DTB there is an algebraic space `U'`, an étale morphism
`g : U' ⟶ U` of algebraic spaces, and a point `u' : Spec κ(u) ⟶ U'` lying over
`u : Spec κ(u) ⟶ U`.

`U'` is the finite part `(R_s/U, e)_fin` of Stacks 04RU, `g` its étale projection, and `u'` the
pair `(u, Z_u)` where `Z_u` is the open and closed piece of the fibre `F_u = R ×_{s, U} Spec κ(u)`
supported on the arrows underlying the points of the stabilizer group scheme over `u`, which is
finite over `κ(u)` by
`AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer`.

What Stacks 0DTC asserts beyond this — that the restriction `R|_{U'}` is *split* over `u'` — is
**not** proved here.  This is the exact analogue, in the splitting situation of Stacks 0DTB, of
`AlgebraicGeometry.Space.exists_etale_point_of_strongSplittingSituation`, which proves the same
three assertions in the strong splitting situation of Stacks 04RL; unlike that statement it is
not a consequence of the strong case, since Stacks 0DTB is the weaker standing hypothesis. -/
theorem exists_etale_point_of_splittingSituation
    (D : AlgebraicGeometry.Space.SplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u))) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      IsEtale C D.S hS g.hom ∧
      ∃ v : U'.obj.obj (Opposite.op
          (residueFieldSiteObject C hS (X := D.groupoid.objects) D.u hK)),
        (yonedaSchemePointEquiv C hS hU (Opposite.op
            (residueFieldSiteObject C hS (X := D.groupoid.objects) D.u hK))
            (g.hom.app _ v)).left =
          D.groupoid.objects.left.fromSpecResidueField D.u := by
  obtain ⟨W, hWstab, _, _, hWfin⟩ := D.exists_fiberOpens_stabilizer
  exact ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale,
    etaleLocalStabilizerFibrePoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab
      (realizationFinitePart D.groupoid C hS hU hR hP),
    lies_over_stabilizerFibrePoint D.groupoid C hS hU hR D.u hK hP W hWfin hWstab
      (realizationFinitePart D.groupoid C hS hU hR hP)⟩

end Stacks.Groupoids.GroupoidScheme

end
