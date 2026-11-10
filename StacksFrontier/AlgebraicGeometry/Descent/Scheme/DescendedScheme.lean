module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Descent.GlueDataOverBase
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.CanonicalInvariantOpen
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EffectiveCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The scheme descending a descent datum

Let `f : X ⟶ S` be a morphism of schemes and let `(V, φ)` be a descent datum relative to
`X/S`. A *descended scheme* for `(V, φ)` is a scheme `U` over `S` together with a morphism
`p : V ⟶ U` which exhibits `V` as the fibre product `U ×_S X` and which equalises the two
legs `φ` followed by the projection of `X ×_S V` to `V`, and the projection of `V ×_S X` to
`V`. Effectivity of `(V, φ)` is exactly the existence of such a pair `(U, p)`: one direction
is the criterion `AlgebraicGeometry.DescentData.isEffective_of_isPullback`, and the other
comes from the projection of a canonical descent datum onto the scheme it descends.

When `f` is surjective, flat and quasi-compact the morphism `p` is a base change of `f`,
hence an effective epimorphism. Consequently the pair `(U, p)` is unique up to a unique
isomorphism over `S`, an invariant open of `V` is the preimage of a unique open of `U`, and such
an open carries a descended scheme of the restricted datum. Descended schemes of the
restrictions of the datum to the members of an invariant open cover of `V` glue to a descended
scheme of the datum.

## Main definitions

* `AlgebraicGeometry.DescentDatum.Descended` is a scheme over `S` descending a descent datum,
  together with its projection, the fibre-product square and the invariance of the
  projection.
* `AlgebraicGeometry.DescentDatum.Descended.ofIso` is the descended scheme read off an
  isomorphism of the datum with a canonical descent datum: its scheme is the one the
  canonical datum is built from, and its projection is the projection of that canonical
  datum transported along the isomorphism.
* `AlgebraicGeometry.DescentDatum.Descended.restrict` is the descended scheme of the
  restriction of the datum to the preimage of an open of `U`: the open subscheme of `U` cut
  out by that open, with the restricted projection.
* `AlgebraicGeometry.DescentDatum.Descended.compare` and
  `AlgebraicGeometry.DescentDatum.Descended.compareIso` are the comparison morphism and the
  comparison isomorphism over `S` between two descended schemes of one datum.
* `AlgebraicGeometry.DescentDatum.restrictOpenMono` is the inclusion of the restriction to a
  smaller invariant open, as a morphism of descent data.
* `AlgebraicGeometry.DescentDatum.Descended.shrinkOpens` is the open of the descended scheme
  cut out by a smaller invariant open of `V`, and
  `AlgebraicGeometry.DescentDatum.Descended.shrink` is the descended scheme of the restriction
  of the datum to that smaller open: the open subscheme `shrinkOpens`, with the projection
  `AlgebraicGeometry.DescentDatum.Descended.shrinkProj`.
* `AlgebraicGeometry.DescentDatum.ChartFamily` is a family of charts: an invariant open
  neighbourhood of every point of `V` together with a descended scheme for the restriction of
  the datum to it. `AlgebraicGeometry.DescentDatum.ChartFamily.overlap` is the part of one
  chart glued to another — the open cut out by the intersection of the two neighbourhoods —
  `AlgebraicGeometry.DescentDatum.ChartFamily.interChart` and `interChart'` are the two
  descended schemes of the restriction to that intersection, and
  `AlgebraicGeometry.DescentDatum.ChartFamily.t` is the transition morphism between the two
  overlaps, namely their comparison isomorphism.
* `AlgebraicGeometry.DescentDatum.ChartFamily.t'` is the transition morphism on triple
  overlaps, and `AlgebraicGeometry.DescentDatum.ChartFamily.glueData` is the glueing datum
  over `S` the family assembles into.
* `AlgebraicGeometry.DescentDatum.GluedChartFamily` is a family of charts glued over the base:
  a glueing datum over `S`, an invariant open of `V` for each of its pieces covering `V`, and a
  projection of each such open onto its piece exhibiting it as a fibre product.
  `AlgebraicGeometry.DescentDatum.GluedChartFamily.glueProj` is the projection of `V` onto the
  glued scheme and `AlgebraicGeometry.DescentDatum.GluedChartFamily.descended` is the descended
  scheme it exhibits.
* `AlgebraicGeometry.DescentDatum.ChartFamily.toGluedChartFamily` presents a family of charts
  as a family glued over the base, along `ChartFamily.glueData`.

## Main results

* `AlgebraicGeometry.DescentDatum.Descended.isEffective`: a datum with a descended scheme is
  effective, `AlgebraicGeometry.DescentDatum.nonempty_descended_of_isEffective` is the
  converse, and `AlgebraicGeometry.DescentDatum.isEffective_iff_nonempty_descended` combines
  the two.
* `AlgebraicGeometry.DescentDatum.Descended.isPullback_legs`: **`V ×_S X` is the self-fibre
  product `V ×_U V`**, with the leg to the first copy of `V` given by `φ` followed by the
  projection of `X ×_S V` to `V` and the leg to the second copy by the projection of
  `V ×_S X` to `V`.
* `AlgebraicGeometry.DescentDatum.Descended.existsUnique_opens_preimage_eq`: **an invariant
  open of `V` is the preimage of exactly one open of `U`**, for `f` surjective, flat and
  quasi-compact.
* `AlgebraicGeometry.DescentDatum.Descended.isTransitionInvariant_proj_preimage`: conversely,
  the preimage of an open of `U` is invariant. No hypothesis on `f` is needed.
* `AlgebraicGeometry.DescentDatum.Descended.comp_proj_invariant`: the projection precomposed
  with the component of a morphism of descent data equalises the two legs of the source
  datum.
* `AlgebraicGeometry.DescentDatum.Descended.fst_comp_proj`: the projection of one descended
  scheme equalises the two projections of the self-fibre product of any other.
* `AlgebraicGeometry.DescentDatum.Descended.existsUnique_comp_eq`: **two descended schemes of
  one datum are canonically isomorphic**: there is exactly one morphism of the descended
  schemes compatible with the two projections. It lies over `S`
  (`AlgebraicGeometry.DescentDatum.Descended.compare_comp_hom`) and is an isomorphism
  (`AlgebraicGeometry.DescentDatum.Descended.isIso_compare`).
* `AlgebraicGeometry.DescentDatum.Descended.proj_preimage_shrinkOpens` and
  `AlgebraicGeometry.DescentDatum.Descended.eq_shrinkOpens`: the open cut out by a smaller
  invariant open is the unique open pulling back to it, and
  `AlgebraicGeometry.DescentDatum.Descended.shrinkProj_comp_ι` characterises the restricted
  projection: followed by the inclusion of that open it is the inclusion of the smaller open
  followed by the projection.
* `AlgebraicGeometry.DescentDatum.GluedChartFamily.isPullback_proj_glueProj`: the `i`-th chart
  of the glued scheme is cut out by the `i`-th member of the family.
* `AlgebraicGeometry.DescentDatum.GluedChartFamily.isPullback_glueProj` and
  `AlgebraicGeometry.DescentDatum.GluedChartFamily.glueProj_invariant`: the two conditions
  making the glued scheme a descended scheme.
* `AlgebraicGeometry.DescentDatum.isEffective_of_forall_exists_restrictOpen`: **effectivity of
  a descent datum is local on the scheme it is carried by**.

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 040L](https://stacks.math.columbia.edu/tag/040L)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

/-- **Two opens of a scheme with the same preimage in every member of an open cover are
equal.** -/
lemma Scheme.opens_eq_of_isOpenCover {Y : Scheme.{u}} {ι : Type*} {U : ι → Y.Opens}
    (hU : TopologicalSpace.IsOpenCover U) {A B : Y.Opens}
    (h : ∀ i, (U i).ι ⁻¹ᵁ A = (U i).ι ⁻¹ᵁ B) : A = B := by
  refine TopologicalSpace.Opens.ext (Set.ext fun y ↦ ?_)
  obtain ⟨i, hi⟩ := hU.exists_mem y
  exact ⟨fun hy ↦ (h i).le (show (⟨y, hi⟩ : (U i).toScheme) ∈ (U i).ι ⁻¹ᵁ A from hy),
    fun hy ↦ (h i).ge (show (⟨y, hi⟩ : (U i).toScheme) ∈ (U i).ι ⁻¹ᵁ B from hy)⟩

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S}

attribute [local implicit_reducible] restrictOpen

/-! ### The inclusion of nested invariant opens -/

section NestedOpens

variable (D : DescentDatum f)

/-- The inclusion of a smaller open into a larger one, as a morphism of the schemes over `X`
underlying the two restricted data. -/
abbrev restrictOpenLE {Z W : D.over.left.Opens} (hle : Z ≤ W) :
    D.restrictOpenObj Z ⟶ D.restrictOpenObj W :=
  Over.homMk (D.over.left.homOfLE hle)
    (by change D.over.left.homOfLE hle ≫ W.ι ≫ D.over.hom = Z.ι ≫ D.over.hom
        rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The inclusion of nested opens factors the larger inclusion into `V`. -/
lemma restrictOpenLE_comp_restrictOpenι {Z W : D.over.left.Opens} (hle : Z ≤ W) :
    D.restrictOpenLE hle ≫ D.restrictOpenι W = D.restrictOpenι Z :=
  Over.OverMorphism.ext (D.over.left.homOfLE_ι hle)

/-- The same factorisation, base changed along `f`. -/
lemma restrictOpenLEMap_comp_restrictOpenιMap {Z W : D.over.left.Opens} (hle : Z ≤ W) :
    (Over.map f).map (D.restrictOpenLE hle) ≫ D.restrictOpenιMap W = D.restrictOpenιMap Z := by
  rw [restrictOpenιMap, restrictOpenιMap, ← Functor.map_comp,
    D.restrictOpenLE_comp_restrictOpenι hle]

/-- **The inclusion of the restriction to a smaller invariant open**, as a morphism of descent
data, whose component is the inclusion of open subschemes. -/
def restrictOpenMono {Z W : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z)
    (hW : D.IsTransitionInvariant W) (hle : Z ≤ W) :
    D.restrictOpen Z hZ ⟶ D.restrictOpen W hW where
  hom _ := D.restrictOpenLE hle
  comm _ _ := by
    rw [← cancel_mono (prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W)), Category.assoc,
      Category.assoc, D.restrictOpen_transition_hom_left W hW, ← Category.assoc, prod.map_map,
      Category.comp_id, D.restrictOpenLEMap_comp_restrictOpenιMap hle, prod.map_map,
      Category.comp_id, D.restrictOpenLEMap_comp_restrictOpenιMap hle,
      D.restrictOpen_transition_hom_left Z hZ]

end NestedOpens

/-- **A scheme over `S` descending a descent datum.** For a descent datum `(V, φ)` relative to
`f : X ⟶ S`, a scheme `base` over `S` together with a morphism `proj : V ⟶ base` which
exhibits `V` as `base ×_S X` and which equalises the two legs of the gluing isomorphism. -/
structure Descended (D : DescentDatum f) where
  /-- The scheme over `S` that the datum descends to. -/
  base : Over S
  /-- The projection of the datum's scheme onto the descended scheme. -/
  proj : D.over.left ⟶ base.left
  /-- The projection and the structure morphism exhibit `V` as `base ×_S X`. -/
  isPullback : IsPullback D.over.hom proj f base.hom
  /-- The projection equalises the gluing isomorphism followed by the projection of
  `X ×_S V` to `V` and the projection of `V ×_S X` to `V`. -/
  proj_invariant : D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫ proj =
    pullback.fst (D.over.hom ≫ f) f ≫ proj

namespace Descended

variable {D D' : DescentDatum f}

/-- **A descent datum carrying a descended scheme is effective.** -/
theorem isEffective (Q : D.Descended) : D.IsEffective :=
  DescentData.isEffective_of_isPullback Q.base Q.proj Q.isPullback.flip Q.proj_invariant

/-- The projection of a descended scheme is surjective, being a base change of `f`. -/
instance (Q : D.Descended) [Surjective f] : Surjective Q.proj :=
  MorphismProperty.of_isPullback Q.isPullback inferInstance

/-- The projection of a descended scheme is flat, being a base change of `f`. -/
instance (Q : D.Descended) [Flat f] : Flat Q.proj :=
  MorphismProperty.of_isPullback Q.isPullback inferInstance

/-- The projection of a descended scheme is quasi-compact, being a base change of `f`. -/
instance (Q : D.Descended) [QuasiCompact f] : QuasiCompact Q.proj :=
  MorphismProperty.of_isPullback Q.isPullback inferInstance

variable (Q : D.Descended)

include Q in
/-- **`V ×_S X` is the self-fibre product `V ×_U V`,** for `U` a scheme descending the datum
`(V, φ)`. The leg to the first copy of `V` is the gluing isomorphism followed by the
projection of `X ×_S V` to `V`; the leg to the second copy is the projection of `V ×_S X` to
`V`. -/
theorem isPullback_legs :
    IsPullback (D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f))
      (pullback.fst (D.over.hom ≫ f) f) Q.proj Q.proj := by
  have hpb : IsPullback D.over.hom Q.proj f Q.base.hom := Q.isPullback
  have hs : IsPullback (pullback.snd (D.over.hom ≫ f) f)
      (pullback.fst (D.over.hom ≫ f) f) f (Q.proj ≫ Q.base.hom) := by
    rw [← hpb.w]
    exact (IsPullback.of_hasPullback (D.over.hom ≫ f) f).flip
  have hmain := IsPullback.of_right' hs hpb
  have heq : hpb.lift (pullback.snd (D.over.hom ≫ f) f)
        (pullback.fst (D.over.hom ≫ f) f ≫ Q.proj) (by rw [hs.w, Category.assoc]) =
      D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) := by
    refine hpb.hom_ext ?_ ?_
    · rw [hpb.lift_fst, Category.assoc]
      exact (D.transitionPullbackIso_hom_comp_pullbackSnd).symm
    · rw [hpb.lift_snd, Category.assoc]
      exact Q.proj_invariant.symm
  rw [heq] at hmain
  exact hmain

include Q in
/-- **An invariant open of `V` descends to the base.** For `f` surjective, flat and
quasi-compact, an open of `V` invariant under the gluing isomorphism is the preimage of
exactly one open of the descended scheme. -/
theorem existsUnique_opens_preimage_eq [Surjective f] [Flat f] [QuasiCompact f]
    (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) :
    ∃! W₀ : Q.base.left.Opens, Q.proj ⁻¹ᵁ W₀ = W := by
  have hpb := Q.isPullback_legs
  have hesurj : Function.Surjective hpb.isoPullback.hom.base :=
    (Scheme.homeoOfIso hpb.isoPullback).surjective
  refine existsUnique_opens_preimage_eq_of_flat_of_quasiCompact_of_surjective
    Q.proj W (hesurj.preimage_injective ?_)
  change (hpb.isoPullback.hom ≫ pullback.fst Q.proj Q.proj).base ⁻¹' (W : Set _) =
    (hpb.isoPullback.hom ≫ pullback.snd Q.proj Q.proj).base ⁻¹' (W : Set _)
  rw [hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd]
  exact DescentData.preimage_transition_snd_eq_preimage_fst D W hW

include Q in
/-- **The preimage of an open of the descended scheme is invariant.** No hypothesis on `f` is
needed. -/
theorem isTransitionInvariant_proj_preimage (W₀ : Q.base.left.Opens) :
    D.IsTransitionInvariant (Q.proj ⁻¹ᵁ W₀) := by
  calc D.transitionPullbackIso.hom ''ᵁ
        (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ (Q.proj ⁻¹ᵁ W₀))
      = (D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f ≫ Q.proj) ⁻¹ᵁ W₀ := by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.inv_preimage]
    _ = pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ (Q.proj ⁻¹ᵁ W₀) := by
        rw [← Q.proj_invariant, Iso.inv_hom_id_assoc, Scheme.Hom.comp_preimage]

/-- The projection of a descended scheme, precomposed with the component of a morphism of
descent data, equalises the two legs of the gluing isomorphism of the source datum. -/
theorem comp_proj_invariant (g : D' ⟶ D) (R : D.Descended) :
    D'.transitionPullbackIso.hom ≫ pullback.snd f (D'.over.hom ≫ f) ≫
        ((g.hom ()).left ≫ R.proj) =
      pullback.fst (D'.over.hom ≫ f) f ≫ ((g.hom ()).left ≫ R.proj) := by
  rw [← DescentDatum.homTargetMap_comp_snd_assoc g R.proj,
    ← DescentDatum.homSourceMap_comp_fst_assoc g R.proj, ← Category.assoc,
    ← DescentDatum.transitionPullbackIso_naturality g, Category.assoc, R.proj_invariant]

/-! ### The descended scheme of a canonical datum, and effectivity unbundled -/

/-- **The descended scheme read off an isomorphism with a canonical descent datum.** Its
scheme over `S` is the one the canonical datum is built from, and its projection is the
projection of that canonical datum precomposed with the component of the inverse
isomorphism. -/
def ofIso {U : Over S} (e : (DescentData.canonicalFunctor f).obj U ≅ D) : D.Descended where
  base := U
  proj := (e.inv.hom ()).left ≫ DescentData.canonicalProj f U
  isPullback := by
    refine (DescentData.isPullback_canonicalProj f U).of_iso
      ((Over.forget X).mapIso ((DescentData.evaluation ()).mapIso e)) (Iso.refl X)
      (Iso.refl U.left) (Iso.refl S) ?_ ?_ (by simp) (by simp)
    · rw [Iso.refl_hom, Category.comp_id]
      exact (Over.w (e.hom.hom ())).symm
    · rw [Iso.refl_hom, Category.comp_id]
      have h : (e.hom.hom ()).left ≫ (e.inv.hom ()).left = 𝟙 _ := by
        rw [← Over.comp_left, ← DescentData.comp_hom, e.hom_inv_id, DescentData.id_hom,
          Over.id_left]
      change _ = (e.hom.hom ()).left ≫ (e.inv.hom ()).left ≫ DescentData.canonicalProj f U
      rw [← Category.assoc, h, Category.id_comp]
  proj_invariant := by
    rw [← DescentDatum.homTargetMap_comp_snd_assoc e.inv (DescentData.canonicalProj f U),
      ← DescentDatum.homSourceMap_comp_fst_assoc e.inv (DescentData.canonicalProj f U),
      ← Category.assoc, ← DescentDatum.transitionPullbackIso_naturality e.inv,
      Category.assoc, DescentData.canonical_transition_comp_canonicalProj f U]

/-! ### Restriction to an open of the descended scheme -/



/-- **The descended scheme of a restriction.** The restriction of the datum to the preimage of
an open `W₀` of the descended scheme is descended by the open subscheme `W₀`, with the
restricted projection. -/
def restrict (W₀ : Q.base.left.Opens) :
    (D.restrictOpen (Q.proj ⁻¹ᵁ W₀) (Q.isTransitionInvariant_proj_preimage W₀)).Descended where
  base := Over.mk (W₀.ι ≫ Q.base.hom)
  proj := Q.proj ∣_ W₀
  isPullback := ((isPullback_morphismRestrict Q.proj W₀).paste_vert Q.isPullback.flip).flip
  proj_invariant := by
    refine (cancel_mono W₀.ι).mp ?_
    rw [Category.assoc, Category.assoc, morphismRestrict_ι, Category.assoc,
      morphismRestrict_ι]
    exact comp_proj_invariant
      (D.restrictOpenHom (Q.proj ⁻¹ᵁ W₀) (Q.isTransitionInvariant_proj_preimage W₀)) Q

/-! ### Two descended schemes of one datum are canonically isomorphic -/

/-- The projection of a descended scheme equalises the two projections of the self-fibre
product of any other descended scheme of the same datum. -/
theorem fst_comp_proj (Q' : D.Descended) :
    pullback.fst Q.proj Q.proj ≫ Q'.proj = pullback.snd Q.proj Q.proj ≫ Q'.proj := by
  have hiso := Q.isPullback_legs
  rw [← cancel_epi hiso.isoPullback.hom, ← Category.assoc, ← Category.assoc,
    hiso.isoPullback_hom_fst, hiso.isoPullback_hom_snd]
  exact Q'.proj_invariant

variable [Surjective f] [Flat f] [QuasiCompact f]

include Q in
/-- **Two descended schemes of one descent datum are canonically isomorphic.** There is
exactly one morphism of the descended schemes compatible with the two projections. -/
theorem existsUnique_comp_eq (Q' : D.Descended) :
    ∃! e : Q.base.left ⟶ Q'.base.left, Q.proj ≫ e = Q'.proj := by
  obtain ⟨ψ, hψ⟩ := exists_desc_of_surjective_flat_quasiCompact' Q.proj Q'.proj
    (Q.fst_comp_proj Q')
  exact ⟨ψ, hψ, fun ψ' hψ' ↦ eq_of_comp_eq_of_surjective_of_flat Q.proj (hψ'.trans hψ.symm)⟩

/-- The comparison morphism between two descended schemes of one descent datum. -/
def compare (Q' : D.Descended) : Q.base.left ⟶ Q'.base.left :=
  (Q.existsUnique_comp_eq Q').choose

/-- The comparison morphism is compatible with the two projections. -/
@[reassoc (attr := simp)]
lemma proj_comp_compare (Q' : D.Descended) : Q.proj ≫ Q.compare Q' = Q'.proj :=
  (Q.existsUnique_comp_eq Q').choose_spec.1

include Q in
/-- The comparison morphism is the only morphism compatible with the two projections. -/
lemma eq_compare (Q' : D.Descended) {e : Q.base.left ⟶ Q'.base.left}
    (he : Q.proj ≫ e = Q'.proj) : e = Q.compare Q' :=
  (Q.existsUnique_comp_eq Q').choose_spec.2 e he

/-- The comparison morphism of a descended scheme with itself is the identity. -/
@[simp]
lemma compare_self : Q.compare Q = 𝟙 _ :=
  (Q.eq_compare Q (Category.comp_id _)).symm

/-- The comparison morphisms compose. -/
@[reassoc (attr := simp)]
lemma compare_comp_compare (Q' Q'' : D.Descended) :
    Q.compare Q' ≫ Q'.compare Q'' = Q.compare Q'' :=
  Q.eq_compare Q'' (e := Q.compare Q' ≫ Q'.compare Q'')
    (by rw [← Category.assoc, proj_comp_compare, proj_comp_compare])

/-- The comparison morphism is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma compare_comp_hom (Q' : D.Descended) : Q.compare Q' ≫ Q'.base.hom = Q.base.hom :=
  eq_of_comp_eq_of_surjective_of_flat Q.proj <| by
    rw [← Category.assoc, proj_comp_compare, ← Q'.isPullback.w, Q.isPullback.w]

/-- The comparison morphism is an isomorphism, with inverse the comparison morphism in the
other direction. -/
instance isIso_compare (Q' : D.Descended) : IsIso (Q.compare Q') :=
  ⟨Q'.compare Q, by rw [compare_comp_compare, compare_self],
    by rw [compare_comp_compare, compare_self]⟩

/-- **Two descended schemes of one descent datum are isomorphic over `S`.** -/
def compareIso (Q' : D.Descended) : Q.base ≅ Q'.base :=
  Over.isoMk (asIso (Q.compare Q')) (Q.compare_comp_hom Q')

/-! ### The chart over a smaller invariant open -/

section Shrink

variable {D : DescentDatum f} {W : D.over.left.Opens} {hW : D.IsTransitionInvariant W}
  (Q : (D.restrictOpen W hW).Descended)

omit [Surjective f] [Flat f] [QuasiCompact f] in
/-- An invariant open of `V` cuts out an invariant open of the scheme of the restriction of
the datum to a larger invariant open. -/
theorem isTransitionInvariant_ι_preimage {Z : D.over.left.Opens}
    (hZ : D.IsTransitionInvariant Z) :
    (D.restrictOpen W hW).IsTransitionInvariant (W.ι ⁻¹ᵁ Z) :=
  DescentDatum.isTransitionInvariant_preimage (D.restrictOpenHom W hW) hZ

/-- The open of the descended scheme cut out by a smaller invariant open of `V`. -/
@[implicit_reducible]
def shrinkOpens {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) : Q.base.left.Opens :=
  (Q.existsUnique_opens_preimage_eq (W.ι ⁻¹ᵁ Z) (isTransitionInvariant_ι_preimage hZ)).choose

/-- The open cut out by a smaller invariant open pulls back to it. -/
@[simp]
lemma proj_preimage_shrinkOpens {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) :
    Q.proj ⁻¹ᵁ Q.shrinkOpens hZ = W.ι ⁻¹ᵁ Z :=
  (Q.existsUnique_opens_preimage_eq (W.ι ⁻¹ᵁ Z)
    (isTransitionInvariant_ι_preimage hZ)).choose_spec.1

/-- The open cut out by a smaller invariant open is the only one pulling back to it. -/
lemma eq_shrinkOpens {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z)
    {O : Q.base.left.Opens} (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) : O = Q.shrinkOpens hZ :=
  (Q.existsUnique_opens_preimage_eq (W.ι ⁻¹ᵁ Z)
    (isTransitionInvariant_ι_preimage hZ)).choose_spec.2 O hO

/-- The open cut out depends only on the smaller invariant open. -/
lemma shrinkOpens_congr {Z Z' : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z)
    (hZ' : D.IsTransitionInvariant Z') (h : Z = Z') :
    Q.shrinkOpens hZ = Q.shrinkOpens hZ' := by
  subst h; rfl

/-- A smaller invariant open of `V`, identified with the part of the datum's scheme cut out by
the open it descends to. -/
def shrinkIso {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W) :
    Z.toScheme ≅ (Q.proj ⁻¹ᵁ Q.shrinkOpens hZ).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.over.left.homOfLE hle) (Q.proj ⁻¹ᵁ Q.shrinkOpens hZ).ι
    (by simp only [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι,
      Scheme.opensRange_homOfLE, Q.proj_preimage_shrinkOpens])

/-- That identification is the inclusion of the smaller open. -/
lemma shrinkIso_hom_ι {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W) :
    (Q.shrinkIso hZ hle).hom ≫ (Q.proj ⁻¹ᵁ Q.shrinkOpens hZ).ι =
      D.over.left.homOfLE hle :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The projection of the descended scheme of the restriction to a smaller invariant open. -/
@[implicit_reducible]
def shrinkProj {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W) :
    Z.toScheme ⟶ (Q.shrinkOpens hZ).toScheme :=
  (Q.shrinkIso hZ hle).hom ≫ (Q.proj ∣_ Q.shrinkOpens hZ)

/-- **The characterisation of the restricted projection**: followed by the inclusion of the
descended open it is the inclusion of the smaller open followed by the projection. -/
@[reassoc]
lemma shrinkProj_comp_ι {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z)
    (hle : Z ≤ W) :
    Q.shrinkProj hZ hle ≫ (Q.shrinkOpens hZ).ι = D.over.left.homOfLE hle ≫ Q.proj := by
  rw [shrinkProj, Category.assoc, morphismRestrict_ι, ← Category.assoc, Q.shrinkIso_hom_ι]

/-- **The descended scheme of the restriction to a smaller invariant open.** -/
@[implicit_reducible]
def shrink {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W) :
    (D.restrictOpen Z hZ).Descended where
  base := Over.mk ((Q.shrinkOpens hZ).ι ≫ Q.base.hom)
  proj := Q.shrinkProj hZ hle
  isPullback := by
    have s : IsPullback (Q.shrinkProj hZ hle) (D.over.left.homOfLE hle)
        (Q.shrinkOpens hZ).ι Q.proj :=
      (isPullback_morphismRestrict Q.proj (Q.shrinkOpens hZ)).of_iso'
        (Q.shrinkIso hZ hle) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by rw [Iso.refl_hom, Category.comp_id]; rfl)
        (by rw [Iso.refl_hom, Category.comp_id]; exact Q.shrinkIso_hom_ι hZ hle)
        (by simp) (by simp)
    have h := s.paste_vert Q.isPullback.flip
    rw [show D.over.left.homOfLE hle ≫ (D.restrictOpen W hW).over.hom =
        (D.restrictOpen Z hZ).over.hom from by
      change D.over.left.homOfLE hle ≫ W.ι ≫ D.over.hom = Z.ι ≫ D.over.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]] at h
    exact h.flip
  proj_invariant := by
    refine (cancel_mono (Q.shrinkOpens hZ).ι).mp ?_
    rw [Category.assoc, Category.assoc, Q.shrinkProj_comp_ι, Category.assoc,
      Q.shrinkProj_comp_ι]
    exact comp_proj_invariant (D.restrictOpenMono hZ hW hle) Q

/-- The projection of the restricted descended scheme. -/
@[simp]
lemma shrink_proj {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W) :
    (Q.shrink hZ hle).proj = Q.shrinkProj hZ hle := rfl

/-- The scheme of the restricted descended scheme. -/
@[simp]
lemma shrink_base {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W) :
    (Q.shrink hZ hle).base = Over.mk ((Q.shrinkOpens hZ).ι ≫ Q.base.hom) := rfl

/-- The restricted projection is surjective, being the projection of a descended scheme. -/
instance surjective_shrinkProj {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z)
    (hle : Z ≤ W) : Surjective (Q.shrinkProj hZ hle) :=
  inferInstanceAs (Surjective (Q.shrink hZ hle).proj)

/-- The restricted projection is flat, being the projection of a descended scheme. -/
instance flat_shrinkProj {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z)
    (hle : Z ≤ W) : Flat (Q.shrinkProj hZ hle) :=
  inferInstanceAs (Flat (Q.shrink hZ hle).proj)

/-- The restricted projection is an epimorphism, being surjective and flat. -/
instance epi_shrinkProj {Z : D.over.left.Opens} (hZ : D.IsTransitionInvariant Z)
    (hle : Z ≤ W) : Epi (Q.shrinkProj hZ hle) :=
  Flat.epi_of_flat_of_surjective _

end Shrink

end Descended

/-- **An effective descent datum has a descended scheme.** This is the converse of
`AlgebraicGeometry.DescentDatum.Descended.isEffective`. -/
theorem nonempty_descended_of_isEffective {D : DescentDatum f} (hD : D.IsEffective) :
    Nonempty D.Descended :=
  ⟨Descended.ofIso hD.getIso⟩

/-- **Effectivity is the existence of a descended scheme.** -/
theorem isEffective_iff_nonempty_descended (D : DescentDatum f) :
    D.IsEffective ↔ Nonempty D.Descended :=
  ⟨nonempty_descended_of_isEffective, fun ⟨Q⟩ ↦ Q.isEffective⟩

/-! ### Families of charts glued over the base -/

/-- **A family of charts glued over the base.** A glueing datum over `S`, an open cover of `V`
indexed by its pieces with each member invariant, and a projection of each member onto the
corresponding piece exhibiting that member as the fibre product of the piece with `X` over `S`,
equalising the two legs of the gluing isomorphism and agreeing with the other projections
inside the glued scheme. -/
structure GluedChartFamily (D : DescentDatum f) where
  /-- The glueing datum over the base: a scheme over `S` for each index, with overlaps and
  transition isomorphisms satisfying the cocycle condition. -/
  glue : Scheme.GlueDataOverBase S
  /-- The member of the cover of `V` attached to the `i`-th piece. -/
  opens : glue.J → D.over.left.Opens
  /-- The members of the family cover `V`. -/
  isOpenCover : TopologicalSpace.IsOpenCover opens
  /-- Each member of the family is invariant under the gluing isomorphism. -/
  invariant : ∀ i, D.IsTransitionInvariant (opens i)
  /-- The projection of the `i`-th member of the family onto the `i`-th piece. -/
  proj : ∀ i, (opens i).toScheme ⟶ glue.obj i
  /-- The `i`-th projection exhibits the `i`-th member of the family as the fibre product of
  the `i`-th piece with `X` over `S`. -/
  isPullback : ∀ i, IsPullback ((opens i).ι ≫ D.over.hom) (proj i) f (glue.proj i)
  /-- The `i`-th projection equalises the gluing isomorphism of the restricted datum followed
  by the projection of `X ×_S Vᵢ` to `Vᵢ` and the projection of `Vᵢ ×_S X` to `Vᵢ`. -/
  proj_invariant : ∀ i, (D.restrictOpen (opens i) (invariant i)).transitionPullbackIso.hom ≫
      pullback.snd f ((D.restrictOpen (opens i) (invariant i)).over.hom ≫ f) ≫ proj i =
    pullback.fst ((D.restrictOpen (opens i) (invariant i)).over.hom ≫ f) f ≫ proj i
  /-- The projections agree on the intersection of two members of the family after passing to
  the glued scheme. -/
  proj_comp_ι : ∀ i j, D.over.left.homOfLE (inf_le_left : opens i ⊓ opens j ≤ opens i) ≫
      proj i ≫ glue.ι i =
    D.over.left.homOfLE (inf_le_right : opens i ⊓ opens j ≤ opens j) ≫ proj j ≫ glue.ι j
  /-- The `i`-th projection pulls the part of the `i`-th piece glued to the `j`-th back to the
  part of the `i`-th member of the family lying in the `j`-th. -/
  proj_preimage_overlap : ∀ i j, proj i ⁻¹ᵁ glue.overlap i j = (opens i).ι ⁻¹ᵁ opens j

namespace GluedChartFamily

variable {D : DescentDatum f} (C : D.GluedChartFamily)

/-- The `i`-th piece, as a descended scheme of the restriction of the datum to the `i`-th
member of the family. -/
def chart (i : C.glue.J) : (D.restrictOpen (C.opens i) (C.invariant i)).Descended where
  base := Over.mk (C.glue.proj i)
  proj := C.proj i
  isPullback := C.isPullback i
  proj_invariant := C.proj_invariant i

/-- The open cover of `V` by the members of the family. -/
@[implicit_reducible]
def cover : D.over.left.OpenCover :=
  D.over.left.openCoverOfIsOpenCover C.opens C.isOpenCover

/-- The two descriptions of the projection onto the glued scheme agree on the fibre product of
two members of the family. -/
lemma pullbackFst_comp_proj_comp_ι (i j : C.glue.J) :
    pullback.fst (C.opens i).ι (C.opens j).ι ≫ C.proj i ≫ C.glue.ι i =
      pullback.snd (C.opens i).ι (C.opens j).ι ≫ C.proj j ≫ C.glue.ι j := by
  rw [← (isPullback_opens_inf (C.opens i) (C.opens j)).isoPullback_inv_fst,
    ← (isPullback_opens_inf (C.opens i) (C.opens j)).isoPullback_inv_snd, Category.assoc,
    Category.assoc, C.proj_comp_ι i j]

/-- **The projection of `V` onto the glued scheme.** On the `i`-th member of the family it is
the `i`-th projection followed by the `i`-th chart of the glued scheme. -/
@[implicit_reducible]
def glueProj : D.over.left ⟶ C.glue.glued :=
  C.cover.glueMorphisms (fun i ↦ C.proj i ≫ C.glue.ι i) C.pullbackFst_comp_proj_comp_ι

/-- **The projection onto the glued scheme, restricted to a member of the family.** -/
@[reassoc]
lemma ι_comp_glueProj (i : C.glue.J) :
    (C.opens i).ι ≫ C.glueProj = C.proj i ≫ C.glue.ι i :=
  Scheme.Cover.ι_glueMorphisms C.cover _ _ i

/-- The projection onto the glued scheme is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma glueProj_comp_toBase : C.glueProj ≫ C.glue.toBase = D.over.hom ≫ f := by
  refine Scheme.Cover.hom_ext C.cover _ _ fun (i : C.glue.J) ↦ ?_
  change (C.opens i).ι ≫ C.glueProj ≫ C.glue.toBase = (C.opens i).ι ≫ D.over.hom ≫ f
  rw [← Category.assoc, C.ι_comp_glueProj i, Category.assoc, C.glue.ι_toBase,
    ← (C.isPullback i).w, Category.assoc]

/-- **The `i`-th member of the family is the part of `V` lying in the `i`-th chart of the glued
scheme.** -/
lemma glueProj_preimage_opensRange (i : C.glue.J) :
    C.glueProj ⁻¹ᵁ (C.glue.ι i).opensRange = C.opens i := by
  refine Scheme.opens_eq_of_isOpenCover C.isOpenCover fun j ↦ ?_
  calc (C.opens j).ι ⁻¹ᵁ (C.glueProj ⁻¹ᵁ (C.glue.ι i).opensRange)
      = (C.proj j ≫ C.glue.ι j) ⁻¹ᵁ (C.glue.ι i).opensRange := by
        rw [← Scheme.Hom.comp_preimage, C.ι_comp_glueProj j]
    _ = C.proj j ⁻¹ᵁ (C.glue.ι j ⁻¹ᵁ (C.glue.ι i).opensRange) := Scheme.Hom.comp_preimage _ _ _
    _ = C.proj j ⁻¹ᵁ C.glue.overlap j i := by rw [C.glue.preimage_opensRange_ι j i]
    _ = (C.opens j).ι ⁻¹ᵁ C.opens i := C.proj_preimage_overlap j i

/-- The `i`-th member of the family, identified with the part of `V` lying in the `i`-th chart
of the glued scheme. -/
@[implicit_reducible]
def gluedPreimageIso (i : C.glue.J) :
    (C.opens i).toScheme ≅ (C.glueProj ⁻¹ᵁ (C.glue.ι i).opensRange).toScheme :=
  D.over.left.isoOfEq (C.glueProj_preimage_opensRange i).symm

/-- **The `i`-th chart of the glued scheme is cut out by the `i`-th member of the family**: the
`i`-th projection and the inclusion of that member exhibit it as the fibre product of the
`i`-th piece with `V` over the glued scheme. -/
lemma isPullback_proj_glueProj (i : C.glue.J) :
    IsPullback (C.proj i) (C.opens i).ι (C.glue.ι i) C.glueProj := by
  refine (isPullback_morphismRestrict C.glueProj (C.glue.ι i).opensRange).of_iso'
    (C.gluedPreimageIso i) (C.glue.ι i).isoOpensRange (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ (by simp)
  · refine (cancel_mono (C.glue.ι i).opensRange.ι).mp ?_
    rw [Category.assoc, morphismRestrict_ι, Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, ← C.ι_comp_glueProj i, ← Category.assoc]
    exact congrArg (· ≫ C.glueProj) (Scheme.isoOfEq_hom_ι _ _)
  · rw [Iso.refl_hom, Category.comp_id]
    exact Scheme.isoOfEq_hom_ι _ _
  · rw [Iso.refl_hom, Category.comp_id]
    exact Scheme.Hom.isoOpensRange_hom_ι _

/-- The open cover of the glued scheme by its charts. -/
@[implicit_reducible]
def gluedCover : C.glue.glued.OpenCover where
  I₀ := C.glue.J
  X i := C.glue.obj i
  f i := C.glue.ι i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun y ↦ C.glue.ι_jointly_surjective y, fun i ↦ C.glue.isOpenImmersion_ι i⟩

/-- **The glued scheme descends the datum**: the projection onto the glued scheme and the
structure morphism of `V` over `X` exhibit `V` as the fibre product of the glued scheme with
`X` over `S`. -/
lemma isPullback_glueProj : IsPullback C.glueProj D.over.hom C.glue.toBase f := by
  refine Precoverage.ZeroHypercover.isPullback_of_forall_isPullback C.glueProj D.over.hom
    C.glue.toBase f C.gluedCover fun i ↦ ?_
  refine (C.isPullback i).flip.of_iso
    (C.isPullback_proj_glueProj i).flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ (by simp)
  · rw [Iso.refl_hom, Category.comp_id]
    exact ((C.isPullback_proj_glueProj i).flip.isoPullback_hom_snd).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    exact congrArg (· ≫ D.over.hom)
      ((C.isPullback_proj_glueProj i).flip.isoPullback_hom_fst).symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.refl_hom, Category.id_comp]
    exact (C.glue.ι_toBase i).symm

/-- The part of `V ×_S X` lying over the `i`-th member of the family, mapped to the fibre
product of that member with `X` over `S`. -/
@[implicit_reducible]
def sourcePart (i : C.glue.J) :
    (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ C.opens i).toScheme ⟶
      pullback ((D.restrictOpen (C.opens i) (C.invariant i)).over.hom ≫ f) f :=
  pullback.lift (pullback.fst (D.over.hom ≫ f) f ∣_ C.opens i)
    ((pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ C.opens i).ι ≫ pullback.snd (D.over.hom ≫ f) f)
    (by
      change (pullback.fst (D.over.hom ≫ f) f ∣_ C.opens i) ≫
          ((C.opens i).ι ≫ D.over.hom) ≫ f =
        ((pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ C.opens i).ι ≫
          pullback.snd (D.over.hom ≫ f) f) ≫ f
      rw [Category.assoc, ← Category.assoc ((pullback.fst (D.over.hom ≫ f) f) ∣_ C.opens i),
        morphismRestrict_ι, Category.assoc, Category.assoc, pullback.condition])

/-- The part of `V ×_S X` lying over the `i`-th member of the family factors through the base
change of the inclusion of that member. -/
lemma sourcePart_comp_homSourceMap (i : C.glue.J) :
    C.sourcePart i ≫
        DescentDatum.homSourceMap (D.restrictOpenHom (C.opens i) (C.invariant i)) =
      (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ C.opens i).ι := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, DescentDatum.homSourceMap_comp_fst,
      DescentDatum.restrictOpenHom_hom_left, sourcePart, ← Category.assoc, pullback.lift_fst,
      morphismRestrict_ι]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, sourcePart, pullback.lift_snd]

/-- The cover of `V ×_S X` by the parts lying over the members of the family. -/
@[implicit_reducible]
def sourceCover : (pullback (D.over.hom ≫ f) f).OpenCover :=
  (pullback (D.over.hom ≫ f) f).openCoverOfIsOpenCover
    (fun i ↦ pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ C.opens i)
    (TopologicalSpace.IsOpenCover.mk (by
      rw [← Scheme.Hom.preimage_iSup, C.isOpenCover.iSup_eq_top, Scheme.Hom.preimage_top]))

/-- **The invariance of the glued projection, checked over the `i`-th member of the family**:
the two legs of the gluing isomorphism followed by the projection onto the glued scheme agree
after precomposing with the base change of the inclusion of that member. -/
lemma homSourceMap_comp_glueProj_invariant (i : C.glue.J) :
    DescentDatum.homSourceMap (D.restrictOpenHom (C.opens i) (C.invariant i)) ≫
        D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫ C.glueProj =
      DescentDatum.homSourceMap (D.restrictOpenHom (C.opens i) (C.invariant i)) ≫
        pullback.fst (D.over.hom ≫ f) f ≫ C.glueProj := by
  rw [← Category.assoc, DescentDatum.transitionPullbackIso_naturality, Category.assoc,
    DescentDatum.homTargetMap_comp_snd_assoc, DescentDatum.homSourceMap_comp_fst_assoc,
    DescentDatum.restrictOpenHom_hom_left, C.ι_comp_glueProj i,
    reassoc_of% (C.proj_invariant i)]

/-- **The projection onto the glued scheme equalises the two legs of the gluing
isomorphism.** -/
lemma glueProj_invariant :
    D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫ C.glueProj =
      pullback.fst (D.over.hom ≫ f) f ≫ C.glueProj := by
  refine Scheme.Cover.hom_ext C.sourceCover _ _ fun (i : C.glue.J) ↦ ?_
  change (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ C.opens i).ι ≫ _ =
    (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ C.opens i).ι ≫ _
  rw [← C.sourcePart_comp_homSourceMap i, Category.assoc, Category.assoc,
    C.homSourceMap_comp_glueProj_invariant i]

/-- **The descended scheme obtained by glueing a family of charts.** Its scheme over `S` is the
glued scheme of the glueing datum, and its projection is
`AlgebraicGeometry.DescentDatum.GluedChartFamily.glueProj`. -/
@[implicit_reducible]
def descended : D.Descended where
  base := Over.mk C.glue.toBase
  proj := C.glueProj
  isPullback := C.isPullback_glueProj.flip
  proj_invariant := C.glueProj_invariant

end GluedChartFamily

/-- **A descent datum with a family of charts glued over the base is effective.** -/
theorem isEffective_of_gluedChartFamily {D : DescentDatum f} (C : D.GluedChartFamily) :
    DescentData.IsEffective D :=
  C.descended.isEffective

/-! ### Families of charts -/

/-- **A family of charts for a descent datum.** An invariant open neighbourhood of each point
of `V`, together with a descended scheme for the restriction of the datum to it. -/
structure ChartFamily (D : DescentDatum f) where
  /-- The invariant open neighbourhood of a point. -/
  opens : D.over.left → D.over.left.Opens
  /-- Each member of the family is invariant. -/
  invariant (v : D.over.left) : D.IsTransitionInvariant (opens v)
  /-- The descended scheme of the restriction to each member. -/
  chart (v : D.over.left) : (D.restrictOpen (opens v) (invariant v)).Descended
  /-- The family covers `V`. -/
  mem (v : D.over.left) : v ∈ opens v

namespace ChartFamily

variable {D : DescentDatum f} (C : D.ChartFamily)

/-- The members of a chart family cover `V`. -/
lemma isOpenCover : TopologicalSpace.IsOpenCover C.opens :=
  top_le_iff.mp fun v _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨v, C.mem v⟩

/-- A pairwise intersection of members is invariant. -/
theorem invariant_inf (v w : D.over.left) :
    D.IsTransitionInvariant (C.opens v ⊓ C.opens w) :=
  DescentDatum.isTransitionInvariant_inf D (C.invariant v) (C.invariant w)

/-- A triple intersection of members is invariant. -/
theorem invariant_inf₃ (v w x : D.over.left) :
    D.IsTransitionInvariant (C.opens v ⊓ C.opens w ⊓ C.opens x) :=
  DescentDatum.isTransitionInvariant_inf D (C.invariant_inf v w) (C.invariant x)

variable [Surjective f] [Flat f] [QuasiCompact f]

/-- The part of the `v`-th chart glued to the `w`-th: the open of the `v`-th descended scheme
cut out by `W v ⊓ W w`. -/
@[implicit_reducible]
def overlap (v w : D.over.left) : (C.chart v).base.left.Opens :=
  (C.chart v).shrinkOpens (C.invariant_inf v w)

/-- The descended scheme of the restriction to `W v ⊓ W w`, seen inside the `v`-th chart. -/
@[implicit_reducible]
def interChart (v w : D.over.left) :
    (D.restrictOpen (C.opens v ⊓ C.opens w) (C.invariant_inf v w)).Descended :=
  (C.chart v).shrink (C.invariant_inf v w) inf_le_left

/-- The descended scheme of the restriction to `W v ⊓ W w`, seen inside the `w`-th chart. -/
@[implicit_reducible]
def interChart' (v w : D.over.left) :
    (D.restrictOpen (C.opens v ⊓ C.opens w) (C.invariant_inf v w)).Descended :=
  (C.chart w).shrink (C.invariant_inf v w) inf_le_right

/-- The projection of the descended scheme of the restriction to `W v ⊓ W w` is surjective. -/
instance (v w : D.over.left) : Surjective (C.interChart v w).proj := inferInstance

/-- The projection of the descended scheme of the restriction to `W v ⊓ W w` is flat. -/
instance (v w : D.over.left) : Flat (C.interChart v w).proj := inferInstance

/-- The projection onto the overlap is an epimorphism, being surjective and flat. -/
instance epi_interChart_proj (v w : D.over.left) : Epi (C.interChart v w).proj :=
  Flat.epi_of_flat_of_surjective _

/-- The open of the `w`-th chart cut out by `W v ⊓ W w` is the one cut out by `W w ⊓ W v`. -/
lemma shrinkOpens_inf_comm (v w : D.over.left) :
    (C.chart w).shrinkOpens (C.invariant_inf v w) = C.overlap w v :=
  (C.chart w).shrinkOpens_congr _ _ (inf_comm _ _)

/-- **The transition morphism of the glueing datum.** The two descended schemes of the
restriction to `W v ⊓ W w` — the one inside the `v`-th chart and the one inside the `w`-th —
are canonically isomorphic, and this is that comparison, read as a morphism from the `(v, w)`-th
overlap to the `(w, v)`-th. -/
@[implicit_reducible]
def t (v w : D.over.left) : (C.overlap v w).toScheme ⟶ (C.overlap w v).toScheme :=
  (C.interChart v w).compare (C.interChart' v w) ≫
    ((C.chart w).base.left.isoOfEq (C.shrinkOpens_inf_comm v w)).hom

/-- The projection onto the `(v, w)`-th overlap, followed by its inclusion into the `v`-th
descended scheme, is the inclusion of `W v ⊓ W w` into `W v` followed by the `v`-th
projection. -/
lemma interChart_proj_comp_ι (v w : D.over.left) :
    (C.interChart v w).proj ≫ (C.overlap v w).ι =
      D.over.left.homOfLE (inf_le_left : C.opens v ⊓ C.opens w ≤ C.opens v) ≫
        (C.chart v).proj :=
  (C.chart v).shrinkProj_comp_ι _ _

/-- The same for the `w`-th chart. -/
lemma interChart'_proj_comp_ι (v w : D.over.left) :
    (C.interChart' v w).proj ≫ ((C.chart w).shrinkOpens (C.invariant_inf v w)).ι =
      D.over.left.homOfLE (inf_le_right : C.opens v ⊓ C.opens w ≤ C.opens w) ≫
        (C.chart w).proj :=
  (C.chart w).shrinkProj_comp_ι _ _

/-- The projection onto the `(v, w)`-th overlap, followed by the transition morphism and the
inclusion of the `(w, v)`-th overlap into the `w`-th descended scheme, is the inclusion of
`W v ⊓ W w` into `W w` followed by the `w`-th projection. -/
lemma interChart_proj_comp_t_comp_ι (v w : D.over.left) :
    (C.interChart v w).proj ≫ C.t v w ≫ (C.overlap w v).ι =
      D.over.left.homOfLE (inf_le_right : C.opens v ⊓ C.opens w ≤ C.opens w) ≫
        (C.chart w).proj := by
  simp only [t, Category.assoc, Scheme.isoOfEq_hom_ι,
    Descended.proj_comp_compare_assoc]
  exact C.interChart'_proj_comp_ι v w

omit [Surjective f] [Flat f] [QuasiCompact f] in
/-- The projection of a chart, restricted to a smaller open `Z`, followed by the structure
morphism of the descended scheme, is the inclusion of `Z` followed by the structure morphism of
`V` over `S`. -/
lemma homOfLE_comp_proj_comp_base_hom (v : D.over.left) {Z : D.over.left.Opens}
    (hle : Z ≤ C.opens v) :
    D.over.left.homOfLE hle ≫ (C.chart v).proj ≫ (C.chart v).base.hom =
      Z.ι ≫ D.over.hom ≫ f := by
  rw [← (C.chart v).isPullback.w]
  change D.over.left.homOfLE hle ≫ ((C.opens v).ι ≫ D.over.hom) ≫ f = Z.ι ≫ D.over.hom ≫ f
  rw [← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, Category.assoc]

/-- **A chart is glued to itself along the whole of itself.** -/
lemma overlap_self (v : D.over.left) : C.overlap v v = ⊤ :=
  ((C.chart v).eq_shrinkOpens (C.invariant_inf v v)
    (by rw [Scheme.Hom.preimage_top, inf_idem, Scheme.Opens.ι_preimage_self])).symm

/-- Two maps out of the `v`-th and `w`-th charts agree on `W v ⊓ W w`, after precomposing with the
restricted projections, exactly when they are compatible with the transition morphism. -/
private lemma homOfLE_comp_proj_eq_iff (v w : D.over.left) {T : Scheme.{u}}
    (k : (C.chart v).base.left ⟶ T) (k' : (C.chart w).base.left ⟶ T) :
    D.over.left.homOfLE (inf_le_left : C.opens v ⊓ C.opens w ≤ C.opens v) ≫
        (C.chart v).proj ≫ k =
      D.over.left.homOfLE (inf_le_right : C.opens v ⊓ C.opens w ≤ C.opens w) ≫
        (C.chart w).proj ≫ k' ↔
    (C.overlap v w).ι ≫ k = C.t v w ≫ (C.overlap w v).ι ≫ k' := by
  rw [← cancel_epi (C.interChart v w).proj, ← Category.assoc, ← Category.assoc,
    ← C.interChart_proj_comp_ι, ← Category.assoc, ← Category.assoc,
    ← C.interChart_proj_comp_t_comp_ι, Category.assoc, Category.assoc]
  simp only [Category.assoc]

/-- **The transition morphisms lie over `S`.** -/
lemma t_over (v w : D.over.left) :
    C.t v w ≫ (C.overlap w v).ι ≫ (C.chart w).base.hom =
      (C.overlap v w).ι ≫ (C.chart v).base.hom :=
  ((C.homOfLE_comp_proj_eq_iff v w _ _).mp (by
    rw [C.homOfLE_comp_proj_comp_base_hom v inf_le_left,
      C.homOfLE_comp_proj_comp_base_hom w inf_le_right])).symm

/-- **The transition from a chart to itself is the identity.** -/
lemma t_self (v : D.over.left) : C.t v v = 𝟙 _ := by
  refine (cancel_mono (C.overlap v v).ι).mp ?_
  refine (cancel_epi (C.interChart v v).proj).mp ?_
  rw [Category.id_comp]
  rw [C.interChart_proj_comp_t_comp_ι v v, C.interChart_proj_comp_ι v v]

/-- **The triple overlap is the open cut out by a triple intersection.** -/
lemma overlap_inf (v w x : D.over.left) :
    C.overlap v w ⊓ C.overlap v x = (C.chart v).shrinkOpens (C.invariant_inf₃ v w x) := by
  refine (C.chart v).eq_shrinkOpens (C.invariant_inf₃ v w x) ?_
  have h : (C.opens v ⊓ C.opens w) ⊓ (C.opens v ⊓ C.opens x) =
      C.opens v ⊓ C.opens w ⊓ C.opens x := by
    rw [inf_inf_inf_comm, inf_idem, inf_assoc]
  rw [Scheme.Hom.preimage_inf]
  simp only [overlap, Descended.proj_preimage_shrinkOpens]
  rw [← Scheme.Hom.preimage_inf, h]

/-! ### The transition morphisms on triple overlaps -/

/-- The descended scheme of the restriction of the datum to the triple intersection
`W v ⊓ W w ⊓ W x`, seen inside the `v`-th chart. -/
@[implicit_reducible]
def tripleChart (v w x : D.over.left) :
    (D.restrictOpen (C.opens v ⊓ C.opens w ⊓ C.opens x)
      (C.invariant_inf₃ v w x)).Descended :=
  (C.chart v).shrink (C.invariant_inf₃ v w x) (le_trans inf_le_left inf_le_left)

/-- The descended scheme of the restriction of the datum to the triple intersection
`W v ⊓ W w ⊓ W x`, seen inside the `w`-th chart. -/
@[implicit_reducible]
def tripleChart' (v w x : D.over.left) :
    (D.restrictOpen (C.opens v ⊓ C.opens w ⊓ C.opens x)
      (C.invariant_inf₃ v w x)).Descended :=
  (C.chart w).shrink (C.invariant_inf₃ v w x) (le_trans inf_le_left inf_le_right)

/-- **The comparison morphism on a triple intersection.** The two descended schemes of the
restriction to `W v ⊓ W w ⊓ W x` — the one inside the `v`-th chart and the one inside the
`w`-th — are canonically isomorphic, and this is that comparison, read between the two opens
they cut out. -/
@[implicit_reducible]
def tripleCompare (v w x : D.over.left) :
    ((C.chart v).shrinkOpens (C.invariant_inf₃ v w x)).toScheme ⟶
      ((C.chart w).shrinkOpens (C.invariant_inf₃ v w x)).toScheme :=
  (C.tripleChart v w x).compare (C.tripleChart' v w x)

/-- The comparison morphism on a triple intersection is compatible with the two restricted
projections. -/
@[reassoc]
lemma shrinkProj_comp_tripleCompare (v w x : D.over.left) :
    (C.chart v).shrinkProj (C.invariant_inf₃ v w x) (le_trans inf_le_left inf_le_left) ≫
        C.tripleCompare v w x =
      (C.chart w).shrinkProj (C.invariant_inf₃ v w x) (le_trans inf_le_left inf_le_right) :=
  (C.tripleChart v w x).proj_comp_compare (C.tripleChart' v w x)

omit [Surjective f] [Flat f] [QuasiCompact f] in
/-- The triple intersections attached to the three cyclic orders of a triple of indices are
equal. -/
lemma opens_inf₃_cycle (v w x : D.over.left) :
    C.opens v ⊓ C.opens w ⊓ C.opens x = C.opens w ⊓ C.opens x ⊓ C.opens v := by
  rw [inf_assoc, inf_comm]

/-- **The projection of a triple intersection onto the triple overlap of the `v`-th chart**:
the restricted projection, followed by the identification of the open cut out by the triple
intersection with the intersection of the `(v, w)`-th and `(v, x)`-th overlaps. -/
@[implicit_reducible]
def tripleProj (v w x : D.over.left) :
    (C.opens v ⊓ C.opens w ⊓ C.opens x).toScheme ⟶
      (C.overlap v w ⊓ C.overlap v x).toScheme :=
  (C.chart v).shrinkProj (C.invariant_inf₃ v w x) (le_trans inf_le_left inf_le_left) ≫
    ((C.chart v).base.left.isoOfEq (C.overlap_inf v w x)).inv

/-- The projection onto a triple overlap, as the composite it is defined to be. -/
lemma tripleProj_eq (v w x : D.over.left) :
    C.tripleProj v w x =
      (C.chart v).shrinkProj (C.invariant_inf₃ v w x) (le_trans inf_le_left inf_le_left) ≫
        ((C.chart v).base.left.isoOfEq (C.overlap_inf v w x)).inv := rfl

/-- The projection onto a triple overlap is an epimorphism. -/
instance epi_tripleProj (v w x : D.over.left) : Epi (C.tripleProj v w x) := epi_comp _ _

/-- The projection onto the triple overlap, followed by its inclusion into the `v`-th descended
scheme, is the inclusion of the triple intersection into `W v` followed by the `v`-th
projection. -/
lemma tripleProj_comp_ι (v w x : D.over.left) :
    C.tripleProj v w x ≫ (C.overlap v w ⊓ C.overlap v x).ι =
      D.over.left.homOfLE
          (le_trans inf_le_left inf_le_left : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens v) ≫
        (C.chart v).proj := by
  rw [tripleProj_eq, Category.assoc, Scheme.isoOfEq_inv_ι]
  exact (C.chart v).shrinkProj_comp_ι _ _

/-- The projection onto the triple overlap, followed by the inclusion of the triple overlap in
the `(v, w)`-th overlap, is the inclusion of the triple intersection in `W v ⊓ W w` followed by
the projection onto the `(v, w)`-th overlap. -/
lemma tripleProj_comp_homOfLE (v w x : D.over.left) :
    C.tripleProj v w x ≫ (C.chart v).base.left.homOfLE
        (inf_le_left : C.overlap v w ⊓ C.overlap v x ≤ C.overlap v w) =
      D.over.left.homOfLE
          (inf_le_left : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens v ⊓ C.opens w) ≫
        (C.interChart v w).proj := by
  refine (cancel_mono (C.overlap v w).ι).mp ?_
  have hL : (C.tripleProj v w x ≫ (C.chart v).base.left.homOfLE
        (inf_le_left : C.overlap v w ⊓ C.overlap v x ≤ C.overlap v w)) ≫ (C.overlap v w).ι =
      D.over.left.homOfLE
          (le_trans inf_le_left inf_le_left : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens v) ≫
        (C.chart v).proj := by
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact C.tripleProj_comp_ι v w x
  have hR : (D.over.left.homOfLE
        (inf_le_left : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens v ⊓ C.opens w) ≫
          (C.interChart v w).proj) ≫ (C.overlap v w).ι =
      D.over.left.homOfLE
          (le_trans inf_le_left inf_le_left : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens v) ≫
        (C.chart v).proj := by
    rw [Category.assoc, C.interChart_proj_comp_ι v w, ← Category.assoc,
      Scheme.homOfLE_homOfLE]
  exact hL.trans hR.symm

/-- **The transition morphism of the glueing datum on triple overlaps.** The comparison of the
two descended schemes of the restriction to `W v ⊓ W w ⊓ W x`, read as a morphism from the
triple overlap of the `v`-th chart to the triple overlap of the `w`-th. -/
@[implicit_reducible]
def t' (v w x : D.over.left) :
    (C.overlap v w ⊓ C.overlap v x).toScheme ⟶ (C.overlap w x ⊓ C.overlap w v).toScheme :=
  ((C.chart v).base.left.isoOfEq (C.overlap_inf v w x)).hom ≫ C.tripleCompare v w x ≫
    ((C.chart w).base.left.isoOfEq
      (((C.chart w).shrinkOpens_congr (C.invariant_inf₃ v w x) (C.invariant_inf₃ w x v)
          (C.opens_inf₃_cycle v w x)).trans (C.overlap_inf w x v).symm)).hom

/-- The transition morphism on triple overlaps, as the composite it is defined to be. -/
lemma t'_eq (v w x : D.over.left) :
    C.t' v w x = ((C.chart v).base.left.isoOfEq (C.overlap_inf v w x)).hom ≫
      C.tripleCompare v w x ≫ ((C.chart w).base.left.isoOfEq
        (((C.chart w).shrinkOpens_congr (C.invariant_inf₃ v w x) (C.invariant_inf₃ w x v)
            (C.opens_inf₃_cycle v w x)).trans (C.overlap_inf w x v).symm)).hom := rfl

/-- The projection onto the triple overlap of the `v`-th chart, followed by the transition
morphism, is the projection onto the triple overlap of the `w`-th chart, read through the
identification of the two triple intersections. -/
lemma tripleProj_comp_t' (v w x : D.over.left) :
    C.tripleProj v w x ≫ C.t' v w x =
      (D.over.left.isoOfEq (C.opens_inf₃_cycle v w x)).hom ≫ C.tripleProj w x v := by
  refine (cancel_mono (C.overlap w x ⊓ C.overlap w v).ι).mp ?_
  have hL : (C.tripleProj v w x ≫ C.t' v w x) ≫ (C.overlap w x ⊓ C.overlap w v).ι =
      D.over.left.homOfLE
          (le_trans inf_le_left inf_le_right : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens w) ≫
        (C.chart w).proj := by
    rw [tripleProj_eq, t'_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Scheme.isoOfEq_hom_ι,
      shrinkProj_comp_tripleCompare_assoc]
    exact (C.chart w).shrinkProj_comp_ι _ _
  have hR : ((D.over.left.isoOfEq (C.opens_inf₃_cycle v w x)).hom ≫ C.tripleProj w x v) ≫
      (C.overlap w x ⊓ C.overlap w v).ι =
      D.over.left.homOfLE
          (le_trans inf_le_left inf_le_right : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens w) ≫
        (C.chart w).proj := by
    rw [Category.assoc, C.tripleProj_comp_ι w x v, Scheme.isoOfEq_hom, ← Category.assoc,
      Scheme.homOfLE_homOfLE]
  exact hL.trans hR.symm

/-- **The transition morphism on triple overlaps restricts the one on double overlaps.** -/
lemma t'_fac (v w x : D.over.left) :
    C.t' v w x ≫ (C.chart w).base.left.homOfLE
        (inf_le_right : C.overlap w x ⊓ C.overlap w v ≤ C.overlap w v) =
      (C.chart v).base.left.homOfLE
        (inf_le_left : C.overlap v w ⊓ C.overlap v x ≤ C.overlap v w) ≫ C.t v w := by
  refine (cancel_mono (C.overlap w v).ι).mp ?_
  refine (cancel_epi (C.tripleProj v w x)).mp ?_
  have hL : C.tripleProj v w x ≫ (C.t' v w x ≫ (C.chart w).base.left.homOfLE
        (inf_le_right : C.overlap w x ⊓ C.overlap w v ≤ C.overlap w v)) ≫
        (C.overlap w v).ι =
      D.over.left.homOfLE
          (le_trans inf_le_left inf_le_right : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens w) ≫
        (C.chart w).proj := by
    rw [Category.assoc, Scheme.homOfLE_ι, ← Category.assoc, C.tripleProj_comp_t' v w x,
      Category.assoc, C.tripleProj_comp_ι w x v, Scheme.isoOfEq_hom, ← Category.assoc,
      Scheme.homOfLE_homOfLE]
  have hR : C.tripleProj v w x ≫ ((C.chart v).base.left.homOfLE
        (inf_le_left : C.overlap v w ⊓ C.overlap v x ≤ C.overlap v w) ≫ C.t v w) ≫
        (C.overlap w v).ι =
      D.over.left.homOfLE
          (le_trans inf_le_left inf_le_right : C.opens v ⊓ C.opens w ⊓ C.opens x ≤ C.opens w) ≫
        (C.chart w).proj := by
    rw [Category.assoc, ← Category.assoc (C.tripleProj v w x),
      C.tripleProj_comp_homOfLE v w x, Category.assoc, C.interChart_proj_comp_t_comp_ι v w,
      ← Category.assoc, Scheme.homOfLE_homOfLE]
  exact hL.trans hR.symm

/-- **The cocycle condition for the transition morphisms on triple overlaps.** -/
lemma cocycle (v w x : D.over.left) :
    C.t' v w x ≫ C.t' w x v ≫ C.t' x v w = 𝟙 _ := by
  refine (cancel_epi (C.tripleProj v w x)).mp ?_
  rw [Category.comp_id, ← Category.assoc, C.tripleProj_comp_t' v w x, Category.assoc,
    ← Category.assoc (C.tripleProj w x v), C.tripleProj_comp_t' w x v, Category.assoc,
    C.tripleProj_comp_t' x v w]
  simp only [Scheme.isoOfEq_hom]
  rw [← Category.assoc, Scheme.homOfLE_homOfLE, ← Category.assoc, Scheme.homOfLE_homOfLE]
  simp

/-! ### Glueing the charts -/

/-- **The glueing datum of a family of charts.** The pieces are the descended schemes of the
charts, the part of the `v`-th piece glued to the `w`-th is the open cut out by `W v ⊓ W w`,
and the transition morphisms are the comparisons of the two descended schemes of the
restriction of the datum to an intersection. -/
@[implicit_reducible]
def glueData : Scheme.GlueDataOverBase S where
  J := D.over.left
  obj v := (C.chart v).base.left
  proj v := (C.chart v).base.hom
  overlap := C.overlap
  overlap_self := C.overlap_self
  t := C.t
  t_over := C.t_over
  t_self := C.t_self
  t' := C.t'
  t'_fac := C.t'_fac
  cocycle := C.cocycle

/-- The pieces of the glueing datum are the descended schemes of the charts. -/
@[simp]
lemma glueData_obj (v : D.over.left) : C.glueData.obj v = (C.chart v).base.left := rfl

/-- The structure morphisms of the glueing datum are those of the charts. -/
@[simp]
lemma glueData_proj (v : D.over.left) : C.glueData.proj v = (C.chart v).base.hom := rfl

/-- The overlaps of the glueing datum are the overlaps of the chart family. -/
@[simp]
lemma glueData_overlap (v w : D.over.left) : C.glueData.overlap v w = C.overlap v w := rfl

/-- The transition morphisms of the glueing datum are those of the chart family. -/
@[simp]
lemma glueData_t (v w : D.over.left) : C.glueData.t v w = C.t v w := rfl

/-- The charts of the glued scheme are open immersions. -/
instance isOpenImmersion_gluedι (v : D.over.left) : IsOpenImmersion (C.glueData.ι v) :=
  C.glueData.isOpenImmersion_ι v

/-- The charts of the glued scheme are compatible with the transition morphisms of the chart
family. -/
lemma t_comp_ι_comp_gluedι (v w : D.over.left) :
    C.t v w ≫ (C.overlap w v).ι ≫ C.glueData.ι w = (C.overlap v w).ι ≫ C.glueData.ι v :=
  C.glueData.t_ι v w

/-- **The `(v, w)`-th overlap is the part of the `v`-th descended scheme lying in the `w`-th
chart of the glued scheme.** -/
lemma gluedι_preimage_opensRange (v w : D.over.left) :
    C.glueData.ι v ⁻¹ᵁ (C.glueData.ι w).opensRange = C.overlap v w :=
  C.glueData.preimage_opensRange_ι v w

/-- The two descriptions of the projection onto the glued scheme agree on an intersection of
two members of the chart family. -/
lemma homOfLE_comp_proj_comp_gluedι (v w : D.over.left) :
    D.over.left.homOfLE (inf_le_left : C.opens v ⊓ C.opens w ≤ C.opens v) ≫
        (C.chart v).proj ≫ C.glueData.ι v =
      D.over.left.homOfLE (inf_le_right : C.opens v ⊓ C.opens w ≤ C.opens w) ≫
        (C.chart w).proj ≫ C.glueData.ι w :=
  (C.homOfLE_comp_proj_eq_iff v w _ _).mpr (C.t_comp_ι_comp_gluedι v w).symm

end ChartFamily

/-- **A family of charts is a family of charts glued over the base.** The glueing datum over
the base is `AlgebraicGeometry.DescentDatum.ChartFamily.glueData`, whose transition morphisms
are the comparison isomorphisms of the two descended schemes of the restriction of the datum to
an intersection of two members. -/
def ChartFamily.toGluedChartFamily [Surjective f] [Flat f] [QuasiCompact f]
    {D : DescentDatum f} (C : D.ChartFamily) : D.GluedChartFamily where
  glue := C.glueData
  opens := C.opens
  isOpenCover := C.isOpenCover
  invariant := C.invariant
  proj v := (C.chart v).proj
  isPullback v := (C.chart v).isPullback
  proj_invariant v := (C.chart v).proj_invariant
  proj_comp_ι := C.homOfLE_comp_proj_comp_gluedι
  proj_preimage_overlap v w := by
    change (C.chart v).proj ⁻¹ᵁ C.overlap v w = _
    rw [ChartFamily.overlap, (C.chart v).proj_preimage_shrinkOpens (C.invariant_inf v w),
      Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

/-- **A descent datum with a family of charts is effective.** -/
theorem isEffective_of_chartFamily [Surjective f] [Flat f] [QuasiCompact f]
    {D : DescentDatum f} (C : D.ChartFamily) : D.IsEffective :=
  C.toGluedChartFamily.descended.isEffective

/-- **Effectivity of a descent datum is local on the scheme it is carried by.** Let
`f : X ⟶ S` be a surjective, quasi-compact, flat morphism of schemes and let `(V, φ)` be a
descent datum relative to `X/S`. If every point of `V` has an invariant open neighbourhood
`W ⊆ V` such that the restricted datum `(W, φ|_{W ×_S X})` is effective, then `(V, φ)` is
effective. -/
@[stacks 0AP4, sga "1 VIII 7.2" "local eff ⇒ effective"]
theorem isEffective_of_forall_exists_restrictOpen {S X : Scheme.{u}} {f : X ⟶ S}
    [Surjective f] [Flat f] [QuasiCompact f] (D : DescentDatum f)
    (h : ∀ v : D.over.left, ∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
      v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) :
    DescentData.IsEffective D := by
  choose W hW hmem heff using h
  exact isEffective_of_chartFamily
    { opens := W
      invariant := hW
      chart := fun v ↦ (nonempty_descended_of_isEffective (heff v)).some
      mem := hmem }

end DescentDatum

end AlgebraicGeometry

end
