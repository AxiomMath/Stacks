module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.BaseOpenDatum
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EtaleDescendedRigidity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effectivity of an étale descent datum is local on the base

Let `f : X ⟶ S` be a morphism of schemes and let `(V, φ)` be a descent datum relative to `X/S`
with `V ⟶ X` étale. Let `S = ⋃ Sᵢ` be an open covering. If the pullback of `(V, φ)` to
`X ×_S Sᵢ / Sᵢ` is effective by an étale scheme for every `i`, if the étale descent functor is
fully faithful for `X ×_S (Sᵢ ∩ Sⱼ) ⟶ Sᵢ ∩ Sⱼ`, and if it is faithful for
`X ×_S (Sᵢ ∩ Sⱼ ∩ Sₖ) ⟶ Sᵢ ∩ Sⱼ ∩ Sₖ`, then `(V, φ)` is effective by a scheme étale over `S`:
the local charts glue to a scheme over `S` which is étale, being étale over each `Sᵢ`.

## Main definitions

* `AlgebraicGeometry.DescentDatum.IsEtaleEffective`: effectivity of a descent datum with étale
  underlying scheme, namely membership in the essential image of the étale descent functor.
* `AlgebraicGeometry.DescentDatum.baseChartOfIsEtaleEffective`: the chart over an open of the
  base read off that effectivity.
* `AlgebraicGeometry.DescentDatum.BaseChart.compare`: the comparison morphism between two charts
  over one open of the base, over that open.
* `AlgebraicGeometry.DescentDatum.EtaleBaseCharts`: a family of étale charts over an open cover
  of the base, together with the full faithfulness on pairwise overlaps and the faithfulness on
  triple overlaps that make them glue.
* `AlgebraicGeometry.DescentDatum.EtaleBaseCharts.t` and
  `AlgebraicGeometry.DescentDatum.EtaleBaseCharts.t'`: the transition morphisms on double and
  on triple overlaps, and `AlgebraicGeometry.DescentDatum.EtaleBaseCharts.glue`: the relative
  glueing datum they assemble into.

## Main results

* `AlgebraicGeometry.DescentDatum.BaseChart.existsUnique_hom_comp_proj_eq` and
  `AlgebraicGeometry.DescentDatum.BaseChart.eq_of_proj_comp_eq`: two charts over one open of the
  base are uniquely isomorphic over that open; uniqueness needs only faithfulness.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.etale_toBase`: a scheme glued over a base is étale
  over it as soon as each piece is.
* `AlgebraicGeometry.DescentDatum.Descended.isEtaleEffective`: a datum with étale underlying
  scheme descended by an étale scheme is étale effective, and
  `AlgebraicGeometry.DescentDatum.IsEtaleEffective.isEffective` is the converse implication to
  plain effectivity.
* `AlgebraicGeometry.DescentDatum.EtaleBaseCharts.isEffective` and
  `AlgebraicGeometry.DescentDatum.EtaleBaseCharts.isEtaleEffective`: a datum carrying a family
  of étale charts over an open cover of the base is effective, and étale effective when its own
  underlying scheme is étale.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isOpenCover`: **effectivity of an étale
  descent datum is Zariski-local on the base,** which is
  [Stacks, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM), with
  `AlgebraicGeometry.DescentDatum.isEffective_of_isOpenCover` reading its conclusion as plain
  effectivity.

## Implementation notes

The glueing vehicle is `AlgebraicGeometry.Scheme.RelativeGlueData`, whose overlaps are the
preimages of the members of the cover of the base rather than free parameters. That is what
makes the transition morphisms available: the part of the `i`-th chart lying over `Sⱼ` is the
part lying over `Sᵢ ∩ Sⱼ`, because the `i`-th chart lies over `Sᵢ`, and that part carries a
chart of the datum over `Sᵢ ∩ Sⱼ`. The two charts of the datum over `Sᵢ ∩ Sⱼ` obtained from the
`i`-th and the `j`-th chart are compared by full faithfulness on the pairwise overlap, which is
the transition morphism.

The transition morphism on triple overlaps is not a third comparison but the restriction of the
one on double overlaps, obtained from `AlgebraicGeometry.IsOpenImmersion.lift`: the part of the
`i`-th chart lying over `Sⱼ ∩ Sₖ` is carried by the transition morphism into the part of the
`j`-th chart lying over `Sₖ`, because the transition morphism lies over `S`. The restriction law
`AlgebraicGeometry.Scheme.RelativeGlueData.t'_fac` is then the factorisation property of that
lift, with nothing to prove.

That the glued scheme is étale over `S` is not proved by hand: being étale is Zariski-local on
the source, which is `CategoryTheory.MorphismProperty.IsLocalAtSource` for the Zariski
precoverage, and the charts of the glued scheme are an open cover of it on which the structure
morphism restricts to the structure morphisms of the pieces. Each of those is an étale chart
over a member of the cover of the base followed by the inclusion of that member, hence étale.
The instance `AlgebraicGeometry.IsZariskiLocalAtSource @AlgebraicGeometry.Etale` has to be
supplied by name, as elaboration does not find it from the étale `HasRingHomProperty` instance
on its own.

The cocycle condition is where the faithfulness on triple overlaps is used, and it is used
through uniqueness rather than through an epimorphism: the projections of a chart are
epimorphisms only under hypotheses on `f` which are not available here. Both the triple
composite and the identity are morphisms of the chart over `Sᵢ ∩ Sⱼ ∩ Sₖ` to itself over that
open, compatible with its projection, and faithfulness says there is at most one such.

## References

* [Stacks Project, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
-/

@[expose] public section

noncomputable section

universe v u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-! ### The glued scheme of a datum with étale pieces -/

namespace Scheme.GlueDataOverBase

/-- **A scheme glued over a base is étale over it as soon as each piece is.** Being étale is
Zariski-local on the source and the charts of the glued scheme cover it, so it is enough that
the structure morphism of each piece be étale. -/
lemma etale_toBase {S : Scheme.{u}} (G : Scheme.GlueDataOverBase S)
    (h : ∀ i, Etale (G.proj i)) : Etale G.toBase :=
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  IsZariskiLocalAtSource.of_openCover (P := @Etale) G.toGlueData.openCover fun i ↦ by
    have hfac : G.toGlueData.openCover.f i ≫ G.toBase = G.proj i := G.ι_toBase i
    rw [hfac]
    exact h i

end Scheme.GlueDataOverBase

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} {D : DescentDatum f}

attribute [local implicit_reducible] restrictOpen

/-! ### Comparing two charts over one open of the base -/

namespace BaseChart

variable {T : S.Opens}

/-- The projection of the descended scheme attached to a chart. -/
lemma toDescended_proj (C : D.BaseChart T) :
    C.toDescended.proj = (D.baseDatumIso T).inv ≫ C.proj := rfl

/-- The descended scheme attached to an étale chart is étale over the base of the descended
datum. -/
private instance etale_toDescended_base_hom (C : D.BaseChart T) [Etale C.base.hom] :
    Etale C.toDescended.base.hom :=
  inferInstanceAs (Etale C.base.hom)

/-- Compatibility with the projections of the descended schemes is the same as with those of
the charts. -/
private lemma toDescended_proj_comp_eq_iff (C C' : D.BaseChart T) (e : C.base ⟶ C'.base) :
    (C.toDescended.proj ≫ e.left = C'.toDescended.proj) ↔ (C.proj ≫ e.left = C'.proj) := by
  rw [toDescended_proj, toDescended_proj, Category.assoc]
  exact cancel_epi (D.baseDatumIso T).inv

/-- **Two charts over one open of the base are uniquely isomorphic over that open.** If the
étale descent functor over `T` is fully faithful, there is exactly one morphism over `T` between
the two charts compatible with their projections. -/
theorem existsUnique_hom_comp_proj_eq
    (hff : (etaleDescentFunctor (pullback.snd f T.ι)).FullyFaithful)
    (C C' : D.BaseChart T) [Etale C.base.hom] [Etale C'.base.hom] :
    ∃! e : C.base ⟶ C'.base, C.proj ≫ e.left = C'.proj := by
  obtain ⟨e, he, huniq⟩ :=
    Descended.existsUnique_hom_comp_proj_eq hff C.toDescended C'.toDescended
  exact ⟨e, (toDescended_proj_comp_eq_iff C C' e).mp he,
    fun e' he' ↦ huniq e' ((toDescended_proj_comp_eq_iff C C' e').mpr he')⟩

/-- **A morphism over `T` compatible with the projections of two charts is unique**, when the
étale descent functor over `T` is faithful. -/
theorem eq_of_proj_comp_eq (hfaith : (etaleDescentFunctor (pullback.snd f T.ι)).Faithful)
    (C C' : D.BaseChart T) [Etale C.base.hom] [Etale C'.base.hom] {e e' : C.base ⟶ C'.base}
    (he : C.proj ≫ e.left = C'.proj) (he' : C.proj ≫ e'.left = C'.proj) : e = e' :=
  Descended.eq_of_proj_comp_eq hfaith C.toDescended C'.toDescended
    ((toDescended_proj_comp_eq_iff C C' e).mpr he) ((toDescended_proj_comp_eq_iff C C' e').mpr he')

variable (hff : (etaleDescentFunctor (pullback.snd f T.ι)).FullyFaithful)
  (C C' : D.BaseChart T) [Etale C.base.hom] [Etale C'.base.hom]

/-- **The comparison morphism between two charts over one open of the base.** -/
@[implicit_reducible]
def compare : C.base ⟶ C'.base :=
  (existsUnique_hom_comp_proj_eq hff C C').choose

/-- The comparison morphism is compatible with the two projections. -/
@[reassoc]
lemma proj_comp_compare : C.proj ≫ (compare hff C C').left = C'.proj :=
  (existsUnique_hom_comp_proj_eq hff C C').choose_spec.1

/-- The comparison morphism is the only morphism over `T` compatible with the two
projections. -/
lemma eq_compare {e : C.base ⟶ C'.base} (he : C.proj ≫ e.left = C'.proj) :
    e = compare hff C C' :=
  (existsUnique_hom_comp_proj_eq hff C C').choose_spec.2 e he

end BaseChart

/-! ### Reading a chart off local effectivity -/

/-- **Effectivity of a descent datum with étale underlying scheme**: membership in the essential
image of the étale descent functor of
[Stacks, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI). This is
`AlgebraicGeometry.DescentData.IsEffective` with an étale witness. -/
abbrev IsEtaleEffective {S X : Scheme.{u}} {g : X ⟶ S} (E : DescentDatum g)
    [Etale E.over.hom] : Prop :=
  (etaleDescentFunctor g).essImage ⟨E, inferInstance⟩

/-- **An étale-effective descent datum is effective.** The witness of étale effectivity is a
scheme over `S`, and the isomorphism with its canonical datum inside the category of descent
data with étale underlying scheme is one inside the category of all descent data. -/
theorem IsEtaleEffective.isEffective {S X : Scheme.{u}} {g : X ⟶ S} {E : DescentDatum g}
    [Etale E.over.hom] (h : E.IsEtaleEffective) : DescentData.IsEffective E :=
  ⟨(Scheme.Etale.forget S).obj h.witness, ⟨(IsEtaleDescentData g).ι.mapIso h.getIso⟩⟩

/-- **A descent datum with an étale underlying scheme and an étale descended scheme is étale
effective.** The descended scheme is the witness, and the isomorphism of the datum with the
canonical datum of that scheme is an isomorphism in the category of descent data with étale
underlying scheme, the two objects lying in it. -/
theorem Descended.isEtaleEffective [Etale D.over.hom] (Q : D.Descended) [Etale Q.base.hom] :
    D.IsEtaleEffective :=
  ⟨Scheme.Etale.mk Q.base.hom, ⟨ObjectProperty.isoMk _ Q.canonicalIso⟩⟩

variable (D) in
/-- **The chart over an open of the base read off local effectivity.** The scheme it is built on
is the étale scheme over `T` witnessing the effectivity of the pulled-back datum. -/
@[implicit_reducible]
def baseChartOfIsEtaleEffective [Etale D.over.hom] (T : S.Opens)
    (h : (D.baseDatum T).IsEtaleEffective) : D.BaseChart T :=
  BaseChart.ofDescended (Descended.ofIso
    ((IsEtaleDescentData (pullback.snd f T.ι)).ι.mapIso h.getIso))

/-- The chart read off local effectivity is étale over the open of the base. -/
instance etale_baseChartOfIsEtaleEffective [Etale D.over.hom] (T : S.Opens)
    (h : (D.baseDatum T).IsEtaleEffective) :
    Etale (D.baseChartOfIsEtaleEffective T h).base.hom :=
  h.witness.prop

/-! ### A family of étale charts over an open cover of the base -/

/-- **A family of étale charts for a descent datum over an open cover of the base.** An open
cover of `S`, a chart of the datum over each member which is étale over it, the full
faithfulness of the étale descent functor over each pairwise overlap and its faithfulness over
each triple overlap. The last two are the hypotheses under which the charts glue. -/
structure EtaleBaseCharts (D : DescentDatum f) where
  /-- The index type of the cover of the base. -/
  J : Type u
  /-- The `i`-th member of the open cover of the base. -/
  base : J → S.Opens
  /-- The members of the cover cover `S`. -/
  iSup_base : ⨆ i, base i = ⊤
  /-- The chart of the datum over the `i`-th member of the cover. -/
  chart : ∀ i, D.BaseChart (base i)
  /-- The `i`-th chart is étale over the `i`-th member of the cover. -/
  etale : ∀ i, Etale (chart i).base.hom
  /-- The étale descent functor is fully faithful over a pairwise overlap. -/
  pairFullyFaithful : ∀ i j,
    (etaleDescentFunctor (pullback.snd f (base i ⊓ base j).ι)).FullyFaithful
  /-- The étale descent functor is faithful over a triple overlap. -/
  tripleFaithful : ∀ i j k,
    (etaleDescentFunctor (pullback.snd f (base i ⊓ base j ⊓ base k).ι)).Faithful

namespace EtaleBaseCharts

variable (C : D.EtaleBaseCharts)

/-- The base of the `i`-th chart is étale over the `i`-th member of the cover. -/
instance etale_chart_base_hom (i : C.J) : Etale (C.chart i).base.hom := C.etale i

/-- The part of the `i`-th chart lying over the `j`-th member of the cover is the part lying
over the overlap of the two members, the `i`-th chart lying entirely over the `i`-th member. -/
lemma preimage_inf_left (i j : C.J) :
    (C.chart i).toBase ⁻¹ᵁ (C.base i ⊓ C.base j) = (C.chart i).toBase ⁻¹ᵁ C.base j := by
  rw [Scheme.Hom.preimage_inf, (C.chart i).toBase_preimage_self, top_inf_eq]

/-- The same for the second factor. -/
lemma preimage_inf_right (i j : C.J) :
    (C.chart j).toBase ⁻¹ᵁ (C.base i ⊓ C.base j) = (C.chart j).toBase ⁻¹ᵁ C.base i := by
  rw [Scheme.Hom.preimage_inf, (C.chart j).toBase_preimage_self, inf_top_eq]

/-- **The part of the `a`-th chart lying over two opens of the base** is the part lying over
their intersection with the `a`-th member of the cover. -/
lemma preimage_inf_eq_of_eq (a : C.J) {b c W : S.Opens} (hW : C.base a ⊓ (b ⊓ c) = W) :
    (C.chart a).toBase ⁻¹ᵁ b ⊓ (C.chart a).toBase ⁻¹ᵁ c = (C.chart a).toBase ⁻¹ᵁ W := by
  rw [← hW, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf,
    (C.chart a).toBase_preimage_self, top_inf_eq]

/-- The chart of the datum over the overlap of two members of the cover, cut out of the `i`-th
chart. -/
abbrev overlapChart (i j : C.J) : D.BaseChart (C.base i ⊓ C.base j) :=
  (C.chart i).restrict inf_le_left

/-- The chart of the datum over the overlap of two members of the cover, cut out of the `j`-th
chart. -/
abbrev overlapChart' (i j : C.J) : D.BaseChart (C.base i ⊓ C.base j) :=
  (C.chart j).restrict inf_le_right

/-- **The projection onto the part of the `i`-th chart lying over the `j`-th member of the
cover**, from the part of `V` lying over the overlap of the two members. -/
@[implicit_reducible]
def overlapProj (i j : C.J) :
    (D.baseOpens (C.base i ⊓ C.base j)).toScheme ⟶
      ((C.chart i).toBase ⁻¹ᵁ C.base j).toScheme :=
  (C.overlapChart i j).proj ≫ ((C.chart i).base.left.isoOfEq (C.preimage_inf_left i j)).hom

/-- The projection onto that part, followed by its inclusion into the `i`-th chart, is the
inclusion of the part of `V` over the overlap followed by the `i`-th projection. -/
@[reassoc]
lemma overlapProj_comp_ι (i j : C.J) :
    C.overlapProj i j ≫ ((C.chart i).toBase ⁻¹ᵁ C.base j).ι =
      D.over.left.homOfLE (D.baseOpens_mono (C.base i) inf_le_left) ≫ (C.chart i).proj := by
  rw [overlapProj]
  simp only [Category.assoc]
  rw [Scheme.isoOfEq_hom_ι]
  exact (C.chart i).restrictProj_comp_ι inf_le_left

/-- **The transition morphism of the glueing datum.** The two charts of the datum over the
overlap of the `i`-th and `j`-th members of the cover — the one cut out of the `i`-th chart and
the one cut out of the `j`-th — are compared by full faithfulness over that overlap, and this is
that comparison, read between the two parts of the charts lying over the other member. -/
@[implicit_reducible]
def t (i j : C.J) :
    ((C.chart i).toBase ⁻¹ᵁ C.base j).toScheme ⟶ ((C.chart j).toBase ⁻¹ᵁ C.base i).toScheme :=
  ((C.chart i).base.left.isoOfEq (C.preimage_inf_left i j)).inv ≫
    (BaseChart.compare (C.pairFullyFaithful i j) (C.overlapChart i j)
      (C.overlapChart' i j)).left ≫
    ((C.chart j).base.left.isoOfEq (C.preimage_inf_right i j)).hom

/-- **The identity that governs the glueing datum.** Passing from the `i`-th chart to the `j`-th
through the transition morphism and then including into the `j`-th chart is the inclusion of the
part of `V` over the overlap followed by the `j`-th projection. -/
@[reassoc]
lemma overlapProj_comp_t_comp_ι (i j : C.J) :
    C.overlapProj i j ≫ C.t i j ≫ ((C.chart j).toBase ⁻¹ᵁ C.base i).ι =
      D.over.left.homOfLE (D.baseOpens_mono (C.base j) inf_le_right) ≫ (C.chart j).proj := by
  rw [t, overlapProj]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, Scheme.isoOfEq_hom_ι, BaseChart.proj_comp_compare_assoc]
  exact (C.chart j).restrictProj_comp_ι inf_le_right

/-- **The transition morphisms lie over the base.** -/
lemma t_over (i j : C.J) :
    C.t i j ≫ ((C.chart j).toBase ⁻¹ᵁ C.base i).ι ≫ (C.chart j).toBase =
      ((C.chart i).toBase ⁻¹ᵁ C.base j).ι ≫ (C.chart i).toBase := by
  have hw := Over.w (BaseChart.compare (C.pairFullyFaithful i j) (C.overlapChart i j)
    (C.overlapChart' i j))
  have h2 : ((C.chart j).base.left.isoOfEq (C.preimage_inf_right i j)).hom ≫
      ((C.chart j).toBase ⁻¹ᵁ C.base i).ι ≫ (C.chart j).toBase =
      (C.overlapChart' i j).base.hom ≫ (C.base i ⊓ C.base j).ι := by
    rw [← Category.assoc, Scheme.isoOfEq_hom_ι, BaseChart.restrict_base_hom]
    exact (morphismRestrict_ι (C.chart j).toBase (C.base i ⊓ C.base j)).symm
  have h1 : ((C.chart i).base.left.isoOfEq (C.preimage_inf_left i j)).inv ≫
      (C.overlapChart i j).base.hom ≫ (C.base i ⊓ C.base j).ι =
      ((C.chart i).toBase ⁻¹ᵁ C.base j).ι ≫ (C.chart i).toBase := by
    rw [BaseChart.restrict_base_hom, morphismRestrict_ι, ← Category.assoc,
      Scheme.isoOfEq_inv_ι]
  rw [t]
  simp only [Category.assoc]
  rw [h2, reassoc_of% hw]
  exact h1

/-- **The transition from a chart to itself is the identity.** -/
lemma t_self (i : C.J) : C.t i i = 𝟙 _ := by
  have hcmp : (BaseChart.compare (C.pairFullyFaithful i i) (C.overlapChart i i)
      (C.overlapChart' i i)).left ≫
      ((C.chart i).base.left.isoOfEq (C.preimage_inf_right i i)).hom =
      ((C.chart i).base.left.isoOfEq (C.preimage_inf_left i i)).hom := by
    rw [← BaseChart.eq_compare (C.pairFullyFaithful i i) (C.overlapChart i i)
      (C.overlapChart' i i) (e := 𝟙 (C.overlapChart i i).base)
      (by rw [Over.id_left, Category.comp_id]), Over.id_left]
    exact Category.id_comp _
  rw [t, hcmp]
  exact Iso.inv_hom_id _

/-! ### The transition morphisms on triple overlaps -/

/-- The part of the `j`-th chart lying over the `k`-th member of the cover, pulled back along
the transition morphism, is the part of the `i`-th chart lying over the `k`-th member. This is
the transition morphisms lying over the base, read on opens. -/
lemma t_preimage (i j k : C.J) :
    C.t i j ⁻¹ᵁ (((C.chart j).toBase ⁻¹ᵁ C.base i).ι ⁻¹ᵁ ((C.chart j).toBase ⁻¹ᵁ C.base k)) =
      ((C.chart i).toBase ⁻¹ᵁ C.base j).ι ⁻¹ᵁ ((C.chart i).toBase ⁻¹ᵁ C.base k) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Category.assoc, C.t_over i j]
  exact Scheme.Hom.comp_preimage _ _ _

/-- An open subscheme lies inside every larger open. -/
private lemma ι_preimage_eq_top {Y : Scheme.{u}} {A B : Y.Opens} (hle : A ≤ B) :
    A.ι ⁻¹ᵁ B = ⊤ :=
  top_le_iff.mp fun x _ ↦ hle x.2

/-- A morphism whose preimage of an open is everything has its image inside that open. -/
private lemma range_subset_of_preimage_eq_top {Y Z : Scheme.{u}} (h : Y ⟶ Z) (W : Z.Opens)
    (htop : h ⁻¹ᵁ W = ⊤) : Set.range h.base ⊆ (W : Set Z) :=
  Set.range_subset_iff.mpr fun y ↦ htop.ge (show y ∈ (⊤ : Y.Opens) from trivial)

/-- **The transition morphism carries a triple overlap into a triple overlap.** The part of the
`i`-th chart lying over both the `j`-th and the `k`-th member of the cover is carried by the
transition morphism into the part of the `j`-th chart lying over the `k`-th member, the
transition morphism lying over the base. -/
lemma range_homOfLE_comp_t_subset (i j k : C.J) :
    Set.range ((C.chart i).base.left.homOfLE
        (inf_le_left : (C.chart i).toBase ⁻¹ᵁ C.base j ⊓ (C.chart i).toBase ⁻¹ᵁ C.base k ≤
          (C.chart i).toBase ⁻¹ᵁ C.base j) ≫ C.t i j).base ⊆
      Set.range ((C.chart j).base.left.homOfLE
        (inf_le_right : (C.chart j).toBase ⁻¹ᵁ C.base k ⊓ (C.chart j).toBase ⁻¹ᵁ C.base i ≤
          (C.chart j).toBase ⁻¹ᵁ C.base i)).base := by
  have hW : ((C.chart j).toBase ⁻¹ᵁ C.base i).ι ⁻¹ᵁ
      ((C.chart j).toBase ⁻¹ᵁ C.base k ⊓ (C.chart j).toBase ⁻¹ᵁ C.base i) =
      ((C.chart j).toBase ⁻¹ᵁ C.base i).ι ⁻¹ᵁ ((C.chart j).toBase ⁻¹ᵁ C.base k) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
  have hrange : Set.range ((C.chart j).base.left.homOfLE
      (inf_le_right : (C.chart j).toBase ⁻¹ᵁ C.base k ⊓ (C.chart j).toBase ⁻¹ᵁ C.base i ≤
        (C.chart j).toBase ⁻¹ᵁ C.base i)).base =
      ((((C.chart j).toBase ⁻¹ᵁ C.base i).ι ⁻¹ᵁ ((C.chart j).toBase ⁻¹ᵁ C.base k) :
        ((C.chart j).toBase ⁻¹ᵁ C.base i).toScheme.Opens) : Set _) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE, hW]
  rw [hrange]
  refine range_subset_of_preimage_eq_top _ _ ?_
  rw [Scheme.Hom.comp_preimage ((C.chart i).base.left.homOfLE inf_le_left) (C.t i j),
    C.t_preimage i j k,
    ← Scheme.Hom.comp_preimage ((C.chart i).base.left.homOfLE inf_le_left)
      ((C.chart i).toBase ⁻¹ᵁ C.base j).ι, Scheme.homOfLE_ι]
  exact ι_preimage_eq_top inf_le_right

/-- **The transition morphism of the glueing datum on triple overlaps**, obtained by restricting
the one on double overlaps. -/
@[implicit_reducible]
def t' (i j k : C.J) :
    ((C.chart i).toBase ⁻¹ᵁ C.base j ⊓ (C.chart i).toBase ⁻¹ᵁ C.base k).toScheme ⟶
      ((C.chart j).toBase ⁻¹ᵁ C.base k ⊓ (C.chart j).toBase ⁻¹ᵁ C.base i).toScheme :=
  IsOpenImmersion.lift
    ((C.chart j).base.left.homOfLE
      (inf_le_right : (C.chart j).toBase ⁻¹ᵁ C.base k ⊓ (C.chart j).toBase ⁻¹ᵁ C.base i ≤
        (C.chart j).toBase ⁻¹ᵁ C.base i))
    ((C.chart i).base.left.homOfLE
      (inf_le_left : (C.chart i).toBase ⁻¹ᵁ C.base j ⊓ (C.chart i).toBase ⁻¹ᵁ C.base k ≤
        (C.chart i).toBase ⁻¹ᵁ C.base j) ≫ C.t i j)
    (C.range_homOfLE_comp_t_subset i j k)

/-- **On triple overlaps the transition morphism restricts the one on double overlaps.** -/
lemma t'_fac (i j k : C.J) :
    C.t' i j k ≫ (C.chart j).base.left.homOfLE inf_le_right =
      (C.chart i).base.left.homOfLE inf_le_left ≫ C.t i j :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The transition morphisms on triple overlaps lie over the base.** -/
lemma t'_over (i j k : C.J) :
    C.t' i j k ≫ ((C.chart j).toBase ⁻¹ᵁ C.base k ⊓ (C.chart j).toBase ⁻¹ᵁ C.base i).ι ≫
        (C.chart j).toBase =
      ((C.chart i).toBase ⁻¹ᵁ C.base j ⊓ (C.chart i).toBase ⁻¹ᵁ C.base k).ι ≫
        (C.chart i).toBase := by
  have h := congr_arg (· ≫ ((C.chart j).toBase ⁻¹ᵁ C.base i).ι ≫ (C.chart j).toBase)
    (C.t'_fac i j k)
  simp only [Category.assoc, Scheme.homOfLE_ι_assoc, C.t_over i j] at h
  exact h

/-- **The projection onto a triple overlap is compatible with the transition morphism on triple
overlaps.** -/
lemma restrictProj_comp_isoOfEq_inv_comp_t' (a b c : C.J) (W : S.Opens) (ha : W ≤ C.base a)
    (hb : W ≤ C.base b)
    (h₁ : (C.chart a).toBase ⁻¹ᵁ C.base b ⊓ (C.chart a).toBase ⁻¹ᵁ C.base c =
      (C.chart a).toBase ⁻¹ᵁ W)
    (h₂ : (C.chart b).toBase ⁻¹ᵁ C.base c ⊓ (C.chart b).toBase ⁻¹ᵁ C.base a =
      (C.chart b).toBase ⁻¹ᵁ W) :
    ((C.chart a).restrictProj ha ≫ ((C.chart a).base.left.isoOfEq h₁).inv) ≫ C.t' a b c =
      (C.chart b).restrictProj hb ≫ ((C.chart b).base.left.isoOfEq h₂).inv := by
  have hle : (C.chart a).toBase ⁻¹ᵁ W ≤ (C.chart a).toBase ⁻¹ᵁ C.base b := fun _ hx ↦ hb hx
  have hiso : ((C.chart a).base.left.isoOfEq h₁).inv ≫
      (C.chart a).base.left.homOfLE (inf_le_left :
        (C.chart a).toBase ⁻¹ᵁ C.base b ⊓ (C.chart a).toBase ⁻¹ᵁ C.base c ≤
          (C.chart a).toBase ⁻¹ᵁ C.base b) =
      (C.chart a).base.left.homOfLE hle := by
    refine (cancel_mono ((C.chart a).toBase ⁻¹ᵁ C.base b).ι).mp ?_
    rw [Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_inv_ι, Scheme.homOfLE_ι]
  have hstep : (C.chart a).restrictProj ha ≫ (C.chart a).base.left.homOfLE hle =
      D.over.left.homOfLE (D.baseOpens_mono (C.base a ⊓ C.base b) (le_inf ha hb)) ≫
        C.overlapProj a b := by
    refine (cancel_mono ((C.chart a).toBase ⁻¹ᵁ C.base b).ι).mp ?_
    rw [Category.assoc, Scheme.homOfLE_ι, (C.chart a).restrictProj_comp_ι ha, Category.assoc,
      C.overlapProj_comp_ι a b, ← Category.assoc, Scheme.homOfLE_homOfLE]
  refine (cancel_mono ((C.chart b).toBase ⁻¹ᵁ C.base c ⊓
    (C.chart b).toBase ⁻¹ᵁ C.base a).ι).mp ?_
  simp only [Category.assoc]
  rw [Scheme.isoOfEq_inv_ι, (C.chart b).restrictProj_comp_ι hb,
    ← Scheme.homOfLE_ι (C.chart b).base.left
      (inf_le_right : (C.chart b).toBase ⁻¹ᵁ C.base c ⊓ (C.chart b).toBase ⁻¹ᵁ C.base a ≤
        (C.chart b).toBase ⁻¹ᵁ C.base a),
    ← Category.assoc (C.t' a b c), C.t'_fac a b c]
  simp only [Category.assoc]
  rw [← Category.assoc (((C.chart a).base.left.isoOfEq h₁).inv), hiso,
    ← Category.assoc ((C.chart a).restrictProj ha), hstep, Category.assoc,
    C.overlapProj_comp_t_comp_ι a b, ← Category.assoc, Scheme.homOfLE_homOfLE]

/-- **The cocycle condition for the transition morphisms on triple overlaps.** Both the triple
composite and the identity are morphisms of the chart over the triple overlap compatible with
its projection, and faithfulness over the triple overlap says there is at most one such. -/
lemma cocycle (i j k : C.J) : C.t' i j k ≫ C.t' j k i ≫ C.t' k i j = 𝟙 _ := by
  have hi : C.base i ⊓ C.base j ⊓ C.base k ≤ C.base i := le_trans inf_le_left inf_le_left
  have hj : C.base i ⊓ C.base j ⊓ C.base k ≤ C.base j := le_trans inf_le_left inf_le_right
  have hk : C.base i ⊓ C.base j ⊓ C.base k ≤ C.base k := inf_le_right
  have h₁ : (C.chart i).toBase ⁻¹ᵁ C.base j ⊓ (C.chart i).toBase ⁻¹ᵁ C.base k =
      (C.chart i).toBase ⁻¹ᵁ (C.base i ⊓ C.base j ⊓ C.base k) :=
    C.preimage_inf_eq_of_eq i (by rw [inf_assoc])
  have h₂ : (C.chart j).toBase ⁻¹ᵁ C.base k ⊓ (C.chart j).toBase ⁻¹ᵁ C.base i =
      (C.chart j).toBase ⁻¹ᵁ (C.base i ⊓ C.base j ⊓ C.base k) :=
    C.preimage_inf_eq_of_eq j (by simp only [inf_assoc, inf_comm, inf_left_comm])
  have h₃ : (C.chart k).toBase ⁻¹ᵁ C.base i ⊓ (C.chart k).toBase ⁻¹ᵁ C.base j =
      (C.chart k).toBase ⁻¹ᵁ (C.base i ⊓ C.base j ⊓ C.base k) :=
    C.preimage_inf_eq_of_eq k (by simp only [inf_assoc, inf_comm])
  have e₁ := C.restrictProj_comp_isoOfEq_inv_comp_t' i j k _ hi hj h₁ h₂
  have e₂ := C.restrictProj_comp_isoOfEq_inv_comp_t' j k i _ hj hk h₂ h₃
  have e₃ := C.restrictProj_comp_isoOfEq_inv_comp_t' k i j _ hk hi h₃ h₁
  have hcomp : ((C.chart i).restrictProj hi ≫
        ((C.chart i).base.left.isoOfEq h₁).inv) ≫
        (C.t' i j k ≫ C.t' j k i ≫ C.t' k i j) =
      (C.chart i).restrictProj hi ≫ ((C.chart i).base.left.isoOfEq h₁).inv := by
    rw [← Category.assoc, e₁, ← Category.assoc, e₂, e₃]
  have hover : C.t' i j k ≫ C.t' j k i ≫ C.t' k i j ≫
      ((C.chart i).toBase ⁻¹ᵁ C.base j ⊓ (C.chart i).toBase ⁻¹ᵁ C.base k).ι ≫
        (C.chart i).toBase =
      ((C.chart i).toBase ⁻¹ᵁ C.base j ⊓ (C.chart i).toBase ⁻¹ᵁ C.base k).ι ≫
        (C.chart i).toBase := by
    rw [C.t'_over k i j, C.t'_over j k i, C.t'_over i j k]
  have hbase : ((C.chart i).restrict hi).base.hom ≫
      (C.base i ⊓ C.base j ⊓ C.base k).ι =
      ((C.chart i).toBase ⁻¹ᵁ (C.base i ⊓ C.base j ⊓ C.base k)).ι ≫ (C.chart i).toBase :=
    morphismRestrict_ι (C.chart i).toBase _
  have hleft : (((C.chart i).base.left.isoOfEq h₁).inv ≫
      (C.t' i j k ≫ C.t' j k i ≫ C.t' k i j) ≫
        ((C.chart i).base.left.isoOfEq h₁).hom) ≫ ((C.chart i).restrict hi).base.hom =
      ((C.chart i).restrict hi).base.hom := by
    refine (cancel_mono (C.base i ⊓ C.base j ⊓ C.base k).ι).mp ?_
    simp only [Category.assoc]
    rw [hbase, ← Category.assoc ((C.chart i).base.left.isoOfEq h₁).hom,
      Scheme.isoOfEq_hom_ι, hover, ← Category.assoc, Scheme.isoOfEq_inv_ι]
  have key : ((C.chart i).base.left.isoOfEq h₁).inv ≫
      (C.t' i j k ≫ C.t' j k i ≫ C.t' k i j) ≫
        ((C.chart i).base.left.isoOfEq h₁).hom = 𝟙 _ := by
    refine congrArg Over.Hom.left (BaseChart.eq_of_proj_comp_eq (C.tripleFaithful i j k)
      ((C.chart i).restrict hi) ((C.chart i).restrict hi)
      (e := Over.homMk _ hleft) (e' := 𝟙 _) ?_ ?_)
    · show ((C.chart i).restrict hi).proj ≫ (((C.chart i).base.left.isoOfEq h₁).inv ≫
        (C.t' i j k ≫ C.t' j k i ≫ C.t' k i j) ≫
          ((C.chart i).base.left.isoOfEq h₁).hom) = ((C.chart i).restrict hi).proj
      rw [BaseChart.restrict_proj, ← Category.assoc, ← Category.assoc, hcomp, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    · show ((C.chart i).restrict hi).proj ≫ 𝟙 _ = ((C.chart i).restrict hi).proj
      rw [Category.comp_id]
  have h4 : (C.t' i j k ≫ C.t' j k i ≫ C.t' k i j) ≫
      ((C.chart i).base.left.isoOfEq h₁).hom = ((C.chart i).base.left.isoOfEq h₁).hom := by
    refine (cancel_epi ((C.chart i).base.left.isoOfEq h₁).inv).mp ?_
    rw [key, Iso.inv_hom_id]
  refine (cancel_mono ((C.chart i).base.left.isoOfEq h₁).hom).mp ?_
  rw [h4, Category.id_comp]

/-! ### The relative glueing datum of a family of étale charts -/

/-- **The relative glueing datum of a family of étale charts over an open cover of the base.**
The pieces are the charts, the part of the `i`-th piece glued to the `j`-th is the part of the
`i`-th chart lying over the `j`-th member of the cover, and the transition morphisms are the
comparisons of the two charts of the datum over an overlap. -/
@[implicit_reducible]
def glue : Scheme.RelativeGlueData S where
  J := C.J
  base := C.base
  iSup_base := C.iSup_base
  obj i := (C.chart i).base.left
  proj i := (C.chart i).toBase
  proj_preimage_eq_top i := (C.chart i).toBase_preimage_self
  t := C.t
  t_over := C.t_over
  t_self := C.t_self
  t' := C.t'
  t'_fac := C.t'_fac
  cocycle := C.cocycle

/-- The charts of the glued scheme are compatible with the transition morphisms. -/
lemma glue_t_ι (i j : C.J) :
    C.t i j ≫ ((C.chart j).toBase ⁻¹ᵁ C.base i).ι ≫ C.glue.ι j =
      ((C.chart i).toBase ⁻¹ᵁ C.base j).ι ≫ C.glue.ι i :=
  C.glue.t_ι i j

/-- The parts of `V` lying over two members of the cover intersect in the part lying over their
overlap. -/
lemma baseOpens_inf (i j : C.J) :
    D.baseOpens (C.base i) ⊓ D.baseOpens (C.base j) = D.baseOpens (C.base i ⊓ C.base j) :=
  rfl

/-- The inclusion of the intersection of two parts of `V`, read through the part lying over the
overlap of the two members of the cover. -/
lemma isoOfEq_hom_comp_homOfLE (i j : C.J) :
    (D.over.left.isoOfEq (C.baseOpens_inf i j)).hom ≫
        D.over.left.homOfLE (D.baseOpens_mono (C.base i) inf_le_left) =
      D.over.left.homOfLE (inf_le_left :
        D.baseOpens (C.base i) ⊓ D.baseOpens (C.base j) ≤ D.baseOpens (C.base i)) := by
  refine (cancel_mono (D.baseOpens (C.base i)).ι).mp ?_
  rw [Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]

/-- The same for the second factor. -/
lemma isoOfEq_hom_comp_homOfLE' (i j : C.J) :
    (D.over.left.isoOfEq (C.baseOpens_inf i j)).hom ≫
        D.over.left.homOfLE (D.baseOpens_mono (C.base j) inf_le_right) =
      D.over.left.homOfLE (inf_le_right :
        D.baseOpens (C.base i) ⊓ D.baseOpens (C.base j) ≤ D.baseOpens (C.base j)) := by
  refine (cancel_mono (D.baseOpens (C.base j)).ι).mp ?_
  rw [Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]

/-- **The projections agree on the intersection of two parts of `V` after passing to the glued
scheme**: this is the governing identity of the family together with the compatibility of the
charts of the glued scheme with the transition morphisms. -/
lemma homOfLE_comp_proj_comp_ι (i j : C.J) :
    D.over.left.homOfLE (inf_le_left :
          D.baseOpens (C.base i) ⊓ D.baseOpens (C.base j) ≤ D.baseOpens (C.base i)) ≫
        (C.chart i).proj ≫ C.glue.ι i =
      D.over.left.homOfLE (inf_le_right :
          D.baseOpens (C.base i) ⊓ D.baseOpens (C.base j) ≤ D.baseOpens (C.base j)) ≫
        (C.chart j).proj ≫ C.glue.ι j := by
  rw [← C.isoOfEq_hom_comp_homOfLE i j, ← C.isoOfEq_hom_comp_homOfLE' i j]
  simp only [Category.assoc]
  rw [← C.overlapProj_comp_ι_assoc i j, ← C.overlapProj_comp_t_comp_ι_assoc i j, C.glue_t_ι i j]

/-- **The family of charts over an open cover of the base** that a family of étale charts
assembles into. -/
@[implicit_reducible]
def baseChartFamily : D.BaseChartFamily where
  glue := C.glue
  proj i := (C.chart i).proj
  isPullback i := (C.chart i).isPullback
  proj_invariant i := (C.chart i).proj_invariant
  proj_comp_ι := C.homOfLE_comp_proj_comp_ι

include C in
/-- **A descent datum with a family of étale charts over an open cover of the base is
effective.** -/
theorem isEffective : DescentData.IsEffective D :=
  isEffective_of_baseChartFamily C.baseChartFamily

/-- The `i`-th piece of the glueing datum is étale over `S`, being an étale chart over the
`i`-th member of the cover followed by the inclusion of that member. -/
instance etale_glue_proj (i : C.J) : Etale (C.glue.proj i) :=
  inferInstanceAs (Etale ((C.chart i).base.hom ≫ (C.base i).ι))

/-- **The glued scheme is étale over the base**, each chart being étale over its member of the
cover and being étale being Zariski-local on the source. -/
instance etale_descended_base_hom :
    Etale C.baseChartFamily.toGluedChartFamily.descended.base.hom :=
  C.glue.toGlueDataOverBase.etale_toBase fun i ↦
    inferInstanceAs (Etale ((C.chart i).base.hom ≫ (C.base i).ι))

include C in
/-- **A descent datum with étale underlying scheme and a family of étale charts over an open
cover of the base is étale effective.** -/
theorem isEtaleEffective [Etale D.over.hom] : D.IsEtaleEffective :=
  C.baseChartFamily.toGluedChartFamily.descended.isEtaleEffective

end EtaleBaseCharts

/-! ### Effectivity of an étale descent datum is local on the base -/

/-- **Effectivity of an étale descent datum is Zariski-local on the base.** Let `f : X ⟶ S` be a
morphism of schemes and `(V, φ)` a descent datum relative to `X/S` with `V ⟶ X` étale, and let
`S = ⋃ Sᵢ` be an open covering. Assume that the pullback of `(V, φ)` to `X ×_S Sᵢ / Sᵢ` is
effective by an étale scheme for every `i`, that the étale descent functor for
`X ×_S (Sᵢ ∩ Sⱼ) ⟶ Sᵢ ∩ Sⱼ` is fully faithful, and that the étale descent functor for
`X ×_S (Sᵢ ∩ Sⱼ ∩ Sₖ) ⟶ Sᵢ ∩ Sⱼ ∩ Sₖ` is faithful. Then `(V, φ)` is effective, by a scheme
étale over `S`. -/
@[stacks 0BTM, sga "1 IX 4.3" "sufficiency", sga "1 VIII 7.3" "partial"]
theorem isEtaleEffective_of_isOpenCover {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)
    [Etale D.over.hom] {ι : Type v} (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤)
    (hlocal : ∀ i, (D.baseDatum (U i)).IsEtaleEffective)
    (hpair : ∀ i j, (etaleDescentFunctor (pullback.snd f (U i ⊓ U j).ι)).FullyFaithful)
    (htriple : ∀ i j k,
      (etaleDescentFunctor (pullback.snd f (U i ⊓ U j ⊓ U k).ι)).Faithful) :
    D.IsEtaleEffective := by
  have hl : ∀ T : {T : S.Opens // ∃ i, T = U i}, (D.baseDatum T.1).IsEtaleEffective := by
    intro T
    rw [T.2.choose_spec]
    exact hlocal T.2.choose
  have hp : ∀ T T' : {T : S.Opens // ∃ i, T = U i},
      (etaleDescentFunctor (pullback.snd f (T.1 ⊓ T'.1).ι)).FullyFaithful := by
    intro T T'
    rw [T.2.choose_spec, T'.2.choose_spec]
    exact hpair _ _
  have ht : ∀ T T' T'' : {T : S.Opens // ∃ i, T = U i},
      (etaleDescentFunctor (pullback.snd f (T.1 ⊓ T'.1 ⊓ T''.1).ι)).Faithful := by
    intro T T' T''
    rw [T.2.choose_spec, T'.2.choose_spec, T''.2.choose_spec]
    exact htriple _ _ _
  refine EtaleBaseCharts.isEtaleEffective
    { J := {T : S.Opens // ∃ i, T = U i}
      base := Subtype.val
      iSup_base := ?_
      chart := fun T ↦ D.baseChartOfIsEtaleEffective T.1 (hl T)
      etale := fun T ↦ inferInstance
      pairFullyFaithful := hp
      tripleFaithful := ht }
  refine top_le_iff.mp (le_trans (le_of_eq hU.symm) (iSup_le fun i ↦ ?_))
  exact le_iSup_of_le ⟨U i, i, rfl⟩ le_rfl

/-- **Effectivity of an étale descent datum is Zariski-local on the base**, read as plain
effectivity of the datum. This is
`AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isOpenCover` with the étaleness of the
descending scheme forgotten. -/
@[sga "1 VIII 7.3" "partial"]
theorem isEffective_of_isOpenCover {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)
    [Etale D.over.hom] {ι : Type v} (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤)
    (hlocal : ∀ i, (D.baseDatum (U i)).IsEtaleEffective)
    (hpair : ∀ i j, (etaleDescentFunctor (pullback.snd f (U i ⊓ U j).ι)).FullyFaithful)
    (htriple : ∀ i j k,
      (etaleDescentFunctor (pullback.snd f (U i ⊓ U j ⊓ U k).ι)).Faithful) :
    DescentData.IsEffective D :=
  (isEtaleEffective_of_isOpenCover D U hU hlocal hpair htriple).isEffective

end DescentDatum

end AlgebraicGeometry

end

end
