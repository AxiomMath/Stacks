module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Glueing two schemes along an open subscheme, over a base

Two schemes `Y₁` and `Y₂` with a common open subscheme, presented as a span `Y₁ ⟵ W ⟶ Y₂` of
open immersions, glue to a single scheme. The two charts are open immersions into the glued
scheme, they cover it, and they agree on `W`. A pair of morphisms `Y₁ ⟶ T` and `Y₂ ⟶ T`
agreeing on `W` descends to the glued scheme, and the descended morphism is flat as soon as
both pieces are: flatness is local on the source, and the two charts cover the glued scheme.

This is the glueing needed to produce a scheme over a base `T` out of two schemes over `T`
identified along an open subscheme, which is the form in which glueing enters the
construction of a quasi-inverse to the two-open comparison functor of a deformation category.

## Main definitions

* `AlgebraicGeometry.SpanGlue.diagram`: the span, as a diagram of shape `WidePushoutShape Bool`.
* `AlgebraicGeometry.SpanGlue.glued`: the glued scheme, as the colimit of the span.
* `AlgebraicGeometry.SpanGlue.ι₁` and `AlgebraicGeometry.SpanGlue.ι₂`: the two charts.
* `AlgebraicGeometry.SpanGlue.openCover`: the cover of the glued scheme by the span.
* `AlgebraicGeometry.SpanGlue.desc`: the morphism out of the glued scheme determined by a
  pair of morphisms agreeing on `W`.
* `AlgebraicGeometry.SpanGlue.chartCover`: the cover of the glued scheme by its two charts.

## Main results

* `AlgebraicGeometry.SpanGlue.glue_condition`: the two charts agree on `W`.
* `AlgebraicGeometry.SpanGlue.ι_jointly_surjective` and
  `AlgebraicGeometry.SpanGlue.opensRange_ι₁_sup_opensRange_ι₂`: the two charts cover the
  glued scheme.
* `AlgebraicGeometry.SpanGlue.hom_ext`: a morphism out of the glued scheme is determined by
  its restrictions to the two charts.
* `AlgebraicGeometry.SpanGlue.ι₁_desc` and `AlgebraicGeometry.SpanGlue.ι₂_desc`: the
  descended morphism restricts to the given ones.
* `AlgebraicGeometry.SpanGlue.flat_desc`: **the glued scheme is flat over the base** as soon
  as both pieces are.
* `AlgebraicGeometry.SpanGlue.exists_eq_iff_mem_range₂`,
  `AlgebraicGeometry.SpanGlue.preimage_opensRange_ι₁` and their counterparts for the other
  chart: the two charts meet in `W` and nowhere else.
* `AlgebraicGeometry.SpanGlue.isPullback_of_charts`: a square over the glued scheme is a
  pullback as soon as it is one over each of the two charts.
* `AlgebraicGeometry.SpanGlue.isPullback_desc`: **the fibre of a glueing is the glueing of the
  fibres**. If each piece of a second glueing is the fibre product of the corresponding piece
  of the first with a scheme over the base, and the common open of the second glueing is the
  part of each piece lying over the common open of the first, then the second glued scheme is
  the fibre product of the first with that scheme over the base. This is the statement that
  identifies the special fibre of a glued deformation.

## Implementation notes

The glued scheme is taken to be the colimit of the span rather than the glued object of a
`AlgebraicGeometry.Scheme.GlueData`. Mathlib provides the colimit of a diagram of open
immersions out of `WidePushoutShape`
(`AlgebraicGeometry.Scheme.IsLocallyDirected.instIsLocallyDirected` and the surrounding
development), and with that presentation the compatibility of the two charts on `W` is
functoriality of the colimit cocone rather than a glueing condition to be discharged. Building
a `AlgebraicGeometry.Scheme.GlueData` instead, through
`CategoryTheory.GlueData.ofGlueData'`, forces the overlap object to be presented as a `dite`
and the charts to be composites with `eqToHom`, and the triple-overlap transition has to be
supplied even though it is vacuous on a two-element index.

Flatness is not inherited from the pieces by any general principle about colimits; it is proved
from `AlgebraicGeometry.IsZariskiLocalAtSource` for `AlgebraicGeometry.Flat`, which does not
fire by instance synthesis because the universe of the associated ring-hom property is not
determined by the goal, and is therefore supplied explicitly from
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`.

That a square over the glued scheme is a pullback is checked chart by chart through
`AlgebraicGeometry.Scheme.isPullback_of_openCover`, and the identification of each chart of the
glued source with the part of it over the corresponding chart of the glued target is
`AlgebraicGeometry.IsOpenImmersion.isPullback`, whose hypothesis on preimages of ranges is
where the assumption that the common open of the source glueing lies over the common open of
the target glueing is used. Without that assumption the charts of the source would be smaller
than the preimages of the charts of the target and the fibre statement would be false.

The index of the span is `Bool`, so the diagram is indexed by `Option Bool`: the two charts are
`some false` and `some true` and the overlap is `none`. The point of `none` carrying `W` is
that the cover of the glued scheme produced by the colimit development has one member for
*every* object of the diagram, so the statements about the cover range over the overlap as
well, and the overlap chart factors through the first one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SpanGlue

variable {W Y₁ Y₂ : Scheme.{u}} (j₁ : W ⟶ Y₁) (j₂ : W ⟶ Y₂)
  [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- The span `Y₁ ⟵ W ⟶ Y₂`, as a diagram of shape `WidePushoutShape Bool`. -/
def diagram : WidePushoutShape Bool ⥤ Scheme.{u} :=
  WidePushoutShape.wideSpan W (fun b => cond b Y₂ Y₁)
    (fun b => match b with | false => j₁ | true => j₂)

/-- Every morphism of the span is an open immersion. -/
instance isOpenImmersion_diagram_map :
    ∀ {i j : WidePushoutShape Bool} (f : i ⟶ j), IsOpenImmersion ((diagram j₁ j₂).map f) := by
  intro i j f
  cases f with
  | id => exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  | init b => cases b <;> dsimp [diagram] <;> infer_instance

/-- The scheme obtained by glueing `Y₁` and `Y₂` along the open subscheme `W`. -/
def glued : Scheme.{u} := colimit (diagram j₁ j₂)

/-- The first chart of the glueing. -/
def ι₁ : Y₁ ⟶ glued j₁ j₂ := colimit.ι (diagram j₁ j₂) (some false)

/-- The second chart of the glueing. -/
def ι₂ : Y₂ ⟶ glued j₁ j₂ := colimit.ι (diagram j₁ j₂) (some true)

/-- The first chart of the glueing is an open immersion. -/
instance isOpenImmersion_ι₁ : IsOpenImmersion (ι₁ j₁ j₂) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram j₁ j₂) (some false)))

/-- The second chart of the glueing is an open immersion. -/
instance isOpenImmersion_ι₂ : IsOpenImmersion (ι₂ j₁ j₂) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (diagram j₁ j₂) (some true)))

/-- The overlap chart of the glueing factors through the first chart. -/
theorem ι_none_eq : colimit.ι (diagram j₁ j₂) none = j₁ ≫ ι₁ j₁ j₂ :=
  (colimit.w (diagram j₁ j₂) (WidePushoutShape.Hom.init false)).symm

/-- The overlap chart of the glueing factors through the second chart. -/
theorem ι_none_eq' : colimit.ι (diagram j₁ j₂) none = j₂ ≫ ι₂ j₁ j₂ :=
  (colimit.w (diagram j₁ j₂) (WidePushoutShape.Hom.init true)).symm

/-- **The glueing condition.** The two charts agree on the common open subscheme. -/
@[reassoc]
theorem glue_condition : j₁ ≫ ι₁ j₁ j₂ = j₂ ≫ ι₂ j₁ j₂ :=
  (ι_none_eq j₁ j₂).symm.trans (ι_none_eq' j₁ j₂)

/-- The cover of the glued scheme by the span. -/
def openCover : (glued j₁ j₂).OpenCover :=
  Scheme.IsLocallyDirected.openCover (diagram j₁ j₂)

/-- The morphism of the cover of the glued scheme by the span at an object of the diagram is
the colimit inclusion at that object. -/
theorem openCover_f (i : WidePushoutShape Bool) :
    (openCover j₁ j₂).f i = colimit.ι (diagram j₁ j₂) i := rfl

/-- **The two charts cover the glued scheme.** -/
theorem ι_jointly_surjective (x : glued j₁ j₂) :
    (∃ y, ι₁ j₁ j₂ y = x) ∨ ∃ y, ι₂ j₁ j₂ y = x := by
  have key : Set.range ⇑(j₁ ≫ ι₁ j₁ j₂) ⊆ Set.range ⇑(ι₁ j₁ j₂) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact Set.image_subset_range _ _
  have hn : Set.range ⇑(colimit.ι (diagram j₁ j₂) none) ⊆ Set.range ⇑(ι₁ j₁ j₂) := by
    rw [ι_none_eq j₁ j₂]
    exact key
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram j₁ j₂) x
  match i with
  | none => exact Or.inl (hn ⟨y, hy⟩)
  | some false => exact Or.inl ⟨y, hy⟩
  | some true => exact Or.inr ⟨y, hy⟩

/-- **The two charts cover the glued scheme**, as an equality of opens. -/
theorem opensRange_ι₁_sup_opensRange_ι₂ :
    (ι₁ j₁ j₂).opensRange ⊔ (ι₂ j₁ j₂).opensRange = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  rcases ι_jointly_surjective j₁ j₂ x with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

/-- **A morphism out of the glued scheme is determined by its two restrictions.** -/
theorem hom_ext {T : Scheme.{u}} {a b : glued j₁ j₂ ⟶ T}
    (h₁ : ι₁ j₁ j₂ ≫ a = ι₁ j₁ j₂ ≫ b) (h₂ : ι₂ j₁ j₂ ≫ a = ι₂ j₁ j₂ ≫ b) : a = b := by
  have key : (j₁ ≫ ι₁ j₁ j₂) ≫ a = (j₁ ≫ ι₁ j₁ j₂) ≫ b := by
    rw [Category.assoc, Category.assoc, h₁]
  have hn : colimit.ι (diagram j₁ j₂) none ≫ a = colimit.ι (diagram j₁ j₂) none ≫ b := by
    rw [ι_none_eq j₁ j₂]
    exact key
  refine colimit.hom_ext fun i => ?_
  match i with
  | none => exact hn
  | some false => exact h₁
  | some true => exact h₂

section Desc

variable {T : Scheme.{u}} (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (h : j₁ ≫ g₁ = j₂ ≫ g₂)

/-- The cocone on the span given by a pair of morphisms agreeing on the common open. -/
def cocone : Cocone (diagram j₁ j₂) where
  pt := T
  ι :=
    { app := fun i => match i with
        | none => j₁ ≫ g₁
        | some false => g₁
        | some true => g₂
      naturality := by
        intro i j f
        cases f with
        | id => simp
        | init b => cases b <;> dsimp [diagram] <;> simp [h] }

/-- The morphism out of the glued scheme determined by a pair of morphisms agreeing on the
common open subscheme. -/
def desc : glued j₁ j₂ ⟶ T := colimit.desc _ (cocone j₁ j₂ g₁ g₂ h)

/-- The descended morphism restricts to the first given morphism on the first chart. -/
@[reassoc (attr := simp)]
theorem ι₁_desc : ι₁ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h = g₁ :=
  colimit.ι_desc (cocone j₁ j₂ g₁ g₂ h) (some false)

/-- The descended morphism restricts to the second given morphism on the second chart. -/
@[reassoc (attr := simp)]
theorem ι₂_desc : ι₂ j₁ j₂ ≫ desc j₁ j₂ g₁ g₂ h = g₂ :=
  colimit.ι_desc (cocone j₁ j₂ g₁ g₂ h) (some true)

/-- The descended morphism is the unique one restricting to the two given morphisms. -/
theorem eq_desc {d : glued j₁ j₂ ⟶ T} (h₁ : ι₁ j₁ j₂ ≫ d = g₁) (h₂ : ι₂ j₁ j₂ ≫ d = g₂) :
    d = desc j₁ j₂ g₁ g₂ h :=
  hom_ext j₁ j₂ (by rw [h₁, ι₁_desc]) (by rw [h₂, ι₂_desc])

/-- **The glued scheme is flat over the base.** If both pieces are flat over `T`, so is the
scheme obtained by glueing them along the common open subscheme. -/
theorem flat_desc [Flat g₁] [Flat g₂] : Flat (desc j₁ j₂ g₁ g₂ h) := by
  have hloc : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have key : ∀ i : WidePushoutShape Bool,
      Flat (colimit.ι (diagram j₁ j₂) i ≫ desc j₁ j₂ g₁ g₂ h) := by
    intro i
    have e : colimit.ι (diagram j₁ j₂) i ≫ desc j₁ j₂ g₁ g₂ h =
        (cocone j₁ j₂ g₁ g₂ h).ι.app i :=
      colimit.ι_desc (cocone j₁ j₂ g₁ g₂ h) i
    rw [e]
    match i with
    | none => exact inferInstanceAs (Flat (j₁ ≫ g₁))
    | some false => exact inferInstanceAs (Flat g₁)
    | some true => exact inferInstanceAs (Flat g₂)
  exact IsZariskiLocalAtSource.of_openCover (openCover j₁ j₂) key

end Desc

/-! ### The two charts meet exactly in the common open -/

/-- Two points of the two charts with the same image in the glued scheme come from a common
point of `W`. -/
private theorem exists_eq_of_ι_apply_eq {x : Y₁} {y : Y₂} (hxy : ι₁ j₁ j₂ x = ι₂ j₁ j₂ y) :
    ∃ w : W, j₁ w = x ∧ j₂ w = y := by
  obtain ⟨k, fi, fj, w, hw₁, hw₂⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram j₁ j₂)).mp
    (show colimit.ι (diagram j₁ j₂) (some false) x = colimit.ι (diagram j₁ j₂) (some true) y
      from hxy)
  cases k with
  | none =>
    cases fi
    cases fj
    exact ⟨w, hw₁, hw₂⟩
  | some b =>
    cases fi
    cases fj

/-- A point of the second chart lies in the first chart exactly when it comes from the common
open subscheme: the two charts of the glueing meet in `W` and nowhere else. -/
theorem exists_eq_iff_mem_range₂ (y : Y₂) :
    (∃ x : Y₁, ι₁ j₁ j₂ x = ι₂ j₁ j₂ y) ↔ ∃ w : W, j₂ w = y := by
  constructor
  · rintro ⟨x, hx⟩
    exact (exists_eq_of_ι_apply_eq j₁ j₂ hx).imp fun _ hw => hw.2
  · rintro ⟨w, rfl⟩
    refine ⟨j₁ w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition j₁ j₂]

/-- A point of the first chart lies in the second chart exactly when it comes from the common
open subscheme. -/
theorem exists_eq_iff_mem_range₁ (x : Y₁) :
    (∃ y : Y₂, ι₂ j₁ j₂ y = ι₁ j₁ j₂ x) ↔ ∃ w : W, j₁ w = x := by
  constructor
  · rintro ⟨y, hy⟩
    exact (exists_eq_of_ι_apply_eq j₁ j₂ hy.symm).imp fun _ hw => hw.1
  · rintro ⟨w, rfl⟩
    refine ⟨j₂ w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition j₁ j₂]

/-- **The common open is the intersection of the two charts**, seen inside the second chart. -/
theorem preimage_opensRange_ι₁ :
    ι₂ j₁ j₂ ⁻¹ᵁ (ι₁ j₁ j₂).opensRange = j₂.opensRange := by
  ext y
  exact exists_eq_iff_mem_range₂ j₁ j₂ y

/-- **The common open is the intersection of the two charts**, seen inside the first chart. -/
theorem preimage_opensRange_ι₂ :
    ι₁ j₁ j₂ ⁻¹ᵁ (ι₂ j₁ j₂).opensRange = j₁.opensRange := by
  ext x
  exact exists_eq_iff_mem_range₁ j₁ j₂ x

/-! ### Checking a pullback square over the glued scheme chart by chart -/

/-- The cover of the glued scheme by its two charts. -/
def chartCover : (glued j₁ j₂).OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b => cond b Y₂ Y₁)
    (fun b => match b with | false => ι₁ j₁ j₂ | true => ι₂ j₁ j₂)
    (fun x => by
      rcases ι_jointly_surjective j₁ j₂ x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy⟩
      · exact ⟨true, y, hy⟩)
    (by intro b; cases b <;> dsimp <;> infer_instance)

/-- **A square over the glued scheme is a pullback as soon as it is one over each chart.** -/
theorem isPullback_of_charts {T Z V : Scheme.{u}} (m : V ⟶ glued j₁ j₂) (n : V ⟶ Z)
    (d : glued j₁ j₂ ⟶ T) (t : Z ⟶ T)
    (h₁ : IsPullback (pullback.snd m (ι₁ j₁ j₂)) (pullback.fst m (ι₁ j₁ j₂) ≫ n)
      (ι₁ j₁ j₂ ≫ d) t)
    (h₂ : IsPullback (pullback.snd m (ι₂ j₁ j₂)) (pullback.fst m (ι₂ j₁ j₂) ≫ n)
      (ι₂ j₁ j₂ ≫ d) t) :
    IsPullback m n d t := by
  refine Scheme.isPullback_of_openCover m n d t (chartCover j₁ j₂) ?_
  intro i
  match i with
  | false => exact h₁
  | true => exact h₂

/-- Pulling back along a chart is compatible with a pullback square over the chart. -/
private theorem isPullback_pullback_snd_of_isPullback {T Z V Y U A : Scheme.{u}}
    {m : V ⟶ Y} {ι : U ⟶ Y} {f : A ⟶ V} {c : A ⟶ U} (P : IsPullback f c m ι)
    {n : V ⟶ Z} {n' : A ⟶ Z} {d : Y ⟶ T} {g : U ⟶ T} {t : Z ⟶ T}
    (sq : IsPullback c n' g t) (hf : f ≫ n = n') (hg : ι ≫ d = g) :
    IsPullback (pullback.snd m ι) (pullback.fst m ι ≫ n) (ι ≫ d) t := by
  subst hf hg
  refine sq.of_iso P.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
    simp [← Category.assoc]

/-! ### The fibre of a glueing is the glueing of the fibres -/

section Fibre

variable {W' X₁ X₂ T Z : Scheme.{u}} (k₁ : W' ⟶ X₁) (k₂ : W' ⟶ X₂)
  [IsOpenImmersion k₁] [IsOpenImmersion k₂]
  (c₁ : X₁ ⟶ Y₁) (c₂ : X₂ ⟶ Y₂) (n₁ : X₁ ⟶ Z) (n₂ : X₂ ⟶ Z)
  (hm : k₁ ≫ (c₁ ≫ ι₁ j₁ j₂) = k₂ ≫ (c₂ ≫ ι₂ j₁ j₂))

/-- The first chart of the glued source is exactly the part of it lying over the first chart of
the glued target. -/
theorem preimage_opensRange_ι₁_desc
    (hW₂ : c₂ ⁻¹ᵁ j₂.opensRange = k₂.opensRange) :
    desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm ⁻¹ᵁ (ι₁ j₁ j₂).opensRange =
      (ι₁ k₁ k₂).opensRange := by
  ext x
  constructor
  · intro hx
    rcases ι_jointly_surjective k₁ k₂ x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨a, rfl⟩
    · have hb : ι₂ j₁ j₂ (c₂ b) ∈ (ι₁ j₁ j₂).opensRange := by
        rw [← Scheme.Hom.comp_apply, ← ι₂_desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm,
          Scheme.Hom.comp_apply]
        exact hx
      obtain ⟨w, hw⟩ := (exists_eq_iff_mem_range₂ j₁ j₂ (c₂ b)).mp hb
      obtain ⟨v, rfl⟩ : b ∈ k₂.opensRange := by
        rw [← hW₂]
        exact ⟨w, hw⟩
      refine ⟨k₁ v, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition k₁ k₂]
  · rintro ⟨a, rfl⟩
    change _ ∈ (ι₁ j₁ j₂).opensRange
    refine ⟨c₁ a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ι₁_desc]

/-- The second chart of the glued source is exactly the part of it lying over the second chart
of the glued target. -/
theorem preimage_opensRange_ι₂_desc
    (hW₁ : c₁ ⁻¹ᵁ j₁.opensRange = k₁.opensRange) :
    desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm ⁻¹ᵁ (ι₂ j₁ j₂).opensRange =
      (ι₂ k₁ k₂).opensRange := by
  ext x
  constructor
  · intro hx
    rcases ι_jointly_surjective k₁ k₂ x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have ha : ι₁ j₁ j₂ (c₁ a) ∈ (ι₂ j₁ j₂).opensRange := by
        rw [← Scheme.Hom.comp_apply, ← ι₁_desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm,
          Scheme.Hom.comp_apply]
        exact hx
      obtain ⟨w, hw⟩ := (exists_eq_iff_mem_range₁ j₁ j₂ (c₁ a)).mp ha
      obtain ⟨v, rfl⟩ : a ∈ k₁.opensRange := by
        rw [← hW₁]
        exact ⟨w, hw⟩
      refine ⟨k₂ v, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← glue_condition k₁ k₂]
    · exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    change _ ∈ (ι₂ j₁ j₂).opensRange
    refine ⟨c₂ b, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ι₂_desc]

variable (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (h : j₁ ≫ g₁ = j₂ ≫ g₂) (t : Z ⟶ T)
  (hn : k₁ ≫ n₁ = k₂ ≫ n₂)

/-- The first chart of the glued source exhibits itself as the fibre product of the first chart
of the glued target with the glued source. -/
theorem isPullback_ι₁_desc (hW₂ : c₂ ⁻¹ᵁ j₂.opensRange = k₂.opensRange) :
    IsPullback (ι₁ k₁ k₂) c₁ (desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm)
      (ι₁ j₁ j₂) :=
  (IsOpenImmersion.isPullback c₁ (ι₁ k₁ k₂) (ι₁ j₁ j₂) _
    (ι₁_desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm)
    (preimage_opensRange_ι₁_desc j₁ j₂ k₁ k₂ c₁ c₂ hm hW₂)).flip

/-- The second chart of the glued source exhibits itself as the fibre product of the second
chart of the glued target with the glued source. -/
theorem isPullback_ι₂_desc (hW₁ : c₁ ⁻¹ᵁ j₁.opensRange = k₁.opensRange) :
    IsPullback (ι₂ k₁ k₂) c₂ (desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm)
      (ι₂ j₁ j₂) :=
  (IsOpenImmersion.isPullback c₂ (ι₂ k₁ k₂) (ι₂ j₁ j₂) _
    (ι₂_desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm)
    (preimage_opensRange_ι₂_desc j₁ j₂ k₁ k₂ c₁ c₂ hm hW₁)).flip

/-- **The fibre of a glueing is the glueing of the fibres.** Let `Y` be glued from `Y₁` and
`Y₂` along `W`, with structure morphism to `T`, and let `t : Z ⟶ T`. If `X₁` and `X₂` are the
fibre products of `Y₁` and `Y₂` with `Z` over `T`, and `X` is glued from `X₁` and `X₂` along
`W'`, where `W'` is the part of each `Xᵢ` lying over `W`, then `X` is the fibre product of `Y`
with `Z` over `T`. -/
theorem isPullback_desc
    (sq₁ : IsPullback c₁ n₁ g₁ t) (sq₂ : IsPullback c₂ n₂ g₂ t)
    (hW₁ : c₁ ⁻¹ᵁ j₁.opensRange = k₁.opensRange)
    (hW₂ : c₂ ⁻¹ᵁ j₂.opensRange = k₂.opensRange) :
    IsPullback (desc k₁ k₂ (c₁ ≫ ι₁ j₁ j₂) (c₂ ≫ ι₂ j₁ j₂) hm) (desc k₁ k₂ n₁ n₂ hn)
      (desc j₁ j₂ g₁ g₂ h) t := by
  refine isPullback_of_charts j₁ j₂ _ _ (desc j₁ j₂ g₁ g₂ h) t ?_ ?_
  · exact isPullback_pullback_snd_of_isPullback
      (isPullback_ι₁_desc j₁ j₂ k₁ k₂ c₁ c₂ hm hW₂) sq₁ (ι₁_desc ..) (ι₁_desc ..)
  · exact isPullback_pullback_snd_of_isPullback
      (isPullback_ι₂_desc j₁ j₂ k₁ k₂ c₁ c₂ hm hW₁) sq₂ (ι₂_desc ..) (ι₂_desc ..)

end Fibre

end AlgebraicGeometry.SpanGlue

end
