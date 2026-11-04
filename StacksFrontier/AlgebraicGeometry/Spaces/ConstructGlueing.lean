module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.GlueingClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale

/-!
# The glueing construction of Stacks 0EDM over an étale chart

Let `f : X ⟶ Y` be an integral morphism of algebraic spaces over `S` and let
`y : Spec k ⟶ Y` be a closed immersion representing a point of `|Y|`.  Over an object `V` of
the big fppf site mapping to `Y`, both `X ×_Y V` and `Spec k ×_Y V` are represented by objects
of the site — `f` is relatively representable because it is integral, and `y` because it is a
closed immersion — the first integral over `V` and the second a closed subscheme of it.  The
scheme-level construction of
`StacksFrontier.AlgebraicGeometry.Pushout.GlueingClosedFibre` therefore applies over `V`, and
gives the pushout `P_V` with all four conclusions of the source.

This file assembles that chart-level data.  It is the input to the descent of the construction
along a surjective étale chart of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.glueingChartSource` and `AlgebraicGeometry.Space.glueingChartSourceHom`:
  the object of the site representing `X ×_Y V`, and its morphism to `V`.
* `AlgebraicGeometry.Space.glueingChartFibre` and `AlgebraicGeometry.Space.glueingChartFibreHom`:
  the object of the site representing `Spec k ×_Y V`, and its morphism to `V`.

## Implementation notes

Representability is not assumed.  For `f` it is
`AlgebraicGeometry.Space.relativelyRepresentable_of_isIntegralHom`, the implication from (1) to
(2) of Stacks 03ZQ; for `y` it is the `rep` field carried by
`CategoryTheory.MorphismProperty.presheaf`, through which
`AlgebraicGeometry.Space.IsClosedImmersion` is defined.

The four objects and structure morphisms of the two chart-level fibre products are `abbrev`s,
hence reducible.  They have to be: each is a projection of the chosen representability datum,
so a morphism such as the projection to `X` has the *unreduced* object in its type, and a
semireducible definition leaves `rw` and `simp` unable to see that it composes with a morphism
whose type mentions the reduced one.  Keeping them reducible is what makes the characterising
equations of the induced chart morphisms usable.  The chart situation and the chart pushout are
reducible for the same reason: the closed immersion and the integral morphism of the situation
are the two projections of a fibre product, and a consumer rewriting along a square stated for
those projections needs to see them through the situation.  What must *not* be unfolded is the
induced chart morphism itself; that is why it is chosen rather than defined.

The chart-level situation is `AlgebraicGeometry.glueingSituation` applied to the two scheme
morphisms.  That declaration is stated for an arbitrary closed immersion target rather than for
the spectrum of a field precisely because of this application: over `V` the point `y` pulls back
to the closed subscheme `Spec k ×_Y V` of `V`, which is étale over `k` and so has several points
in general.

## References

* [Stacks Project, Tag 0EDM](https://stacks.math.columbia.edu/tag/0EDM)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsIntegralHom B S hS f.hom)
  {Ky : BigFppfOver B S hS} {y : yoneda.obj Ky ⟶ Y.1} (hy : IsClosedImmersion B S hS y)
  {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ Y.1)

/-- The object of the site representing `X ×_Y V`, for `f : X ⟶ Y` integral. -/
abbrev glueingChartSource : BigFppfOver B S hS :=
  (relativelyRepresentable_of_isIntegralHom B S hS f hf).pullback v

/-- Its structure morphism to `V`. -/
abbrev glueingChartSourceHom : glueingChartSource B S hS f hf v ⟶ V :=
  (relativelyRepresentable_of_isIntegralHom B S hS f hf).snd v

/-- The cartesian square presenting `X ×_Y V`. -/
theorem glueingChartSource_isPullback :
    IsPullback ((relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v)
      (yoneda.map (glueingChartSourceHom B S hS f hf v)) f.hom v :=
  (relativelyRepresentable_of_isIntegralHom B S hS f hf).isPullback v

/-- The object of the site representing `Spec k ×_Y V`, for `y` a closed immersion. -/
abbrev glueingChartFibre : BigFppfOver B S hS := hy.rep.pullback v

/-- Its structure morphism to `V`. -/
abbrev glueingChartFibreHom : glueingChartFibre B S hS hy v ⟶ V := hy.rep.snd v

/-- The cartesian square presenting `Spec k ×_Y V`. -/
theorem glueingChartFibre_isPullback :
    IsPullback (hy.rep.fst v) (yoneda.map (glueingChartFibreHom B S hS hy v)) y v :=
  hy.rep.isPullback v

/-- The chart-level morphism `X ×_Y V ⟶ V` is an integral morphism of schemes. -/
theorem isIntegralHom_glueingChartSourceHom :
    _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v)) :=
  ((isIntegralHom_iff_representable B S hS f.hom X.property Y.property).mp hf).2.property v
    ((relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v)
    (glueingChartSourceHom B S hS f hf v) (glueingChartSource_isPullback B S hS f hf v)

/-- The chart-level morphism `Spec k ×_Y V ⟶ V` is a closed immersion of schemes. -/
theorem isClosedImmersion_glueingChartFibreHom :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy v)) :=
  hy.property v (hy.rep.fst v) (glueingChartFibreHom B S hS hy v)
    (glueingChartFibre_isPullback B S hS hy v)

/-- **The situation of [Stacks Project, Tag 0ECI] over an étale chart.**  Over an object `V` of
the site mapping to `Y`, the fibre `X ×_Y V` is integral over `V` and `Spec k ×_Y V` is a closed
subscheme of it, so the scheme-level construction of
`StacksFrontier.AlgebraicGeometry.Pushout.GlueingClosedFibre` applies. -/
abbrev glueingChartSituation : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
  letI := isIntegralHom_glueingChartSourceHom B S hS f hf v
  letI := isClosedImmersion_glueingChartFibreHom B S hS hy v
  glueingSituation ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v))
    ((BigFppfOver.toScheme B S hS).map (glueingChartFibreHom B S hS hy v))

/-- The pushout over the chart: the scheme `P_V` of [Stacks Project, Tag 0EDM] over `V`. -/
abbrev glueingChartPushout : Scheme.{u} := pushoutScheme (glueingChartSituation B S hS f hf hy v)

/-- Its structure morphism to the chart. -/
abbrev glueingChartPushoutToBase :
    glueingChartPushout B S hS f hf hy v ⟶ (BigFppfOver.toScheme B S hS).obj V :=
  pushoutToBase (glueingChartSituation B S hS f hf hy v)

/-- **Clause (1) of [Stacks Project, Tag 0EDM] over the chart.**  The pushout is integral over
the chart. -/
theorem isIntegralHom_glueingChartPushoutToBase :
    _root_.AlgebraicGeometry.IsIntegralHom (glueingChartPushoutToBase B S hS f hf hy v) :=
  let := isIntegralHom_glueingChartSourceHom B S hS f hf v
  let := isClosedImmersion_glueingChartFibreHom B S hS hy v
  isIntegralHom_glueingToBase _ _

/-- The chart-level morphism `X ×_Y V ⟶ V` is a finite morphism of schemes as soon as `f` is
finite. -/
theorem isFinite_glueingChartSourceHom (hfin : IsFinite B S hS f.hom) :
    _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (glueingChartSourceHom B S hS f hf v)) :=
  ((isFinite_iff_representable B S hS f.hom X.property Y.property).mp hfin).2.property v
    ((relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v)
    (glueingChartSourceHom B S hS f hf v) (glueingChartSource_isPullback B S hS f hf v)

/-- **The final assertion of [Stacks Project, Tag 0EDM] over the chart.**  If `f` is finite and
the chart is locally Noetherian, the pushout is finite over the chart. -/
theorem isFinite_glueingChartPushoutToBase (hfin : IsFinite B S hS f.hom)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] :
    _root_.AlgebraicGeometry.IsFinite (glueingChartPushoutToBase B S hS f hf hy v) :=
  let := isIntegralHom_glueingChartSourceHom B S hS f hf v
  let := isClosedImmersion_glueingChartFibreHom B S hS hy v
  let := isFinite_glueingChartSourceHom B S hS f hf v hfin
  isFinite_glueingToBase _ _

/-- A morphism of charts over the base induces a morphism of the representing objects of two
pullbacks of a presheaf morphism, compatible with both projections. -/
private theorem exists_map_of_isPullback {C : Type*} [Category C] {X Y : Cᵒᵖ ⥤ Type _}
    {g : X ⟶ Y} {V V' P P' : C} {v : yoneda.obj V ⟶ Y} {v' : yoneda.obj V' ⟶ Y}
    (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v) {p : yoneda.obj P ⟶ X} {q : P ⟶ V}
    {p' : yoneda.obj P' ⟶ X} {q' : P' ⟶ V'} (h : IsPullback p (yoneda.map q) g v)
    (h' : IsPullback p' (yoneda.map q') g v') :
    ∃ m : P ⟶ P', m ≫ q' = q ≫ a ∧ yoneda.map m ≫ p' = p := by
  have hw : p ≫ g = (yoneda.map q ≫ yoneda.map a) ≫ v' := by
    rw [Category.assoc, ha]
    exact h.w
  obtain ⟨m, hm⟩ : ∃ m : P ⟶ P', yoneda.map m = h'.lift p (yoneda.map q ≫ yoneda.map a) hw :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  refine ⟨m, ?_, ?_⟩
  · apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hm]
    exact h'.lift_snd _ _ hw
  · rw [hm]
    exact h'.lift_fst _ _ hw

/-! ### Functoriality in the chart -/

section ChartMap

variable {V V' : BigFppfOver B S hS} {v : yoneda.obj V ⟶ Y.1} {v' : yoneda.obj V' ⟶ Y.1}
  (a : V ⟶ V') (ha : yoneda.map a ≫ v' = v)

include ha in
/-- **The morphism of chart-level sources induced by a morphism of charts over `Y`.**  A
morphism `a : V ⟶ V'` with `yoneda.map a ≫ v' = v` induces `X ×_Y V ⟶ X ×_Y V'`, over `a` and
compatible with the two projections to `X`.

Stated as an existence lemma rather than a definition plus two characterisations: the morphism
is `CategoryTheory.Functor.preimage` of a `CategoryTheory.IsPullback.lift`, and unfolding a
definition wrapping that term to apply `CategoryTheory.Functor.map_preimage` exhausts the
heartbeat budget, the `lift` carrying the chosen representability data inside it.  Keeping the
term syntactically visible inside a single proof avoids the unfolding entirely. -/
theorem exists_glueingChartSourceMap :
    ∃ m : glueingChartSource B S hS f hf v ⟶ glueingChartSource B S hS f hf v',
      m ≫ glueingChartSourceHom B S hS f hf v' =
          glueingChartSourceHom B S hS f hf v ≫ a ∧
        yoneda.map m ≫ (relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v' =
          (relativelyRepresentable_of_isIntegralHom B S hS f hf).fst v :=
  exists_map_of_isPullback a ha (glueingChartSource_isPullback B S hS f hf v)
    (glueingChartSource_isPullback B S hS f hf v')

include ha in
/-- **The morphism of chart-level fibres induced by a morphism of charts over `Y`.**  The
analogue of `AlgebraicGeometry.Space.exists_glueingChartSourceMap` for the closed immersion
`y`, and stated the same way for the same reason. -/
theorem exists_glueingChartFibreMap :
    ∃ m : glueingChartFibre B S hS hy v ⟶ glueingChartFibre B S hS hy v',
      m ≫ glueingChartFibreHom B S hS hy v' = glueingChartFibreHom B S hS hy v ≫ a ∧
        yoneda.map m ≫ hy.rep.fst v' = hy.rep.fst v :=
  exists_map_of_isPullback a ha (glueingChartFibre_isPullback B S hS hy v)
    (glueingChartFibre_isPullback B S hS hy v')

end ChartMap

end Chart

end AlgebraicGeometry.Space

end
