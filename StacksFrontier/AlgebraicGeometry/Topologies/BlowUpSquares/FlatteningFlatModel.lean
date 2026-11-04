module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescentFiniteType
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FlatRestrict
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatteningApproximation

/-!
# Stacks tag 0EVC with the tag's own flatness hypothesis

Stacks tag 0EVC assumes, of its quasi-compact open `V ⊆ Y`, that the base change `X_V ⟶ V` is
flat. `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_affineChartFlatteningCentre_model`
removes the Noetherian hypothesis from the Noetherian case, but does not assume that
flatness, and so has to carry the affine case of the flatness assertion of Stacks tag 0815 at
*every* Noetherian model of the data — a hypothesis which cannot be discharged, because the affine
case of tag 0815 has flatness over the open among its own hypotheses, and that flatness is
available at the model only after it has been descended there.

This module descends it. Step (6) of the Stacks proof is tag 04AI, available for a restriction as
`AlgebraicGeometry.exists_flat_morphismRestrict_of_limit`, so the Noetherian model can be chosen
at a stage where `f₀ ∣_ V₀` is already flat. The carried hypothesis then becomes a statement about
a Noetherian base and a morphism flat over an open — the affine case of tag 0815 under exactly its
own hypotheses — with no reference to `f` and `V` at all.

## Main definitions

* `AlgebraicGeometry.NoetherianAffineChartFlatteningCentre` is the affine case of the flatness
  assertion of Stacks tag 0815, over a Noetherian base, for a morphism of finite presentation
  flat over a quasi-compact open.

## Main results

* `AlgebraicGeometry.exists_isNoetherian_model_of_finitePresentation_of_flat`: steps (3)-(6) of
  the Stacks proof — a morphism of finite presentation over a quasi-compact quasi-separated base,
  flat over a quasi-compact open, is the base change of the same data, *still flat over the
  open*, over a Noetherian base.
* `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat`: Stacks tag 0EVC under exactly
  the tag's hypotheses, carrying only
  `AlgebraicGeometry.NoetherianAffineChartFlatteningCentre`.
* `AlgebraicGeometry.NoetherianAffineChartFlatteningCentre.of_affineCase`: that hypothesis
  holds, from
  `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace` — the
  affine case of the flatness assertion of Stacks tag 0815 for an arbitrary quasi-coherent
  module, proved from Stacks tag 0811 with nothing granted.
* `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_affineCase`: **Stacks tag 0EVC** under
  exactly the tag's hypotheses, carrying nothing. This is where the tag is registered.
* `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat_pullback`: the same, with the
  flatness hypothesis read for the projection out of the fibre product, which is the shape the
  converse direction of Stacks tag 0EVF asks for.

## Implementation notes

**Why the approximation is run again.** The stage at which the flatness of `f ∣_ V` descends
depends on that flatness, so it cannot be read off the model that
`AlgebraicGeometry.exists_isNoetherian_model_of_finitePresentation` produces: tag 04AI moves the
model to a *later* stage, and reaching that stage needs the inverse system, which that statement
does not expose. The approximation is therefore re-run here, and the model is taken at the stage
tag 04AI supplies rather than at the stage where the data first descends.

**What is carried.** The affine case of the flatness assertion of
Stacks tag 0815 is carried, exactly as in the library's form of tag 081R
(`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`) and in the Noetherian case
of tag 0EVC. Its shape is different: it is not quantified over the models of one
particular pair `(f, V)`, but is the affine case under its own hypotheses — a Noetherian base, a
morphism of finite presentation, and flatness over a quasi-compact open. The only unconditional
instance of it in the tree remains
`AlgebraicGeometry.AffineChartFlatteningCentre.of_isFlatOver`, the region where no blowup is
needed; closing it is the affine case of Raynaud–Gruson flattening, whose root is Stacks tag
0811.

## References

* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- Pasting a pullback square `P ⟶ X` over `q = s ≫ t` with the pullback of `t`: the induced map
`P ⟶ T ×_W Z` exhibits `P` as the pullback of `T ×_W Z ⟶ T` along `s`. -/
private theorem CategoryTheory.IsPullback.lift_of_comp_eq {C : Type*} [Category C] {P X Z T W : C}
    {a : P ⟶ Z} {f : P ⟶ X} {b : Z ⟶ W} {q : X ⟶ W} (h : IsPullback a f b q) {s : X ⟶ T}
    {t : T ⟶ W} [HasPullback t b] (hst : s ≫ t = q) (w : (f ≫ s) ≫ t = a ≫ b) :
    IsPullback (pullback.lift (f ≫ s) a w) f (pullback.fst t b) s := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback t b).flip
  rwa [pullback.lift_snd, hst]

namespace AlgebraicGeometry

/-- The source of a morphism of finite presentation to a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_finitePresentation {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y)
    (hf : FinitePresentation f) : IsNoetherian X := by
  have := hf.locallyOfFinitePresentation
  have := hf.quasiCompact
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

/-- A base-change-stable property of the projection out of `X ×_Y V` holds for `f ∣_ V`. -/
private theorem morphismRestrict_of_pullback_snd {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (h : P (pullback.snd f V.ι)) : P (f ∣_ V) := by
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
  rwa [← MorphismProperty.cancel_left_of_respectsIso P (pullbackRestrictIsoRestrict f V).hom,
    pullbackRestrictIsoRestrict_hom_morphismRestrict]

/-- **The affine case of the flatness assertion of Stacks tag 0815, over a Noetherian base.**
For every Noetherian scheme `Y₀`, every morphism of finite presentation `f₀ : X₀ ⟶ Y₀` and every
quasi-compact open `V₀ ⊆ Y₀` over which `f₀` is flat, the affine charts of `f₀` admit flattening
centres away from `V₀`, in the sense of `AlgebraicGeometry.AffineChartFlatteningCentre`.

These are exactly the hypotheses the affine case of Stacks tag 0815 has in the source — the
induction on the maximum fibre-support dimension takes place over affines, and `f₀` locally of
finite presentation and flat over `V₀` are two of the five hypotheses it consumes — so carrying
this is carrying that case, and nothing more. -/
def NoetherianAffineChartFlatteningCentre : Prop :=
  ∀ {X₀ Y₀ : Scheme.{u}} (f₀ : X₀ ⟶ Y₀) (V₀ : Y₀.Opens), IsNoetherian Y₀ →
    FinitePresentation f₀ → IsCompact (V₀ : Set Y₀) → Flat (f₀ ∣_ V₀) →
      AffineChartFlatteningCentre f₀ X₀.unitModule V₀

/-- **Absolute Noetherian approximation of a finitely presented morphism flat over a
quasi-compact open.** A morphism of finite presentation `f : X ⟶ Y` over a quasi-compact and
quasi-separated base, together with a quasi-compact open `V ⊆ Y` over which `f` is flat, is the
base change of the same data over a Noetherian base — and the model is still flat over the model
of `V`.

These are steps (3)-(6) of the Stacks proof of tag 0EVC. Steps (3)-(5) are
`AlgebraicGeometry.exists_isNoetherian_model_of_finitePresentation`, re-run here because step (6)
moves the model to a later stage of the inverse system: step (6) is Stacks tag 04AI, in the form
`AlgebraicGeometry.exists_flat_morphismRestrict_of_limit`, which descends the flatness of
`f ∣_ V` to some stage later than the one at which `f` and `V` first descend. -/
theorem exists_isNoetherian_model_of_finitePresentation_of_flat {X Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) (hf : FinitePresentation f)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) (hflat : Flat (f ∣_ V)) :
    ∃ (Y₀ X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Y₀) (V₀ : Y₀.Opens) (p : Y ⟶ Y₀) (x : X ⟶ X₀),
      IsNoetherian Y₀ ∧ FinitePresentation f₀ ∧ IsCompact (V₀ : Set Y₀) ∧
        IsPullback x f f₀ p ∧ p ⁻¹ᵁ V₀ = V ∧ Flat (f₀ ∣_ V₀) := by
  obtain ⟨I, hI, hIne, hIdir, D, c, haff, hlft, hqc, ⟨hc⟩, hpt⟩ := exists_isLimit_finiteType Y
  let _ := hI
  have := hIne
  have := hIdir
  subst hpt
  have : ∀ {i j : Iᵒᵖ} (v : i ⟶ j), IsAffineHom (D.map v) := haff
  have hnoeth : ∀ i : Iᵒᵖ, IsNoetherian (D.obj i) := fun i ↦
    isNoetherian_of_locallyOfFiniteType_terminalFrom (D.obj i) (hlft i) (hqc i)
  have : ∀ i : Iᵒᵖ, CompactSpace (D.obj i) := fun i ↦ have := hnoeth i; inferInstance
  have : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i ↦ have := hnoeth i; inferInstance
  obtain ⟨i₀, Z₀, p₀, g₀, hfp₀, hpb₀⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall D c hc f hf
  obtain ⟨i₁, V₁, -, hV₁⟩ := exists_preimage_eq D c hc V hV
  obtain ⟨k, u, v, -⟩ := IsCofilteredOrEmpty.cone_objs i₀ i₁
  have hnk := hnoeth k
  -- The model of `(f, V)` at the common stage `k`, as in steps (3)-(5).
  have hwk : (f ≫ c.π.app k) ≫ D.map u = g₀ ≫ p₀ := by rw [Category.assoc, c.w u, hpb₀.w]
  have hsqk : IsPullback (pullback.lift (f ≫ c.π.app k) g₀ hwk) f
      (pullback.fst (D.map u) p₀) (c.π.app k) :=
    hpb₀.lift_of_comp_eq (c.w u) hwk
  have hprek : c.π.app k ⁻¹ᵁ (D.map v ⁻¹ᵁ V₁) = V := by
    rwa [show c.π.app k ⁻¹ᵁ D.map v ⁻¹ᵁ V₁ = c.π.app i₁ ⁻¹ᵁ V₁ from congr($(c.w v) ⁻¹ᵁ V₁)]
  have hfpk : FinitePresentation (pullback.fst (D.map u) p₀) :=
    finitePresentation_pullback_fst p₀ (D.map u) hfp₀
  -- The stage `k` is Noetherian, so the model and the two opens are Noetherian too; this is what
  -- tag 04AI asks of its data.
  have : LocallyOfFinitePresentation (pullback.fst (D.map u) p₀) :=
    hfpk.locallyOfFinitePresentation
  have : IsNoetherian (pullback (D.map u) p₀) :=
    isNoetherian_of_finitePresentation (pullback.fst (D.map u) p₀) hfpk
  have : CompactSpace (pullback.fst (D.map u) p₀ ⁻¹ᵁ (D.map v ⁻¹ᵁ V₁)).toScheme :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : CompactSpace (D.map v ⁻¹ᵁ V₁ : (D.obj k).Opens).toScheme :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  -- Step (6): tag 04AI descends the flatness over the open to a later stage `i`.
  obtain ⟨i, g, hgflat⟩ := exists_flat_morphismRestrict_of_limit D c hc k
    (pullback.fst (D.map u) p₀) (D.map v ⁻¹ᵁ V₁) hsqk.flip (by rwa [hprek])
  have hni := hnoeth i
  have hwi : (f ≫ c.π.app i) ≫ D.map g =
      pullback.lift (f ≫ c.π.app k) g₀ hwk ≫ pullback.fst (D.map u) p₀ := by
    rw [Category.assoc, c.w g, pullback.lift_fst]
  refine ⟨D.obj i, pullback (D.map g) (pullback.fst (D.map u) p₀),
    pullback.fst (D.map g) (pullback.fst (D.map u) p₀), D.map g ⁻¹ᵁ (D.map v ⁻¹ᵁ V₁),
    c.π.app i, pullback.lift (f ≫ c.π.app i) (pullback.lift (f ≫ c.π.app k) g₀ hwk) hwi,
    hni, finitePresentation_pullback_fst (pullback.fst (D.map u) p₀) (D.map g) hfpk,
    NoetherianSpace.isCompact _, hsqk.lift_of_comp_eq (c.w g) hwi, ?_, hgflat⟩
  rwa [show c.π.app i ⁻¹ᵁ D.map g ⁻¹ᵁ (D.map v ⁻¹ᵁ V₁) = c.π.app k ⁻¹ᵁ (D.map v ⁻¹ᵁ V₁) from
    congr($(c.w g) ⁻¹ᵁ (D.map v ⁻¹ᵁ V₁))]

/-- **Stacks Project, Tag 0EVC.** Let `Y` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ Y` be of finite presentation and let `V ⊆ Y` be a quasi-compact open over which `f` is
flat. Then there is a diagram as in the tag: two almost blowup squares, over `Y` with a centre
disjoint from `V` and over `X` with the inverse-image centre, whose lower and top squares are
cartesian (`AlgebraicGeometry.lowerSquareIso`, `AlgebraicGeometry.topSquareIso`) and whose
relative morphism `X' ⟶ Y'` is flat and of finite presentation.

These are the tag's own hypotheses, with no Noetherian assumption on `Y`. The data is descended
to a Noetherian model, still flat over the model of `V`, by
`AlgebraicGeometry.exists_isNoetherian_model_of_finitePresentation_of_flat` (steps (3)-(6)); the
Noetherian case `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair` is applied there (steps (1) and
(2)); and the diagram is pulled back to `Y` by
`AlgebraicGeometry.HasFlatAlmostBlowUpSquarePair.of_isPullback`, which is tag 0EV7 (steps (7) and
(8)).

The one thing carried beyond the tag is the affine case of the flatness assertion of Stacks tag
0815, as `AlgebraicGeometry.NoetherianAffineChartFlatteningCentre` — the hypothesis the library's
form of Stacks tag 081R carries, read under its own hypotheses.

This tag is NOT registered on this declaration, which keeps that hypothesis explicit. It is not
an unproved one: `AlgebraicGeometry.NoetherianAffineChartFlatteningCentre.of_affineCase`
below proves it outright. The tag is registered on
`AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_affineCase`, which is this statement with
that producer supplied.
-/
theorem hasFlatAlmostBlowUpSquarePair_of_flat_of_noetherianAffineChart {X Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : X ⟶ Y) (hf : FinitePresentation f) (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) (hflat : Flat (f ∣_ V))
    (H : NoetherianAffineChartFlatteningCentre.{u}) :
    HasFlatAlmostBlowUpSquarePair f V := by
  obtain ⟨Y₀, X₀, f₀, V₀, p, x, hnoeth, hfp₀, hV₀, hsq, rfl, hflat₀⟩ :=
    exists_isNoetherian_model_of_finitePresentation_of_flat f hf V hV hflat
  have := hnoeth
  exact HasFlatAlmostBlowUpSquarePair.of_isPullback hsq V₀
    (hasFlatAlmostBlowUpSquarePair f₀ hfp₀ V₀ hV₀ (H f₀ V₀ hnoeth hfp₀ hV₀ hflat₀))

/-- **Stacks Project, Tag 0EVC for the flatness stated at the fibre product.** The hypothesis
that `X_V ⟶ V` be flat, read for the projection out of the literal fibre product rather than for
the restriction `f ∣_ V`. The two agree up to the isomorphism
`AlgebraicGeometry.pullbackRestrictIsoRestrict` of the source.

This is the shape in which the converse direction of Stacks tag 0EVF asks for the tag; see
`AlgebraicGeometry.FinitePresentationHasAlmostBlowUpFlattening`. -/
theorem hasFlatAlmostBlowUpSquarePair_of_flat_pullback {X Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (f : X ⟶ Y) (hf : FinitePresentation f) (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) (hflat : Flat (pullback.snd f V.ι))
    (H : NoetherianAffineChartFlatteningCentre.{u}) :
    HasFlatAlmostBlowUpSquarePair f V := by
  exact hasFlatAlmostBlowUpSquarePair_of_flat_of_noetherianAffineChart f hf V hV
    (morphismRestrict_of_pullback_snd (P := @Flat) f V hflat) H

/-- **The affine case of [Stacks, Tag 0815] gives its Noetherian form.**
`AlgebraicGeometry.NoetherianAffineChartFlatteningCentre` asks for the hypothesis-free
chart predicate at every Noetherian base, every morphism of finite presentation and every
quasi-compact open the morphism is flat over. Those are exactly hypothesis (2) of
[Stacks, Tag 081R] plus more, so
`AlgebraicGeometry.AffineChartFlatteningCentre.of_affineCase` supplies the predicate, and that
producer is unconditional.

A Noetherian scheme is quasi-separated, a morphism of finite presentation is locally of finite
type, and local finite presentation over the open is local finite presentation of the projection
out of the fibre product, read through `AlgebraicGeometry.pullbackRestrictIsoRestrict`. -/
theorem NoetherianAffineChartFlatteningCentre.of_affineCase :
    NoetherianAffineChartFlatteningCentre.{u} := by
  intro X₀ Y₀ f₀ V₀ hnoeth hfp hV₀ hflat
  have _ := hnoeth
  have := hfp.locallyOfFinitePresentation
  have := hfp.quasiCompact
  exact AffineChartFlatteningCentre.of_affineCase f₀ V₀ hV₀ hflat
    (morphismRestrict_of_pullback_snd (P := @LocallyOfFinitePresentation) f₀ V₀ inferInstance)

/-- **Stacks Project, Tag 0EVC.** Let `Y` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ Y` be of finite presentation and let `V ⊆ Y` be a quasi-compact open such that
`X_V ⟶ V` is flat. Then there is a diagram as in the tag: two almost blowup squares, over `Y`
with a centre disjoint from `V` and over `X` with the inverse-image centre, whose lower and top
squares are cartesian (`AlgebraicGeometry.lowerSquareIso`, `AlgebraicGeometry.topSquareIso`) and
whose relative morphism `X' ⟶ Y'` is flat and of finite presentation.

Every hypothesis of the source is present, with no Noetherian hypothesis on `Y`: the Noetherian
case is `AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair_of_flat`, run at the Noetherian model
supplied by `AlgebraicGeometry.exists_isNoetherian_model_of_finitePresentation_of_flat` and
pulled back along `Y ⟶ Y₀`. The affine case of the flatness assertion of
[Stacks, Tag 0815] it consumes is
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, itself proved
from [Stacks, Tag 0811], which
`AlgebraicGeometry.NoetherianAffineChartFlatteningCentre.of_affineCase` turns into the form the
Noetherian case consumes.

The tag's hypothesis that `X_V ⟶ V` be flat is essential and is present here, where
`AlgebraicGeometry.hasFlatAlmostBlowUpSquarePair` omits it: without it the affine case cannot be
applied at the model at all, its own hypothesis (5) being exactly that flatness. -/
@[stacks 0EVC "the conclusion in full, under exactly the source's hypotheses and with no \
Noetherian hypothesis on the base: the affine case of the flatness \
assertion of [Stacks, Tag 0815] that the proof consumes is \
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, itself proved from \
[Stacks, Tag 0811]"]
theorem hasFlatAlmostBlowUpSquarePair_of_affineCase {X Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (f : X ⟶ Y) (hf : FinitePresentation f) (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) (hflat : Flat (f ∣_ V)) :
    HasFlatAlmostBlowUpSquarePair f V :=
  hasFlatAlmostBlowUpSquarePair_of_flat_of_noetherianAffineChart f hf V hV hflat
    NoetherianAffineChartFlatteningCentre.of_affineCase

end AlgebraicGeometry

end
