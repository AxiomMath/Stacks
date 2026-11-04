module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Pushouts of algebraic spaces along a thickening and an affine morphism

Let `i : X ⟶ X'` be a thickening of algebraic spaces over `S` and `f : X ⟶ Y` an affine
morphism.  The pushout `Y' = Y ⨿_X X'` exists in the category of algebraic spaces over `S`.
It is built from a compatible pair of étale scheme charts: a chart `U' ⟶ X'` restricting to a
chart `U ⟶ X` and an affine `U ⟶ V` over a chart `V ⟶ Y`, together with the pushouts
`P = U' ⨿_U V` and `Rel = (U' ×_{X'} U') ⨿ (V ×_Y V)` of schemes; then `Y' = P/Rel`.

## Main definitions

* `AlgebraicGeometry.Space.ThickeningAffineAtlas`: such a compatible pair of charts, with the
  two scheme pushouts and the étale equivalence relation they carry.
* `AlgebraicGeometry.Space.HasThickeningAffineAtlases`: every thickening-and-affine span of
  algebraic spaces over `S` admits one.

## Main results

* `AlgebraicGeometry.Space.isPushout_quotient_of_thickeningAffineAtlas`: the quotient of the
  scheme pushout by the pushed-out relation is a pushout of the span of algebraic spaces.
* `AlgebraicGeometry.Space.isPullback_chart_of_isPullback_source`: Stacks 07S3 on representable
  charts, a cartesian square on the first projections of the kernel pairs of two surjective
  étale charts stays cartesian after passing to the sheaves the charts present.
* `AlgebraicGeometry.Space.hasPushout_of_isThickening_of_isAffineHom`: the existence of the
  pushout, for a span admitting a compatible pair of étale scheme charts.
* `AlgebraicGeometry.Space.pushout_inr_isThickening`: the morphism from the affine target to
  the pushout is again a thickening, for such a span.

## Implementation notes

The quotient is formed with `AlgebraicGeometry.Space.quotientMap` and is an algebraic space by
Stacks 02WW; its universal property comes from Stacks 07SY applied twice, to the chart span and
to the relation span, together with the descent of morphisms along a surjective étale atlas
(Stacks 0262).  The étale clause of Stacks 07RX that Stacks 07SY carries as a hypothesis is
discharged here from `Stacks.Pushout.etale_gluingFunctor_obj_iff`.

That the morphism from the affine target is a thickening is read off the chart `V ⟶ P`, which
is the right leg of a pushout of schemes and hence a thickening by Stacks 07RT; the étale-local
criterion for closed immersions is Stacks 03M4.

Stacks 07S3 enters as `AlgebraicGeometry.Space.isPullback_chart_of_isPullback_source`, which
transports the functor-of-points statement `Stacks.Groupoids.isPullback_toQuotientSheaf` along
the identification of a sheaf with the quotient sheaf of the kernel pair of a surjective étale
chart; that identification is Stacks 0262, both the equivalence relation of part (1) and the
universal property of part (3).

`ThickeningAffineAtlas` is the scheme-level half of the source's argument.  Everything stated
about the quotient itself is proved here.

## What is not covered

Stacks 07VX is **not** registered in this module, and the two theorems that would carry it do
not claim it.  Both take a `ThickeningAffineAtlas` for the span as a hypothesis, and producing
one is the part of the source's argument that this library cannot yet supply: it asks for the
lift of an étale *scheme* chart across the thickening, and for the verification that the
pushed-out relation is again an étale equivalence relation, whose details the source omits.

Lifting the chart is Stacks 05ZS on the small étale sites of scheme charts.  Of that, full
faithfulness is available
(`AlgebraicGeometry.Space.fullyFaithfulThickeningChartBaseChangeOfIsFirstOrderThickening`) but
essential surjectivity is not: that is Stacks 07VW, and it needs that the lifted space `V'` is
a scheme whenever `V = X ×_{X'} V'` is, which is Stacks 05ZR.  In this library Stacks 05ZR
rests on Stacks 07VT, an algebraic space admitting a surjective universally closed morphism
from an affine scheme being affine, and that in turn on Stacks 09YA and Stacks 07SQ, neither of
which is proved here.  So the gap is a chain of source results, not a missing piece of
substrate, and it is not closed by restricting to first-order thickenings either, since
Stacks 05ZR is needed at first order too.

## References

* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfOver.hasSheafify_type

/-- The étale clause of Stacks 07RX, in the shape in which Stacks 07SY takes it as a
hypothesis. -/
private theorem etale_gluingFunctor_obj_iff_forall :
    ∀ {Z Z' W : Scheme.{u}} (k : Z ⟶ Z') (g : Z ⟶ W) (hk : Stacks.Thickenings.IsThickening k)
      [_root_.AlgebraicGeometry.IsAffineHom g] [HasPushout k g]
      (T : Stacks.Pushout.gluingData k g),
      Etale ((Stacks.Pushout.gluingFunctor k g hk).obj T).hom ↔
        (Etale T.obj.left.hom ∧ Etale T.obj.right.hom) := by
  intro Z Z' W k g hk hg hpo T
  have := hg
  have := hpo
  exact Stacks.Pushout.etale_gluingFunctor_obj_iff k g hk T

/-- A compatible pair of étale scheme charts for a thickening `i : X ⟶ X'` and an affine
morphism `f : X ⟶ Y` of algebraic spaces over `S`, together with the pushouts of schemes they
determine: `P = U' ⨿_U V` for the charts themselves and `Rel = R' ⨿_{R₀} T` for their kernel
pairs, and the resulting étale equivalence relation `Rel ⇉ P`. -/
structure ThickeningAffineAtlas {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y) where
  /-- The chart of `X`. -/
  U : BigFppfOver B S hS
  /-- The chart of `X'` restricting to `U`. -/
  U' : BigFppfOver B S hS
  /-- The chart of `Y`. -/
  V : BigFppfOver B S hS
  /-- The kernel pair of the chart of `X`. -/
  R₀ : BigFppfOver B S hS
  /-- The kernel pair of the chart of `X'`. -/
  R' : BigFppfOver B S hS
  /-- The kernel pair of the chart of `Y`. -/
  T : BigFppfOver B S hS
  /-- The pushout `U' ⨿_U V` of schemes. -/
  P : BigFppfOver B S hS
  /-- The pushout `R' ⨿_{R₀} T` of schemes. -/
  Rel : BigFppfOver B S hS
  /-- The chart map of `X`. -/
  p : yoneda.obj U ⟶ X.1
  /-- The chart map of `X'`. -/
  p' : yoneda.obj U' ⟶ X'.1
  /-- The chart map of `Y`. -/
  q : yoneda.obj V ⟶ Y.1
  /-- The thickening of charts. -/
  k : U ⟶ U'
  /-- The affine morphism of charts. -/
  g : U ⟶ V
  /-- The thickening of kernel pairs. -/
  kR : R₀ ⟶ R'
  /-- The affine morphism of kernel pairs. -/
  gR : R₀ ⟶ T
  /-- The first projection of the kernel pair of the chart of `X'`. -/
  s' : R' ⟶ U'
  /-- The second projection of the kernel pair of the chart of `X'`. -/
  t' : R' ⟶ U'
  /-- The first projection of the kernel pair of the chart of `Y`. -/
  sY : T ⟶ V
  /-- The second projection of the kernel pair of the chart of `Y`. -/
  tY : T ⟶ V
  /-- The left leg of the pushout of charts. -/
  a : U' ⟶ P
  /-- The right leg of the pushout of charts. -/
  b : V ⟶ P
  /-- The left leg of the pushout of kernel pairs. -/
  aR : R' ⟶ Rel
  /-- The right leg of the pushout of kernel pairs. -/
  bR : T ⟶ Rel
  /-- The first projection of the relation on `P`. -/
  s : Rel ⟶ P
  /-- The second projection of the relation on `P`. -/
  t : Rel ⟶ P
  /-- The chart of `X` is the base change of the chart of `Y` along `f`. -/
  isPullback_affine : IsPullback p (yoneda.map g) f.hom q
  /-- The chart of `X` is the base change of the chart of `X'` along `i`. -/
  isPullback_thickening : IsPullback (yoneda.map k) p p' i.hom
  /-- The morphism of charts over `i` is a thickening of schemes. -/
  isThickening_k : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)
  /-- The morphism of charts over `f` is an affine morphism of schemes. -/
  isAffineHom_g : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g)
  /-- The morphism of kernel pairs over `i` is a thickening of schemes. -/
  isThickening_kR : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map kR)
  /-- The morphism of kernel pairs over `f` is an affine morphism of schemes. -/
  isAffineHom_gR : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map gR)
  /-- The chart of `X` is surjective. -/
  surjective_p : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) p
  /-- The chart of `X` is étale. -/
  etale_p : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) p
  /-- The chart of `X'` is surjective. -/
  surjective_p' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) p'
  /-- The chart of `X'` is étale. -/
  etale_p' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) p'
  /-- The chart of `Y` is surjective. -/
  surjective_q : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) q
  /-- The chart of `Y` is étale. -/
  etale_q : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) q
  /-- `R'` is the kernel pair of the chart of `X'`. -/
  kernelPair_X' : IsPullback (yoneda.map s') (yoneda.map t') p' p'
  /-- `T` is the kernel pair of the chart of `Y`. -/
  kernelPair_Y : IsPullback (yoneda.map sY) (yoneda.map tY) q q
  /-- `P` is the pushout of the charts. -/
  isPushout_chart : IsPushout ((BigFppfOver.toScheme B S hS).map k)
    ((BigFppfOver.toScheme B S hS).map g) ((BigFppfOver.toScheme B S hS).map a)
    ((BigFppfOver.toScheme B S hS).map b)
  /-- `Rel` is the pushout of the kernel pairs. -/
  isPushout_relation : IsPushout ((BigFppfOver.toScheme B S hS).map kR)
    ((BigFppfOver.toScheme B S hS).map gR) ((BigFppfOver.toScheme B S hS).map aR)
    ((BigFppfOver.toScheme B S hS).map bR)
  /-- The first projection restricts on `R'` to the first projection of the kernel pair. -/
  aR_s : aR ≫ s = s' ≫ a
  /-- The second projection restricts on `R'` to the second projection of the kernel pair. -/
  aR_t : aR ≫ t = t' ≫ a
  /-- The first projection restricts on `T` to the first projection of the kernel pair. -/
  bR_s : bR ≫ s = sY ≫ b
  /-- The second projection restricts on `T` to the second projection of the kernel pair. -/
  bR_t : bR ≫ t = tY ≫ b
  /-- `Rel ⇉ P` is an étale equivalence relation. -/
  etaleRelation : IsEtaleEquivalenceRelation (relation B S hS s t)

/-- Every thickening-and-affine span of algebraic spaces over `S` admits a compatible pair of
étale scheme charts in the sense of `AlgebraicGeometry.Space.ThickeningAffineAtlas`. -/
abbrev HasThickeningAffineAtlases : Prop :=
  ∀ {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y),
    IsThickeningHom B S hS i → IsAffineHom B S hS f.hom →
      Nonempty (ThickeningAffineAtlas B S hS i f)

/-- A map `h` out of `P` that restricts along `a` to a map equal on the two projections of a
kernel pair coequalizes the pulled-back projections `s, t` of `ℓ`. -/
private theorem yoneda_map_comp_eq_of_kernelPair {R U P Rel : BigFppfOver B S hS}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ℓ : R ⟶ Rel) (s t : Rel ⟶ P) (s' t' : R ⟶ U)
    (a : U ⟶ P) (p : yoneda.obj U ⟶ F) (z : F ⟶ G) (h : yoneda.obj P ⟶ G)
    (hs : ℓ ≫ s = s' ≫ a) (ht : ℓ ≫ t = t' ≫ a)
    (hp : yoneda.map s' ≫ p = yoneda.map t' ≫ p) (hh : yoneda.map a ≫ h = p ≫ z) :
    yoneda.map ℓ ≫ yoneda.map s ≫ h = yoneda.map ℓ ≫ yoneda.map t ≫ h := by
  rw [← Category.assoc, ← Functor.map_comp, hs, ← Category.assoc, ← Functor.map_comp, ht,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hh, ← Category.assoc,
    hp, Category.assoc]

/-- The quotient of the scheme pushout `P` by the relation `Rel` carried by a compatible pair of
étale scheme charts is a pushout of the span `X' ⟵ X ⟶ Y` in the category of algebraic spaces
over `S`, and the quotient map is a surjective étale chart of it restricting to the two given
charts. -/
theorem isPushout_quotient_of_thickeningAffineAtlas
    {X X' Y : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y}
    (A : ThickeningAffineAtlas B S hS i f) :
    ∃ (E : AlgebraicSpaces B S hS) (a : X' ⟶ E) (b : Y ⟶ E), IsPushout i f a b ∧
      ∃ qm : yoneda.obj A.P ⟶ E.1,
        IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) qm ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) qm ∧
        A.p' ≫ a.hom = yoneda.map A.a ≫ qm ∧ A.q ≫ b.hom = yoneda.map A.b ≫ qm := by
  have := A.etaleRelation
  have := A.isAffineHom_g
  have := A.isAffineHom_gR
  let E : AlgebraicSpaces B S hS :=
    ⟨_, isAlgebraicSpace_quotient_unconditional B S hS A.s A.t⟩
  let qm : yoneda.obj A.P ⟶ E.1 := quotientMap B S hS A.s A.t
  have hqm : IsPullback (yoneda.map A.s) (yoneda.map A.t) qm qm :=
    (quotientMap_isPullback B S hS A.s A.t).flip
  have hqmS := quotientMap_surjective_unconditional B S hS A.s A.t
  have hqmE := quotientMap_etale_unconditional B S hS A.s A.t
  obtain ⟨a₀, ha₀, -⟩ := existsUnique_hom_of_atlas_square B S hS X'.property.isSheaf
    E.property.isSheaf A.p' qm A.surjective_p' A.etale_p' A.kernelPair_X' hqm A.a A.aR
    A.aR_s.symm A.aR_t.symm
  obtain ⟨b₀, hb₀, -⟩ := existsUnique_hom_of_atlas_square B S hS Y.property.isSheaf
    E.property.isSheaf A.q qm A.surjective_q A.etale_q A.kernelPair_Y hqm A.b A.bR
    A.bR_s.symm A.bR_t.symm
  have hab : A.k ≫ A.a = A.g ≫ A.b :=
    (BigFppfOver.toScheme B S hS).map_injective
      (by simpa only [Functor.map_comp] using A.isPushout_chart.w)
  have hAB := isPushout_algebraicSpaces_of_isThickening_of_isAffineHom
    etale_gluingFunctor_obj_iff_forall B S hS A.k A.g A.a A.b A.isThickening_k A.isPushout_chart
  have hRR := isPushout_algebraicSpaces_of_isThickening_of_isAffineHom
    etale_gluingFunctor_obj_iff_forall B S hS A.kR A.gR A.aR A.bR A.isThickening_kR
    A.isPushout_relation
  let a : X' ⟶ E := ObjectProperty.homMk a₀
  let b : Y ⟶ E := ObjectProperty.homMk b₀
  let pX' : (⟨yoneda.obj A.U', isAlgebraicSpace_yoneda B S hS A.U'⟩ :
    AlgebraicSpaces B S hS) ⟶ X' := ObjectProperty.homMk A.p'
  let pY : (⟨yoneda.obj A.V, isAlgebraicSpace_yoneda B S hS A.V⟩ :
    AlgebraicSpaces B S hS) ⟶ Y := ObjectProperty.homMk A.q
  let qE : (⟨yoneda.obj A.P, isAlgebraicSpace_yoneda B S hS A.P⟩ :
    AlgebraicSpaces B S hS) ⟶ E := ObjectProperty.homMk qm
  have haQ : (ObjectProperty.homMk (yoneda.map A.a) :
      (⟨yoneda.obj A.U', isAlgebraicSpace_yoneda B S hS A.U'⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj A.P, isAlgebraicSpace_yoneda B S hS A.P⟩) ≫ qE = pX' ≫ a := by
    apply ObjectProperty.hom_ext
    exact ha₀.symm
  have hbQ : (ObjectProperty.homMk (yoneda.map A.b) :
      (⟨yoneda.obj A.V, isAlgebraicSpace_yoneda B S hS A.V⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj A.P, isAlgebraicSpace_yoneda B S hS A.P⟩) ≫ qE = pY ≫ b := by
    apply ObjectProperty.hom_ext
    exact hb₀.symm
  have hw : i ≫ a = f ≫ b := by
    apply ObjectProperty.hom_ext
    refine hom_ext_of_etale_atlas B S hS X.property.isSheaf E.property.isSheaf A.p
      A.surjective_p A.etale_p ?_
    show A.p ≫ i.hom ≫ a₀ = A.p ≫ f.hom ≫ b₀
    rw [← reassoc_of% A.isPullback_thickening.w, reassoc_of% A.isPullback_affine.w, ha₀, hb₀]
    simp only [← Functor.map_comp_assoc, hab]
  refine ⟨E, a, b, IsPushout.mk' hw ?_ ?_, qm, hqm, hqmS, hqmE, ha₀, hb₀⟩
  · intro Z l m hl hm
    apply ObjectProperty.hom_ext
    refine hom_ext_of_etale_atlas B S hS E.property.isSheaf Z.property.isSheaf qm
      hqmS hqmE ?_
    have hlm : qE ≫ l = qE ≫ m := by
      refine hAB.hom_ext ?_ ?_
      · rw [← Category.assoc, ← Category.assoc, haQ, Category.assoc, Category.assoc, hl]
      · rw [← Category.assoc, ← Category.assoc, hbQ, Category.assoc, Category.assoc, hm]
    exact congrArg (fun φ => φ.hom) hlm
  · intro Z aZ bZ hwZ
    have hc : (ObjectProperty.homMk (yoneda.map A.k) :
        (⟨yoneda.obj A.U, isAlgebraicSpace_yoneda B S hS A.U⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj A.U', isAlgebraicSpace_yoneda B S hS A.U'⟩) ≫ (pX' ≫ aZ) =
        (ObjectProperty.homMk (yoneda.map A.g) :
          (⟨yoneda.obj A.U, isAlgebraicSpace_yoneda B S hS A.U⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj A.V, isAlgebraicSpace_yoneda B S hS A.V⟩) ≫ (pY ≫ bZ) := by
      apply ObjectProperty.hom_ext
      show yoneda.map A.k ≫ A.p' ≫ aZ.hom = yoneda.map A.g ≫ A.q ≫ bZ.hom
      rw [reassoc_of% A.isPullback_thickening.w, ← reassoc_of% A.isPullback_affine.w]
      exact congrArg (fun φ => A.p ≫ φ.hom) hwZ
    let h := hAB.desc (pX' ≫ aZ) (pY ≫ bZ) hc
    have hhA : yoneda.map A.a ≫ h.hom = A.p' ≫ aZ.hom :=
      congrArg (fun φ => φ.hom) (hAB.inl_desc (pX' ≫ aZ) (pY ≫ bZ) hc)
    have hhB : yoneda.map A.b ≫ h.hom = A.q ≫ bZ.hom :=
      congrArg (fun φ => φ.hom) (hAB.inr_desc (pX' ≫ aZ) (pY ≫ bZ) hc)
    have hrel : yoneda.map A.s ≫ h.hom = yoneda.map A.t ≫ h.hom := by
      have hRel : (ObjectProperty.homMk (yoneda.map A.s) :
          (⟨yoneda.obj A.Rel, isAlgebraicSpace_yoneda B S hS A.Rel⟩ :
            AlgebraicSpaces B S hS) ⟶
              ⟨yoneda.obj A.P, isAlgebraicSpace_yoneda B S hS A.P⟩) ≫ h =
          (ObjectProperty.homMk (yoneda.map A.t) :
            (⟨yoneda.obj A.Rel, isAlgebraicSpace_yoneda B S hS A.Rel⟩ :
              AlgebraicSpaces B S hS) ⟶
                ⟨yoneda.obj A.P, isAlgebraicSpace_yoneda B S hS A.P⟩) ≫ h := by
        refine hRR.hom_ext ?_ ?_
        · apply ObjectProperty.hom_ext
          exact yoneda_map_comp_eq_of_kernelPair B S hS A.aR A.s A.t A.s' A.t' A.a A.p'
            aZ.hom h.hom A.aR_s A.aR_t A.kernelPair_X'.w hhA
        · apply ObjectProperty.hom_ext
          exact yoneda_map_comp_eq_of_kernelPair B S hS A.bR A.s A.t A.sY A.tY A.b A.q
            bZ.hom h.hom A.bR_s A.bR_t A.kernelPair_Y.w hhB
      exact congrArg (fun φ => φ.hom) hRel
    obtain ⟨l, hl, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS
      E.property.isSheaf qm hqm hqmS hqmE Z.property.isSheaf h.hom hrel
    refine ⟨ObjectProperty.homMk l, ?_, ?_⟩ <;> apply ObjectProperty.hom_ext
    · refine hom_ext_of_etale_atlas B S hS X'.property.isSheaf Z.property.isSheaf A.p'
        A.surjective_p' A.etale_p' ?_
      show A.p' ≫ a₀ ≫ l = A.p' ≫ aZ.hom
      rw [reassoc_of% ha₀, hl, hhA]
    · refine hom_ext_of_etale_atlas B S hS Y.property.isSheaf Z.property.isSheaf A.q
        A.surjective_q A.etale_q ?_
      show A.q ≫ b₀ ≫ l = A.q ≫ bZ.hom
      rw [reassoc_of% hb₀, hl, hhB]

/-- A thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` of algebraic spaces over `S`
whose spans all admit a compatible pair of étale scheme charts have a pushout
`Y' = Y ⨿_X X'` in the category of algebraic spaces over `S`.

This is the space-level half of Stacks 07VX, which is not registered here: the charts are a
hypothesis rather than a result, for the reasons set out under `What is not covered` in the
module docstring. -/
theorem hasPushout_of_isThickening_of_isAffineHom
    (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) :
    HasPushout i f := by
  obtain ⟨A⟩ := hatlas i f hi hf
  obtain ⟨E, a, b, h, -⟩ := isPushout_quotient_of_thickeningAffineAtlas B S hS A
  exact h.hasPushout

/-- The right leg of a pushout of a thickening along an affine morphism of schemes is again a
thickening. -/
private theorem isThickening_inr_of_isPushout {Z Z' W P : Scheme.{u}}
    (k : Z ⟶ Z') (g : Z ⟶ W) (hk : Stacks.Thickenings.IsThickening k)
    [_root_.AlgebraicGeometry.IsAffineHom g] {a : Z' ⟶ P} {b : W ⟶ P}
    (h : IsPushout k g a b) : Stacks.Thickenings.IsThickening b := by
  have := h.hasPushout
  have hb := Stacks.Pushout.pushout_inr_isThickening
    Stacks.Thickenings.forall_isAffine_of_isThickening k g hk
  have : _root_.AlgebraicGeometry.IsClosedImmersion (pushout.inr k g) := hb.1
  have : Surjective (pushout.inr k g) := ⟨hb.2⟩
  rw [← h.inr_isoPushout_inv]
  exact ⟨inferInstance,
    (inferInstance : Surjective (pushout.inr k g ≫ h.isoPushout.inv)).surj⟩

/-- A commuting square of two thickenings over two étale morphisms is cartesian. -/
private theorem isPullback_of_isThickening_of_etale {Z W R P : Scheme.{u}}
    (j : Z ⟶ R) (b : W ⟶ P) (s : R ⟶ P) (s₀ : Z ⟶ W)
    (hj : Stacks.Thickenings.IsThickening j) (hb : Stacks.Thickenings.IsThickening b)
    [Etale s] [Etale s₀] (hw : j ≫ s = s₀ ≫ b) : IsPullback j s₀ s b := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion j := hj.1
  have : _root_.AlgebraicGeometry.IsClosedImmersion b := hb.1
  let l := pullback.lift j s₀ hw
  have hl : l ≫ pullback.fst s b = j := pullback.lift_fst _ _ _
  have hl' : l ≫ pullback.snd s b = s₀ := pullback.lift_snd _ _ _
  have : Mono l := mono_of_mono_fac hl
  have : Etale (l ≫ pullback.snd s b) := by rw [hl']; infer_instance
  have : Etale l := Etale.of_comp l (pullback.snd s b)
  have : _root_.AlgebraicGeometry.IsOpenImmersion l := IsOpenImmersion.of_flat_of_mono l
  have : Surjective l := by
    constructor
    intro x
    obtain ⟨z, hz⟩ := hj.2 ((pullback.fst s b) x)
    refine ⟨z, ?_⟩
    apply (inferInstance :
      _root_.AlgebraicGeometry.IsClosedImmersion (pullback.fst s b)).isClosedEmbedding.injective
    simpa only [← Scheme.Hom.comp_apply, hl] using hz
  have : IsIso l := (isIso_iff_isOpenImmersion_and_surjective l).mpr
    ⟨inferInstance, inferInstance⟩
  exact (IsPullback.of_hasPullback s b).of_iso (asIso l).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [l, pullback.lift_fst]) (by simp [l, pullback.lift_snd]) (by simp) (by simp)

/-- The comparison isomorphism between the restricted functor of points of an object of the
site and the presheaf it represents is natural. -/
private theorem whiskerLeft_pointsYonedaIso_hom {X Y : BigFppfOver B S hS} (φ : X ⟶ Y) :
    (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map φ)) ≫
      (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) Y).hom =
      (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) X).hom ≫ yoneda.map φ := by
  have h := pointsYonedaIso_inv_comp (Over.post (X := B.obj hS) B.inclusion)
    ((Over.post (X := B.obj hS) B.inclusion).map φ)
  rw [Functor.preimage_map] at h
  rw [← h, Iso.hom_inv_id_assoc]

/-- The target map of the relation carried by `s, t : R ⟶ U` is the source map of the relation
carried by the pair in the other order. -/
private theorem sourceMap_relation_swap {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS t s) =
      Stacks.Groupoids.targetMap (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS s t) := by
  show (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
    (yoneda.map (prod.lift _ _ ≫ prod.snd)) = _
  rw [prod.lift_snd]
  show _ = (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
    (yoneda.map (prod.lift _ _ ≫ prod.fst))
  rw [prod.lift_fst]

/-- The source map of the relation carried by `s, t : R ⟶ U` is conjugate to `s` under the
comparison isomorphisms between the restricted functors of points and the represented
presheaves. -/
private theorem sourceMap_comp_pointsYonedaIso_hom {R U : BigFppfOver B S hS} (s t : R ⟶ U) :
    Stacks.Groupoids.sourceMap (Over.post (X := B.obj hS) B.inclusion)
          (relation B S hS s t) ≫
        (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) U).hom =
      (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) R).hom ≫ yoneda.map s := by
  rw [← whiskerLeft_pointsYonedaIso_hom B S hS s]
  congr 1
  show (Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
    (yoneda.map (prod.lift _ _ ≫ prod.snd)) = _
  rw [prod.lift_snd]

/-- A sheaf with a surjective étale chart is the quotient sheaf of the kernel pair of that
chart: both carry the universal property of the quotient, so there is an isomorphism between
them taking the projection onto the quotient sheaf to the chart. -/
private theorem exists_quotientSheafIso_of_etale_atlas
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (p : yoneda.obj U ⟶ F) {s t : R ⟶ U}
    (hkp : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p) :
    ∃ e : (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t)).obj ≅ F,
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s t) ≫ e.hom =
        (pointsYonedaIso (Over.post (X := B.obj hS) B.inclusion) U).hom ≫ p := by
  have h1 := sourceMap_comp_pointsYonedaIso_hom B S hS s t
  have h2 := sourceMap_comp_pointsYonedaIso_hom B S hS t s
  rw [sourceMap_relation_swap B S hS s t] at h2
  -- the quotient projection, read on the representable chart
  obtain ⟨k, hk⟩ : ∃ k : yoneda.obj U ⟶ (Stacks.Groupoids.quotientSheaf
      (BigFppfOver.topology B S hS) (Over.post B.inclusion) (relation B S hS s t)).obj,
      (pointsYonedaIso (Over.post B.inclusion) U).hom ≫ k =
        Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS s t) :=
    ⟨(pointsYonedaIso (Over.post B.inclusion) U).inv ≫
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t), by rw [Iso.hom_inv_id_assoc]⟩
  have hkrel : yoneda.map s ≫ k = yoneda.map t ≫ k := by
    refine (cancel_epi (pointsYonedaIso (Over.post B.inclusion) R).hom).mp ?_
    rw [← Category.assoc _ (yoneda.map s) k, ← Category.assoc _ (yoneda.map t) k,
      ← h1, ← h2, Category.assoc, Category.assoc, hk,
      Stacks.Groupoids.sourceMap_toQuotientSheaf]
  -- the universal property of the quotient sheaf, read through the comparison isomorphism
  have hQuniv : ∀ W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u,
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) W → ∀ l : yoneda.obj U ⟶ W,
        yoneda.map s ≫ l = yoneda.map t ≫ l → ∃! d, k ≫ d = l := by
    intro W hW l hl
    have hcond : Stacks.Groupoids.sourceMap (Over.post B.inclusion) (relation B S hS s t) ≫
        ((pointsYonedaIso (Over.post B.inclusion) U).hom ≫ l) =
        Stacks.Groupoids.targetMap (Over.post B.inclusion) (relation B S hS s t) ≫
        ((pointsYonedaIso (Over.post B.inclusion) U).hom ≫ l) := by
      rw [← Category.assoc _ _ l, ← Category.assoc _ _ l, h1, h2,
        Category.assoc, Category.assoc, hl]
    refine ⟨(Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t) ⟨W, hW⟩ _ hcond).hom, ?_, ?_⟩
    · refine (cancel_epi (pointsYonedaIso (Over.post B.inclusion) U).hom).mp ?_
      rw [← Category.assoc _ k _, hk,
        Stacks.Groupoids.toQuotientSheaf_quotientSheafDesc]
    · intro d hd
      have hdd : Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS s t) ≫ d =
          (pointsYonedaIso (Over.post B.inclusion) U).hom ≫ l := by
        rw [← hk, Category.assoc, hd]
      exact congrArg (fun η : _ ⟶ (⟨W, hW⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ↦
        η.hom) (Stacks.Groupoids.quotientSheafDesc_unique (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS s t) ⟨W, hW⟩ _ hcond ⟨d⟩ hdd)
  obtain ⟨m, hm, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hF p hkp hsurj hetale
    (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t)).property k hkrel
  obtain ⟨d, hd, -⟩ := hQuniv F hF p hkp.w
  refine ⟨⟨d, m, ?_, ?_⟩, ?_⟩
  · obtain ⟨w, -, huniq⟩ := hQuniv _ (Stacks.Groupoids.quotientSheaf
      (BigFppfOver.topology B S hS) (Over.post B.inclusion) (relation B S hS s t)).property
      k hkrel
    rw [huniq (d ≫ m) (show k ≫ d ≫ m = k by rw [← Category.assoc k d m, hd, hm]),
      huniq (𝟙 _) (Category.comp_id k)]
  · obtain ⟨w, -, huniq⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hF p hkp
      hsurj hetale hF p hkp.w
    rw [huniq (m ≫ d) (show p ≫ m ≫ d = p by rw [← Category.assoc p m d, hm, hd]),
      huniq (𝟙 F) (Category.comp_id p)]
  · rw [← hk, Category.assoc, hd]

/-- The functor from the big fppf site to `S`-schemes preserves fibre products, the forgetful
functor to schemes reflecting them. -/
private theorem preservesPullbacks_post_inclusion :
    PreservesLimitsOfShape WalkingCospan (Over.post (X := B.obj hS) B.inclusion) :=
  have : PreservesLimitsOfShape WalkingCospan
      (Over.post (X := B.obj hS) B.inclusion ⋙ Over.forget S) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- **Stacks 07S3** read on representable charts: a cartesian square on the first projections
of the kernel pairs of two surjective étale charts stays cartesian after passing to the sheaves
the charts present. -/
theorem isPullback_chart_of_isPullback_source
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U R' U' : BigFppfOver B S hS}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (p : yoneda.obj U ⟶ F) (p' : yoneda.obj U' ⟶ G) {s t : R ⟶ U} {s' t' : R' ⟶ U'}
    {c : U ⟶ U'} {ρ : R ⟶ R'} (φ : F ⟶ G)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p)
    (hsurj' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p')
    (hetale' : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) p')
    (hkp : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (hkp' : IsPullback (yoneda.map s') (yoneda.map t') p' p')
    (hρs : ρ ≫ s' = s ≫ c) (hρt : ρ ≫ t' = t ≫ c) (hcart : IsPullback ρ s s' c)
    (hφ : p ≫ φ = yoneda.map c ≫ p') :
    IsPullback (yoneda.map c) p p' φ := by
  have hsrc : (relation B S hS s t).source =
      (Over.post (X := B.obj hS) B.inclusion).map s := prod.lift_snd _ _
  have htgt : (relation B S hS s t).target =
      (Over.post (X := B.obj hS) B.inclusion).map t := prod.lift_fst _ _
  have hsrc' : (relation B S hS s' t').source =
      (Over.post (X := B.obj hS) B.inclusion).map s' := prod.lift_snd _ _
  have htgt' : (relation B S hS s' t').target =
      (Over.post (X := B.obj hS) B.inclusion).map t' := prod.lift_fst _ _
  have _ : IsEquivalenceRelation (relation B S hS s t).target
      (relation B S hS s t).source := by
    rw [htgt, hsrc]
    exact isEquivalenceRelation_of_isPullback B S hS p t s hkp.flip
  have _ : IsEquivalenceRelation (relation B S hS s' t').target
      (relation B S hS s' t').source := by
    rw [htgt', hsrc']
    exact isEquivalenceRelation_of_isPullback B S hS p' t' s' hkp'.flip
  have hs07 : (Over.post (X := B.obj hS) B.inclusion).map ρ ≫
      (relation B S hS s' t').source =
      (relation B S hS s t).source ≫ (Over.post (X := B.obj hS) B.inclusion).map c := by
    rw [hsrc, hsrc', ← Functor.map_comp, ← Functor.map_comp, hρs]
  have ht07 : (Over.post (X := B.obj hS) B.inclusion).map ρ ≫
      (relation B S hS s' t').target =
      (relation B S hS s t).target ≫ (Over.post (X := B.obj hS) B.inclusion).map c := by
    rw [htgt, htgt', ← Functor.map_comp, ← Functor.map_comp, hρt]
  have hcart07 : IsPullback ((Over.post (X := B.obj hS) B.inclusion).map ρ)
      (relation B S hS s t).source (relation B S hS s' t').source
      ((Over.post (X := B.obj hS) B.inclusion).map c) := by
    rw [hsrc, hsrc']
    have := preservesPullbacks_post_inclusion B S hS
    exact hcart.map (Over.post (X := B.obj hS) B.inclusion)
  have h07 := Stacks.Groupoids.isPullback_toQuotientSheaf (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) (relation B S hS s t) (relation B S hS s' t')
    ((Over.post (X := B.obj hS) B.inclusion).map ρ)
    ((Over.post (X := B.obj hS) B.inclusion).map c) hs07 ht07 hcart07
    (Stacks.Groupoids.isSheaf_points B S hS ((Over.post B.inclusion).obj U))
    (Stacks.Groupoids.isSheaf_points B S hS ((Over.post B.inclusion).obj U'))
  obtain ⟨eF, heF⟩ := exists_quotientSheafIso_of_etale_atlas B S hS hF p hkp hsurj hetale
  obtain ⟨eG, heG⟩ := exists_quotientSheafIso_of_etale_atlas B S hS hG p' hkp' hsurj' hetale'
  have hnc := whiskerLeft_pointsYonedaIso_hom B S hS (X := U) (Y := U') c
  -- the induced map of quotient sheaves agrees with `φ` across the two isomorphisms
  have hcond : Stacks.Groupoids.sourceMap (Over.post B.inclusion) (relation B S hS s t) ≫
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t) ≫ eF.hom ≫ φ) =
      Stacks.Groupoids.targetMap (Over.post B.inclusion) (relation B S hS s t) ≫
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t) ≫ eF.hom ≫ φ) := by
    calc Stacks.Groupoids.sourceMap (Over.post B.inclusion) (relation B S hS s t) ≫
          (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
            (Over.post B.inclusion) (relation B S hS s t) ≫ eF.hom ≫ φ)
        = (Stacks.Groupoids.sourceMap (Over.post B.inclusion) (relation B S hS s t) ≫
            Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
              (Over.post B.inclusion) (relation B S hS s t)) ≫ (eF.hom ≫ φ) :=
          (Category.assoc _ _ _).symm
      _ = (Stacks.Groupoids.targetMap (Over.post B.inclusion) (relation B S hS s t) ≫
            Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
              (Over.post B.inclusion) (relation B S hS s t)) ≫ (eF.hom ≫ φ) := by
          rw [Stacks.Groupoids.sourceMap_toQuotientSheaf]
      _ = _ := Category.assoc _ _ _
  have key : ∀ d : (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t)) ⟶ (⟨G, hG⟩ :
        Sheaf (BigFppfOver.topology B S hS) (Type u)),
      Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS s t) ≫ d.hom =
        Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (relation B S hS s t) ≫ eF.hom ≫ φ →
      d = Stacks.Groupoids.quotientSheafDesc (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t) ⟨G, hG⟩ _ hcond :=
    fun d hd ↦ Stacks.Groupoids.quotientSheafDesc_unique (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t) ⟨G, hG⟩ _ hcond d hd
  have hleft : Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t) (relation B S hS s' t')
      ((Over.post (X := B.obj hS) B.inclusion).map ρ)
      ((Over.post (X := B.obj hS) B.inclusion).map c) hs07 ht07 ≫ ⟨eG.hom⟩ =
      (⟨eF.hom ≫ φ⟩ : _ ⟶ (⟨G, hG⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u))) := by
    refine (key _ ?_).trans (key _ rfl).symm
    show Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t) ≫
      (Stacks.Groupoids.quotientSheafMap (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (relation B S hS s t) (relation B S hS s' t')
        ((Over.post (X := B.obj hS) B.inclusion).map ρ)
        ((Over.post (X := B.obj hS) B.inclusion).map c) hs07 ht07).hom ≫ eG.hom = _
    rw [← Category.assoc (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t)),
      Stacks.Groupoids.toQuotientSheaf_comp_quotientSheafMap, Category.assoc, heG,
      ← Category.assoc ((Over.post B.inclusion).op.whiskerLeft
        (yoneda.map ((Over.post (X := B.obj hS) B.inclusion).map c))),
      hnc, Category.assoc, ← hφ, ← Category.assoc _ p φ, ← heF, Category.assoc]
  refine h07.flip.of_iso (pointsYonedaIso (Over.post B.inclusion) U)
    (pointsYonedaIso (Over.post B.inclusion) U') eF eG hnc heF heG ?_
  exact congrArg (fun η : _ ⟶ (⟨G, hG⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ↦
    η.hom) hleft

/-- Being a thickening is invariant under composing with an isomorphism on the right. -/
private theorem isThickeningHom_comp_iso {X Y Z : AlgebraicSpaces B S hS} {g : X ⟶ Y}
    (hg : IsThickeningHom B S hS g) (e : Y ≅ Z) : IsThickeningHom B S hS (g ≫ e.hom) := by
  have : IsIso e.hom.hom := ⟨⟨e.inv.hom, congrArg (fun φ => φ.hom) e.hom_inv_id,
    congrArg (fun φ => φ.hom) e.inv_hom_id⟩⟩
  refine (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS (g ≫ e.hom)).mpr
    ⟨?_, ?_⟩
  · let Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    have : Q.RespectsIso := inferInstance
    exact MorphismProperty.RespectsIso.postcomp Q e.hom.hom g.hom hg.isClosedImmersion
  · intro z
    obtain ⟨y, hy⟩ := pointsMap_surjective_of_isIso B S hS e.hom.hom z
    obtain ⟨x, hx⟩ := hg.surjective_pointsMap y
    refine ⟨x, ?_⟩
    show pointsMap B S hS X.1 (g.hom ≫ e.hom.hom) x = z
    rw [pointsMap_comp]
    simp only [Function.comp_apply]
    rw [hx]
    exact hy

/-- The morphism `Y ⟶ Y'` from the affine target into the pushout is a thickening, for a span
all of whose thickening-and-affine spans admit a compatible pair of étale scheme charts.

This is the space-level half of the corresponding assertion of Stacks 07VX, which is not
registered here; see `What is not covered` in the module docstring. -/
theorem pushout_inr_isThickening
    (hatlas : HasThickeningAffineAtlases B S hS)
    {X X' Y : AlgebraicSpaces B S hS} (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickeningHom B S hS i) (hf : IsAffineHom B S hS f.hom) [HasPushout i f] :
    IsThickeningHom B S hS (pushout.inr i f) := by
  obtain ⟨A⟩ := hatlas i f hi hf
  obtain ⟨E, a, b, hpush, qm, hqm, hqmS, hqmE, -, hb₀⟩ :=
    isPushout_quotient_of_thickeningAffineAtlas B S hS A
  have := A.isAffineHom_g
  have := A.isAffineHom_gR
  -- the right leg of each scheme pushout is a thickening
  have hbT : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map A.b) :=
    isThickening_inr_of_isPushout _ _ A.isThickening_k A.isPushout_chart
  have hbRT : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map A.bR) :=
    isThickening_inr_of_isPushout _ _ A.isThickening_kR A.isPushout_relation
  -- the two first projections are étale
  have hEs : Etale ((BigFppfOver.toScheme B S hS).map A.s) := by
    have h : (relation B S hS A.s A.t).source = (Over.post B.inclusion).map A.s :=
      prod.lift_snd _ _
    have hrel := A.etaleRelation.etale_source
    rw [h] at hrel
    exact hrel
  have hEsY : Etale ((BigFppfOver.toScheme B S hS).map A.sY) :=
    A.etale_q.property A.q (yoneda.map A.tY) A.sY A.kernelPair_Y.flip
  -- the relation square over the first projections is cartesian
  have hcartScheme : IsPullback ((BigFppfOver.toScheme B S hS).map A.bR)
      ((BigFppfOver.toScheme B S hS).map A.sY) ((BigFppfOver.toScheme B S hS).map A.s)
      ((BigFppfOver.toScheme B S hS).map A.b) :=
    isPullback_of_isThickening_of_etale _ _ _ _ hbRT hbT
      (by simpa only [← Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map A.bR_s)
  have hcart : IsPullback A.bR A.sY A.s A.b :=
    IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hcartScheme
  -- hence the chart of `Y` is the base change of the chart of the pushout
  have hbase : IsPullback (yoneda.map A.b) A.q qm b.hom :=
    isPullback_chart_of_isPullback_source B S hS Y.property.isSheaf E.property.isSheaf
      A.q qm b.hom A.surjective_q A.etale_q hqmS hqmE A.kernelPair_Y hqm
      A.bR_s A.bR_t hcart hb₀
  -- `b` is a closed immersion, by the étale-local criterion on the chart `qm`
  have hstabCI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have hstabS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have hbCI : IsClosedImmersion B S hS (yoneda.map A.b) :=
    MorphismProperty.relative_map hbT.1
  have hbS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map A.b) :=
    MorphismProperty.relative_map (show (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) A.b from ⟨hbT.2⟩)
  have hsnd : IsClosedImmersion B S hS (pullback.snd b.hom qm) := by
    have heq : hbase.flip.isoPullback.inv ≫ yoneda.map A.b = pullback.snd b.hom qm := by simp
    have h := MorphismProperty.RespectsIso.precomp
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) hbase.flip.isoPullback.inv _ hbCI
    rwa [heq] at h
  have hclosed : IsClosedImmersion B S hS b.hom := by
    refine ((isClosedImmersion_tfae B S hS Y.property E.property b.hom).out 4 1).mp ?_
    exact ⟨A.P, qm, hqmS, hqmE, hsnd⟩
  -- `b` is surjective on points
  have hbPts : Function.Surjective
      (pointsMap B S hS (yoneda.obj A.V) (yoneda.map A.b)) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj A.P)
      (isAlgebraicSpace_yoneda B S hS A.P) A.V (yoneda.map A.b)).mp hbS
  have hqmPts : Function.Surjective (pointsMap B S hS (yoneda.obj A.P) qm) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS E.1 E.property A.P qm).mp hqmS
  have hbSurj : Function.Surjective (pointsMap B S hS Y.1 b.hom) := by
    intro e
    obtain ⟨z, hz⟩ := hqmPts e
    obtain ⟨v, hv⟩ := hbPts z
    refine ⟨pointsMap B S hS (yoneda.obj A.V) A.q v, ?_⟩
    have h : pointsMap B S hS (yoneda.obj A.V) (A.q ≫ b.hom) v = e := by
      rw [hb₀, pointsMap_comp]
      simp only [Function.comp_apply]
      rw [hv, hz]
    rw [pointsMap_comp] at h
    simpa only [Function.comp_apply] using h
  have hbThick : IsThickeningHom B S hS b :=
    (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS b).mpr ⟨hclosed, hbSurj⟩
  have hiso := isThickeningHom_comp_iso B S hS hbThick hpush.isoPushout
  rwa [hpush.inr_isoPushout_hom] at hiso

end AlgebraicGeometry.Space

end
