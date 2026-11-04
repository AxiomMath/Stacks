module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecAtlasRelation

/-!
# The relative spectra over a relation of étale charts form an étale equivalence relation

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site, and let `pr₁, pr₂ : V' ⟶ V₂` be a pair of morphisms of
étale charts of `X` exhibiting `V'` as the fibre product `V₂ ×_X V₂`.
`AlgebraicGeometry.Space.chartRelativeSpecSiteMap` turns the pair into a pair of morphisms
`\underline{Spec}_{V'}(A|_{V'}) ⇉ \underline{Spec}_{V₂}(A|_{V₂})` of objects of the big fppf site
over `S`, and this file proves that **that pair is an étale equivalence relation**.

This is the hypothesis `hrel` of
`AlgebraicGeometry.Space.isEtaleEquivalenceRelation_chartRelativeSpecSiteMap`, the last
mathematical input the atlas construction of Stacks 081V needed at a single algebra: with it, the
quotient of Tag 02WW is formed, and for `A` the integral closure of `𝒪_X` in `f_* 𝒪_Y` the
quotient is the normalization of `X` in `Y` of Definition 0822.

## Main definitions

* `AlgebraicGeometry.Space.chartRelationLift`: the morphism of étale charts into `V'` that a pair
  of morphisms into `V₂` determines, by the universal property of `V' = V₂ ×_X V₂`.
* `AlgebraicGeometry.Space.chartRelationDiag`, `AlgebraicGeometry.Space.chartRelationSwap` and
  `AlgebraicGeometry.Space.chartRelationOuter`: the diagonal `V₂ ⟶ V'`, the swap `V' ⟶ V'` and
  the composition `V' ×_{V₂} V' ⟶ V'` of the relation of charts.
* `AlgebraicGeometry.Space.chartRelativeSpecSiteToChart`: the structure morphism of the relative
  spectrum over a chart, read on objects of the site.
* `AlgebraicGeometry.Space.equivalenceRelation_chartRelativeSpecSiteMap`: the internal
  equivalence-relation structure on the pair of relative spectra.

## Main results

* `AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap`: the cartesian square of
  `AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap`, read in the big fppf category
  over `S` rather than in schemes.
* `AlgebraicGeometry.Space.jointlyMono₂_chartRelativeSpecSiteMap`: the two induced morphisms are
  jointly monic.
* `AlgebraicGeometry.Space.isPullback_chartRelativeSpecSiteMap₂`: the relative spectrum over the
  triple fibre product `V' ×_{V₂} V'` is the fibre product of two copies of the relative spectrum
  over `V'`, which is the limiting cone transitivity needs.
* `AlgebraicGeometry.Space.isEquivalenceRelation_chartRelativeSpecSiteMap`: **the pair of
  morphisms of relative spectra is an internal equivalence relation of presheaves.**
* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_chartRelativeSpecSiteMap_of_isPullback`:
  **it is an étale equivalence relation over `S`**, in the sense of Tag 02WS, so that Tag 02WW
  applies to its quotient sheaf.

## Implementation notes

The whole file is the transposition of
`AlgebraicGeometry.Space.NormalizationGluing.equivalenceRelation_normRel`, which does the same
for the chart normalizations of a relatively representable morphism, from the chart
normalizations to the chart relative spectra.  Two things make the transposition possible, and
neither was available when the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecAtlasRelation` were written:

* the functoriality `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp` and
  `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_id`, which is what all five of the
  reflexivity, symmetry and transitivity identities reduce to — exactly as
  `AlgebraicGeometry.Space.NormalizationGluing.normChartMap_comp` is in the representable
  analogue;
* `AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap`, which supplies the two
  cartesian squares for joint monicity and, pasted with the cartesian square of the triple fibre
  product of charts, the transitivity cone.

**The structural morphisms come from the charts, not from the algebra.**  The diagonal, the swap
and the composition of the relation of charts are produced by
`AlgebraicGeometry.Space.chartRelationLift` from the hypothesis `hsq` that `V'` is `V₂ ×_X V₂`,
through the fullness of `CategoryTheory.yoneda`, and the triple fibre product `V' ×_{V₂} V'` is
the one that `AlgebraicGeometry.Space.SmallEtale.instHasPullbacks` provides in the small étale
site itself.  No property of `A` beyond quasi-coherence is used anywhere.

**The three containment hypotheses.**  `hV'`, `hV₂` and `hV''` ask that the relative spectra over
the three charts be objects of the site.  Carrying them is not a weakening: it is the same
set-theoretic side condition at three charts, it is what
`AlgebraicGeometry.Space.chartRelativeSpecSite` takes at one chart, and for the algebra of
Definition 0822 all three are theorems —
`AlgebraicGeometry.Space.contains_chartRelativeSpec_integralClosureSheaf_pushforwardAlgebra`
proves the containment for *every* étale chart of `X` at quasi-compactness and
quasi-separatedness of `f` and nothing else.

**No `stacks` attribute is carried.**  What is proved here is the equivalence-relation condition
for one step of the atlas construction of Stacks 081V, not a numbered assertion of the source;
Tag 02WS is the definition of an étale equivalence relation and is registered on
`Stacks.Groupoids.IsEtaleEquivalenceRelation` where it is stated, and Tag 02WW is registered on
the quotient.  Definition 0822 is still not reached here: the morphism `ν` and the factorization
of `f` through it are not constructed in this file.

## References

* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

/-! ### The structural morphisms of a relation of étale charts -/

section ChartRelation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V' V₂ : SmallEtale B S hS F} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS F).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS F).map pr₂)) V₂.obj.hom V₂.obj.hom)

/-- **The morphism of étale charts into `V'` determined by a pair of morphisms into `V₂`**, for a
pair `pr₁, pr₂ : V' ⟶ V₂` exhibiting `V'` as the fibre product `V₂ ×_X V₂`.

The two composites with the structure morphism of `V₂` agree automatically — both are the
structure morphism of the source — so the universal property of the cartesian square applies with
no condition, and the resulting morphism of the big fppf category over `S` is a morphism of
charts because its composite with the structure morphism of `V'` is that of the source. -/
def chartRelationLift {W : SmallEtale B S hS F} (a b : W ⟶ V₂) : W ⟶ V' :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (yoneda.preimage (hsq.lift (yoneda.map ((SmallEtale.toOver B S hS F).map a))
      (yoneda.map ((SmallEtale.toOver B S hS F).map b))
      ((yoneda_map_toOver_map_comp_hom a).trans
        (yoneda_map_toOver_map_comp_hom b).symm))) (by
    rw [← yoneda_map_toOver_map_comp_hom pr₁, ← Category.assoc, yoneda.map_preimage,
      hsq.lift_fst]
    exact yoneda_map_toOver_map_comp_hom a))

/-- The image of `chartRelationLift pr₁ pr₂ hsq a b` in the big fppf category over `S` is the
morphism given by the universal property of the cartesian square `hsq`. -/
@[simp]
theorem toOver_map_chartRelationLift {W : SmallEtale B S hS F} (a b : W ⟶ V₂) :
    (SmallEtale.toOver B S hS F).map (chartRelationLift pr₁ pr₂ hsq a b) =
      yoneda.preimage (hsq.lift (yoneda.map ((SmallEtale.toOver B S hS F).map a))
        (yoneda.map ((SmallEtale.toOver B S hS F).map b))
        ((yoneda_map_toOver_map_comp_hom a).trans
          (yoneda_map_toOver_map_comp_hom b).symm)) :=
  rfl

/-- The composite of `chartRelationLift pr₁ pr₂ hsq a b` with `pr₁` is `a`. -/
@[reassoc]
theorem chartRelationLift_comp_fst {W : SmallEtale B S hS F} (a b : W ⟶ V₂) :
    chartRelationLift pr₁ pr₂ hsq a b ≫ pr₁ = a := by
  refine (SmallEtale.toOver B S hS F).map_injective (yoneda.map_injective ?_)
  simp only [Functor.map_comp, toOver_map_chartRelationLift, yoneda.map_preimage,
    hsq.lift_fst]

/-- The composite of `chartRelationLift pr₁ pr₂ hsq a b` with `pr₂` is `b`. -/
@[reassoc]
theorem chartRelationLift_comp_snd {W : SmallEtale B S hS F} (a b : W ⟶ V₂) :
    chartRelationLift pr₁ pr₂ hsq a b ≫ pr₂ = b := by
  refine (SmallEtale.toOver B S hS F).map_injective (yoneda.map_injective ?_)
  simp only [Functor.map_comp, toOver_map_chartRelationLift, yoneda.map_preimage,
    hsq.lift_snd]

/-- **The diagonal `V₂ ⟶ V'` of a relation of étale charts.** -/
def chartRelationDiag : V₂ ⟶ V' := chartRelationLift pr₁ pr₂ hsq (𝟙 V₂) (𝟙 V₂)

/-- The composite of the diagonal `chartRelationDiag pr₁ pr₂ hsq` with `pr₁` is the identity. -/
@[reassoc]
theorem chartRelationDiag_comp_fst : chartRelationDiag pr₁ pr₂ hsq ≫ pr₁ = 𝟙 V₂ :=
  chartRelationLift_comp_fst pr₁ pr₂ hsq _ _

/-- The composite of the diagonal `chartRelationDiag pr₁ pr₂ hsq` with `pr₂` is the identity. -/
@[reassoc]
theorem chartRelationDiag_comp_snd : chartRelationDiag pr₁ pr₂ hsq ≫ pr₂ = 𝟙 V₂ :=
  chartRelationLift_comp_snd pr₁ pr₂ hsq _ _

/-- **The swap `V' ⟶ V'` of a relation of étale charts**, interchanging the two projections. -/
def chartRelationSwap : V' ⟶ V' := chartRelationLift pr₁ pr₂ hsq pr₂ pr₁

/-- The composite of the swap `chartRelationSwap pr₁ pr₂ hsq` with `pr₁` is `pr₂`. -/
@[reassoc]
theorem chartRelationSwap_comp_fst : chartRelationSwap pr₁ pr₂ hsq ≫ pr₁ = pr₂ :=
  chartRelationLift_comp_fst pr₁ pr₂ hsq _ _

/-- The composite of the swap `chartRelationSwap pr₁ pr₂ hsq` with `pr₂` is `pr₁`. -/
@[reassoc]
theorem chartRelationSwap_comp_snd : chartRelationSwap pr₁ pr₂ hsq ≫ pr₂ = pr₁ :=
  chartRelationLift_comp_snd pr₁ pr₂ hsq _ _

/-- **The composition `V' ×_{V₂} V' ⟶ V'` of a relation of étale charts**: the outer pair of the
three points.  The triple fibre product is the one the small étale site itself provides. -/
def chartRelationOuter : Limits.pullback pr₁ pr₂ ⟶ V' :=
  chartRelationLift pr₁ pr₂ hsq (Limits.pullback.snd pr₁ pr₂ ≫ pr₁)
    (Limits.pullback.fst pr₁ pr₂ ≫ pr₂)

/-- The composite of `chartRelationOuter pr₁ pr₂ hsq` with `pr₁` is the second projection of
`V' ×_{V₂} V'` followed by `pr₁`. -/
@[reassoc]
theorem chartRelationOuter_comp_fst :
    chartRelationOuter pr₁ pr₂ hsq ≫ pr₁ = Limits.pullback.snd pr₁ pr₂ ≫ pr₁ :=
  chartRelationLift_comp_fst pr₁ pr₂ hsq _ _

/-- The composite of `chartRelationOuter pr₁ pr₂ hsq` with `pr₂` is the first projection of
`V' ×_{V₂} V'` followed by `pr₂`. -/
@[reassoc]
theorem chartRelationOuter_comp_snd :
    chartRelationOuter pr₁ pr₂ hsq ≫ pr₂ = Limits.pullback.fst pr₁ pr₂ ≫ pr₂ :=
  chartRelationLift_comp_snd pr₁ pr₂ hsq _ _

end ChartRelation

/-! ### The relative spectra over the charts, read in the site -/

section RelativeSpec

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent)

/-- **The structure morphism of the relative spectrum over an étale chart, as a morphism of the
big fppf site over `S`.**  Underlying it is
`AlgebraicGeometry.Space.chartRelativeSpecToChart`. -/
def chartRelativeSpecSiteToChart (V : SmallEtale B S hS X.1)
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    chartRelativeSpecSite B S hS X A hA V hV ⟶ (SmallEtale.toOver B S hS X.1).obj V :=
  BigFppfOver.siteMapOver B S hS ((SmallEtale.toOver B S hS X.1).obj V) hV
    (chartRelativeSpecToChart B S hS X A hA V)

/-- The underlying morphism of schemes of `chartRelativeSpecSiteToChart` is
`chartRelativeSpecToChart`. -/
@[simp]
theorem toScheme_map_chartRelativeSpecSiteToChart (V : SmallEtale B S hS X.1)
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    (BigFppfOver.toScheme B S hS).map (chartRelativeSpecSiteToChart B S hS X A hA V hV) =
      chartRelativeSpecToChart B S hS X A hA V :=
  rfl

/-- **The cartesian square of `AlgebraicGeometry.Space.isPullback_chartRelativeSpecChartMap`,
read in the big fppf category over `S`.**  The forgetful functor to schemes is faithful and
reflects fibre products, so the square of site objects is cartesian because the square of
underlying schemes is. -/
theorem isPullback_chartRelativeSpecSiteMap {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV : B.Contains (chartRelativeSpec B S hS X A hA V)) :
    IsPullback (chartRelativeSpecSiteMap B S hS X A hA h hV' hV)
      (chartRelativeSpecSiteToChart B S hS X A hA V' hV')
      (chartRelativeSpecSiteToChart B S hS X A hA V hV)
      ((SmallEtale.toOver B S hS X.1).map h) :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_chartRelativeSpecChartMap B S hS X A hA h)

end RelativeSpec

/-! ### The equivalence relation -/

section Relation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent) {V' V₂ : SmallEtale B S hS X.1} (pr₁ pr₂ : V' ⟶ V₂)
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₁))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map pr₂)) V₂.obj.hom V₂.obj.hom)
    (hV' : B.Contains (chartRelativeSpec B S hS X A hA V'))
    (hV₂ : B.Contains (chartRelativeSpec B S hS X A hA V₂))
    (hV'' : B.Contains (chartRelativeSpec B S hS X A hA (Limits.pullback pr₁ pr₂)))

include hsq in
/-- **The two induced morphisms of relative spectra are jointly monic.**  A morphism into the
relative spectrum over `V'` is determined by its composites with the two projections: the square
over the second projection is cartesian, and the component in `V'` is determined because `V'` is
`V₂ ×_X V₂`. -/
theorem jointlyMono₂_chartRelativeSpecSiteMap :
    JointlyMono₂ (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
      (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)) := by
  have hA₁ := (isPullback_chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂).map yoneda
  have hA₂ := (isPullback_chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂).map yoneda
  refine ⟨fun Z a b h₁ h₂ => hA₂.hom_ext h₂ (hsq.hom_ext ?_ ?_)⟩ <;>
    simp only [Category.assoc, ← hA₁.w, ← hA₂.w, reassoc_of% h₁, reassoc_of% h₂]

include hA in
/-- The composition identity of the triple fibre product of charts, read on the relative
spectra. -/
theorem chartRelativeSpecSiteMap_pullbackSnd_comp :
    chartRelativeSpecSiteMap B S hS X A hA (Limits.pullback.snd pr₁ pr₂) hV'' hV' ≫
        chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂ =
      chartRelativeSpecSiteMap B S hS X A hA (Limits.pullback.fst pr₁ pr₂) hV'' hV' ≫
        chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂ := by
  rw [← chartRelativeSpecSiteMap_comp, ← chartRelativeSpecSiteMap_comp,
    Limits.pullback.condition]

/-- **The relative spectrum over the triple fibre product of charts is the fibre product of two
copies of the relative spectrum over `V'`.**  This is the limiting cone which the transitivity of
the relation needs: the cartesian square over the second projection of `V' ×_{V₂} V'`, pasted
with the cartesian square of the triple fibre product of charts. -/
theorem isPullback_chartRelativeSpecSiteMap₂ :
    IsPullback
      (chartRelativeSpecSiteMap B S hS X A hA (Limits.pullback.snd pr₁ pr₂) hV'' hV')
      (chartRelativeSpecSiteMap B S hS X A hA (Limits.pullback.fst pr₁ pr₂) hV'' hV')
      (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
      (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂) := by
  have h₁ := isPullback_chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂
  have h₂ := isPullback_chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂
  have hfst := isPullback_chartRelativeSpecSiteMap B S hS X A hA
    (Limits.pullback.fst pr₁ pr₂) hV'' hV'
  have hsnd := isPullback_chartRelativeSpecSiteMap B S hS X A hA
    (Limits.pullback.snd pr₁ pr₂) hV'' hV'
  have hbase : IsPullback
      ((SmallEtale.toOver B S hS X.1).map (Limits.pullback.snd pr₁ pr₂))
      ((SmallEtale.toOver B S hS X.1).map (Limits.pullback.fst pr₁ pr₂))
      ((SmallEtale.toOver B S hS X.1).map pr₂)
      ((SmallEtale.toOver B S hS X.1).map pr₁) :=
    (IsPullback.of_hasPullback pr₁ pr₂).flip.map (SmallEtale.toOver B S hS X.1)
  have houter := hsnd.paste_vert hbase
  rw [← hfst.w, ← h₂.w] at houter
  exact houter.of_bot
    (chartRelativeSpecSiteMap_pullbackSnd_comp B S hS X A hA pr₁ pr₂ hV' hV₂ hV'') h₁

include hsq in
/-- **The two morphisms of relative spectra attached to a relation of étale charts form an
internal equivalence relation of presheaves.**  All four conditions are instances of the
functoriality `AlgebraicGeometry.Space.chartRelativeSpecSiteMap_comp` of the relative spectrum in
the chart, applied to the diagonal, the swap and the composition of the relation of charts,
together with the joint monicity and the transitivity cone which the cartesian squares supply. -/
def equivalenceRelation_chartRelativeSpecSiteMap :
    EquivalenceRelation (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
      (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)) where
  __ := jointlyMono₂_chartRelativeSpecSiteMap B S hS X A hA pr₁ pr₂ hsq hV' hV₂
  r := yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
    (chartRelationDiag pr₁ pr₂ hsq) hV₂ hV')
  reflexivity₁ := by
    rw [← CategoryTheory.Functor.map_comp, ← chartRelativeSpecSiteMap_comp,
      chartRelationDiag_comp_fst, chartRelativeSpecSiteMap_id,
      CategoryTheory.Functor.map_id]
  reflexivity₂ := by
    rw [← CategoryTheory.Functor.map_comp, ← chartRelativeSpecSiteMap_comp,
      chartRelationDiag_comp_snd, chartRelativeSpecSiteMap_id,
      CategoryTheory.Functor.map_id]
  s := yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
    (chartRelationSwap pr₁ pr₂ hsq) hV' hV')
  symmetry₁ := by
    rw [← CategoryTheory.Functor.map_comp, ← chartRelativeSpecSiteMap_comp,
      chartRelationSwap_comp_fst]
  symmetry₂ := by
    rw [← CategoryTheory.Functor.map_comp, ← chartRelativeSpecSiteMap_comp,
      chartRelationSwap_comp_snd]
  c := ((isPullback_chartRelativeSpecSiteMap₂ B S hS X A hA pr₁ pr₂ hV' hV₂
    hV'').map yoneda).cone
  isLimit := ((isPullback_chartRelativeSpecSiteMap₂ B S hS X A hA pr₁ pr₂ hV' hV₂
    hV'').map yoneda).isLimit
  t := yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
    (chartRelationOuter pr₁ pr₂ hsq) hV'' hV')
  transitivity₁ := by
    change yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
          (chartRelationOuter pr₁ pr₂ hsq) hV'' hV') ≫
        yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂) =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
          (Limits.pullback.snd pr₁ pr₂) hV'' hV') ≫
        yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← chartRelativeSpecSiteMap_comp, ← chartRelativeSpecSiteMap_comp,
      chartRelationOuter_comp_fst]
  transitivity₂ := by
    change yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
          (chartRelationOuter pr₁ pr₂ hsq) hV'' hV') ≫
        yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂) =
      yoneda.map (chartRelativeSpecSiteMap B S hS X A hA
          (Limits.pullback.fst pr₁ pr₂) hV'' hV') ≫
        yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      ← chartRelativeSpecSiteMap_comp, ← chartRelativeSpecSiteMap_comp,
      chartRelationOuter_comp_snd]

include hsq hV'' in
/-- **The equivalence-relation condition on the pair of relative spectra.**  This is the
hypothesis `hrel` of
`AlgebraicGeometry.Space.isEtaleEquivalenceRelation_chartRelativeSpecSiteMap`, discharged. -/
theorem isEquivalenceRelation_chartRelativeSpecSiteMap :
    IsEquivalenceRelation (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂))
      (yoneda.map (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)) :=
  (equivalenceRelation_chartRelativeSpecSiteMap B S hS X A hA pr₁ pr₂ hsq hV' hV₂
    hV'').isEquivalenceRelation

include hsq hV'' in
/-- **The pair of morphisms of relative spectra attached to a relation of étale charts is an
étale equivalence relation over `S`**, in the sense of Tag 02WS.

Both étaleness conditions are
`AlgebraicGeometry.Space.etale_chartRelativeSpecChartMap` and need no hypothesis; the
equivalence-relation condition is
`AlgebraicGeometry.Space.isEquivalenceRelation_chartRelativeSpecSiteMap`.  Nothing is assumed
beyond quasi-coherence of `A`, the hypothesis that `V'` is `V₂ ×_X V₂`, and the three
containment conditions asking that the three relative spectra be objects of the site.

Applied to the two projections of `R = U ×_X U` for a surjective étale chart `U ⟶ X` this is the
étale equivalence relation whose quotient, by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`, is the algebraic space
`\underline{Spec}_X(A)` of Stacks 081V — and, for `A` the integral closure of `𝒪_X` in
`f_* 𝒪_Y`, the normalization of `X` in `Y` of Definition 0822. -/
theorem isEtaleEquivalenceRelation_chartRelativeSpecSiteMap_of_isPullback :
    IsEtaleEquivalenceRelation (relation B S hS
      (chartRelativeSpecSiteMap B S hS X A hA pr₂ hV' hV₂)
      (chartRelativeSpecSiteMap B S hS X A hA pr₁ hV' hV₂)) :=
  isEtaleEquivalenceRelation_chartRelativeSpecSiteMap B S hS X A hA pr₁ pr₂ hV' hV₂
    (isEquivalenceRelation_chartRelativeSpecSiteMap B S hS X A hA pr₁ pr₂ hsq hV' hV₂ hV'')

end Relation

end AlgebraicGeometry.Space

end
