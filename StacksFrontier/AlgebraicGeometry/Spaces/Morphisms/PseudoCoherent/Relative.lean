module

public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DirectSums
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFlatBase
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksCore.Tactic.StacksAttribute

/-!
# Relative pseudo-coherence on the étale charts of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` locally of finite type, let
`m` be an integer and let `E` be an object of `D_QCoh(𝒪_X)`.  Relative `m`-pseudo-coherence of
`E` over `Y` may be tested on every commuting square of étale scheme charts of `f`, on one such
square whose chart of `X` is surjective, or — on affine charts — on the complexes of derived
sections.

## Main definitions

* `AlgebraicGeometry.Space.ZariskiComparisonData`: the second sentence of Remark 0CSW at one
  object of the site — the comparison of `D_QCoh` of a representable algebraic space with
  `D_QCoh` of a representing scheme.
* `AlgebraicGeometry.Space.chartComplex`: the complex `E|_U` of Remark 0CSW on an étale scheme
  chart `U ⟶ X`, built from such a comparison datum.
* `AlgebraicGeometry.Scheme.Hom.RelativePseudoCoherenceFppfDescent`: the descent implication of
  Stacks 0CSN as a proposition.
* `AlgebraicGeometry.Space.RelativePseudoCoherenceInput`: the carried inputs of Stacks 0CSX.
* `AlgebraicGeometry.Space.IsPseudoCoherentFromOnChart`: relative `m`-pseudo-coherence of `E|_U`
  over `V` on a commuting square of étale scheme charts.

## Main results

* `AlgebraicGeometry.Space.relativePseudoCoherence_chart_tfae`: **Stacks 0CSX**, the three
  equivalent tests, over a `RelativePseudoCoherenceInput`.

## What is carried, and why

`AlgebraicGeometry.Space.RelativePseudoCoherenceInput` bundles the inputs of the source's proof
of Stacks 0CSX which this repository does not prove.  Nothing else is assumed, and the
equivalence itself is proved.

* `comparison`: for every object `T` of the site, an
  `AlgebraicGeometry.Space.ZariskiComparisonData`, that is, an equivalence between `D_QCoh` of
  the algebraic space represented by `T` and `D_QCoh` of the representing scheme.  This is the
  **second sentence of Remark 0CSW**: an object of `D_QCoh(𝒪_X)` on a representable algebraic
  space `X` is the pullback of a unique object of `D_QCoh(𝒪_{X_0})` on a representing scheme
  `X_0`, by Stacks 071Q.  The library carries `@[stacks 0CSW]` only on the *first* sentence,
  `AlgebraicGeometry.Space.locallyOfFiniteType_of_represents`, which says that a scheme morphism
  representing a morphism locally of finite type is locally of finite type; the comparison of the
  two derived categories is absent from the library, and it is what gives `E|_U` its meaning.
* `chartComplexPullback`: that `E|_U` is compatible with passing to a finer chart, that is, that
  `E|_{U'}` is the derived pullback of `E|_U` along `U' ⟶ U` for a morphism of the site over `X`.
  This is the part of Remark 0CSW's uniqueness assertion that the proof of Stacks 0CSX uses, in
  both the step from one surjective chart to all charts and the step from affine charts to all
  charts; it does not follow from the comparison datum alone, which says nothing about how the
  comparisons at two different objects of the site are related.
* `fppfDescent`: `AlgebraicGeometry.Scheme.Hom.RelativePseudoCoherenceFppfDescent`, the
  **descent implication of Stacks 0CSN**.  The library has only the forward implication,
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage`,
  whose own file records that the converse is not proved; both steps of the proof below that pass
  from a covering of a chart to the chart itself are that converse.
* `torIndependentBaseChange`: `AlgebraicGeometry.DerivedBaseChangeIsoOfTorIndependent`, i.e.
  **Stacks 0E23**, which is the one hypothesis the library's Stacks 09US
  (`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback`) carries.  It is
  carried through here rather than Stacks 09US being carried a second time, and
  `AlgebraicGeometry.Space.RelativePseudoCoherenceInput.pullbackAlongPseudoCoherent` recovers
  Stacks 09US from it in the shape the library's Stacks 0CSN asks for.

## Implementation notes

The chart condition is not a property of the morphism `U_0 ⟶ V_0` of schemes alone — it depends
on `E` — so `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`, the machine
that upgrades one surjective square to every square for a
`CategoryTheory.MorphismProperty Scheme`, does not apply, and the equivalence of the first two
conditions is proved by hand, exactly as the source does.

Everything is read at the module universe `u` of the structure rings, where
`AlgebraicGeometry.Space.SmallEtale` supplies as instances the two sheafification hypotheses that
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` takes; so no sheafification binders occur.

The comparison is recorded as an equivalence of the two *quasi-coherent* derived categories and
not, as the source's Stacks 071Q would also allow, as the derived functor of restriction of
`𝒪`-modules to Zariski opens between the two ambient derived categories of all `𝒪`-modules.  The
reason is that the ambient derived category of the Zariski `𝒪`-modules of a scheme cannot be
named here: the relevant `CategoryTheory.HasDerivedCategory` instance is a file-local instance of
the modules of the files that state the scheme theory, and outside them
`DerivedCategory (Scheme.Modules X)` elaborates at a different universe than the one
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom` is stated at.  Every complex here is
therefore the underlying object of an object of a quasi-coherent derived category, which is also
why the quasi-coherence of `E|_U` that Stacks 09VF and Stacks 0CSN need is immediate.

The derived pullback along an étale chart is `AlgebraicGeometry.Space.etaleModulePullback`
carried into derived categories rather than a total left derived functor: an étale pullback of
`𝒪`-modules is restriction of sections along `AlgebraicGeometry.Space.smallEtalePostcomp` and so
is exact.  That it preserves quasi-coherent cohomology is Stacks 08F4 for étale morphisms of
algebraic spaces, `AlgebraicGeometry.Space.derivedQuasicoherent_etaleModulePullback`, so nothing
about `E|_U` beyond the comparison has to be carried.

Each implication of the equivalence is a separate declaration; elaborating them inside one
`List.TFAE` proof exceeds the default heartbeat budget.

## References

* [Stacks Project, Tag 0CSX](https://stacks.math.columbia.edu/tag/0CSX)
* [Stacks Project, Tag 0CSW](https://stacks.math.columbia.edu/tag/0CSW)
* [Stacks Project, Tag 0CSN](https://stacks.math.columbia.edu/tag/0CSN)
* [Stacks Project, Tag 0CSP](https://stacks.math.columbia.edu/tag/0CSP)
* [Stacks Project, Tag 09US](https://stacks.math.columbia.edu/tag/09US)
* [Stacks Project, Tag 09VF](https://stacks.math.columbia.edu/tag/09VF)
* [Stacks Project, Tag 0695](https://stacks.math.columbia.edu/tag/0695)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The descent implication of Stacks 0CSN -/

/-- **The descent implication of Stacks 0CSN** as a proposition: let `f : X ⟶ S` be locally of
finite type, let `{g i : Y i ⟶ X}` be an fppf covering of schemes and let `E` be an object of
`D_QCoh(𝒪_X)`.  If every derived pullback `L(g i)^*E` is `m`-pseudo-coherent relative to `S`,
then so is `E`.

The forward implication is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage`; this
is the half that the library does not prove.  Quasi-coherence of the cohomology sheaves of `E`,
which the source's proof uses and the forward implication does not, is built into the hypothesis
by taking `E` in `D_QCoh(𝒪_X)`.  Local finite type of a composite `g i ≫ f` is quantified over
rather than derived from the covering, the predicate not depending on which derivation is
used. -/
abbrev Scheme.Hom.RelativePseudoCoherenceFppfDescent : Prop :=
  ∀ {X S : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ X) (f : X ⟶ S)
      [LocallyOfFiniteType f], Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage X →
    ∀ (E : QuasicoherentDerivedCategory X) (m : ℤ),
      (∀ (i : ι) (_ : LocallyOfFiniteType (g i ≫ f)),
        (g i ≫ f).IsPseudoCoherentFrom
          ((derivedPullback (g i).toLRSHom.toShHom).obj E.obj) m) →
      f.IsPseudoCoherentFrom E.obj m

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étale scheme charts -/

/-- An étale scheme chart is an étale morphism of presheaves in the sense of Stacks 03FR: the
represented étale morphisms are stable under composition. -/
theorem isEtale_of_isEtaleSchemeChart {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ F}
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a) :
    IsEtale B S hS a :=
  have := isMultiplicative_presheaf_etale B S hS
  fun _ φ hφ ↦ MorphismProperty.comp_mem _ φ a hφ ha

/-- The chart `a : yoneda.obj U ⟶ X` read as a morphism of algebraic spaces from the algebraic
space represented by `U`. -/
abbrev chartArrow {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) :
    (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩ :=
  ObjectProperty.homMk a

/-! ### The comparison of Remark 0CSW -/

/-- **The second sentence of Remark 0CSW** at one object `T` of the site: the comparison of
Stacks 071Q between the derived category of complexes with quasi-coherent cohomology on the
algebraic space represented by `T` and the one on the representing scheme.

This is what lets an object of `D_QCoh` of a representable algebraic space be read as a complex
on a scheme, and so what makes the complex `E|_U` of the source's notation meaningful. -/
structure ZariskiComparisonData (T : BigFppfOver B S hS) where
  /-- The equivalence of Stacks 071Q between `D_QCoh` of the represented algebraic space and
  `D_QCoh` of the representing scheme. -/
  equivalence :
    QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T) ≌
      AlgebraicGeometry.QuasicoherentDerivedCategory ((BigFppfOver.toScheme B S hS).obj T)

/-! ### The complex `E|_U` on an étale scheme chart -/

/-- The derived pullback of `E` along an étale scheme chart `a : yoneda.obj U ⟶ X`, as an object
of `D_QCoh` of the algebraic space represented by `U`.

Along an étale morphism of algebraic spaces the derived pullback is exact, so it is the functor
induced by `AlgebraicGeometry.Space.etaleModulePullback`, and it preserves quasi-coherence of the
cohomology sheaves by Stacks 08F4. -/
def chartDerivedPullback {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) {U : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X} (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a) :
    QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) :=
  (quasicoherentDerivedEtalePullback B S hS (chartArrow B S hS hX a)
    (isEtale_of_isEtaleSchemeChart B S hS ha)).obj E

/-- **The complex `E|_U` of Remark 0CSW.**  For an étale scheme chart `a : yoneda.obj U ⟶ X` of
an algebraic space `X` and an object `E` of `D_QCoh(𝒪_X)`, this is the object of `D_QCoh(𝒪_{U_0})`
attached by the comparison of Remark 0CSW to the derived pullback of `E` to the algebraic space
represented by `U`, where `U_0` is the representing scheme. -/
def chartComplex {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) {U : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X} (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (d : ZariskiComparisonData B S hS U) :
    AlgebraicGeometry.QuasicoherentDerivedCategory ((BigFppfOver.toScheme B S hS).obj U) :=
  d.equivalence.functor.obj (chartDerivedPullback B S hS hX E ha)

/-- The complex `E|_U` depends on the chart only through the morphism, not through the proof that
it is an étale chart. -/
theorem chartComplex_congr {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    {U : BigFppfOver B S hS} {a a' : yoneda.obj U ⟶ X} (haa' : a = a')
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (ha' : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a')
    (d : ZariskiComparisonData B S hS U) :
    (chartComplex B S hS hX E ha d).obj = (chartComplex B S hS hX E ha' d).obj := by
  subst haa'
  rfl

/-! ### The carried inputs -/

/-- **The inputs of Stacks 0CSX which this repository does not prove.**

See the module docstring for what each field is and why it is carried: `comparison` is the second
sentence of Remark 0CSW, `chartComplexPullback` its compatibility with passing to a finer chart,
`fppfDescent` the descent implication of Stacks 0CSN, and `torIndependentBaseChange` the
Stacks 0E23 input that the library's Stacks 09US carries. -/
structure RelativePseudoCoherenceInput where
  /-- The comparison of Remark 0CSW at every object of the site. -/
  comparison : ∀ T : BigFppfOver B S hS, ZariskiComparisonData B S hS T
  /-- The complex `E|_U` of Remark 0CSW is compatible with passing to a finer chart: for a
  morphism `g : U ⟶ V` of the site and an étale chart `a` of `V`, the complex attached to the
  chart `yoneda.map g ≫ a` is the derived pullback along `g` of the one attached to `a`. -/
  chartComplexPullback : ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    {U V : BigFppfOver B S hS} (g : U ⟶ V) {a : yoneda.obj V ⟶ X}
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hga : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map g ≫ a)),
    Nonempty ((chartComplex B S hS hX E hga (comparison U)).obj ≅
      (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj
        (chartComplex B S hS hX E ha (comparison V)).obj)
  /-- The descent implication of Stacks 0CSN. -/
  fppfDescent : Scheme.Hom.RelativePseudoCoherenceFppfDescent.{u}
  /-- Stacks 0E23, the hypothesis the library's Stacks 09US carries. -/
  torIndependentBaseChange : DerivedBaseChangeIsoOfTorIndependent.{u}

namespace RelativePseudoCoherenceInput

variable {B S hS}

/-- **Stacks 09US** recovered from the carried Stacks 0E23: along a pseudo-coherent morphism of
schemes, relative `m`-pseudo-coherence is preserved by derived pullback.

This is `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback`, now
unconditional, packaged in the shape the library's Stacks 0CSN asks for. -/
theorem pullbackAlongPseudoCoherent (_h : RelativePseudoCoherenceInput B S hS) :
    Scheme.Hom.RelativePseudoCoherencePullbackAlongPseudoCoherent.{u} := by
  intro _ _ _ p q _ _ E m hE
  exact Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback p q E m hE

/-- The complex `E|_U` of Remark 0CSW, read through the carried comparison. -/
abbrev chartComplex (h : RelativePseudoCoherenceInput B S hS)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) {U : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X} (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a) :
    AlgebraicGeometry.QuasicoherentDerivedCategory ((BigFppfOver.toScheme B S hS).obj U) :=
  Space.chartComplex B S hS hX E ha (h.comparison U)

end RelativePseudoCoherenceInput

/-! ### The chart condition -/

/-- The condition of Stacks 0CSX on one commuting square of étale scheme charts: the complex
`E|_U` is `m`-pseudo-coherent relative to the chart `V` of the target. -/
abbrev IsPseudoCoherentFromOnChart (h : RelativePseudoCoherenceInput B S hS)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f) : Prop :=
  haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
  ((BigFppfOver.toScheme B S hS).map g).IsPseudoCoherentFrom (h.chartComplex hX E ha).obj m

/-! ### Open subobjects of an object of the site -/

/-- An open subscheme of the scheme underlying an object of the site, as an object of the site
over the same base. -/
def openChartObject (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Over.mk ((show B.obj (Scheme.size_lt_of_isOpenImmersion W.ι U.left.property) ⟶ U.left from
    ⟨W.ι⟩) ≫ U.hom)

/-- The open immersion of an open subscheme of an object of the site into that object. -/
def openChartMap (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) : openChartObject B S hS U W ⟶ U :=
  Over.homMk ⟨W.ι⟩

/-- The inclusion of an open subscheme of an object of the site is étale, an open immersion of
schemes being étale. -/
theorem etale_openChartMap (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (openChartMap B S hS U W)) := by
  change AlgebraicGeometry.Etale W.ι
  infer_instance

/-! ### The implications of Stacks 0CSX -/

section Implications

variable {B S hS} (h : RelativePseudoCoherenceInput B S hS)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
  (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ)

include hY in
/-- **Stacks 0CSX, (1) ⟹ (2).**  An algebraic space has a surjective étale chart, and such a
chart of the target lifts to one of the source by Stacks 02X1, so a square as in (2) exists. -/
theorem exists_surjectiveChart_of_forall_chart
    (hall : ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (g : U ⟶ V) (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
      (hc : yoneda.map g ≫ b = a ≫ f),
      IsPseudoCoherentFromOnChart B S hS h hX f hf E m U V a b g ha hb hc) :
    ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
      (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b),
      IsSurjective B S hS a ∧ ∃ hc : yoneda.map g ≫ b = a ≫ f,
        IsPseudoCoherentFromOnChart B S hS h hX f hf E m U V a b g ha hb hc := by
  obtain ⟨V, b, hbSurjective, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, g, hc, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurjective hbEtale
  exact ⟨U, V, a, b, g, haEtale, hbEtale,
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurjective, hc.symm,
    hall U V a b g haEtale hbEtale hc.symm⟩

/-- **Stacks 0CSX, (1) ⟹ (3).**  On a square of affine charts the condition on `E|_U` is the
condition on the complex of derived sections `RΓ(U, E)`, by Stacks 09VF. -/
theorem derivedSections_of_forall_chart
    (hall : ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (g : U ⟶ V) (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
      (hc : yoneda.map g ≫ b = a ≫ f),
      IsPseudoCoherentFromOnChart B S hS h hX f hf E m U V a b g ha hb hc)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
    haveI := hU
    haveI := hV
    ((BigFppfOver.toScheme B S hS).map g).DerivedSectionsPseudoCoherentOn'
      (h.chartComplex hX E ha).obj m (isAffineOpen_top _) (isAffineOpen_top _) (by simp) := by
  have := hU
  have := hV
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
  have hiff := (derivedSectionsPseudoCoherentComparison' ((BigFppfOver.toScheme B S hS).map g)
    (h.chartComplex hX E ha).obj (h.chartComplex hX E ha).property m).out 1 3
  exact hiff.mp (hall U V a b g ha hb hc) ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) (by simp)

/-- **Stacks 0CSX, (2) ⟹ (1).**  Let the condition hold on one square whose chart `a` of the
source is surjective, and let a second square be given.  The fibre product `U'' = U ×_X U'` is
surjective étale over `U'` and maps to `V'' = V' ×_Y V`, which is étale over `V'`; so by the
carried descent half of Stacks 0CSN and by Stacks 0CSP it suffices to treat `E|_{U''}` over `V`,
and that is Stacks 09US together with the pseudo-coherence of an étale morphism, Stacks 0695. -/
theorem forall_chart_of_surjectiveChart
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hsurj : IsSurjective B S hS a) (hc : yoneda.map g ≫ b = a ≫ f)
    (hcond : IsPseudoCoherentFromOnChart B S hS h hX f hf E m U V a b g ha hb hc)
    (U' V' : BigFppfOver B S hS) (a' : yoneda.obj U' ⟶ X) (b' : yoneda.obj V' ⟶ Y) (g' : U' ⟶ V')
    (ha' : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a')
    (hb' : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b')
    (hc' : yoneda.map g' ≫ b' = a' ≫ f) :
    IsPseudoCoherentFromOnChart B S hS h hX f hf E m U' V' a' b' g' ha' hb' hc' := by
  let T := BigFppfOver.toScheme B S hS
  let W := ha.rep.pullback a'
  let left : W ⟶ U := ha.rep.fst' a'
  let right : W ⟶ U' := ha.rep.snd a'
  let tleft : hb.rep.pullback b' ⟶ V := hb.rep.fst' b'
  let tright : hb.rep.pullback b' ⟶ V' := hb.rep.snd b'
  have sq : IsPullback (yoneda.map left) (yoneda.map right) a a' := ha.rep.isPullback' a'
  have tsq : IsPullback (yoneda.map tleft) (yoneda.map tright) b b' := hb.rep.isPullback' b'
  have hleft : AlgebraicGeometry.Etale (T.map left) :=
    ha'.property a (yoneda.map right) left sq.flip
  have hright : AlgebraicGeometry.Etale (T.map right) := ha.property_snd a'
  have htleft : AlgebraicGeometry.Etale (T.map tleft) :=
    hb'.property b (yoneda.map tright) tleft tsq.flip
  have htright : AlgebraicGeometry.Etale (T.map tright) := hb.property_snd b'
  have hrightSurjective : AlgebraicGeometry.Surjective (T.map right) :=
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mpr hsurj).property
      a' (yoneda.map left) right sq
  have := hf U V a b g ha hb hc
  have := hf U' V' a' b' g' ha' hb' hc'
  have hcomm : yoneda.map (left ≫ g) ≫ b = yoneda.map (right ≫ g') ≫ b' := by
    simp only [Functor.map_comp, Category.assoc, hc, hc']
    rw [← Category.assoc, ← Category.assoc, sq.w]
  let lift := hb.rep.lift' (left ≫ g) (right ≫ g') hcomm
  have hliftLeft : lift ≫ tleft = left ≫ g := hb.rep.lift'_fst _ _ _
  have hliftRight : lift ≫ tright = right ≫ g' := hb.rep.lift'_snd _ _ _
  have hleftEq : T.map lift ≫ T.map tleft = T.map left ≫ T.map g := by
    rw [← T.map_comp, hliftLeft, T.map_comp]
  have hliftType : LocallyOfFiniteType (T.map lift) := by
    have : LocallyOfFiniteType (T.map lift ≫ T.map tleft) := by
      rw [hleftEq]
      infer_instance
    exact locallyOfFiniteType_of_comp (T.map lift) (T.map tleft)
  have hga : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map left ≫ a) :=
    etale_comp_of_scheme B S hS left a hleft ha
  have hga' : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map right ≫ a') :=
    etale_comp_of_scheme B S hS right a' hright ha'
  have hpulled : (T.map left ≫ T.map g).IsPseudoCoherentFrom
      ((derivedPullback (T.map left).toLRSHom.toShHom).obj (h.chartComplex hX E ha).obj) m :=
    Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback (T.map left) (T.map g) _ m hcond
  have hrightEq : T.map lift ≫ T.map tright = T.map right ≫ T.map g' := by
    rw [← T.map_comp, hliftRight, T.map_comp]
  have hoverLeft : (T.map lift ≫ T.map tleft).IsPseudoCoherentFrom
      ((derivedPullback (T.map left).toLRSHom.toShHom).obj (h.chartComplex hX E ha).obj) m :=
    (Scheme.Hom.isPseudoCoherentFrom_congr_hom hleftEq.symm _ m).mp hpulled
  have hoverRight := (Scheme.Hom.isPseudoCoherentFrom_comp_iff_of_flat (T.map lift)
      (T.map tright) _ m).mpr
    ((Scheme.Hom.isPseudoCoherentFrom_comp_iff_of_flat (T.map lift) (T.map tleft) _ m).mp
      hoverLeft)
  obtain ⟨isoLeft⟩ := h.chartComplexPullback hX E left ha hga
  obtain ⟨isoRight⟩ := h.chartComplexPullback hX E right ha' hga'
  let chartIso :
      (derivedPullback (T.map left).toLRSHom.toShHom).obj (h.chartComplex hX E ha).obj ≅
        (derivedPullback (T.map right).toLRSHom.toShHom).obj (h.chartComplex hX E ha').obj :=
    isoLeft.symm ≪≫
      eqToIso (chartComplex_congr B S hS hX E sq.w hga hga' (h.comparison W)) ≪≫ isoRight
  have hoverSource : (T.map right ≫ T.map g').IsPseudoCoherentFrom
      ((derivedPullback (T.map right).toLRSHom.toShHom).obj (h.chartComplex hX E ha').obj) m :=
    Scheme.Hom.IsPseudoCoherentFrom.of_iso _
      ((Scheme.Hom.isPseudoCoherentFrom_congr_hom hrightEq _ m).mp hoverRight) chartIso
  have hcover : Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ T.obj W)
      (fun _ ↦ T.map right) ∈ Scheme.fppfPrecoverage (T.obj U') :=
    (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨PUnit.unit, hrightSurjective.surj x⟩, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩
  exact h.fppfDescent (fun _ : PUnit.{u + 1} ↦ T.obj W) (fun _ ↦ T.map right) (T.map g')
    hcover (h.chartComplex hX E ha') m fun _ _ ↦ hoverSource

/-- **Stacks 0CSX, (3) ⟹ (1).**  A square of étale charts is covered by squares of affine
charts: choose an affine open covering of `V` and affine open coverings of the inverse images of
its members in `U`.  On each the condition is the one of (3), by Stacks 09VF and Stacks 0CSP, and
the carried descent half of Stacks 0CSN assembles them. -/
theorem forall_chart_of_derivedSections
    (hall : ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y)
      (g : U ⟶ V) (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
      (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
      (hc : yoneda.map g ≫ b = a ≫ f)
      (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)),
      haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hf U V a b g ha hb hc
      haveI := hU
      haveI := hV
      ((BigFppfOver.toScheme B S hS).map g).DerivedSectionsPseudoCoherentOn'
        (h.chartComplex hX E ha).obj m (isAffineOpen_top _) (isAffineOpen_top _) (by simp))
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hc : yoneda.map g ≫ b = a ≫ f) :
    IsPseudoCoherentFromOnChart B S hS h hX f hf E m U V a b g ha hb hc := by
  let T := BigFppfOver.toScheme B S hS
  have := hf U V a b g ha hb hc
  let idx := {p : (T.obj U).affineOpens × (T.obj V).affineOpens // p.1.1 ≤ T.map g ⁻¹ᵁ p.2.1}
  let srcs : idx → Scheme.{u} := fun i ↦ (i.1.1.1 : Scheme.{u})
  let arrows : ∀ i : idx, srcs i ⟶ T.obj U := fun i ↦ i.1.1.1.ι
  have hcover : Presieve.ofArrows srcs arrows ∈ Scheme.fppfPrecoverage (T.obj U) := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨?_, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩
    intro x
    obtain ⟨Vx, hVxAffine, hxVx, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := T.obj V) (U := ⊤) (x := (T.map g).base x) (by trivial)
    obtain ⟨Ux, hUxAffine, hxUx, hUxV⟩ := exists_isAffineOpen_mem_and_subset
      (X := T.obj U) (U := T.map g ⁻¹ᵁ Vx) (x := x) hxVx
    exact ⟨⟨(⟨Ux, hUxAffine⟩, ⟨Vx, hVxAffine⟩), hUxV⟩, ⟨x, hxUx⟩, rfl⟩
  refine h.fppfDescent srcs arrows (T.map g) hcover (h.chartComplex hX E ha) m ?_
  intro i hiType
  have := hiType
  let sIncl := openChartMap B S hS U i.1.1.1
  let tIncl := openChartMap B S hS V i.1.2.1
  have hsEtale : AlgebraicGeometry.Etale (T.map sIncl) := etale_openChartMap B S hS U i.1.1.1
  have htEtale : AlgebraicGeometry.Etale (T.map tIncl) := etale_openChartMap B S hS V i.1.2.1
  have : IsAffine (T.obj (openChartObject B S hS U i.1.1.1)) := by
    change IsAffine (i.1.1.1 : Scheme.{u})
    infer_instance
  have : IsAffine (T.obj (openChartObject B S hS V i.1.2.1)) := by
    change IsAffine (i.1.2.1 : Scheme.{u})
    infer_instance
  let rmap : openChartObject B S hS U i.1.1.1 ⟶ openChartObject B S hS V i.1.2.1 :=
    Over.homMk ⟨(T.map g).resLE i.1.2.1 i.1.1.1 i.2⟩ (by
      apply ObjectProperty.hom_ext
      change (T.map g).resLE i.1.2.1 i.1.1.1 i.2 ≫ (i.1.2.1.ι ≫ V.hom.hom) =
        i.1.1.1.ι ≫ U.hom.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι]
      exact congrArg (fun φ ↦ i.1.1.1.ι ≫ φ) (congrArg (fun φ ↦ φ.hom) g.w))
  have hsquare : rmap ≫ tIncl = sIncl ≫ g := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Scheme.Hom.resLE_comp_ι _ _
  have hse : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map sIncl ≫ a) :=
    etale_comp_of_scheme B S hS sIncl a hsEtale ha
  have hte : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map tIncl ≫ b) :=
    etale_comp_of_scheme B S hS tIncl b htEtale hb
  have hcomm : yoneda.map rmap ≫ (yoneda.map tIncl ≫ b) = (yoneda.map sIncl ≫ a) ≫ f := by
    rw [← Category.assoc, ← Functor.map_comp, hsquare, Functor.map_comp]
    simp only [Category.assoc, hc]
  have := hf _ _ _ _ rmap hse hte hcomm
  have haffine : (T.map rmap).IsPseudoCoherentFrom (h.chartComplex hX E hse).obj m := by
    refine ((derivedSectionsPseudoCoherentComparison' (T.map rmap)
      (h.chartComplex hX E hse).obj (h.chartComplex hX E hse).property m).out 2 1).mp ?_
    refine ⟨PUnit.{u + 1}, fun _ ↦ ⟨⊤, isAffineOpen_top _⟩, by simp, fun _ ↦ ?_⟩
    refine ⟨PUnit.{u + 1}, fun _ ↦ ⟨⊤, isAffineOpen_top _⟩, by simp, fun _ ↦ ?_⟩
    exact ⟨by simp, hall _ _ _ _ rmap hse hte hcomm inferInstance inferInstance⟩
  have hover := (Scheme.Hom.isPseudoCoherentFrom_comp_iff_of_flat (T.map rmap) (T.map tIncl)
    (h.chartComplex hX E hse).obj m).mpr haffine
  have hmapEq : arrows i ≫ T.map g = T.map rmap ≫ T.map tIncl := by
    have hT : T.map (sIncl ≫ g) = T.map (rmap ≫ tIncl) := congrArg T.map hsquare.symm
    rw [T.map_comp, T.map_comp] at hT
    exact hT
  have honOpen : (arrows i ≫ T.map g).IsPseudoCoherentFrom (h.chartComplex hX E hse).obj m :=
    (@Scheme.Hom.isPseudoCoherentFrom_congr_hom _ _ _ _ hmapEq.symm inferInstance hiType _ m).mp
      hover
  obtain ⟨iso⟩ := h.chartComplexPullback hX E sIncl ha hse
  exact Scheme.Hom.IsPseudoCoherentFrom.of_iso _ honOpen iso

end Implications

/-! ### Stacks 0CSX -/

/-- **Stacks 0CSX.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` locally of
finite type, let `m` be an integer and let `E` be an object of `D_QCoh(𝒪_X)`.  With the complex
`E|_U` of Remark 0CSW the following are equivalent:

1. for every commuting square of étale scheme charts `U ⟶ V` over `X ⟶ Y`, the complex `E|_U` is
   `m`-pseudo-coherent relative to `V`;
2. for some such square with `U ⟶ X` surjective, the complex `E|_U` is `m`-pseudo-coherent
   relative to `V`;
3. for every such square with `U` and `V` affine, the complex `RΓ(U, E)` of `𝒪_X(U)`-modules is
   `m`-pseudo-coherent relative to `𝒪_Y(V)`.

See the module docstring for the four inputs that `h` carries. -/
@[stacks 0CSX "proved relative to the carried inputs `h`. Its `comparison` field is the second \
sentence of Remark 0CSW — that an object of D_QCoh of a representable algebraic space is the \
pullback of a unique object of D_QCoh of a representing scheme, which is what gives E|_U its \
meaning — and is absent from the library, whose 0CSW is the first sentence only; \
`chartComplexPullback` is its compatibility with passing to a finer chart. The descent half of \
0CSN is carried as `fppfDescent` because only the forward half is proved. 09US is not carried: \
it is recovered from its own 0E23 input, carried through as `torIndependentBaseChange`."]
theorem relativePseudoCoherence_chart_tfae (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (h : RelativePseudoCoherenceInput B S hS)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX) (m : ℤ) :
    List.TFAE
      [∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
          (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
          (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
          (hc : yoneda.map g ≫ b = a ≫ f),
          IsPseudoCoherentFromOnChart B S hS h hX f hf E m U V a b g ha hb hc,
       ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
          (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
          (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b),
          IsSurjective B S hS a ∧ ∃ hc : yoneda.map g ≫ b = a ≫ f,
            IsPseudoCoherentFromOnChart B S hS h hX f hf E m U V a b g ha hb hc,
       ∀ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V)
          (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
          (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
          (hc : yoneda.map g ≫ b = a ≫ f)
          (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
          (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)),
          haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
            hf U V a b g ha hb hc
          haveI := hU
          haveI := hV
          ((BigFppfOver.toScheme B S hS).map g).DerivedSectionsPseudoCoherentOn'
            (h.chartComplex hX E ha).obj m (isAffineOpen_top _) (isAffineOpen_top _)
            (by simp)] := by
  tfae_have 1 → 2 := exists_surjectiveChart_of_forall_chart h hX hY f hf E m
  tfae_have 1 → 3 := derivedSections_of_forall_chart h hX f hf E m
  tfae_have 2 → 1 := by
    rintro ⟨U, V, a, b, g, ha, hb, hsurj, hc, hcond⟩ U' V' a' b' g' ha' hb' hc'
    exact forall_chart_of_surjectiveChart h hX f hf E m U V a b g ha hb hsurj hc hcond
      U' V' a' b' g' ha' hb' hc'
  tfae_have 3 → 1 := forall_chart_of_derivedSections h hX f hf E m
  tfae_finish

end Space

end AlgebraicGeometry

end
