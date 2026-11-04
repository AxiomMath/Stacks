module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Descent

/-!
# Comparing `𝒪(1)` with the exceptional ideal sheaf on an affine blowup

Let `R` be a commutative ring and `I ⊆ R` an ideal, and let `Proj (⨁ₙ Iⁿ)` be the blowup of
`Spec R` in `I`. Part (3) of Stacks tag 02OS asserts that the twisting sheaf `𝒪(1)` of that
`Proj` is the ideal sheaf `I·𝒪` of the exceptional divisor. This file proves that for the
affine blowup. The comparison over the standard chart `D₊(a⁽¹⁾)` is "divide by the trivializing
section `a⁽¹⁾`, then multiply by the pullback of `a`", and the comparisons over two charts agree
because `a⁽⁰⁾·b⁽¹⁾` and `b⁽⁰⁾·a⁽¹⁾` are both the monomial `ab·T` of the Rees algebra.

## Main definitions

* `Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv.gluedIso`: the isomorphism of sheaves of
  modules glued from a family of comparison isomorphisms over a cover of the whole space.
* `Stacks.Blowup.baseSection`: the global section of `𝒪` on the affine blowup obtained by pulling
  an element of the base ring back along the blowup morphism.
* `Stacks.Blowup.chartCoeff`: the chartwise comparison on sections — a section of `𝒪(1)` divided
  by the trivializing section of the chart `D₊(b⁽¹⁾)`.
* `Stacks.Blowup.chartEquiv`: the chartwise comparison `𝒪(1)|_V ≅ (I·𝒪)|_V` over an open of
  that chart, and `Stacks.Blowup.twistOneLocalEquiv` the glueing datum these assemble into.

## Main results

* `Stacks.Blowup.twistOneIsoExceptionalIdealSheaf`: **Stacks tag 02OS part (3), for the affine
  blowup.** The twisting sheaf `𝒪(1)` of `Proj (⨁ₙ Iⁿ)` is the ideal sheaf of the exceptional
  divisor.
* `Stacks.Blowup.baseSection_val`: the pullback of `r` has the constant fraction `r / 1` as its
  value at every point. This is what makes the comparison computable pointwise.
* `Stacks.Blowup.chartSections_baseSection`: **the generator of the exceptional ideal on the
  chart `D₊(b⁽¹⁾)` is the pullback of `b`.** The generator produced by
  `Stacks.Blowup.exists_isRegular_ideal_comap_toSpec_eq_span` is the image of `b` under the chart
  identification `Γ(X, D₊(b⁽¹⁾)) ≅ (⨁ₙ Iⁿ)₍b⁽¹⁾₎`, and this identifies it with a section
  described by one formula on the whole blowup — which is what lets two charts be compared.
* `Stacks.Blowup.ideal_comap_toSpec_eq_span_baseSection` and
  `Stacks.Blowup.baseSection_mem_nonZeroDivisors`: the two hypotheses that
  `Stacks.CartierAffineLocalConverse.trivialization` asks for over the chart, stated at that
  generator.
* `Stacks.Blowup.baseSection_mul_trivializingFun_comm`: **the comparisons over two charts
  agree.** Multiplying the pullback of `a` by the trivializing section `b⁽¹⁾` of `𝒪(1)` gives the
  same thing as multiplying the pullback of `b` by `a⁽¹⁾`.
  `Stacks.Blowup.chartCoeff_mul_baseSectionRes_comm` is the same statement one level up, for
  sections rather than for their values, and `Stacks.Blowup.chartEquiv_agree` is what it becomes
  once the injection of the ideal sheaf into the structure sheaf is divided out.
* `Stacks.Blowup.reesGradingZero_mul_reesDegOne_comm`: the underlying identity
  `a⁽⁰⁾·b⁽¹⁾ = b⁽⁰⁾·a⁽¹⁾` in the Rees algebra.
* `Stacks.Blowup.iSup_chartImage_eq_top`: the charts `D₊(b⁽¹⁾)` for `b ∈ I` cover the blowup.

## Implementation notes

`Stacks.Blowup.appTop_eq_appIso` is the bridge between the two ways an open immersion acts on
sections: `AlgebraicGeometry.Scheme.Hom.appTop`, which is what a factorization of morphisms
through `Spec` produces, and `AlgebraicGeometry.Scheme.Hom.appIso`, which is what the chart
identifications of `StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalCartier.lean` are phrased
with. The two differ by restriction maps between opens that are all equal to the top open, and
those compose to the identity by proof irrelevance in `Opens`.

The pointwise description of the pullback of a base element is
`Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val`, which describes the global
sections of `AlgebraicGeometry.Proj.toSpecZero` for an arbitrary graded ring; the blowup
morphism `Stacks.Blowup.toSpec` is that morphism followed by `Spec` of the identification of `R`
with the degree-zero part of the Rees algebra.

The chartwise comparison over an open `V ≤ D₊(b⁽¹⁾)` is the composite

    Γ(V, 𝒪(1)) --(trivializingEquiv b⁽¹⁾)⁻¹--> Γ(V, 𝒪) --(θ_b)⁻¹--> Γ(V, I·𝒪),

with `Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv` at `n = 1` and `θ_b` the
`Stacks.SheafDescent.Trivialization.θ` of `Stacks.Blowup.chartTrivialization`. The two halves
are `Stacks.Blowup.chartTwistEquiv` and `Stacks.Blowup.chartIdealEquiv`, which exist only to
restate the two trivializations with their scalars at one spelling: `trivializingEquiv` is
linear over the `CommRingCat` object `Γ(V, 𝒪)` and `θ` over its image under
`forget₂ CommRingCat RingCat`, and `LinearEquiv.trans` asks for a `RingHomCompTriple` that
instance search, which unfolds nothing semireducible, does not find between the two. A `def`
whose stated type names the one spelling settles it by a definitional-equality check instead.
For the same reason `Stacks.CartierAffineLocalConverse.incl_app_eq_θ_mul` takes the coefficient
as an argument rather than writing `θ ... * ...` into its statement.

## Only the affine blowup is covered here

Only the affine blowup is covered in this file, so no `@[stacks 02OS]` attribute is attached
here; the unconditional statement is `AlgebraicGeometry.twistOneIsoExceptionalIdealModule` in
`StacksFrontier/AlgebraicGeometry/Blowup/TwistOneExceptionalIdeal.lean`, and the rest of this section
records how it was reached from here.

**The obstruction was not Stacks tag 01NR.** The graded twists on a relative `Proj` exist with
no carried hypothesis: `Stacks.RelativeProj.Situation.twistSheaf`, and for the blowup of an
*arbitrary* scheme `AlgebraicGeometry.blowUpTwist I 1` with its chart identification
`AlgebraicGeometry.blowUpTwistChartIso`.

The general statement is a `Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv` over the
affine charts `Stacks.BlowUpChartCover.chartOpen I U a` of `AlgebraicGeometry.blowUp I`, fed to
`gluedIso` below, which is stated for an arbitrary space. The two sheaves it compares are
`AlgebraicGeometry.blowUpTwist I 1` and `AlgebraicGeometry.exceptionalIdeal I`; both live on
`AlgebraicGeometry.blowUp I = (AlgebraicGeometry.reesSituation I).relativeProj`, which is *not*
the scheme `Stacks.Blowup.blowUp I` of `Stacks.Blowup.exceptionalIdeal`, and not the scheme this
file's affine case is about either. The charts cover the blowup
(`Stacks.BlowUpChartCover.iSup_opensRange_chart_eq_top`), and all four inputs now exist:

* **the ideal-sheaf side.** `Stacks.BlowUpChartCover.exceptionalChartTrivialization` is the
  trivialization of the exceptional ideal sheaf over a chart, at the *named* generator
  `Stacks.BlowUpChartCover.chartGenerator I U a` — the pullback of `a` along the blowup
  morphism — with `chartGenerator_mem_nonZeroDivisors` and
  `ideal_exceptionalIdeal_eq_span_chartGenerator`. Its coefficient is pinned by
  `Stacks.CartierAffineLocalConverse.incl_app_eq_θ_mul`, so the agreement of two charts becomes
  an identity between sections of the *structure* sheaf of the blowup.
* **the naturality in the base**, which earlier notes recorded as proved nowhere.
  `Stacks.ProjTwistComparison.app_trivializingEquiv_symm` transports the trivializing
  coefficient of `𝒪(1)` along any graded homomorphism carrying a degree-one element to a
  degree-one element, with no finiteness, affineness or quasi-compactness hypothesis;
  `Stacks.Blowup.app_projMap_chartCoeff_mul_baseSectionRes` is the combined form at the Tag 01NO
  chart transition. The transition itself, on sections, is
  `Stacks.RelativeProj.Situation.twistPushforwardMap`, which `twistPushforwardMap_apply` reads
  as `Stacks.ProjTwistComparison.sectionsMap`.
* **the chart-level algebra.** The charts of `AlgebraicGeometry.blowUp I` are the `Proj` of
  `(AlgebraicGeometry.reesSituation I).sectionRingGrading U`, *not* of
  `Stacks.Blowup.reesGrading (I.ideal U)`, which is the grading this file and
  `Blowup.TwistOneBaseTransport` are written at. `AlgebraicGeometry.reesSectionGradedHom`
  identifies the two, and `StacksFrontier/AlgebraicGeometry/Blowup/ReesDegreeOneComparison.lean`
  carries the degree-one generator, its restriction, the chart it cuts out and the cross
  identity `a⁽⁰⁾·a'⁽¹⁾ = a'⁽⁰⁾·a⁽¹⁾` across that comparison.

* **the two descriptions of the generator.**
  `Stacks.RelativeProj.Situation.chartBaseSection` is the pullback of a section of the base to the
  chart over an affine open; `chartBaseSection_val` says its value at every point is the constant
  fraction of `(AlgebraicGeometry.reesSituation I).sectionRingBaseMap U a`, and
  `app_relativeProjChart_appLE` says the chart reads
  `Stacks.BlowUpChartCover.chartGenerator I U a` as exactly that. This was recorded here as the
  one missing input; it is in
  `StacksFrontier/AlgebraicGeometry/RelativeProj/ChartBaseSection.lean`.

With those, the agreement of two charts *over one affine open of the base* is proved:
`AlgebraicGeometry.twistOneCoeff_mul_chartBaseSectionRes_comm` in
`StacksFrontier/AlgebraicGeometry/Blowup/TwistOneChartAgreement.lean`, at the grading
`(reesSituation I).sectionRingGrading U` that the charts actually carry, with
`Stacks.AlgebraicGeometry.ProjTrivialization.twistOneCoeff` the general-grading counterpart of
`Stacks.Blowup.chartCoeff` below.

A fifth input has since been added:
`Stacks.BlowUpChartCover.preimage_relativeProjChart_chartOpen` in
`StacksFrontier/AlgebraicGeometry/BlowUpChartCover/ChartImage.lean` identifies the preimage of
`Stacks.BlowUpChartCover.chartOpen I U a` under the chart over `U` with the standard open
`D₊(a⁽¹⁾)` of `Proj 𝒜(U)`, which is where the twist trivializes.

**The general case is proved.**
`AlgebraicGeometry.twistOneIsoExceptionalIdealModule` in
`StacksFrontier/AlgebraicGeometry/Blowup/TwistOneExceptionalIdeal.lean` carries
`@[stacks 02OS "part (3)"]` for an arbitrary scheme and an arbitrary quasi-coherent sheaf of
ideals. The three steps of its proof are

1. the sections isomorphism of the structure sheaf over a chart —
   `Stacks.RelativeProj.Situation.chartSectionsIso` in
   `StacksFrontier/AlgebraicGeometry/RelativeProj/ChartStructureSections.lean`, from
   `AlgebraicGeometry.Scheme.Hom.isIso_app_of_le_opensRange`;
2. the chartwise comparison itself — `AlgebraicGeometry.chartEquiv` in
   `StacksFrontier/AlgebraicGeometry/Blowup/TwistOneChartEquiv.lean`, characterised by
   `AlgebraicGeometry.incl_app_chartEquiv`;
3. the agreement of two charts over different affine opens of the base —
   `AlgebraicGeometry.chartEquiv_agree`, which checks it on the cover of the overlap by the parts
   lying over the affine opens inside `U ⊓ U'` and propagates it by the sheaf condition. The two
   elementary cases are `AlgebraicGeometry.chartEquiv_agree_of_eq_base` (one affine open of the
   base, two sections) and `AlgebraicGeometry.chartEquiv_agree_of_le` (an inclusion of affine
   opens, with the restricted section).

The affine case below is kept because it is stated at
`Stacks.Blowup.reesGrading`, the ordinary Rees algebra of an ideal of a ring, which is the grading
the rest of this file and `Blowup.TwistOneBaseTransport` are written at; the general statement is
at `(reesSituation I).sectionRingGrading`, on a different scheme.

Parts (1) and (2) of the tag are proved for an arbitrary scheme elsewhere:
`AlgebraicGeometry.isIso_blowUp_restrict_compl_support` in
`StacksFrontier/AlgebraicGeometry/Blowup/IsomorphismOffCenter/Basic.lean` and
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal` in
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalCartier.lean`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Polynomial
open HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (moduleSections twistGrading twistingSheaf)

universe u

namespace Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv

attribute [local implicit_reducible] TopCat.Sheaf

variable {X : TopCat.{u}} {O : TopCat.Sheaf RingCat.{u} X}

/-- **A family of comparison isomorphisms over a cover of the whole space glues to an isomorphism
of sheaves of modules.** Naturality of the glued comparison is
`Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv.glueLinearEquiv_map`. -/
def gluedIso {M N : _root_.SheafOfModules.{u} O} {ι : Type u}
    (E : LocalEquiv (ofSheafOfModules M ⊤) (ofSheafOfModules N ⊤) ι) : M ≅ N :=
  (_root_.SheafOfModules.fullyFaithfulForget O).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (E.glueLinearEquiv (isSheaf_ofSheafOfModules M ⊤)
        (isSheaf_ofSheafOfModules N ⊤) (le_top (a := V.unop))).toModuleIso)
      (fun {_ _} f => by
        refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
        exact E.glueLinearEquiv_map (isSheaf_ofSheafOfModules M ⊤)
          (isSheaf_ofSheafOfModules N ⊤) le_top (leOfHom f.unop) m))

end Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv

namespace Stacks.Blowup

attribute [local implicit_reducible] blowUpSpec chartImage
attribute [local instance] ProjectiveSpectrum.isPrime

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The two ways an open immersion acts on global sections -/

/-- Global sections of an open immersion factor through the identification of the sections over
the image: the two restriction maps involved are between opens equal to the top open. -/
theorem appTop_eq_appIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.appTop = Y.presheaf.map (homOfLE (le_top (a := f ''ᵁ (⊤ : X.Opens)))).op ≫
      (f.appIso ⊤).hom := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE, ← Category.assoc, Scheme.Hom.naturality,
    Category.assoc, ← Functor.map_comp]
  refine Eq.trans ?_ (congrArg (fun g => Scheme.Hom.app f ⊤ ≫ X.presheaf.map g)
    (Subsingleton.elim (𝟙 (op (f ⁻¹ᵁ (⊤ : Y.Opens)))) _))
  show Scheme.Hom.app f ⊤ = _
  exact (Category.comp_id _).symm.trans
    (congrArg (Scheme.Hom.app f ⊤ ≫ ·) (X.presheaf.map_id _).symm)

/-! ### Pulling a base element back to the blowup -/

/-- The global section of the structure sheaf of the affine blowup attached to an element of the
base ring: the pullback of that element along the blowup morphism. -/
def baseSection (r : R) : Γ(blowUpSpec I, ⊤) :=
  (toSpec I).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)

/-- Applying a ring map out of the global sections to the pullback of `r` is evaluating at `r` any
ring map known to agree with it after precomposing the pullback. -/
private theorem hom_baseSection_eq {S : CommRingCat.{u}} (g : Γ(blowUpSpec I, ⊤) ⟶ S)
    (φ : CommRingCat.of R ⟶ S)
    (h : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (toSpec I).appTop ≫ g = φ) (r : R) :
    g.hom (baseSection I r) = φ.hom r := by
  rw [← h]
  rfl

/-- **The pullback of `r` has the constant fraction `r / 1` as its value at every point.** -/
theorem baseSection_val (r : R) (x : ProjectiveSpectrum.top (reesGrading I)) :
    HomogeneousLocalization.val ((baseSection I r).1 ⟨x, trivial⟩) =
      algebraMap (reesAlgebra I) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        ((reesGradingZeroEquiv I r : reesGrading I 0) : reesAlgebra I) := by
  have hb : baseSection I r =
      (Proj.toSpecZero (reesGrading I)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (reesGrading I 0))).inv
          (reesGradingZeroEquiv I r)) :=
    hom_baseSection_eq I (𝟙 _) _ (by
      rw [Category.comp_id, toSpec, Scheme.Hom.comp_appTop, ← Category.assoc,
        ← Scheme.ΓSpecIso_inv_naturality]) r
  rw [hb]
  exact Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val (reesGrading I)
    (reesGradingZeroEquiv I r) x

/-- **The generator of the exceptional ideal on the chart `D₊(b⁽¹⁾)` is the pullback of `b`.**
The generator of `Stacks.Blowup.exists_isRegular_ideal_comap_toSpec_eq_span` is the image of `b`
under the chart identification; this says it is the restriction of `Stacks.Blowup.baseSection`,
which is described by one formula on the whole blowup. -/
theorem chartSections_baseSection {b : R} (hb : b ∈ I) :
    (chartSections I hb).hom.hom
        (((blowUpSpec I).presheaf.map (homOfLE (le_top (a := chartImage I hb))).op).hom
          (baseSection I b))
      = (chartGamma I hb).inv.hom (chartAwayMap I hb b) := by
  have h3 : ((awayChartι I hb).appTop).hom (baseSection I b) =
      (chartGamma I hb).inv.hom (chartAwayMap I hb b) :=
    hom_baseSection_eq I _ (CommRingCat.ofHom (chartAwayMap I hb) ≫ (chartGamma I hb).inv)
      (by rw [← Scheme.Hom.comp_appTop, awayι_comp_toSpec, ← Scheme.ΓSpecIso_inv_naturality]) b
  rw [← h3, appTop_eq_appIso, CommRingCat.hom_comp, RingHom.comp_apply]

/-- **The chart generator is the restriction of the pullback of `b`.** -/
theorem chartGenerator_eq_baseSection {b : R} (hb : b ∈ I) :
    chartGenerator I hb =
      ((blowUpSpec I).presheaf.map (homOfLE (le_top (a := chartImage I hb))).op).hom
        (baseSection I b) := by
  rw [chartGenerator, ← chartSections_baseSection I hb, ← CommRingCat.comp_apply,
    Iso.hom_inv_id, CommRingCat.id_apply]

/-- **The inverse image of the centre on the chart `D₊(b⁽¹⁾)` is generated by the restriction of
the pullback of `b`.** -/
theorem ideal_comap_toSpec_eq_span_baseSection
    (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) {b : R} (hb : b ∈ I) :
    (J.comap (toSpec I)).ideal ⟨chartImage I hb, isAffineOpen_chartImage I hb⟩ =
      Ideal.span {((blowUpSpec I).presheaf.map
        (homOfLE (le_top (a := chartImage I hb))).op).hom (baseSection I b)} := by
  rw [← chartGenerator_eq_baseSection]
  exact ideal_comap_toSpec_eq_span_chartGenerator I J hJ hb

/-- **The restriction of the pullback of `b` to the chart `D₊(b⁽¹⁾)` is a nonzerodivisor.** -/
theorem baseSection_mem_nonZeroDivisors {b : R} (hb : b ∈ I) :
    ((blowUpSpec I).presheaf.map (homOfLE (le_top (a := chartImage I hb))).op).hom
        (baseSection I b) ∈ nonZeroDivisors Γ(blowUpSpec I, chartImage I hb) := by
  rw [← chartGenerator_eq_baseSection]
  exact isRegular_iff_mem_nonZeroDivisors.mp (isRegular_chartGenerator I hb)

/-! ### The comparisons over two charts agree -/

/-- **The cross identity of two degree-one Rees generators**: `a⁽⁰⁾·b⁽¹⁾` and `b⁽⁰⁾·a⁽¹⁾` are
both the monomial `ab·T`. -/
theorem reesGradingZero_mul_reesDegOne_comm {a b : R} (ha : a ∈ I) (hb : b ∈ I) :
    ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I) * reesDegOne I hb
      = ((reesGradingZeroEquiv I b : reesGrading I 0) : reesAlgebra I) * reesDegOne I ha := by
  refine Subtype.ext ?_
  have h : ∀ {c d : R} (hd : d ∈ I),
      ((((reesGradingZeroEquiv I c : reesGrading I 0) : reesAlgebra I) * reesDegOne I hd :
        reesAlgebra I) : R[X]) = monomial 1 (c * d) := by
    intro c d hd
    rw [Subalgebra.coe_mul, coe_coe_reesGradingZeroEquiv, coe_reesDegOne_eq_C_mul_X,
      ← C_mul_X_pow_eq_monomial, pow_one, C_mul]
    ring
  rw [h hb, h ha, mul_comm]

/-- **The comparison of `𝒪(1)` with the ideal sheaf does not depend on the chart.** Over a point
of `D₊(a⁽¹⁾) ∩ D₊(b⁽¹⁾)` the pullback of `a` times the trivializing value of `b⁽¹⁾` equals the
pullback of `b` times the trivializing value of `a⁽¹⁾`. -/
theorem baseSection_mul_trivializingFun_comm {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    {W : Opens (ProjectiveSpectrum.top (reesGrading I))}
    (hWa : W ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I ha))
    (hWb : W ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb)) (x : W) :
    HomogeneousLocalization.val ((baseSection I a).1 ⟨x.1, trivial⟩) *
        Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (reesGrading I) 1 hWb x
      = HomogeneousLocalization.val ((baseSection I b).1 ⟨x.1, trivial⟩) *
        Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun (reesGrading I) 1 hWa x := by
  rw [baseSection_val, baseSection_val,
    Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun,
    Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun,
    ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, Int.toNat_one, pow_one,
    show ((-1 : ℤ)).toNat = 0 from rfl, pow_zero, one_mul, mul_one]
  rw [reesGradingZero_mul_reesDegOne_comm I ha hb]

/-! ### The chartwise comparison of `𝒪(1)` with the exceptional ideal sheaf -/

/-- The pullback of an element of the base ring, restricted to an open of the blowup. -/
def baseSectionRes (r : R) (W : (blowUpSpec I).Opens) : Γ(blowUpSpec I, W) :=
  ((blowUpSpec I).presheaf.map (homOfLE (le_top (a := W))).op).hom (baseSection I r)

/-- The restricted pullback has the same value at a point of the open as the pullback itself. -/
theorem baseSectionRes_val (r : R) {W : (blowUpSpec I).Opens} (x : W) :
    (baseSectionRes I r W).1 x = (baseSection I r).1 ⟨x.1, trivial⟩ := rfl

/-- The chartwise comparison: a section of `𝒪(1)` divided by the trivializing section of the
chart `D₊(b⁽¹⁾)`. -/
def chartCoeff {b : R} (hb : b ∈ I) {W : (blowUpSpec I).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb))
    (t : moduleSections (reesGrading I) (twistGrading (reesGrading I) 1) W) :
    Γ(blowUpSpec I, W) :=
  (trivializingEquiv (reesGrading I) (reesDegOne_mem_reesGrading I hb) 1 hW).symm t

/-- **The chartwise comparison inverts multiplication by the trivializing section.** At every
point its value times the trivializing value of `b⁽¹⁾` is the value of the section of `𝒪(1)`. -/
theorem chartCoeff_val_mul {b : R} (hb : b ∈ I) {W : (blowUpSpec I).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb))
    (t : moduleSections (reesGrading I) (twistGrading (reesGrading I) 1) W) (x : W) :
    HomogeneousLocalization.val ((chartCoeff I hb hW t).1 x) *
      trivializingFun (reesGrading I) 1 hW x = t.1 x := by
  have h : (trivializingEquiv (reesGrading I) (reesDegOne_mem_reesGrading I hb) 1 hW)
      (chartCoeff I hb hW t) = t :=
    (trivializingEquiv (reesGrading I) (reesDegOne_mem_reesGrading I hb) 1 hW).apply_symm_apply t
  conv_rhs => rw [← h]
  rfl

/-- **The chartwise comparisons over two charts agree.** On an open contained in both
`D₊(a⁽¹⁾)` and `D₊(b⁽¹⁾)`, the comparison through `a` times the pullback of `a` equals the
comparison through `b` times the pullback of `b`. -/
theorem chartCoeff_mul_baseSectionRes_comm {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    {W : (blowUpSpec I).Opens}
    (hWa : W ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I ha))
    (hWb : W ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb))
    (t : moduleSections (reesGrading I) (twistGrading (reesGrading I) 1) W) :
    chartCoeff I ha hWa t * baseSectionRes I a W
      = chartCoeff I hb hWb t * baseSectionRes I b W := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  have hA := chartCoeff_val_mul I ha hWa t x
  have hB := chartCoeff_val_mul I hb hWb t x
  have hc : HomogeneousLocalization.val ((baseSectionRes I a W).1 x) *
        trivializingFun (reesGrading I) 1 hWb x
      = HomogeneousLocalization.val ((baseSectionRes I b W).1 x) *
        trivializingFun (reesGrading I) 1 hWa x :=
    baseSection_mul_trivializingFun_comm I ha hb hWa hWb x
  show HomogeneousLocalization.val ((chartCoeff I ha hWa t).1 x * (baseSectionRes I a W).1 x)
      = HomogeneousLocalization.val ((chartCoeff I hb hWb t).1 x * (baseSectionRes I b W).1 x)
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mul]
  refine ((isUnit_trivializingFun (reesGrading I) 1 hWa x).mul
    (isUnit_trivializingFun (reesGrading I) 1 hWb x)).mul_right_cancel ?_
  linear_combination
    (HomogeneousLocalization.val ((baseSectionRes I a W).1 x) *
        trivializingFun (reesGrading I) 1 hWb x) * hA -
      (HomogeneousLocalization.val ((baseSectionRes I b W).1 x) *
        trivializingFun (reesGrading I) 1 hWa x) * hB + t.1 x * hc

/-- **The chartwise comparison of sections commutes with restriction.** Pointwise both sides
are the value of `t` divided by the trivializing value, which is given by one formula. -/
theorem chartCoeff_map {b : R} (hb : b ∈ I) {V W : (blowUpSpec I).Opens}
    (hV : V ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb))
    (hW : W ≤ ProjectiveSpectrum.basicOpen (reesGrading I) (reesDegOne I hb)) (hWV : W ≤ V)
    (t : moduleSections (reesGrading I) (twistGrading (reesGrading I) 1) V) :
    chartCoeff I hb hW ((twistingSheaf (reesGrading I) 1).val.restrictₛₗ (homOfLE hWV).op t)
      = ((blowUpSpec I).presheaf.map (homOfLE hWV).op).hom (chartCoeff I hb hV t) :=
  Subtype.ext (funext fun x => eq_of_val_mul_eq (reesGrading I) 1 hW x
    ((chartCoeff_val_mul I hb hW _ x).trans
      (chartCoeff_val_mul I hb hV t ⟨x.1, hWV x.2⟩).symm))

/-! ### The comparison glued over the charts -/

/-- **The charts `D₊(b⁽¹⁾)` for `b ∈ I` cover the affine blowup.** This is
`Stacks.Blowup.iSup_basicOpen_reesGrading_one_eq_top` with the index set cut down from the
degree-one part of the Rees algebra to the ideal itself. -/
theorem iSup_chartImage_eq_top : ⨆ b : I, chartImage I b.2 = ⊤ := by
  refine top_unique fun y _ => ?_
  obtain ⟨f, hyf⟩ : ∃ f : reesGrading I 1,
      y ∈ Proj.basicOpen (reesGrading I) ((f : reesAlgebra I)) := by
    have hy : y ∈ (⊤ : (AlgebraicGeometry.Proj (reesGrading I)).Opens) := trivial
    rw [← iSup_basicOpen_reesGrading_one_eq_top I] at hy
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨b, hb, hfeq⟩ : ∃ (b : R) (hb : b ∈ I), (f : reesAlgebra I) = reesDegOne I hb := by
    refine ⟨((f : reesAlgebra I) : R[X]).coeff 1,
      by simpa [pow_one] using (f : reesAlgebra I).2 1, ?_⟩
    exact Subtype.ext (coe_eq_monomial I f.2)
  rw [hfeq] at hyf
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hb⟩, by rwa [chartImage_eq_basicOpen]⟩

/-- The exceptional ideal sheaf of the affine blowup: the ideal sheaf of the inverse image of
the centre `J`, read as a sheaf of modules over the structure sheaf of `Proj`. -/
abbrev exceptionalIdealSheaf (J : (Spec (CommRingCat.of R)).IdealSheafData) :
    _root_.SheafOfModules.{u} (projRingSheaf (reesGrading I)) :=
  Stacks.ClosedImmersion.idealSheaf (J.comap (toSpec I)).subschemeι.toLRSHom.toShHom

/-- The sectionwise trivialization of the exceptional ideal sheaf over the chart `D₊(b⁽¹⁾)`,
at the generator `Stacks.Blowup.baseSectionRes`. -/
def chartTrivialization (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) {b : R} (hb : b ∈ I) :
    Stacks.SheafDescent.Trivialization (blowUpSpec I).presheaf
      (exceptionalIdealSheaf I J).val (chartImage I hb) :=
  Stacks.CartierAffineLocalConverse.trivialization (J.comap (toSpec I))
    ⟨chartImage I hb, isAffineOpen_chartImage I hb⟩ (baseSectionRes I b (chartImage I hb))
    (baseSection_mem_nonZeroDivisors I hb) (ideal_comap_toSpec_eq_span_baseSection I J hJ hb)

/-- Restricting the pullback of `r` from one open to a smaller one gives the pullback there. -/
theorem map_baseSectionRes {V W : (blowUpSpec I).Opens} (hWV : W ≤ V) (r : R) :
    ((blowUpSpec I).presheaf.map (homOfLE hWV).op).hom (baseSectionRes I r V)
      = baseSectionRes I r W := by
  rw [baseSectionRes, baseSectionRes, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The trivialization of `𝒪(1)` over an open of the chart `D₊(b⁽¹⁾)`, with its scalars at the
spelling the glueing data of `Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv` uses. -/
def chartTwistEquiv {b : R} (hb : b ∈ I) {V : (blowUpSpec I).Opens}
    (hV : V ≤ chartImage I hb) :
    ToType ((projRingSheaf (reesGrading I)).obj.obj (op V))
      ≃ₗ[ToType ((projRingSheaf (reesGrading I)).obj.obj (op V))]
        ((twistingSheaf (reesGrading I) 1).val.obj (op V)) :=
  trivializingEquiv (reesGrading I) (reesDegOne_mem_reesGrading I hb) 1
    (hV.trans (chartImage_eq_basicOpen I hb).le)

/-- The trivialization of the exceptional ideal sheaf over an open of the chart `D₊(b⁽¹⁾)`,
with its scalars at the same spelling. -/
def chartIdealEquiv (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) {b : R} (hb : b ∈ I)
    {V : (blowUpSpec I).Opens} (hV : V ≤ chartImage I hb) :
    ((exceptionalIdealSheaf I J).val.obj (op V))
      ≃ₗ[ToType ((projRingSheaf (reesGrading I)).obj.obj (op V))]
        ToType ((projRingSheaf (reesGrading I)).obj.obj (op V)) :=
  (chartTrivialization I J hJ hb).θ V (homOfLE hV)

/-- The chartwise comparison of `𝒪(1)` with the exceptional ideal sheaf over an open of the
chart `D₊(b⁽¹⁾)`: divide by the trivializing section of `𝒪(1)`, then multiply by the pullback
of `b`. -/
def chartEquiv (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) {b : R} (hb : b ∈ I)
    {V : (blowUpSpec I).Opens} (hV : V ≤ chartImage I hb) :
    ((twistingSheaf (reesGrading I) 1).val.obj (op V))
      ≃ₗ[ToType ((projRingSheaf (reesGrading I)).obj.obj (op V))]
        ((exceptionalIdealSheaf I J).val.obj (op V)) :=
  (chartTwistEquiv I hb hV).symm.trans (chartIdealEquiv I J hJ hb hV).symm

/-- **The chartwise comparison is division by the pullback of `b`.** The image in the structure
sheaf of the section of the exceptional ideal sheaf attached to `t` is the chartwise
comparison of `t` times the pullback of `b`. -/
theorem incl_app_chartEquiv (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) {b : R} (hb : b ∈ I)
    {V : (blowUpSpec I).Opens} (hV : V ≤ chartImage I hb)
    (t : (twistingSheaf (reesGrading I) 1).val.obj (op V)) :
    ((Stacks.CartierAffineLocal.incl (J.comap (toSpec I))).val.app (op V)).hom
        (chartEquiv I J hJ hb hV t)
      = chartCoeff I hb (hV.trans (chartImage_eq_basicOpen I hb).le) t *
        baseSectionRes I b V := by
  have ha : (chartTrivialization I J hJ hb).θ V (homOfLE hV) (chartEquiv I J hJ hb hV t)
      = chartCoeff I hb (hV.trans (chartImage_eq_basicOpen I hb).le) t :=
    (chartIdealEquiv I J hJ hb hV).apply_symm_apply _
  refine Eq.trans (Stacks.CartierAffineLocalConverse.incl_app_eq_θ_mul (J.comap (toSpec I))
    ⟨chartImage I hb, isAffineOpen_chartImage I hb⟩ (baseSectionRes I b (chartImage I hb))
    (baseSection_mem_nonZeroDivisors I hb) (ideal_comap_toSpec_eq_span_baseSection I J hJ hb)
    (homOfLE hV) (chartEquiv I J hJ hb hV t) _ ha) ?_
  exact congrArg _ (map_baseSectionRes I hV b)

/-- **The chartwise comparisons over two charts agree.** This is
`Stacks.Blowup.chartCoeff_mul_baseSectionRes_comm` read through the injection of the ideal
sheaf into the structure sheaf. -/
theorem chartEquiv_agree (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    {V : (blowUpSpec I).Opens} (hVa : V ≤ chartImage I ha) (hVb : V ≤ chartImage I hb)
    (t : (twistingSheaf (reesGrading I) 1).val.obj (op V)) :
    chartEquiv I J hJ ha hVa t = chartEquiv I J hJ hb hVb t :=
  Stacks.CartierAffineLocal.injective_incl_app (J.comap (toSpec I)) V
    ((incl_app_chartEquiv I J hJ ha hVa t).trans
      ((chartCoeff_mul_baseSectionRes_comm I ha hb _ _ t).trans
        (incl_app_chartEquiv I J hJ hb hVb t).symm))

/-- **The chartwise comparison commutes with restriction.** -/
theorem chartEquiv_map (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) {b : R} (hb : b ∈ I)
    {V W : (blowUpSpec I).Opens} (hV : V ≤ chartImage I hb) (hWV : W ≤ V)
    (t : (twistingSheaf (reesGrading I) 1).val.obj (op V)) :
    chartEquiv I J hJ hb (hWV.trans hV)
        ((twistingSheaf (reesGrading I) 1).val.restrictₛₗ (homOfLE hWV).op t)
      = (exceptionalIdealSheaf I J).val.restrictₛₗ (homOfLE hWV).op
          (chartEquiv I J hJ hb hV t) := by
  refine Stacks.CartierAffineLocal.injective_incl_app (J.comap (toSpec I)) W ?_
  have hL := incl_app_chartEquiv I J hJ hb (hWV.trans hV)
    ((twistingSheaf (reesGrading I) 1).val.restrictₛₗ (homOfLE hWV).op t)
  have hnat := PresheafOfModules.naturality_apply
    (Stacks.CartierAffineLocal.incl (J.comap (toSpec I))).val (homOfLE hWV).op
    (chartEquiv I J hJ hb hV t)
  have hR := incl_app_chartEquiv I J hJ hb hV t
  have hc := chartCoeff_map I hb (hV.trans (chartImage_eq_basicOpen I hb).le)
    ((hWV.trans hV).trans (chartImage_eq_basicOpen I hb).le) hWV t
  refine hL.trans (Eq.symm (hnat.trans ?_))
  refine (congrArg ((blowUpSpec I).presheaf.map (homOfLE hWV).op).hom hR).trans ?_
  refine (map_mul ((blowUpSpec I).presheaf.map (homOfLE hWV).op).hom _ _).trans ?_
  refine (congrArg (fun y => y * ((blowUpSpec I).presheaf.map (homOfLE hWV).op).hom
    (baseSectionRes I b V)) hc.symm).trans ?_
  exact congrArg (fun z => chartCoeff I hb
    ((hWV.trans hV).trans (chartImage_eq_basicOpen I hb).le)
    ((twistingSheaf (reesGrading I) 1).val.restrictₛₗ (homOfLE hWV).op t) * z)
    (map_baseSectionRes I hWV b)

/-- The glueing datum of the comparison `𝒪(1) ≅ I·𝒪`: the chartwise comparisons over the
charts `D₊(b⁽¹⁾)` for `b ∈ I`, which cover the blowup and on which any two agree. -/
def twistOneLocalEquiv (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) :
    Stacks.SheafOfModules.OModuleLocalPresheaf.LocalEquiv
      (Stacks.SheafOfModules.OModuleLocalPresheaf.ofSheafOfModules
        (twistingSheaf (reesGrading I) 1) ⊤)
      (Stacks.SheafOfModules.OModuleLocalPresheaf.ofSheafOfModules
        (exceptionalIdealSheaf I J) ⊤) I where
  cover k := chartImage I k.2
  cover_le _ := le_top
  le_iSup_cover := (iSup_chartImage_eq_top I).ge
  equiv k _ hV := chartEquiv I J hJ k.2 hV
  equiv_map k _ _ hV hWV t := chartEquiv_map I J hJ k.2 hV hWV t
  equiv_agree k l _ hk hl t := chartEquiv_agree I J hJ k.2 l.2 hk hl t

/-- Part (3) of [Stacks, Tag 02OS] **for the blowup of an affine scheme**: on
`Proj (⨁ₙ Iⁿ)` of `Spec R` in an ideal `I`, the twisting sheaf `𝒪(1)` is the ideal sheaf of
the exceptional divisor, the inverse image of the centre.

The tag states part (3) for a blowup of an arbitrary scheme, so **no `@[stacks 02OS]` attribute
is attached here**: a registration may only sit on a declaration that proves the clause under the
source's hypotheses, and this one is restricted to an affine base. The unconditional statement,
which carries the registration, is `AlgebraicGeometry.twistOneIsoExceptionalIdealModule` in
`StacksFrontier/AlgebraicGeometry/Blowup/TwistOneExceptionalIdeal.lean`. Parts (1) and (2) are
registered for an arbitrary scheme, in `Blowup.IsomorphismOffCenter.Basic` and
`Blowup.ExceptionalCartier`. -/
def twistOneIsoExceptionalIdealSheaf (J : (Spec (CommRingCat.of R)).IdealSheafData)
    (hJ : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (J.ideal ⟨⊤, isAffineOpen_top _⟩) = I) :
    twistingSheaf (reesGrading I) 1 ≅ exceptionalIdealSheaf I J :=
  (twistOneLocalEquiv I J hJ).gluedIso

/-- Part (3) of [Stacks, Tag 02OS] for the blowup of an affine scheme, with no hypothesis: the
centre is the ideal sheaf on `Spec R` attached to `I` through
`AlgebraicGeometry.Scheme.ΓSpecIso`.

Untagged for the same reason as `twistOneIsoExceptionalIdealSheaf` above: the base is affine
where the source's is arbitrary. -/
def twistOneIsoExceptionalIdealSheafOfIdealTop :
    twistingSheaf (reesGrading I) 1 ≅
      exceptionalIdealSheaf I (Scheme.IdealSheafData.ofIdealTop
        (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom I)) :=
  twistOneIsoExceptionalIdealSheaf I _ (map_ideal_ofIdealTop_comap_eq I)

end Stacks.Blowup

end
