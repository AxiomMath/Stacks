module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal

/-!
# The canonical global section of the determinant on an arbitrary scheme

Let `X` be a scheme and `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` of rank
zero. `AlgebraicGeometry.DeterminantTwoTerm.determinantSection` is the canonical global section
`δ(L)` of the determinant of `L` on `X`, glued from the canonical elements of More on Algebra,
Section 0FJI on the affine charts. This file proves the two remaining assertions of
[Stacks, Tag 0FJX] about it: that it is **compatible with isomorphisms**, `det(a)(δ(L)) = δ(K)`,
and that it is **affine locally the canonical element of More on Algebra, Section 0FJI** — on an
affine open `V` of `X` it is the determinant of the differential of any two-term finite-projective
presentation of the complex of `Γ(X, V)`-modules that `L` restricts to on the chart of `V`.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictPresentationIso`: the determinant of `L`
  on an affine open `V`, identified with the *restriction* along
  `AlgebraicGeometry.IsAffineOpen.isoSpec` of the sheaf associated with the determinant line of
  More on Algebra, Section 0FJI of a two-term finite-projective presentation of the chart complex.

## Main results

* `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec_glueHom` and
  `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec_glueIso`: **reading a glued morphism
  on a chart.** A section of the first glued module, pushed through the morphism glued from a
  compatible family and read on the chart of an affine open, is the member of the family applied to
  the reading of the section on that chart.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetIso_chartDeltaTop`: the determinant of an
  isomorphism carries the canonical global section of the determinant on an affine open to the
  canonical global section there.
* `AlgebraicGeometry.DeterminantTwoTerm.chartSec_globalDetIso`: the determinant of an isomorphism
  on an arbitrary scheme reads on an affine chart as the determinant of that isomorphism there.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetPresentationIso_eq`: the affine-local comparison
  used here and `AlgebraicGeometry.DeterminantTwoTerm.chartDetPresentationIso` differ by the
  identification of the restriction along `AlgebraicGeometry.IsAffineOpen.isoSpec` with the
  pullback along it.
* `AlgebraicGeometry.DeterminantTwoTerm.determinantFunctor_map_determinantSection`: **[Stacks, Tag
  0FJX], part (2), on an arbitrary scheme**: for every isomorphism `a : L ⟶ K` of rank-zero perfect
  objects of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`, `det(a)(δ(L)) = δ(K)`.
* `AlgebraicGeometry.DeterminantTwoTerm.determinantChartPresentationIso_determinantSection`:
  **[Stacks, Tag 0FJX], part (3), on an arbitrary scheme**: the canonical global section `δ(L)`,
  restricted to an affine open `V` and read on the chart of `V` through
  `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictPresentationIso`, is the canonical element
  `TwoTermComplex.delta` of More on Algebra, Section 0FJI of the presentation, read as a global
  section of the associated sheaf.

## Implementation notes

The kernel does not reconcile two spellings of one module twice in a single term, so each
definitional step is a one-line lemma of its own, stated on variables wherever possible.

*The affine-local description.* The comparison used for part (3) is
`chartDetRestrictPresentationIso`, which lands in the *restriction* along `isoSpec` of the
associated sheaf rather than in the pullback. That is what makes the right-hand side the canonical
element of More on Algebra, Section 0FJI with nothing interposed: a section of a restriction over
an open of `V` is a section of the sheaf on `Spec Γ(X, V)` over its image, so the statement is an
equality of sections of the associated sheaf of the determinant line itself. The comparison with
the pullback is `AlgebraicGeometry.DeterminantTwoTerm.chartDetPresentationIso`, and the two differ
by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetPresentationIso_eq`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
-/


@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant Opposite
open Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Reading a glued morphism on a chart -/

namespace AffineOpensGlue.ChartComparison

/-- **Reading a glued morphism on a chart.** Let `D` and `D'` be glueing data on the affine opens
of `X` and `α` a family of morphisms on the charts compatible with their comparisons. Over an open
`O` inside an affine open `V`, the glued morphism followed by the reading on the chart of `V` is
the reading on that chart followed by the pushforward of the member of the family at `V`. -/
theorem chartSec_glueHom (D D' : ChartComparison X)
    (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V) (hα : IsCompatible α) (V : X.affineOpens)
    {O : X.Opens} (hO : O ≤ (V.1 : X.Opens)) (x : ToType (D.glued.val.obj (op O))) :
    D'.chartSec V O (Scheme.Modules.Hom.app (D.glueHom D' α hα) O x) =
      pushSec V (α V) O (D.chartSec V O x) := by
  have e1 : Scheme.Modules.Hom.app (D.glueHom D' α hα) O x =
      localAppFun (D.localHom D' α V) O hO x :=
    (localAppFun_restrictFunctor_map (W := (V.1 : X.Opens)) (D.glueHom D' α hα) hO x).symm.trans
      (congrArg (fun φ => localAppFun φ O hO x) (D.restrictFunctor_map_glueHom D' α hα V))
  rw [e1, D.localAppFun_localHom D' α V hO x, D'.chartSec_localAppFun_chartHomIso_inv V hO]

/-- `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec_glueHom` for a compatible family
of *isomorphisms*: the glued isomorphism reads on the chart of an affine open as the member of the
family there. -/
theorem chartSec_glueIso (D D' : ChartComparison X)
    (α : ∀ V : X.affineOpens, D.mod V ≅ D'.mod V) (hα : IsCompatible (fun V => (α V).hom))
    (V : X.affineOpens) {O : X.Opens} (hO : O ≤ (V.1 : X.Opens))
    (x : ToType (D.glued.val.obj (op O))) :
    D'.chartSec V O (Scheme.Modules.Hom.app (D.glueIso D' α hα).hom O x) =
      pushSec V (α V).hom O (D.chartSec V O x) :=
  D.chartSec_glueHom D' (fun V => (α V).hom) hα V hO x

end AffineOpensGlue.ChartComparison

namespace DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Section calculus at a chart

The calculus that does not mention a chart is in
`StacksFrontier.AlgebraicGeometry.DeterminantTwoTermSectionCalculus`. -/

/-- The sections map of the pushforward along the chart of an affine open of a morphism there is
the component of that morphism at the preimage open. -/
private theorem pushSec_eq_app (V : X.affineOpens)
    {M N : ((V.1 : X.Opens) : Scheme.{u}).Modules} (φ : M ⟶ N) (O : X.Opens)
    (s : ToType (((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj M).val.obj
      (op O))) :
    AffineOpensGlue.pushSec V φ O s =
      Scheme.Modules.Hom.app φ ((V.1 : X.Opens).ι ⁻¹ᵁ O) s := rfl

/-! ### The insides of the chart-level data, named -/

/-- The determinant of an isomorphism on an affine chart is the pullback along
`AlgebraicGeometry.IsAffineOpen.isoSpec` of the determinant of that isomorphism on the spectrum.
This is the definition of `AlgebraicGeometry.DeterminantTwoTerm.chartDetIso`, recorded as an
equality of *isomorphisms*. -/
private theorem chartDetIso_eq {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    (V : X.affineOpens) :
    chartDetIso a V = (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso
      (chartDetSpecOfEquiv V (detLinearEquivOfIso (chartComplexIso a V))) :=
  rfl

/-- The canonical global section of the determinant on an affine open is the canonical element on
the spectrum, restricted to the image of the top open and read through
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrictIso`. This is the definition of
`AlgebraicGeometry.DeterminantTwoTerm.chartDeltaTop`. -/
private theorem chartDeltaTop_eq_app {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) :
    chartDeltaTop hL V =
      Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤
        (globalRes (chartDetSpec L V)
          (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens))
          (chartDelta hL V)) :=
  rfl

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDeltaTop_eq_app` with
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrictIso` spelled as the component of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` that it is. -/
private theorem chartDeltaTop_eq_isoPullback_app {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) (V : X.affineOpens) :
    chartDeltaTop hL V =
      Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback V.2.isoSpec.hom).app
          (chartDetSpec L V)).hom ⊤
        (globalRes (chartDetSpec L V)
          (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens))
          (chartDelta hL V)) :=
  rfl

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection` is the canonical global section of the
determinant on an affine open, restricted to the preimage of that open in itself. This is
`AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection_eq`, with the restriction named. -/
private theorem chartDeltaSection_eq_globalRes {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) (V : X.affineOpens) :
    chartDeltaSection hL V =
      globalRes (chartDet L V) ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartDeltaTop hL V) :=
  rfl

/-! ### The determinant of an isomorphism on the canonical global section of a chart -/

/-- The image of an isomorphism under a restriction functor commutes with the restriction of a
global section to the image of the top open. -/
private theorem restrictFunctor_mapIso_app_globalRes {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] {M N : Z.Modules} (i : M ≅ N) (s : ToType (M.val.obj (op ⊤))) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor f).mapIso i).hom ⊤
        (globalRes M (f ''ᵁ ⊤) s) =
      globalRes N (f ''ᵁ ⊤) (Scheme.Modules.Hom.app i.hom ⊤ s) :=
  (restrictFunctor_mapIso_apply f i ⊤ _).trans (app_globalRes _ _ s)

/-- **The determinant of an isomorphism carries the canonical global section of the determinant on
an affine open to the canonical global section there.** For an isomorphism `a : L ≅ K` of rank-zero
perfect objects of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and an affine open `V` of `X`, the
isomorphism `AlgebraicGeometry.DeterminantTwoTerm.chartDetIso` of the determinants on `V` carries
`AlgebraicGeometry.DeterminantTwoTerm.chartDeltaTop` to `chartDeltaTop`. -/
theorem chartDetIso_chartDeltaTop {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    (hL : IsRankZeroOn L) (hK : IsRankZeroOn K) (V : X.affineOpens) :
    Scheme.Modules.Hom.app (chartDetIso a V).hom ⊤ (chartDeltaTop hL V) = chartDeltaTop hK V := by
  have hspec : Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapIso
        (chartDetSpecOfEquiv V (detLinearEquivOfIso (chartComplexIso a V)))).hom ⊤
      (globalRes (chartDetSpec L V)
        (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens)) (chartDelta hL V)) =
      globalRes (chartDetSpec K V)
        (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens)) (chartDelta hK V) :=
    (restrictFunctor_mapIso_app_globalRes V.2.isoSpec.hom _ _).trans
      (congrArg (globalRes (chartDetSpec K V)
          (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens)))
        (chartDetSpecIso_chartDelta a hL hK V))
  rw [chartDetIso_eq a V, chartDeltaTop_eq_isoPullback_app hL V,
    chartDeltaTop_eq_isoPullback_app hK V]
  exact (app_mapIso_naturality (Scheme.Modules.restrictFunctorIsoPullback V.2.isoSpec.hom)
    (chartDetSpecOfEquiv V (detLinearEquivOfIso (chartComplexIso a V))) ⊤ _).trans
    (congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback V.2.isoSpec.hom).app
        (chartDetSpec K V)).hom ⊤ z) hspec)

/-- **The determinant of an isomorphism carries the canonical chart section to the canonical chart
section.** This is `AlgebraicGeometry.DeterminantTwoTerm.chartDetIso_chartDeltaTop`, read on the
chart of `V`. -/
private theorem pushSec_chartDetIso_chartDeltaSection {L K : PerfectTwoTermAmplitude X}
    (a : L.obj ≅ K.obj) (hL : IsRankZeroOn L) (hK : IsRankZeroOn K) (V : X.affineOpens) :
    AffineOpensGlue.pushSec V (chartDetIso a V).hom (V.1 : X.Opens) (chartDeltaSection hL V) =
      chartDeltaSection hK V := by
  refine Eq.trans (pushSec_eq_app V (chartDetIso a V).hom (V.1 : X.Opens)
    (chartDeltaSection hL V)) ?_
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app (chartDetIso a V).hom
      ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) z) (chartDeltaSection_eq_globalRes hL V)) ?_
  refine Eq.trans (app_globalRes (chartDetIso a V).hom
    ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartDeltaTop hL V)) ?_
  exact (congrArg (fun z => globalRes (chartDet K V)
      ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) z) (chartDetIso_chartDeltaTop a hL hK V)).trans
    (chartDeltaSection_eq_globalRes hK V).symm

/-! ### The compatibility of the canonical global section with isomorphisms -/

/-- `AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartSec_glueHom` for a global section,
restricted to an affine open. -/
private theorem chartSec_glueHom_globalRes (D D' : AffineOpensGlue.ChartComparison X)
    (α : ∀ V : X.affineOpens, D.mod V ⟶ D'.mod V)
    (hα : AffineOpensGlue.ChartComparison.IsCompatible α) (V : X.affineOpens)
    (t : ToType (D.glued.val.obj (op (⊤ : X.Opens)))) :
    D'.chartSec V (V.1 : X.Opens)
        (globalRes D'.glued (V.1 : X.Opens)
          (Scheme.Modules.Hom.app (D.glueHom D' α hα) ⊤ t)) =
      AffineOpensGlue.pushSec V (α V) (V.1 : X.Opens)
        (D.chartSec V (V.1 : X.Opens) (globalRes D.glued (V.1 : X.Opens) t)) := by
  refine Eq.trans (congrArg (fun z => D'.chartSec V (V.1 : X.Opens) z)
    (app_globalRes (D.glueHom D' α hα) (V.1 : X.Opens) t).symm) ?_
  exact D.chartSec_glueHom D' α hα V le_rfl (globalRes D.glued (V.1 : X.Opens) t)

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartSec_glueHom_globalRes` for a compatible family of
isomorphisms. -/
private theorem chartSec_glueIso_globalRes (D D' : AffineOpensGlue.ChartComparison X)
    (α : ∀ V : X.affineOpens, D.mod V ≅ D'.mod V)
    (hα : AffineOpensGlue.ChartComparison.IsCompatible (fun V => (α V).hom))
    (V : X.affineOpens) (t : ToType (D.glued.val.obj (op (⊤ : X.Opens)))) :
    D'.chartSec V (V.1 : X.Opens)
        (globalRes D'.glued (V.1 : X.Opens)
          (Scheme.Modules.Hom.app (D.glueIso D' α hα).hom ⊤ t)) =
      AffineOpensGlue.pushSec V (α V).hom (V.1 : X.Opens)
        (D.chartSec V (V.1 : X.Opens) (globalRes D.glued (V.1 : X.Opens) t)) :=
  chartSec_glueHom_globalRes D D' (fun V => (α V).hom) hα V t

/-- The determinant of an isomorphism is the isomorphism glued from the determinants of that
isomorphism on the affine charts. This is the definition of
`AlgebraicGeometry.DeterminantTwoTerm.globalDetIso`, recorded as an equality of
*isomorphisms*. -/
private theorem globalDetIso_eq {L K : PerfectTwoTermAmplitude X} (b : L.obj ≅ K.obj) :
    globalDetIso b = (chartComparison L).glueIso (chartComparison K)
      (fun V => chartDetIso b V) (isCompatible_chartDetIso b) :=
  rfl

/-- **The determinant of an isomorphism reads on an affine chart as the determinant of that
isomorphism there.** A global section of the determinant of `L`, pushed through the determinant of
`b : L ≅ K` and read on the chart of an affine open `V`, is the determinant of `b` on the chart of
`V` applied to the reading of the section there. -/
theorem chartSec_globalDetIso {L K : PerfectTwoTermAmplitude X} (b : L.obj ≅ K.obj)
    (V : X.affineOpens) (t : ToType ((chartComparison L).glued.val.obj (op (⊤ : X.Opens)))) :
    (chartComparison K).chartSec V (V.1 : X.Opens)
        ((chartComparison K).glued.val.map (homOfLE le_top).op
          (Scheme.Modules.Hom.app (globalDetIso b).hom ⊤ t)) =
      AffineOpensGlue.pushSec V (chartDetIso b V).hom (V.1 : X.Opens)
        ((chartComparison L).chartSec V (V.1 : X.Opens)
          ((chartComparison L).glued.val.map (homOfLE le_top).op t)) := by
  rw [globalDetIso_eq b]
  exact chartSec_glueIso_globalRes (chartComparison L) (chartComparison K)
    (fun V => chartDetIso b V) (isCompatible_chartDetIso b) V t

/-- The determinant functor sends an isomorphism to the determinant of the underlying isomorphism
of `D(𝒪_X)`. This is the definition of
`AlgebraicGeometry.DeterminantTwoTerm.determinantFunctor` on morphisms. -/
private theorem ι_map_determinantFunctor_map {L K : PerfectTwoTermAmplitude X}
    (a : (⟨L⟩ : Core (PerfectTwoTermAmplitude X)) ⟶ ⟨K⟩) :
    (IsInvertibleProperty X).ι.map ((determinantFunctor X).map a).iso.hom =
      (globalDetIso ((IsPerfectTwoTermAmplitude X).ι.mapIso a.iso)).hom :=
  rfl

/-- **The determinant of an isomorphism carries the canonical global section to the canonical chart
section on every affine chart.** -/
private theorem chartSec_determinantFunctor_map {L K : PerfectTwoTermAmplitude X}
    (a : (⟨L⟩ : Core (PerfectTwoTermAmplitude X)) ⟶ ⟨K⟩) (hL : IsRankZeroOn L)
    (hK : IsRankZeroOn K) (V : X.affineOpens) :
    (chartComparison K).chartSec V (V.1 : X.Opens)
        ((chartComparison K).glued.val.map (homOfLE le_top).op
          (Scheme.Modules.Hom.app
            ((IsInvertibleProperty X).ι.map ((determinantFunctor X).map a).iso.hom) ⊤
            (determinantSection hL))) =
      chartDeltaSection hK V := by
  rw [ι_map_determinantFunctor_map a]
  refine Eq.trans (chartSec_globalDetIso ((IsPerfectTwoTermAmplitude X).ι.mapIso a.iso) V
    (determinantSection hL)) ?_
  refine Eq.trans (congrArg (fun z => AffineOpensGlue.pushSec V
      (chartDetIso ((IsPerfectTwoTermAmplitude X).ι.mapIso a.iso) V).hom (V.1 : X.Opens) z)
    (determinantSection_chartSec hL V)) ?_
  exact pushSec_chartDetIso_chartDeltaSection
    ((IsPerfectTwoTermAmplitude X).ι.mapIso a.iso) hL hK V

/-- For every isomorphism `a : L ⟶ K` of rank-zero perfect objects of `D(𝒪_X)` of Tor-amplitude in
`[-1, 0]` on an arbitrary scheme `X`, the determinant of `a` carries the canonical global section
of the determinant of `L` to that of `K`: `det(a)(δ(L)) = δ(K)`. -/
@[stacks 0FJX "part (2): the compatibility det(a)(δ(L)) = δ(K) of the canonical global section with
isomorphisms, on an arbitrary scheme"]
theorem determinantFunctor_map_determinantSection {L K : PerfectTwoTermAmplitude X}
    (a : (⟨L⟩ : Core (PerfectTwoTermAmplitude X)) ⟶ ⟨K⟩)
    (hL : IsRankZeroOn L) (hK : IsRankZeroOn K) :
    Scheme.Modules.Hom.app
        ((IsInvertibleProperty X).ι.map ((determinantFunctor X).map a).iso.hom) ⊤
        (determinantSection hL) = determinantSection hK :=
  (chartComparison K).section_ext fun V =>
    (chartSec_determinantFunctor_map a hL hK V).trans (determinantSection_chartSec hK V).symm

/-! ### The affine-local description of the canonical global section -/

/-- **The determinant of `L` on an affine open is the restriction along
`AlgebraicGeometry.IsAffineOpen.isoSpec` of the determinant line of a presentation of the chart
complex.** For an affine open `V` of `X` and a two-term finite-projective presentation `P` of the
complex of `Γ(X, V)`-modules attached to `L` there, the determinant of `L` on `V` is the
restriction along `isoSpec` of the sheaf associated with the determinant line of More on Algebra,
Section 0FJI of `P`.

This is `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrictIso`, read backwards, followed by
the image under the restriction functor of
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPresentationIso`. -/
def chartDetRestrictPresentationIso (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    chartDet L V ≅
      Scheme.Modules.restrict (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom))) V.2.isoSpec.hom :=
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  (chartDetSpecRestrictIso L V).symm ≪≫
    (Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapIso (chartDetSpecPresentationIso L V P)

/-- The image of an isomorphism under a functor, conjugated by a natural isomorphism to another
functor, is its image under that other functor. -/
private theorem mapIso_eq_conj {Y Z : Scheme.{u}} {F G : Z.Modules ⥤ Y.Modules} (ν : F ≅ G)
    {M N : Z.Modules} (χ : M ≅ N) :
    G.mapIso χ = ((ν.app M).symm ≪≫ F.mapIso χ) ≪≫ ν.app N :=
  Iso.ext (by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
      Category.assoc, ν.hom.naturality χ.hom, Iso.inv_hom_id_app_assoc])

/-- **The two forms of the affine-local comparison agree.**
`AlgebraicGeometry.DeterminantTwoTerm.chartDetPresentationIso`, the affine-local description of
[Stacks, Tag 0FJX] in the pullback form, is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictPresentationIso` followed by the
identification `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` of the restriction
along `AlgebraicGeometry.IsAffineOpen.isoSpec` with the pullback along it. -/
theorem chartDetPresentationIso_eq (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    chartDetPresentationIso L V P =
      chartDetRestrictPresentationIso L V P ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback V.2.isoSpec.hom).app
          (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
            (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom))) := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  exact mapIso_eq_conj (Scheme.Modules.restrictFunctorIsoPullback V.2.isoSpec.hom)
    (chartDetSpecPresentationIso L V P)

/-- **The canonical global section of the determinant on an affine open is the canonical element of
a presentation.** The comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictPresentationIso` carries
`AlgebraicGeometry.DeterminantTwoTerm.chartDeltaTop` to the determinant of the differential of `P`,
read as a global section of the associated sheaf and restricted to the image of the top open. -/
private theorem chartDetRestrictPresentationIso_chartDeltaTop {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) (hP : P.IsRankZero) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    Scheme.Modules.Hom.app (chartDetRestrictPresentationIso L V P).hom ⊤
        (chartDeltaTop hL V) =
      globalRes (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)))
        (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens))
        ((tilde.toOpen (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤).hom
          (TwoTermComplex.delta (P.complex.d (-1) 0).hom hP)) := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  have hsymm : Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).symm.hom ⊤
      (chartDeltaTop hL V) =
      globalRes (chartDetSpec L V)
        (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens)) (chartDelta hL V) :=
    symm_hom_app_apply_eq (chartDetSpecRestrictIso L V) ⊤ _ _
      (chartDeltaTop_eq_app hL V).symm
  have hpres : Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapIso
        (chartDetSpecPresentationIso L V P)).hom ⊤
      (globalRes (chartDetSpec L V)
        (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens)) (chartDelta hL V)) =
      globalRes (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)))
        (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens))
        ((tilde.toOpen (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤).hom
          (TwoTermComplex.delta (P.complex.d (-1) 0).hom hP)) :=
    (restrictFunctor_mapIso_app_globalRes V.2.isoSpec.hom _ _).trans
      (congrArg (globalRes (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
            (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)))
          (V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens)))
        (chartDetSpecPresentationIso_chartDelta hL V P hP))
  refine Eq.trans (twoIsoHom_app (chartDetSpecRestrictIso L V).symm
    ((Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapIso
      (chartDetSpecPresentationIso L V P)) ⊤ (chartDeltaTop hL V)) ?_
  exact (congrArg (fun z => Scheme.Modules.Hom.app
    ((Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapIso
      (chartDetSpecPresentationIso L V P)).hom ⊤ z) hsymm).trans hpres

/-- Let `X` be a scheme, `L` a rank-zero perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`,
`V` an affine open of `X` and `P` a rank-zero two-term finite-projective presentation of the
complex of `Γ(X, V)`-modules that `L` restricts to on the chart of `V`. Then the canonical global
section `δ(L)` of the determinant of `L`, restricted to `V` and read on the chart of `V` through
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictPresentationIso`, is the canonical element of
More on Algebra, Section 0FJI of `P` — the determinant of the differential of `P` — read as a
global section of the associated sheaf of the determinant line and restricted to the image open.

So the construction is affine locally the one of More on Algebra, Section 0FJI, canonical element
included: `δ(L)` reads on an affine open as `TwoTermComplex.delta` of the differential of any
two-term finite-projective presentation there. -/
@[stacks 0FJX "part (3): the canonical global section is affine locally the canonical element of
More on Algebra, Section 0FJI — on an affine open of an arbitrary scheme it is the determinant of
the differential of a two-term finite-projective presentation"]
theorem determinantChartPresentationIso_determinantSection {L : PerfectTwoTermAmplitude X}
    (hL : IsRankZeroOn L) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) (hP : P.IsRankZero) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    Scheme.Modules.Hom.app (chartDetRestrictPresentationIso L V P).hom
        ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens))
        ((chartComparison L).chartSec V (V.1 : X.Opens)
          ((chartComparison L).glued.val.map (homOfLE le_top).op (determinantSection hL))) =
      (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom))).val.map
        (homOfLE (le_top :
          V.2.isoSpec.hom ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) ≤ ⊤)).op
        ((tilde.toOpen (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom)) ⊤).hom
          (TwoTermComplex.delta (P.complex.d (-1) 0).hom hP)) := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  have hI : V.2.isoSpec.hom ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) ≤
      V.2.isoSpec.hom ''ᵁ (⊤ : ((V.1 : X.Opens) : Scheme.{u}).Opens) :=
    V.2.isoSpec.hom.image_mono le_top
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
      (chartDetRestrictPresentationIso L V P).hom ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) z)
    (determinantSection_chartSec hL V)) ?_
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
      (chartDetRestrictPresentationIso L V P).hom ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) z)
    (chartDeltaSection_eq_globalRes hL V)) ?_
  refine Eq.trans (app_globalRes (chartDetRestrictPresentationIso L V P).hom
    ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartDeltaTop hL V)) ?_
  refine Eq.trans (congrArg (fun z => globalRes
      (Scheme.Modules.restrict (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
        (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom))) V.2.isoSpec.hom)
      ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) z)
    (chartDetRestrictPresentationIso_chartDeltaTop hL V P hP)) ?_
  exact (restrict_resSec V.2.isoSpec.hom _
      (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤) hI _).trans
    (resSec_globalRes _ hI _)

end DeterminantTwoTerm

end AlgebraicGeometry

end
