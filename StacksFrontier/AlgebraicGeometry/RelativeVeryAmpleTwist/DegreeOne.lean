module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ChartCocycleRigidity.DegreeOneIdentity
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 01VM: relative very ampleness, with the twist `𝒪_{𝐏(E)}(1)` named

Stacks Tag 01VM reads: an invertible `𝒪_X`-module `L` is *relatively very ample* for
`f : X ⟶ S` when there are a quasi-coherent `𝒪_S`-module `E` and an immersion `i : X ⟶ 𝐏(E)`
over `S` with `L ≅ i^* 𝒪_{𝐏(E)}(1)`. Both objects it names are now available over an arbitrary
base: the projective bundle is `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of `Sym(E)`,
and the degree-one twist on it is
`Stacks.AlgebraicGeometry.ChartCocycleRigidity.symGluedTwistOne`, which is unconditional for
quasi-coherent `E`. So the definition below *names* the twist instead of quantifying over a
characterisation of it.

## Main definitions

* `Stacks.Tag01VMVeryAmple.twistOne`: the twist `𝒪_{𝐏(E)}(1)` of the projective bundle of a
  quasi-coherent module, at the `relativeProj (symAlgebra E)` spelling.
* `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple`: **Stacks Tag 01VM.**
* `Stacks.Tag01VMVeryAmple.isInvertibleModule_modulesPullback`: the pullback of an invertible
  module along a morphism of schemes is invertible, as a scoped instance at the
  `AlgebraicGeometry.Scheme.Modules.pullback` spelling.

## Main results

* `Stacks.Tag01VMVeryAmple.isInvertibleModule_of_chartIso`: a module on a relative `Proj` that
  restricts on every affine chart to the absolute twist `𝒪(n)` is invertible, when the graded
  section ring over each affine open of the base is generated in degree one. This is Stacks Tag
  01O4 in a single degree, with no graded algebra and no twist datum.
* `Stacks.Tag01VMVeryAmple.isInvertibleModule_twistOne`: hence `𝒪_{𝐏(E)}(1)` is invertible.
* `Stacks.Tag01VMVeryAmple.isDegreeOneTwist_twistOne`: `𝒪_{𝐏(E)}(1)` is a degree-one twist in the
  sense of `Stacks.Tag01VMRelativeVeryAmple.IsDegreeOneTwist`, so Tag 01VM implies the local
  predicate already in the tree, and with it Tag 01VN's content.
* `Stacks.Tag01VMVeryAmple.isRelativelyAmple_of_isRelativelyVeryAmple`: relatively very ample
  implies relatively ample for a quasi-compact morphism, on
  `Stacks.Tag01VNChartBasis.ProjOneBasisClause` as its only premise.
* `Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_isIso`: relative very ampleness over a fixed
  base is carried along an isomorphism of the source.

## Implementation notes

**`𝐏(E)` is `(relativeProj (symAlgebra E)).scheme`.** That is the same scheme as
`(Stacks.SymGraded.schemeProjectiveBundle E _).scheme` — by `rfl`, recorded as
`Stacks.Tag01VMVeryAmple.schemeProjectiveBundle_eq` — and it is the spelling the twist and the
rest of the relative-`Proj` chart API are stated at, so no comparison is needed.
`Stacks.RelativeProj.projectiveBundle` is *not* this scheme: it belongs to the parallel
`Stacks.RelativeProj.Situation` development, whose relative `Proj` is glued by
`Stacks.RelativeProj.Situation.chartData`, and nothing in the tree identifies the two
constructions.

**The chart identification is restated at the `gluedTwist`/`twistingSheaf` spelling.**
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.chartIso` is stated through the fields of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelData`; `gluedChartIso` below is the same
isomorphism with its declared type written out, which is what both consumers here match against.
Its chart open-immersion instance is supplied by name, since the instance
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` does not fire at the
`modelData` spelling.

## What is not proved

**The converse to `isDegreeOneTwist_twistOne` is not available, and neither is
`Stacks.Tag01VNChartBasis.HasRelativeVeryAmpleTwist`.** The latter existentially quantifies over
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`, Stacks Tag 01NR's nine-field structure
carrying the twists in *all* integer degrees together with the multiplication, the unit and the
homogeneous-section map of the graded algebra `⨁ₙ 𝒪(n)`. A single degree-one twist does not
produce one: `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A n` is proved here
only at `n = 1`, degree-one rigidity being the only rigidity statement available without
multiplicativity. So Tag 01VM is *not* shown to imply that predicate, in either direction.

## References

* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.Tag01VMRelativeVeryAmple

universe u

namespace Stacks.Tag01VMVeryAmple

variable {S : Scheme.{u}}

/-! ### The chart identification of a glued twist, and invertibility from it -/

/-- **The chart identification of the glued twist**, at the spelling its consumers use: over an
affine open `U` of the base, the restriction of `gluedTwist A n hcoc` along the chart is the
absolute twist `𝒪(n)` of `Proj Γ(U, A)`. -/
def gluedChartIso (A : SheafGradedAlgebra S) (n : ℤ) (hcoc : IsNestedCocycle A n)
    (U : S.Opens) (hU : IsAffineOpen U) :
    Scheme.Modules.restrict (gluedTwist A n hcoc) ((relativeProj A).chart U hU) ≅
      twistingSheaf (A.grading U) n :=
  ChartTransRelativeProj.chartIso A n hcoc ⟨U, hU⟩
    (hchart := RelativeProjTwistGlue.isOpenImmersion_chart (relativeProj A) U hU)

/-- **Stacks Tag 01O4 in a single degree.** An `𝒪`-module on a relative `Proj` whose restriction
along the chart over every affine open `U` of the base is the absolute twist `𝒪(n)` of
`Proj Γ(U, A)` is invertible, as soon as each of those graded section rings is generated in
degree one over its degree-zero part.

This is `Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_piece` with the twist
datum replaced by the one family of chart isomorphisms its proof uses, so that it applies to a
twist in a single degree. -/
theorem isInvertibleModule_of_chartIso {A : SheafGradedAlgebra S}
    (M : (relativeProj A).scheme.Modules) (n : ℤ)
    (e : ∀ (U : S.Opens) (hU : IsAffineOpen U),
      Scheme.Modules.restrict M ((relativeProj A).chart U hU) ≅ twistingSheaf (A.grading U) n)
    (hgen : ∀ U : S.Opens, IsAffineOpen U →
      Algebra.adjoin (A.grading U 0) ((A.grading U 1 : Set (A.sectionRing U))) = ⊤) :
    IsInvertibleModule (relativeProj A).scheme M := by
  refine TwistMapsInvertible.isInvertibleModule_of_forall_exists_isoUnit_openImmersion M
    fun x => ?_
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)).ge
      (TopologicalSpace.Opens.mem_top x))
  have hoi : IsOpenImmersion ((relativeProj A).chart U.1 U.2) :=
    RelativeProjTwistGlue.isOpenImmersion_chart (relativeProj A) U.1 U.2
  have hrange : x ∈ ((relativeProj A).chart U.1 U.2).opensRange := by
    rw [← Scheme.Hom.image_top_eq_opensRange,
      RelativeProjTwistGlue.chart_image_top (relativeProj A) U.1 U.2]
    exact hxU
  obtain ⟨y, hy⟩ := hrange
  obtain ⟨V, hyV, ⟨eV⟩⟩ := TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin
    (A.grading U.1) (hgen U.1 U.2) n y
  refine ⟨V.toScheme, V.ι ≫ (relativeProj A).chart U.1 U.2, inferInstance,
    ⟨⟨y, hyV⟩, hy⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorComp V.ι ((relativeProj A).chart U.1 U.2)).app M ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapIso (e U.1 U.2) ≪≫ eV

/-! ### The twist `𝒪_{𝐏(E)}(1)` on a projective bundle -/

/-- **The twist `𝒪_{𝐏(E)}(1)` of the projective bundle of a quasi-coherent module `E`**, at the
`relativeProj (symAlgebra E)` spelling: the degree-one twists of the affine charts of
`Proj_S(Sym(E))`, glued along Stacks Tag 01NO's comparisons. -/
abbrev twistOne (E : S.Modules) [E.IsQuasicoherent] :
    (relativeProj (symAlgebra E)).scheme.Modules :=
  ChartCocycleRigidity.symGluedTwistOne E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)

/-- `𝐏(E) = Proj_S(Sym(E))` carries only one name here: the relative `Proj` of `Sym(E)` and
`Stacks.SymGraded.schemeProjectiveBundle` are the same relative `Proj` datum. -/
theorem schemeProjectiveBundle_eq (E : S.Modules) [E.IsQuasicoherent] :
    Stacks.SymGraded.schemeProjectiveBundle E
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E) =
      relativeProj (symAlgebra E) :=
  rfl

/-- **The chart identification of `𝒪_{𝐏(E)}(1)`**: over each affine open `U` of the base it
restricts along the chart to the absolute twist `𝒪(1)` of `Proj Γ(U, Sym(E))`. -/
def twistOneChartIso (E : S.Modules) [E.IsQuasicoherent] (U : S.Opens) (hU : IsAffineOpen U) :
    Scheme.Modules.restrict (twistOne E) ((relativeProj (symAlgebra E)).chart U hU) ≅
      twistingSheaf ((symAlgebra E).grading U) 1 :=
  gluedChartIso (symAlgebra E) 1
    (ChartCocycleRigidity.isNestedCocycle_one_sym E
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) U hU

/-- **`𝒪_{𝐏(E)}(1)` is an invertible `𝒪_{𝐏(E)}`-module**, Stacks Tag 01O4 in degree one: it is
the absolute twist `𝒪(1)` on each chart, and `Sym(E)` is generated in degree one over every
affine open of the base. -/
instance isInvertibleModule_twistOne (E : S.Modules) [E.IsQuasicoherent] :
    IsInvertibleModule (relativeProj (symAlgebra E)).scheme (twistOne E) :=
  isInvertibleModule_of_chartIso (twistOne E) 1 (twistOneChartIso E) (adjoin_symAlgebra_eq_top E)

/-! ### Stacks Tag 01VM -/

/-- **Stacks Tag 01VM: relative very ampleness.** An invertible `𝒪_X`-module `L` is *very ample
relative to* `f : X ⟶ S` when there are a quasi-coherent `𝒪_S`-module `E` and an immersion
`i : X ⟶ 𝐏(E) = Proj_S(Sym(E))` over `S` with `L ≅ i^* 𝒪_{𝐏(E)}(1)`. -/
@[stacks 01VM, ega "II 4.4.2"]
def IsRelativelyVeryAmple {X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Prop :=
  ∃ (E : S.Modules) (hE : E.IsQuasicoherent),
    have := hE
    ∃ i : X ⟶ (relativeProj (symAlgebra E)).scheme,
      IsImmersion i ∧ i ≫ (relativeProj (symAlgebra E)).toBase = f ∧
        Nonempty (L ≅ (Scheme.Modules.pullback i).obj (twistOne E))

/-- **The introduction rule for relative very ampleness**: a quasi-coherent `E`, an immersion
into `𝐏(E)` over the base, and an isomorphism of `L` with the pullback of `𝒪_{𝐏(E)}(1)`. -/
theorem isRelativelyVeryAmple_of_immersion {X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (E : S.Modules) [hE : E.IsQuasicoherent]
    (i : X ⟶ (relativeProj (symAlgebra E)).scheme) (him : IsImmersion i)
    (hover : i ≫ (relativeProj (symAlgebra E)).toBase = f)
    (e : L ≅ (Scheme.Modules.pullback i).obj (twistOne E)) :
    IsRelativelyVeryAmple f L :=
  ⟨E, hE, i, him, hover, ⟨e⟩⟩

/-- **Relative very ampleness over a fixed base is carried along an isomorphism of the source.**
If `L` is very ample for `f : X ⟶ S`, `p : X' ⟶ X` is an isomorphism and `L'` is an invertible
`𝒪_{X'}`-module isomorphic to `p^* L`, then `L'` is very ample for `p ≫ f : X' ⟶ S`: the
immersion `i : X ⟶ 𝐏(E)` over `S` is replaced by `p ≫ i`, which is again an immersion and again
lies over `p ≫ f`, and `L' ≅ p^* L ≅ p^* i^* 𝒪_{𝐏(E)}(1) ≅ (p ≫ i)^* 𝒪_{𝐏(E)}(1)`. -/
theorem isRelativelyVeryAmple_of_isIso {X X' : Scheme.{u}} (p : X' ⟶ X) [IsIso p] (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (L' : X'.Modules) [IsInvertibleModule X' L']
    (e : L' ≅ (Scheme.Modules.pullback p).obj L) (h : IsRelativelyVeryAmple f L) :
    IsRelativelyVeryAmple (p ≫ f) L' := by
  obtain ⟨E, hE, i, him, hover, ⟨eL⟩⟩ := h
  have := hE
  have := him
  refine ⟨E, hE, p ≫ i, inferInstance, ?_, ⟨?_⟩⟩
  · rw [Category.assoc, hover]
  · exact e ≪≫ (Scheme.Modules.pullback p).mapIso eL ≪≫
      (Scheme.Modules.pullbackComp p i).app (twistOne E)

/-! ### Comparison with the local degree-one-twist predicate -/

/-- **The glued degree-one twist is the absolute twist `𝒪(1)` on the inverse image of each affine
open of the base**, in the module-pullback spelling.

This is `Stacks.Tag01VNChartBasis.chartTwistIso` with the degree-one piece of a twist datum
replaced by `gluedTwist A 1 hcoc`; the two passages between
`AlgebraicGeometry.Scheme.Modules.restrict` and
`RingedSpaceModuleAdjunction.modulePullback` are the same. -/
def chartTwistOneIsoPreimage (A : SheafGradedAlgebra S) (hcoc : IsNestedCocycle A 1)
    (V : S.Opens) (hV : IsAffineOpen V) :
    (Scheme.Modules.pullback (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).obj
        (twistingSheaf (A.grading V) 1) ≅
      (Scheme.Modules.pullback ((relativeProj A).toBase ⁻¹ᵁ V).ι).obj (gluedTwist A 1 hcoc) :=
  letI := RelativeProjTwistGlue.isOpenImmersion_chart (relativeProj A) V hV
  ((Scheme.Modules.restrictFunctorIsoPullback
        (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).app
      (twistingSheaf (A.grading V) 1)).symm ≪≫
    (Scheme.Modules.restrictFunctor
        (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV).hom).mapIso
      (gluedChartIso A 1 hcoc V hV).symm ≪≫
    AlgebraicGeometry.ProjectiveSpectrum.Proj.restrictIsoOfIsoOver (gluedTwist A 1 hcoc)
      ((relativeProj A).chart V hV) ((relativeProj A).toBase ⁻¹ᵁ V)
      (RelativeProjTwistQcoh.chartIsoPreimage (A := A) V hV)
      (RelativeProjTwistQcoh.chartIsoPreimage_hom_comp V hV) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).toBase ⁻¹ᵁ V).ι).app
      (gluedTwist A 1 hcoc)

/-- **`𝒪_{𝐏(E)}(1)` is a degree-one twist** in the sense of
`Stacks.Tag01VMRelativeVeryAmple.IsDegreeOneTwist`, which pins a module on `𝐏(E)` only over the
inverse image of each affine open of the base. -/
theorem isDegreeOneTwist_twistOne (E : S.Modules) [E.IsQuasicoherent] :
    IsDegreeOneTwist (symAlgebra E) (twistOne E) :=
  fun V hV => ⟨chartTwistOneIsoPreimage (symAlgebra E)
    (ChartCocycleRigidity.isNestedCocycle_one_sym E
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) V hV⟩

/-- **Stacks Tag 01VM implies the local predicate `IsRelativelyVeryAmple` of
`RelativeVeryAmpleTwist/Basic.lean`**, whose twist is quantified over rather than named: the
named twist `𝒪_{𝐏(E)}(1)` is invertible and is a degree-one twist, hence one of the modules that
predicate quantifies over. -/
theorem isRelativelyVeryAmple_isDegreeOneTwist {X : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (h : IsRelativelyVeryAmple f L) :
    Stacks.Tag01VMRelativeVeryAmple.IsRelativelyVeryAmple f L := by
  obtain ⟨E, hE, i, him, hover, ⟨e⟩⟩ := h
  have := hE
  exact ⟨E, hE, twistOne E, isInvertibleModule_twistOne E, isDegreeOneTwist_twistOne E,
    i, him, hover, ⟨e⟩⟩

/-! ### The first consequence: relatively very ample implies relatively ample -/

/-- **Stacks Tag 01VN against the named twist**: a quasi-compact morphism and a relatively very
ample invertible module give a relatively ample one, on
`Stacks.Tag01VNChartBasis.ProjOneBasisClause` as the only premise beyond the source's. -/
theorem isRelativelyAmple_of_isRelativelyVeryAmple
    (hclause : Stacks.Tag01VNChartBasis.ProjOneBasisClause.{u, u}) {X : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : IsRelativelyVeryAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.Tag01VMRelativeVeryAmple.isRelativelyAmple_of_isRelativelyVeryAmple hclause f L hf
    (isRelativelyVeryAmple_isDegreeOneTwist f L h)

/-! ### Invertibility of pullbacks -/

/-- **Stacks Tag 0B8L at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling**: the pullback
of an invertible `𝒪_Y`-module along `h : X ⟶ Y` is an invertible `𝒪_X`-module.

`Stacks.InvertiblePullback.isInvertibleModule_pullback` is the same assertion for
`RingedSpaceModuleAdjunction.modulePullback` of the underlying morphism of ringed spaces, which
for a morphism of schemes is the same functor but which instance search does not match against
`AlgebraicGeometry.Scheme.Modules.pullback`. The invertible module whose very ampleness
Stacks Tag 0B3F asserts is a pullback along a bound morphism, so its statement cannot be written
without this instance. It is `scoped` so that a
second route to invertibility of a pullback is not added to global instance search; a consumer
writes `open scoped Stacks.Tag01VMVeryAmple`. -/
scoped instance isInvertibleModule_modulesPullback {X Y : Scheme.{u}} (h : X ⟶ Y)
    (M : Y.Modules) [IsInvertibleModule Y M] :
    IsInvertibleModule X ((Scheme.Modules.pullback h).obj M) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback h M

end Stacks.Tag01VMVeryAmple

end
