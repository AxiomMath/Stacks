module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.MapDomain
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.ProjPoly
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.TerminalPullback
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.FreeChart

/-!
# `ℙⁿ_X` is the projective bundle of `𝒪_X^{n+1}`

**Stacks Tag 01OE**: `ℙⁿ_S` is a projective bundle over `S`, namely
`ℙ(𝒪_S^{n+1}) = Proj_S(Sym(𝒪_S^{n+1}))`.  This file builds the comparison morphism over an
**arbitrary** base scheme and proves that it is an isomorphism over that base.

The route avoids base change of the relative homogeneous spectrum. Tag 01O3 is carried, by
`Stacks.RelativeProj.Situation.relativeProjBaseChangeIso`, but it takes as its input an
identification of the graded algebra over the new base with the pullback of the one over the old
base, and that identification is not available for the symmetric algebra used here.
`Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProj` is literally a colimit of its affine
charts, so a **cocone** of chart comparisons gives a morphism out of it with no cofinality
question; and `ℙⁿ_X` is by definition the pullback `X ×_{Spec ℤ} ℙⁿ_ℤ`, so a morphism into it
is a pair of morphisms with a commuting square, and the square commutes because both composites
land in the terminal scheme.

## Main definitions

* `Stacks.SymGraded.coordGradedHom` and `Stacks.SymGraded.chartCoordHom`: **the homogeneous
  coordinates.** The integral polynomial ring `ℤ[T₀, …, Tₙ]` maps to the graded ring of
  homogeneous sections of `Sym(𝒪_X^{n+1})` over an open `U`, sending `Tᵢ` to the `i`-th
  coordinate section; the first homomorphism changes the coefficients and reindexes the
  variables, the second is `Stacks.SymGraded.chartGradedHom`.
* `Stacks.SymGraded.chartToProjectiveSpace`: the induced morphism
  `Proj Γ(U, Sym(𝒪_X^{n+1})) ⟶ ℙⁿ_ℤ`.
* `Stacks.SymGraded.projectiveSpaceCocone`: those morphisms as a cocone on the chart functor.
* `Stacks.SymGraded.freeProjectiveBundle`: the projective bundle `ℙ(𝒪_X^{n+1})`, with its
  projection to `X` and its charts.
* `Stacks.SymGraded.projectiveBundleToProjectiveSpace`: **the comparison morphism
  `ℙ(𝒪_X^{n+1}) ⟶ ℙⁿ_X`, over `X`.**
* `Stacks.SymGraded.chartIsoProjPoly`: **a chart of the bundle is the polynomial model of
  projective `n`-space over `Γ(X, U)`.**
* `Stacks.SymGraded.chartCompare` and `Stacks.SymGraded.chartBaseMap`: the comparison over an
  affine open of `X`, and the open immersion of `ℙⁿ` over that open into `ℙⁿ_X`.
* `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace`: **Tag 01OE**, the isomorphism
  `ℙ(𝒪_X^{n+1}) ≅ ℙⁿ_X`.

## Main results

* `Stacks.SymGraded.res_comp_chartCoordHom`: **the homogeneous coordinates are natural in the
  open.** This is the cocone condition.
* `Stacks.SymGraded.irrelevant_le_map_chartCoordHom`: Mathlib's irrelevant-ideal hypothesis for
  `AlgebraicGeometry.Proj.map` holds for the coordinate homomorphism, so the chart comparison is
  defined on the whole chart.
* `Stacks.SymGraded.projectiveBundleToProjectiveSpace_fst`: the comparison is a morphism **over
  `X`**, by construction.
* `Stacks.SymGraded.chart_comp_projectiveBundleToIntegralModel`: on each chart the comparison is
  the chart comparison.
* `Stacks.SymGraded.chartIsoProjPoly_hom_comp_coordinateProjMap`: **the `snd` leg of the chart
  comparison.** Through `Stacks.SymGraded.chartIsoProjPoly`, the chart's morphism to the integral
  model is the polynomial model's, that is the `snd` leg of
  `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare`.
* `Stacks.SymGraded.chartIsoProjPoly_hom_comp_projToSpecCoeff`: **the `fst` leg of the chart
  comparison.** Through the same isomorphism, the structure morphism of the polynomial model to
  `Spec Γ(X, U)` is the chart's own projection to the affine open `U`. This is the leg that needs
  the degree-zero half `Stacks.SymGraded.chartSectionsRingEquiv_C`.
* `Stacks.SymGraded.isIso_projectiveBundleToProjectiveSpace`: **the comparison morphism is an
  isomorphism.** Being an isomorphism is Zariski-local at the target, the inverse images of the
  affine opens of `X` cover `ℙⁿ_X`, and over each of them the comparison is the chart comparison.
* `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst`: the isomorphism is an
  isomorphism **over `X`**, which is the rest of what Tag 01OE asserts.

## Implementation notes

**Naturality is proved on the variables only, and that is enough.** The source of the coordinate
homomorphism is a polynomial ring over `ℤ` — strictly, over `ULift ℤ`, which the definition of
`AlgebraicGeometry.projectiveSpaceAtUniverse` forces — and `ℤ` is initial among rings, so two
ring homomorphisms out of it agree as soon as they agree on the variables
(`Stacks.subsingleton_uliftIntRingHom`).  The degree-`0` half of
`MvPolynomial.ringHom_ext` therefore needs no computation, and the whole content of naturality is
`Stacks.SymGraded.resRingHom_chartSectionsRingEquiv_X`.

**The universe of `Stacks.SymGraded.coordIndex` has to be written down.** `coordIndex n` is
`ULift (Fin (n + 1))` with the lift level free, so in a statement that does not also mention
`freeModule` the elaborator auto-binds a fresh universe for it and the result does not match the
chart comparison. Every occurrence below is spelled `coordIndex.{u} n`.

**The colimit is addressed through the gluing datum.**
`Stacks.AlgebraicGeometry.RelativeProjGlue.chartFunctor 𝒜` and
`(relativeGluingData 𝒜).functor` are equal by `rfl`, but `relativeGluingData` is a `def`, so
`CategoryTheory.Limits.HasColimit` is found only for the second spelling; the cocone and its
descent are stated with it.

## References

* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NP](https://stacks.math.columbia.edu/tag/01NP)

## Implementation notes, continued

**The affine case used is the comparison of the two models of projective space over a ring**,
`Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare`, and not
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOverRing`. That one is an isomorphism of
bare schemes: it says nothing about either structure morphism, so it would leave the `fst` leg of
the chart comparison — the degree-zero half — still owed.

**Everything is forced into term mode where the two spellings of the structure-sheaf sections
meet.** `Stacks.SymGraded.siteRing` is the `RingCat`-valued forgetful image of `Γ(X, U)`, and the
two spellings are definitionally but not reducibly equal; in a statement mentioning both, `rw`
cannot build a motive that is type-correct at `implicit` transparency. That defeats
`CategoryTheory.Category.assoc` as readily as anything else, which is not obvious from the error.
`Eq.trans` and `congrArg` build no motive and go through.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjPoly (renameGradedHom irrelevant_le_map_renameGradedHom
  projIsoULiftIndex projIsoULiftIndex_hom projIsoULiftIndex_inv)

attribute [local instance] MvPolynomial.gradedAlgebra

universe v w u

/-- **The universe copy of `ℤ` is initial among rings**, exactly as `ℤ` itself is: there is at
most one ring homomorphism out of it. -/
instance Stacks.subsingleton_uliftIntRingHom {S : Type w} [Ring S] :
    Subsingleton (ULift.{v} ℤ →+* S) where
  allEq f g := by
    have h : f.comp (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ).symm.toRingHom =
        g.comp (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ).symm.toRingHom := Subsingleton.elim _ _
    refine RingHom.ext fun r => ?_
    have h2 := DFunLike.congr_fun h ((ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ) r)
    rw [RingHom.comp_apply, RingHom.comp_apply] at h2
    rwa [show (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ).symm.toRingHom
        ((ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ) r) = r from
      (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ).symm_apply_apply r] at h2

namespace Stacks.SymGraded

variable {X : Scheme.{u}} (n : ℕ)

/-- Coefficient change and reindexing in one step: the integral polynomial ring in the variables
of projective `n`-space, into the polynomial ring on the chart coordinates over an open of `X`. -/
def coordGradedHom (U : X.Opens) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) →+*ᵍ
      MvPolynomial.homogeneousSubmodule (coordIndex.{u} n) ↥(siteRing X (op U)) where
  toRingHom :=
    (MvPolynomial.rename (ULift.up : Fin (n + 1) → coordIndex.{u} n)).toRingHom.comp
      (MvPolynomial.map (integralCoeffHom ↥(siteRing X (op U))))
  map_mem hx := MvPolynomial.IsHomogeneous.rename_isHomogeneous (hx.map _)

/-- `Stacks.SymGraded.coordGradedHom` maps the coefficients of a polynomial into the sections and
renames each variable `i` to `ULift.up i`. -/
@[simp] theorem coordGradedHom_apply (U : X.Opens)
    (F : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :
    coordGradedHom n U F =
      MvPolynomial.rename (ULift.up : Fin (n + 1) → coordIndex.{u} n)
        (MvPolynomial.map (integralCoeffHom ↥(siteRing X (op U))) F) :=
  rfl

/-- `Stacks.SymGraded.coordGradedHom` sends the variable `Tᵢ` to the chart coordinate
`ULift.up i`. -/
@[simp] theorem coordGradedHom_X (U : X.Opens) (i : Fin (n + 1)) :
    coordGradedHom n U (MvPolynomial.X i) =
      MvPolynomial.X (ULift.up i : coordIndex.{u} n) := by
  rw [coordGradedHom_apply, MvPolynomial.map_X, MvPolynomial.rename_X]

/-- **The homogeneous coordinates of projective space, as sections of `Sym(𝒪_X^{n+1})` over an
open.** The integral polynomial ring in the variables of projective `n`-space maps to the graded
ring of homogeneous sections of `Sym(𝒪_X^{n+1})` over `U`, sending `Tᵢ` to the `i`-th coordinate
section. -/
def chartCoordHom (U : X.Opens) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) →+*ᵍ
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U :=
  (chartGradedHom n U).comp (coordGradedHom n U)

/-- `Stacks.SymGraded.chartCoordHom` is `Stacks.SymGraded.coordGradedHom` followed by the
identification `Stacks.SymGraded.chartSectionsRingEquiv` of the polynomial ring on the chart
coordinates with the homogeneous sections over `U`. -/
theorem chartCoordHom_apply (U : X.Opens) (F : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :
    chartCoordHom n U F = chartSectionsRingEquiv n U (coordGradedHom n U F) :=
  rfl

/-- **The homogeneous coordinates are natural in the open.** This is the cocone condition the
comparison with projective space rests on.

A homomorphism out of the integral polynomial ring is pinned by its values on the variables,
since `ℤ` is initial among rings; on the variables the statement is
`Stacks.SymGraded.resRingHom_chartSectionsRingEquiv_X`. -/
theorem res_comp_chartCoordHom {U V : X.Opens} (h : U ≤ V) :
    ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).res h).comp (chartCoordHom n V) =
      chartCoordHom n U := by
  have key : (((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).res h).toRingHom.comp
      (chartCoordHom n V).toRingHom) = (chartCoordHom n U).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · exact DFunLike.congr_fun
        (Subsingleton.elim
          ((((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).res h).toRingHom.comp
            (chartCoordHom n V).toRingHom).comp
              (MvPolynomial.C : ULift.{u} ℤ →+* MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)))
          ((chartCoordHom n U).toRingHom.comp MvPolynomial.C)) r
    · show (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).resRingHom h
          (chartSectionsRingEquiv n V (coordGradedHom n V (MvPolynomial.X i))) =
        chartSectionsRingEquiv n U (coordGradedHom n U (MvPolynomial.X i))
      rw [coordGradedHom_X, coordGradedHom_X]
      exact resRingHom_chartSectionsRingEquiv_X n h (ULift.up i)
  exact GradedRingHom.ext fun F => DFunLike.congr_fun key F

/-! ### Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` -/

/-- Coefficient change and reindexing satisfies the irrelevant-ideal hypothesis of
`AlgebraicGeometry.Proj.map`: the image of the irrelevant ideal contains every variable, and a
homogeneous polynomial of positive degree lies in the ideal the variables generate. -/
theorem irrelevant_le_map_coordGradedHom (U : X.Opens) :
    HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (coordIndex.{u} n) ↥(siteRing X (op U))) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).map
        (coordGradedHom n U) := by
  refine Stacks.AlgebraicGeometry.ProjShared.irrelevant_le_map_of_mem_span
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.homogeneousSubmodule (coordIndex.{u} n) ↥(siteRing X (op U)))
    (coordGradedHom n U) (fun d hd g hg => ?_)
  refine Ideal.span_mono ?_ (mem_span_X_of_mem_homogeneousSubmodule hd hg)
  rintro _ ⟨j, rfl⟩
  exact ⟨MvPolynomial.X j.down, Set.mem_biUnion (Set.mem_Ioi.mpr Nat.zero_lt_one)
    ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X _ _)),
    by rw [coordGradedHom_X]⟩

/-- The coordinate homomorphism satisfies the irrelevant-ideal hypothesis of
`AlgebraicGeometry.Proj.map`. The chart comparison contributes nothing, being invertible. -/
theorem irrelevant_le_map_chartCoordHom (U : X.Opens) :
    HomogeneousIdeal.irrelevant
        ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).map
        (chartCoordHom n U) :=
  HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_coordGradedHom n U)
    (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (chartGradedHom_comp_inv n U))

/-! ### The comparison morphism -/

/-- **The comparison of a chart of the projective bundle of `𝒪_X^{n+1}` with the integral model
of projective `n`-space**, induced by the homogeneous coordinates. -/
def chartToProjectiveSpace (U : X.Opens) :
    AlgebraicGeometry.Proj ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) ⟶
      AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n :=
  Proj.map (chartCoordHom n U) (irrelevant_le_map_chartCoordHom n U)

/-- **The chart comparisons are compatible with the transition morphisms.** This is the cocone
condition: the transition morphism is `AlgebraicGeometry.Proj.map` of the restriction map
(`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.transition_eq_map`), so the statement is
naturality of the homogeneous coordinates in the open. -/
theorem transition_comp_chartToProjectiveSpace {U V : X.AffineZariskiSite} (φ : U ⟶ V) :
    (Stacks.AlgebraicGeometry.RelativeProjGlue.relativeGluingData
        (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra).functor.map φ ≫
      chartToProjectiveSpace n V.toOpens = chartToProjectiveSpace n U.toOpens := by
  show (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra.transition
      (Scheme.AffineZariskiSite.toOpens_mono φ.le)
      (Stacks.AlgebraicGeometry.RelativeProjGlue.mapDomain_res_eq_top_of_le _ φ.le _) ≫
      chartToProjectiveSpace n V.toOpens = chartToProjectiveSpace n U.toOpens
  rw [(freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra.transition_eq_map
      (Scheme.AffineZariskiSite.toOpens_mono φ.le) _
      (Stacks.AlgebraicGeometry.RelativeProjGlue.irrelevant_le_map_res_of_le _ φ.le _),
    chartToProjectiveSpace, chartToProjectiveSpace]
  refine Eq.trans (Proj.map_comp (chartCoordHom n V.toOpens)
    ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).res
      (Scheme.AffineZariskiSite.toOpens_mono φ.le))
    (irrelevant_le_map_chartCoordHom n V.toOpens)
    (Stacks.AlgebraicGeometry.RelativeProjGlue.irrelevant_le_map_res_of_le
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra φ.le _)).symm ?_
  exact Proj.map_congr
    (res_comp_chartCoordHom n (Scheme.AffineZariskiSite.toOpens_mono φ.le)) _ _

/-- **The charts, compared with projective space, form a cocone on the chart functor.** -/
def projectiveSpaceCocone :
    Cocone (Stacks.AlgebraicGeometry.RelativeProjGlue.relativeGluingData
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra).functor where
  pt := AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n
  ι :=
    { app := fun U => chartToProjectiveSpace n U.toOpens
      naturality := fun {_U _V} φ =>
        (transition_comp_chartToProjectiveSpace n φ).trans (Category.comp_id _).symm }

/-- **The projective bundle `P(𝒪_X^{n+1}) = Proj_X(Sym(𝒪_X^{n+1}))`**, with its projection to
`X` and its affine charts. -/
abbrev freeProjectiveBundle :
    Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)) :=
  Stacks.AlgebraicGeometry.RelativeProj.relativeProj _

/-- **The descent of the chart comparisons to the projective bundle.** -/
def projectiveBundleToIntegralModel :
    (freeProjectiveBundle (X := X) n).scheme ⟶
      AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n :=
  colimit.desc (Stacks.AlgebraicGeometry.RelativeProjGlue.relativeGluingData
    (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra).functor
    (projectiveSpaceCocone n)

/-- The chart of the projective bundle over an affine open `U`, followed by
`Stacks.SymGraded.projectiveBundleToIntegralModel`, is the chart comparison
`Stacks.SymGraded.chartToProjectiveSpace`. -/
@[simp] theorem chart_comp_projectiveBundleToIntegralModel (U : X.Opens) (hU : IsAffineOpen U) :
    (freeProjectiveBundle (X := X) n).chart U hU ≫ projectiveBundleToIntegralModel n =
      chartToProjectiveSpace n U := by
  rw [projectiveBundleToIntegralModel]
  exact colimit.ι_desc (projectiveSpaceCocone n) ⟨U, hU⟩

/-- **The comparison morphism `P(𝒪_X^{n+1}) ⟶ ℙⁿ_X`, over `X`.** The relative homogeneous
spectrum is a colimit of its charts, so the cocone of chart comparisons descends; the two
projections of `ℙⁿ_X = X ×_{Spec ℤ} ℙⁿ_ℤ` are the structure morphism of the bundle and that
descent, and the pullback square commutes because both composites land in the terminal
scheme. -/
def projectiveBundleToProjectiveSpace :
    (freeProjectiveBundle (X := X) n).scheme ⟶
      AlgebraicGeometry.projectiveSpaceOver.{u} n X :=
  pullback.lift (freeProjectiveBundle (X := X) n).toBase
    (projectiveBundleToIntegralModel n) (terminal.hom_ext _ _)

/-- **The comparison morphism is a morphism over `X`.** -/
@[simp] theorem projectiveBundleToProjectiveSpace_fst :
    projectiveBundleToProjectiveSpace (X := X) n ≫ pullback.fst _ _ =
      (freeProjectiveBundle (X := X) n).toBase :=
  pullback.lift_fst _ _ _

/-- The comparison morphism is compatible with the projections to the integral model. -/
@[simp] theorem projectiveBundleToProjectiveSpace_snd :
    projectiveBundleToProjectiveSpace (X := X) n ≫ pullback.snd _ _ =
      projectiveBundleToIntegralModel n :=
  pullback.lift_snd _ _ _

/-! ### The chart, compared with the polynomial model -/

/-- The chart comparison satisfies the irrelevant-ideal hypothesis of
`AlgebraicGeometry.Proj.map`, being invertible. -/
theorem irrelevant_le_map_chartGradedHom (U : X.Opens) :
    HomogeneousIdeal.irrelevant ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (coordIndex.{u} n) ↥(siteRing X (op U)))).map
          (chartGradedHom n U) :=
  Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (chartGradedHom_comp_inv n U)

/-- **A chart of the projective bundle of `𝒪_X^{n+1}` is the polynomial model of projective
`n`-space over the sections of the structure sheaf.** Two steps: the graded ring of homogeneous
sections over `U` is a polynomial ring (`Stacks.SymGraded.chartGradedHom`, invertible, so
`AlgebraicGeometry.Proj.isIso_map` applies), and its variables, which are indexed in the module
universe, are reindexed by `Fin (n + 1)`
(`Stacks.AlgebraicGeometry.ProjPoly.projIsoULiftIndex`). -/
def chartIsoProjPoly (U : X.Opens) :
    AlgebraicGeometry.Proj ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) ≅
      AlgebraicGeometry.Proj (polyGrading ↥(siteRing X (op U)) n) :=
  haveI : IsIso (Proj.map (chartGradedHom n U) (irrelevant_le_map_chartGradedHom n U)) :=
    Proj.isIso_map _
      (Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id (chartGradedInv_comp_hom n U))
      (chartGradedInv_comp_hom n U) (chartGradedHom_comp_inv n U)
  asIso (Proj.map (chartGradedHom n U) (irrelevant_le_map_chartGradedHom n U)) ≪≫
    Stacks.AlgebraicGeometry.ProjPoly.projIsoULiftIndex ↥(siteRing X (op U)) n

/-- The forward map of `Stacks.SymGraded.chartIsoProjPoly` is the map on `Proj` induced by
`Stacks.SymGraded.chartGradedHom`, followed by the reindexing of the variables by `Fin (n + 1)`. -/
@[simp] theorem chartIsoProjPoly_hom (U : X.Opens) :
    (chartIsoProjPoly n U).hom =
      Proj.map (chartGradedHom n U) (irrelevant_le_map_chartGradedHom n U) ≫
        (Stacks.AlgebraicGeometry.ProjPoly.projIsoULiftIndex ↥(siteRing X (op U)) n).hom :=
  rfl

/-- **Reindexing undoes the coordinate homomorphism's reindexing.** Composing the canonical
coefficient homomorphism with the renaming that lifts `Fin (n + 1)` into the module universe is
the coordinate homomorphism of this file. -/
theorem renameGradedHom_symm_comp_integralGradedHom (U : X.Opens) :
    (Stacks.AlgebraicGeometry.ProjPoly.renameGradedHom ↥(siteRing X (op U))
          ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1)))).comp
        (integralGradedHom ↥(siteRing X (op U)) n) =
      coordGradedHom n U :=
  GradedRingHom.ext fun F => by
    show MvPolynomial.rename _ (MvPolynomial.map _ F) = _
    rw [coordGradedHom_apply]
    rfl

/-- **The `snd` leg of the chart comparison.** Through
`Stacks.SymGraded.chartIsoProjPoly`, the chart's comparison with the integral model of projective
`n`-space is the one of the polynomial model, that is the `snd` leg of
`Stacks.AlgebraicGeometry.ProjPolyChart.projCompare`.

Everything here is `AlgebraicGeometry.Proj.map` of a graded ring homomorphism — the polynomial
model's morphism to the integral model is
(`Stacks.AlgebraicGeometry.ProjBaseChange.coordinateProjMap_eq_projMap`) — so the statement is the
single graded-hom identity `Stacks.SymGraded.renameGradedHom_symm_comp_integralGradedHom` moved
through `AlgebraicGeometry.Proj.map_comp`.

The proof is in term mode on purpose. Every spelling of the structure-sheaf sections reaches this
statement at once, and `rw` — `Category.assoc` included — fails to build a motive that is
type-correct at `implicit` transparency; `Eq.trans` and `congrArg` do not form motives at all. -/
theorem chartIsoProjPoly_hom_comp_coordinateProjMap (U : X.Opens) :
    (chartIsoProjPoly n U).hom ≫
        coordinateProjMap ↥(siteRing X (op U)) n (integralGradedHom ↥(siteRing X (op U)) n)
          (mapDomain_integralGradedHom_eq_top ↥(siteRing X (op U)) n) =
      chartToProjectiveSpace n U :=
  ((congrArg (fun φ => (chartIsoProjPoly n U).hom ≫ φ)
        (Stacks.AlgebraicGeometry.ProjBaseChange.coordinateProjMap_eq_projMap
          ↥(siteRing X (op U)) n)).trans
      (Category.assoc _ _ _)).trans
    (((congrArg
          (fun φ => Proj.map (chartGradedHom n U) (irrelevant_le_map_chartGradedHom n U) ≫ φ)
          ((Proj.map_comp (integralGradedHom ↥(siteRing X (op U)) n)
              (Stacks.AlgebraicGeometry.ProjPoly.renameGradedHom ↥(siteRing X (op U))
                ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1))))
              (Stacks.AlgebraicGeometry.ProjBaseChange.irrelevant_le_map_integralGradedHom
                ↥(siteRing X (op U)) n)
              (Stacks.AlgebraicGeometry.ProjPoly.irrelevant_le_map_renameGradedHom
                ↥(siteRing X (op U)) (Equiv.ulift.{u, 0}).symm)).symm.trans
            (Proj.map_congr (renameGradedHom_symm_comp_integralGradedHom n U) _ _))).trans
        (Proj.map_comp (coordGradedHom n U) (chartGradedHom n U)
          (irrelevant_le_map_coordGradedHom n U)
          (irrelevant_le_map_chartGradedHom n U)).symm).trans
      (Proj.map_congr rfl _ (irrelevant_le_map_chartCoordHom n U)))

/-! ### The `fst` leg of the chart comparison: the structure morphism -/

/-- **The degree-`0` part of the chart comparison, read on elements.** The composite of the
coefficient map of the polynomial model with the two degree-zero components of
`Stacks.SymGraded.chartIsoProjPoly` carries `r` to
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.strHom` of `r`.

This is `Stacks.SymGraded.chartSectionsRingEquiv_C` with the degree bookkeeping done: the
degree-`0` projection of a constant is that constant, and renaming the variables of a constant
does nothing. -/
theorem coe_gradedZeroRingHom_C (U : X.Opens) (r : ↥(siteRing X (op U))) :
    ((chartGradedHom n U).gradedZeroRingHom
        ((renameGradedHom ↥(siteRing X (op U))
            ((Equiv.ulift.{u, 0}).symm :
              Fin (n + 1) → ULift.{u} (Fin (n + 1)))).gradedZeroRingHom
          (GradedRing.projZeroRingHom' (polyGrading ↥(siteRing X (op U)) n)
            (MvPolynomial.C r))) :
        (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).sectionRing U) =
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).strHom U r := by
  have hz : ((GradedRing.projZeroRingHom' (polyGrading ↥(siteRing X (op U)) n)
        (MvPolynomial.C r) : polyGrading ↥(siteRing X (op U)) n 0) :
      MvPolynomial (Fin (n + 1)) ↥(siteRing X (op U))) = MvPolynomial.C r := by
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply]
    exact DirectSum.decompose_of_mem_same _
      (MvPolynomial.C_mem_homogeneousSubmodule_zero (Fin (n + 1)) ↥(siteRing X (op U)) r)
  show chartSectionsRingEquiv n U
      (MvPolynomial.rename _
        ((GradedRing.projZeroRingHom' (polyGrading ↥(siteRing X (op U)) n) (MvPolynomial.C r) :
            polyGrading ↥(siteRing X (op U)) n 0) :
          MvPolynomial (Fin (n + 1)) ↥(siteRing X (op U)))) = _
  rw [hz, MvPolynomial.rename_C, chartSectionsRingEquiv_C]

/-- **The chart comparison is an isomorphism of `Γ(X, U)`-algebras**, at the level of the
degree-zero structure maps: the coefficient map of the polynomial model, pushed through
`Stacks.SymGraded.chartIsoProjPoly`, is
`Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.strZero`. -/
theorem strZero_eq_comp (U : X.Opens) (hU : IsAffineOpen U) :
    CommRingCat.ofHom ((GradedRing.projZeroRingHom' (polyGrading ↥(siteRing X (op U)) n)).comp
        (algebraMap ↥(siteRing X (op U))
          (MvPolynomial (Fin (n + 1)) ↥(siteRing X (op U))))) ≫
      CommRingCat.ofHom (renameGradedHom ↥(siteRing X (op U))
        ((Equiv.ulift.{u, 0}).symm :
          Fin (n + 1) → ULift.{u} (Fin (n + 1)))).gradedZeroRingHom ≫
      CommRingCat.ofHom (chartGradedHom n U).gradedZeroRingHom =
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra.strZero ⟨U, hU⟩ :=
  CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext (by
    show ((chartGradedHom n U).gradedZeroRingHom
      ((renameGradedHom ↥(siteRing X (op U))
          ((Equiv.ulift.{u, 0}).symm :
            Fin (n + 1) → ULift.{u} (Fin (n + 1)))).gradedZeroRingHom
        (GradedRing.projZeroRingHom' (polyGrading ↥(siteRing X (op U)) n)
          (algebraMap ↥(siteRing X (op U))
            (MvPolynomial (Fin (n + 1)) ↥(siteRing X (op U))) r))) :
        (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).sectionRing U) = _
    rw [MvPolynomial.algebraMap_eq, coe_gradedZeroRingHom_C]
    exact (Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.coe_strZero_apply
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra ⟨U, hU⟩ r).symm))

/-- **The `fst` leg of the chart comparison.** Through `Stacks.SymGraded.chartIsoProjPoly`, the
structure morphism of the polynomial model to `Spec Γ(X, U)` is the chart's own projection to the
affine open `U`.

This is the leg that needs the degree-zero half of the chart comparison, and it is the reason the
affine isomorphism `Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOverRing` cannot be
used in its place: that one is an isomorphism of bare schemes and says nothing about the two
structure morphisms. -/
theorem chartIsoProjPoly_hom_comp_projToSpecCoeff (U : X.Opens) (hU : IsAffineOpen U) :
    (chartIsoProjPoly n U).hom ≫ projToSpecCoeff ↥(siteRing X (op U)) n =
      Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)) U hU ≫ hU.isoSpec.hom := by
  have hRHS : Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)) U hU ≫ hU.isoSpec.hom =
      Proj.toSpecZero ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) ≫
        Spec.map ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra.strZero
          ⟨U, hU⟩) :=
    (Iso.eq_comp_inv hU.isoSpec).mp (Category.assoc _ _ _).symm
  rw [hRHS]
  simp only [chartIsoProjPoly_hom, projIsoULiftIndex_hom, projToSpecCoeff, Category.assoc,
    Proj.map_toSpecZero_assoc, ← Spec.map_comp]
  exact congrArg (fun φ => Proj.toSpecZero _ ≫ Spec.map φ) (strZero_eq_comp n U hU)

/-! ### The comparison is an isomorphism, chart by chart -/

/-- **The chart of the bundle over an affine open `U` is the inverse image of `Spec Γ(X, U)`.**
This is the cartesian square of the chart with the affine identification pasted onto its bottom
edge. -/
theorem isPullback_chart_isoSpec (U : X.Opens) (hU : IsAffineOpen U) :
    IsPullback ((freeProjectiveBundle (X := X) n).chart U hU)
      (Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)) U hU ≫ hU.isoSpec.hom)
      (freeProjectiveBundle (X := X) n).toBase (hU.isoSpec.inv ≫ U.ι) := by
  have hiso : IsPullback hU.isoSpec.hom U.ι (hU.isoSpec.inv ≫ U.ι) (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [Iso.hom_inv_id_assoc, Category.comp_id]⟩
  have h := ((freeProjectiveBundle (X := X) n).chart_isPullback U hU).paste_vert hiso.flip
  rwa [Category.comp_id] at h

/-- **The comparison on a chart**: the chart of the bundle over an affine open `U`, compared with
projective `n`-space over `Spec Γ(X, U)`. It is the chart's identification with the polynomial
model followed by `Stacks.AlgebraicGeometry.ProjPolyChart.projCompare`. -/
def chartCompare (U : X.Opens) :
    AlgebraicGeometry.Proj ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) ⟶
      AlgebraicGeometry.projectiveSpaceOver.{u} n (Spec Γ(X, U)) :=
  (chartIsoProjPoly n U).hom ≫ projCompare ↥(siteRing X (op U)) n

/-- **The comparison on a chart is an isomorphism.** This is the affine case of Tag 01OE, and it
is `Stacks.AlgebraicGeometry.ProjBaseChange.isIso_projCompare` — the comparison of the polynomial
and base-change models of projective space over a ring — not the affine isomorphism
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpaceOverRing`, which is an isomorphism of bare
schemes and carries no information about the structure morphisms. -/
instance isIso_chartCompare (U : X.Opens) : IsIso (chartCompare n U) :=
  inferInstanceAs
    (IsIso ((chartIsoProjPoly n U).hom ≫ projCompare ↥(siteRing X (op U)) n))

/-- The chart comparison, through the structure morphism to `Spec Γ(X, U)`. This is the `fst`
leg. -/
theorem chartCompare_comp_fst (U : X.Opens) (hU : IsAffineOpen U) :
    chartCompare n U ≫ pullback.fst (terminal.from (Spec Γ(X, U)))
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) =
      Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
        (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)) U hU ≫ hU.isoSpec.hom :=
  ((Category.assoc _ _ _).trans
      (congrArg (fun φ => (chartIsoProjPoly n U).hom ≫ φ)
        (projCompare_fst ↥(siteRing X (op U)) n))).trans
    (chartIsoProjPoly_hom_comp_projToSpecCoeff n U hU)

/-- The chart comparison, through the projection to the integral model. This is the `snd` leg. -/
theorem chartCompare_comp_snd (U : X.Opens) :
    chartCompare n U ≫ pullback.snd (terminal.from (Spec Γ(X, U)))
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) =
      chartToProjectiveSpace n U :=
  ((Category.assoc _ _ _).trans
      (congrArg (fun φ => (chartIsoProjPoly n U).hom ≫ φ)
        (projCompare_snd ↥(siteRing X (op U)) n))).trans
    (chartIsoProjPoly_hom_comp_coordinateProjMap n U)

/-- **Projective `n`-space over `Spec Γ(X, U)` as an open subscheme of `ℙⁿ_X`**, for `U` an
affine open of `X`: projective space is a product over the terminal scheme, so it is stable under
base change in its first factor
(`Stacks.CategoryTheory.TerminalPullback.isPullback_baseMap`). -/
abbrev chartBaseMap (U : X.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.projectiveSpaceOver.{u} n (Spec Γ(X, U)) ⟶
      AlgebraicGeometry.projectiveSpaceOver.{u} n X :=
  Stacks.CategoryTheory.TerminalPullback.baseMap
    (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n) (hU.isoSpec.inv ≫ U.ι)

/-- `ℙⁿ_{Spec Γ(X, U)} ⟶ ℙⁿ_X` is the base change of `Spec Γ(X, U) ≅ U ⟶ X` along the
projections to the base. -/
private theorem isPullback_chartBaseMap (U : X.Opens) (hU : IsAffineOpen U) :
    IsPullback (chartBaseMap n U hU)
      (pullback.fst (terminal.from (Spec Γ(X, U)))
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)))
      (pullback.fst (terminal.from X)
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)))
      (hU.isoSpec.inv ≫ U.ι) :=
  Stacks.CategoryTheory.TerminalPullback.isPullback_baseMap _ _

/-- **The comparison restricted to a chart is the chart comparison.** Both sides are morphisms
into the pullback `ℙⁿ_X = X ×_{Spec ℤ} ℙⁿ_ℤ`, so the statement is its two legs: the `fst` leg is
`Stacks.SymGraded.chartCompare_comp_fst`, which rests on the degree-zero half of the chart
comparison, and the `snd` leg is `Stacks.SymGraded.chartCompare_comp_snd`. -/
theorem chart_comp_comparison (U : X.Opens) (hU : IsAffineOpen U) :
    (freeProjectiveBundle (X := X) n).chart U hU ≫ projectiveBundleToProjectiveSpace n =
      chartCompare n U ≫ chartBaseMap n U hU := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveBundleToProjectiveSpace_fst, Category.assoc,
      Stacks.CategoryTheory.TerminalPullback.baseMap_comp_fst, ← Category.assoc,
      chartCompare_comp_fst n U hU]
    exact (((freeProjectiveBundle (X := X) n).chart_isPullback U hU).w).trans
      ((congrArg (fun φ => Stacks.AlgebraicGeometry.RelativeProj.projInclusionToOpen
            (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)) U hU ≫ φ)
          (Iso.hom_inv_id_assoc hU.isoSpec U.ι)).symm.trans (Category.assoc _ _ _).symm)
  · rw [Category.assoc, projectiveBundleToProjectiveSpace_snd,
      chart_comp_projectiveBundleToIntegralModel, Category.assoc,
      Stacks.CategoryTheory.TerminalPullback.baseMap_comp_snd, chartCompare_comp_snd]

/-- **The chart is the inverse image of its piece of `ℙⁿ_X`.** The outer rectangle is
`Stacks.SymGraded.isPullback_chart_isoSpec` and the bottom square is the base change of
projective space, so the top square is cartesian. -/
theorem isPullback_chart_comparison (U : X.Opens) (hU : IsAffineOpen U) :
    IsPullback ((freeProjectiveBundle (X := X) n).chart U hU) (chartCompare n U)
      (projectiveBundleToProjectiveSpace n) (chartBaseMap n U hU) := by
  refine IsPullback.of_bot ?_ (chart_comp_comparison n U hU)
    (isPullback_chartBaseMap n U hU)
  rw [chartCompare_comp_fst n U hU, projectiveBundleToProjectiveSpace_fst]
  exact isPullback_chart_isoSpec n U hU

/-- For `U` an affine open of `X`, the morphism `ℙⁿ_{Spec Γ(X, U)} ⟶ ℙⁿ_X` is an open immersion,
being the base change of the open immersion `Spec Γ(X, U) ≅ U ⟶ X`. -/
instance isOpenImmersion_chartBaseMap (U : X.Opens) (hU : IsAffineOpen U) :
    IsOpenImmersion (chartBaseMap n U hU) := by
  have hoi : IsOpenImmersion (hU.isoSpec.inv ≫ U.ι) := inferInstance
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (Stacks.CategoryTheory.TerminalPullback.isPullback_baseMap
      (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)
      (hU.isoSpec.inv ≫ U.ι)).flip hoi

/-- **`ℙⁿ` over an affine open of `X` is the inverse image of that open.** -/
theorem opensRange_chartBaseMap (U : X.Opens) (hU : IsAffineOpen U) :
    (chartBaseMap n U hU).opensRange =
      pullback.fst (terminal.from X)
        (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) ⁻¹ᵁ U := by
  refine (AlgebraicGeometry.Proj.opensRange_eq_preimage_of_isPullback
    (isPullback_chartBaseMap n U hU).flip).trans ?_
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- **The comparison morphism is an isomorphism.** Being an isomorphism is Zariski-local at the
target; the inverse images of the affine opens of `X` cover `ℙⁿ_X`, each is `ℙⁿ` over that affine
open, and over each the comparison is the chart comparison, which is an isomorphism. -/
instance isIso_projectiveBundleToProjectiveSpace :
    IsIso (projectiveBundleToProjectiveSpace (X := X) n) := by
  refine Stacks.AlgebraicGeometry.ProjBaseChange.isIso_of_isPullback_cover
    (projectiveBundleToProjectiveSpace n)
    (fun U : X.affineOpens => pullback.fst (terminal.from X)
      (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) ⁻¹ᵁ (U.1 : X.Opens))
    ?_ _ (fun U => chartBaseMap n U.1 U.2)
    (fun U => isOpenImmersion_chartBaseMap n U.1 U.2) (fun U => ?_)
    _ (fun U => (freeProjectiveBundle (X := X) n).chart U.1 U.2)
    (fun U => chartCompare n U.1) (fun U => isPullback_chart_comparison n U.1 U.2)
    (fun U => inferInstance)
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · rw [← opensRange_chartBaseMap n U.1 U.2]
    rfl

/-! ### Tag 01OE -/

/-- **`ℙⁿ_X` is a projective bundle over `X`**: the projective bundle of the free module sheaf
`𝒪_X^{n+1}` — that is `Proj_X(Sym(𝒪_X^{n+1}))` — is projective `n`-space over `X`.

This is the isomorphism; `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst` is
the other half of the statement, that it is an isomorphism **over `X`**. -/
@[stacks 01OE]
def projectiveBundleIsoProjectiveSpace :
    (freeProjectiveBundle (X := X) n).scheme ≅
      AlgebraicGeometry.projectiveSpaceOver.{u} n X :=
  asIso (projectiveBundleToProjectiveSpace n)

/-- **The isomorphism of Tag 01OE is an isomorphism over `X`**: it carries the structure morphism
of `ℙⁿ_X` to the projection of the bundle. Together with
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` this is the whole assertion of the tag,
which is that `ℙⁿ_X` is a projective bundle **over `X`** and not merely abstractly isomorphic to
one. -/
@[stacks 01OE]
theorem projectiveBundleIsoProjectiveSpace_hom_comp_fst :
    (projectiveBundleIsoProjectiveSpace (X := X) n).hom ≫
        pullback.fst (terminal.from X)
          (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} n)) =
      (freeProjectiveBundle (X := X) n).toBase :=
  projectiveBundleToProjectiveSpace_fst n

end Stacks.SymGraded

end
