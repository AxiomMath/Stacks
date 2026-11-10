module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine

/-!
# The projective line is universally closed

The structure morphism of the projective line over a commutative ring satisfies the existence
part of the valuative criterion: a map from the fraction field of a valuation ring extends over
the valuation ring after choosing one of the two affine charts, the coordinate or its inverse
being an integer according to which. The two-chart cover also makes the structure morphism
quasi-compact. Together these give universal closedness.

## Main results

* `AlgebraicGeometry.projectiveLine_valuativeCriterion_existence`: every valuative square for
  the structure morphism of the projective line has a diagonal lift.
* `AlgebraicGeometry.projectiveLine_quasiCompact`: the structure morphism is quasi-compact.
* `AlgebraicGeometry.projectiveLine_universallyClosed`: the structure morphism is universally
  closed.

## Implementation notes

Given a valuative square, the map from the fraction field factors through one of the two charts
because its image is a single point, which lies in the range of one of the two chart immersions;
`IsOpenImmersion.lift` produces the factorization. Whether the coordinate or its inverse is an
integer of the valuation ring then decides which chart the lift is built in, and in the second
case the map is re-factored through the other chart by composing with the inversion isomorphism
of the punctured line and the gluing datum's transition morphism. Once the coordinate is an
integer, `Polynomial.eval₂RingHom` extends the ring map, which is all the universal property of
`Spec` needs.

Quasi-compactness comes from compactness of the underlying space, itself from the two-chart
cover; universal closedness is then `UniversallyClosed.eq_valuativeCriterion`.

All three statements hold for an arbitrary commutative coefficient ring, not only a field.

## References

* [Stacks Project, Tag 01KG](https://stacks.math.columbia.edu/tag/01KG)
-/

public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- Two `eqToHom`s between the same pair of objects, in either order, cancel. This is
`eqToHom_trans` in the shape a right-associated composite presents it, stated with the leading
factor explicit so that it can be applied by `exact` rather than matched by `rw`: the middle
object produced by `CategoryTheory.GlueData.ofGlueData'` is an unreduced `if _ = _ then _ else _`,
which blocks syntactic matching but not definitional unification. -/
private lemma comp_eqToHom_comp_eqToHom_comp {C : Type*} [Category C] {W X Y Z : C}
    (g : W ⟶ X) (p : X = Y) (q : Y = X) (h : X ⟶ Z) :
    g ≫ eqToHom p ≫ eqToHom q ≫ h = g ≫ h := by
  cases p
  simp

private theorem projectiveLine_compactSpace (k : Type u) [CommRing k] :
    CompactSpace (projectiveLine k) := by
  refine ⟨?_⟩
  have hcover : Set.range (projectiveLineXChart k) ∪
      Set.range (projectiveLineYChart k) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨⟨_ | _⟩, y, hy⟩ := Scheme.GlueData.ι_jointly_surjective
      (projectiveLineGluingData k) x
    · exact Set.mem_union_left _ ⟨y, by
        change (projectiveLineGluingData k).ι (projectiveLineXIndex k) y = x
        exact hy⟩
    · exact Set.mem_union_right _ ⟨y, by
        change (projectiveLineGluingData k).ι (projectiveLineYIndex k) y = x
        exact hy⟩
  rw [← hcover]
  exact (isCompact_range (projectiveLineXChart k).continuous).union
    (isCompact_range (projectiveLineYChart k).continuous)

private theorem projectiveLine_chartFactor (k K : Type u) [CommRing k] [Field K]
    (ξ : Spec (.of K) ⟶ projectiveLine k) :
    ∃ b : Bool, ∃ φ : Spec (.of K) ⟶ Spec (.of (Polynomial k)),
      φ ≫ (if b then projectiveLineYChart k else projectiveLineXChart k) = ξ := by
  obtain ⟨⟨_ | _⟩, z, hz⟩ := Scheme.GlueData.ι_jointly_surjective
    (projectiveLineGluingData k) (ξ (IsLocalRing.closedPoint K))
  · refine ⟨false, IsOpenImmersion.lift (projectiveLineXChart k) ξ ?_, ?_⟩
    · rintro y ⟨x, rfl⟩
      obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact ⟨z, by
        change (projectiveLineGluingData k).ι (projectiveLineXIndex k) z =
          ξ (IsLocalRing.closedPoint K)
        exact hz⟩
    · simpa using IsOpenImmersion.lift_fac (projectiveLineXChart k) ξ _
  · refine ⟨true, IsOpenImmersion.lift (projectiveLineYChart k) ξ ?_, ?_⟩
    · rintro y ⟨x, rfl⟩
      obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact ⟨z, by
        change (projectiveLineGluingData k).ι (projectiveLineYIndex k) z =
          ξ (IsLocalRing.closedPoint K)
        exact hz⟩
    · simpa using IsOpenImmersion.lift_fac (projectiveLineYChart k) ξ _

private theorem polynomial_extension_of_integer
    {k : Type u} {A : Type v} {K : Type w}
    [CommRing k] [CommRing A] [Field K] [Algebra A K]
    (fA : k →+* A) (fK : Polynomial k →+* K) (cA : A)
    (hcoeff : (algebraMap A K).comp fA = fK.comp Polynomial.C)
    (hcoord : algebraMap A K cA = fK Polynomial.X) :
    ∃ F : Polynomial k →+* A,
      (algebraMap A K).comp F = fK ∧ F.comp Polynomial.C = fA := by
  refine ⟨Polynomial.eval₂RingHom fA cA, ?_, ?_⟩
  · apply Polynomial.ringHom_ext
    · intro a
      simpa using DFunLike.congr_fun hcoeff a
    · simp [hcoord]
  · ext a
    simp

/-- Every valuative square for the structure morphism of the projective line
has a diagonal lift. -/
@[stacks 01KG "valuative extension"]
theorem projectiveLine_valuativeCriterion_existence (k : Type u) [CommRing k] :
    ValuativeCriterion.Existence
      (projectiveLine k ↘ Spec (.of k)) := by
  rintro ⟨A, K, ξ, φ, hsq⟩
  let p := projectiveLine k ↘ Spec (.of k)
  obtain ⟨b, ξchart, hξchart⟩ := projectiveLine_chartFactor k K ξ
  let chart := if b then projectiveLineYChart k else projectiveLineXChart k
  let fA : k →+* A := (Spec.preimage φ).hom
  let fK : Polynomial k →+* K := (Spec.preimage ξchart).hom
  let cK : K := fK Polynomial.X
  have hchartP : chart ≫ p = projectiveLineAffineStructureMorphism k := by
    cases b <;> simp [chart, p]
  have hbase : ξchart ≫ projectiveLineAffineStructureMorphism k =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ φ := by
    rw [← hchartP, ← Category.assoc, hξchart]
    exact hsq.w
  have hbaseRing : CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫
      CommRingCat.ofHom fK = CommRingCat.ofHom fA ≫
      CommRingCat.ofHom (algebraMap A K) := by
    simpa only [Spec.preimage_comp, Spec.preimage_map, fA, fK,
      CommRingCat.ofHom_hom] using
      congrArg Spec.preimage hbase
  have hcoeff : (algebraMap A K).comp fA = fK.comp Polynomial.C := by
    have hh := congrArg CommRingCat.Hom.hom hbaseRing
    exact hh.symm
  have hDirect (chartMap : Spec (.of K) ⟶ Spec (.of (Polynomial k)))
      (chart' : Spec (.of (Polynomial k)) ⟶ projectiveLine k)
      (hchart' : chartMap ≫ chart' = ξ)
      (hchart'P : chart' ≫ p = projectiveLineAffineStructureMorphism k)
      (fK' : Polynomial k →+* K)
      (hfK' : (Spec.preimage chartMap).hom = fK')
      (hcoeff' : (algebraMap A K).comp fA = fK'.comp Polynomial.C)
      (cA : A) (hcA : algebraMap A K cA = fK' Polynomial.X) :
      ∃ l : Spec (.of A) ⟶ projectiveLine k,
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ l = ξ ∧ l ≫ p = φ := by
    obtain ⟨F, hF, hFC⟩ := polynomial_extension_of_integer fA fK' cA hcoeff' hcA
    let chartLift := Spec.map (CommRingCat.ofHom F)
    have htop : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ chartLift = chartMap := by
      rw [← Spec.map_comp, ← Spec.map_preimage chartMap]
      congr 1
      apply CommRingCat.hom_ext
      rw [hfK']
      exact hF
    have hbottom : chartLift ≫ projectiveLineAffineStructureMorphism k = φ := by
      rw [← Spec.map_comp, ← Spec.map_preimage φ]
      congr 1
      apply CommRingCat.hom_ext
      simpa [fA] using hFC
    refine ⟨chartLift ≫ chart', ?_, ?_⟩
    · calc
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ (chartLift ≫ chart') =
            (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ chartLift) ≫ chart' := by
              simp [Category.assoc]
        _ = chartMap ≫ chart' := by rw [htop]
        _ = ξ := hchart'
    · calc
        (chartLift ≫ chart') ≫ p = chartLift ≫ (chart' ≫ p) := by
          simp [Category.assoc]
        _ = chartLift ≫ projectiveLineAffineStructureMorphism k := by rw [hchart'P]
        _ = φ := hbottom
  rcases ValuationRing.isInteger_or_isInteger A cK with hc | hc
  · obtain ⟨cA, hcA⟩ := hc
    obtain ⟨l, hl₁, hl₂⟩ := hDirect ξchart chart hξchart hchartP fK rfl hcoeff cA hcA
    exact ⟨⟨l, hl₁, hl₂⟩⟩
  · obtain ⟨cA, hcA⟩ := hc
    by_cases hc' : IsLocalization.IsInteger A cK
    · obtain ⟨cA', hcA'⟩ := hc'
      obtain ⟨l, hl₁, hl₂⟩ := hDirect ξchart chart hξchart hchartP fK rfl hcoeff cA' hcA'
      exact ⟨⟨l, hl₁, hl₂⟩⟩
    · have hcK : cK ≠ 0 := by
        intro hzero
        apply hc'
        exact ⟨0, by simp [hzero]⟩
      let cUnit : Kˣ := Units.mk0 cK hcK
      let overlapEval : LaurentPolynomial k →+* K :=
        LaurentPolynomial.eval₂ (fK.comp Polynomial.C) cUnit
      let overlapMap := Spec.map (CommRingCat.ofHom overlapEval)
      have hVxy : (projectiveLineGluingData k).V
          (projectiveLineXIndex k, projectiveLineYIndex k) =
          Spec (.of (LaurentPolynomial k)) := by
        simp [projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
          projectiveLineGluingData', projectiveLineXIndex, projectiveLineYIndex]
      have hVyx : (projectiveLineGluingData k).V
          (projectiveLineYIndex k, projectiveLineXIndex k) =
          Spec (.of (LaurentPolynomial k)) := by
        simp [projectiveLineGluingData, CategoryTheory.GlueData.ofGlueData',
          projectiveLineGluingData', projectiveLineXIndex, projectiveLineYIndex]
      let overlapMapXY := overlapMap ≫ eqToHom hVxy.symm
      let overlapMapYX := overlapMap ≫ eqToHom hVyx.symm
      let oppositeChart := if b then projectiveLineXChart k else projectiveLineYChart k
      let oppositeTopData := if b then
        overlapMapYX ≫ (projectiveLineGluingData k).t
          (projectiveLineYIndex k) (projectiveLineXIndex k) ≫
          (projectiveLineGluingData k).f
            (projectiveLineXIndex k) (projectiveLineYIndex k)
        else
        overlapMapXY ≫ (projectiveLineGluingData k).t
          (projectiveLineXIndex k) (projectiveLineYIndex k) ≫
          (projectiveLineGluingData k).f
            (projectiveLineYIndex k) (projectiveLineXIndex k)
      let oppositeTop := overlapMap ≫
        (if b then (projectiveLineInversionIso k).inv else
          (projectiveLineInversionIso k).hom) ≫ projectiveLinePuncturedChart k
      have hoppositeChartP : oppositeChart ≫ p = projectiveLineAffineStructureMorphism k := by
        cases b <;> simp [oppositeChart, p]
      have hOverlap : overlapMap ≫ projectiveLinePuncturedChart k = ξchart := by
        rw [← Spec.map_preimage (overlapMap ≫ projectiveLinePuncturedChart k),
          ← Spec.map_preimage ξchart, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        simp only [Spec.preimage_map]
        change overlapEval.comp Polynomial.toLaurent = fK
        apply Polynomial.ringHom_ext
        · intro a
          simp [overlapEval]
        · simp [overlapEval, cUnit, cK]
      have hDataLift : oppositeTopData ≫ oppositeChart = ξ := by
        cases b
        · have hglue := congrArg
            (fun f : (projectiveLineGluingData k).V
                (projectiveLineXIndex k, projectiveLineYIndex k) ⟶
                (projectiveLineGluingData k).glued => overlapMapXY ≫ f)
            ((projectiveLineGluingData k).glue_condition
              (projectiveLineXIndex k) (projectiveLineYIndex k))
          have hfx : overlapMapXY ≫ (projectiveLineGluingData k).f
              (projectiveLineXIndex k) (projectiveLineYIndex k) =
              overlapMap ≫ projectiveLinePuncturedChart k := by
            simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
              projectiveLinePuncturedChart, CategoryTheory.GlueData.ofGlueData', dite_eq_ite,
              CategoryTheory.GlueData'.f', projectiveLineXIndex, projectiveLineYIndex,
              ULift.up.injEq, Bool.false_eq_true, ↓reduceDIte, Category.assoc, overlapMapXY]
            exact comp_eqToHom_comp_eqToHom_comp _ _ _ _
          have hxi : ξchart ≫ (projectiveLineGluingData k).ι
              (projectiveLineXIndex k) = ξ := by
            change ξchart ≫ projectiveLineXChart k = ξ
            exact hξchart
          change (overlapMapXY ≫ (projectiveLineGluingData k).t
              (projectiveLineXIndex k) (projectiveLineYIndex k) ≫
              (projectiveLineGluingData k).f
                (projectiveLineYIndex k) (projectiveLineXIndex k)) ≫
              (projectiveLineGluingData k).ι (projectiveLineYIndex k) = ξ
          simp only [← Category.assoc, hfx, hOverlap] at hglue
          exact hglue.trans hxi
        · have hglue := congrArg
            (fun f : (projectiveLineGluingData k).V
                (projectiveLineYIndex k, projectiveLineXIndex k) ⟶
                (projectiveLineGluingData k).glued => overlapMapYX ≫ f)
            ((projectiveLineGluingData k).glue_condition
              (projectiveLineYIndex k) (projectiveLineXIndex k))
          have hfy : overlapMapYX ≫ (projectiveLineGluingData k).f
              (projectiveLineYIndex k) (projectiveLineXIndex k) =
              overlapMap ≫ projectiveLinePuncturedChart k := by
            simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
              projectiveLinePuncturedChart, CategoryTheory.GlueData.ofGlueData', dite_eq_ite,
              CategoryTheory.GlueData'.f', projectiveLineYIndex, projectiveLineXIndex,
              ULift.up.injEq, Bool.true_eq_false, ↓reduceDIte, Category.assoc, overlapMapYX]
            exact comp_eqToHom_comp_eqToHom_comp _ _ _ _
          have hxi : ξchart ≫ (projectiveLineGluingData k).ι
              (projectiveLineYIndex k) = ξ := by
            change ξchart ≫ projectiveLineYChart k = ξ
            exact hξchart
          change (overlapMapYX ≫ (projectiveLineGluingData k).t
              (projectiveLineYIndex k) (projectiveLineXIndex k) ≫
              (projectiveLineGluingData k).f
                (projectiveLineXIndex k) (projectiveLineYIndex k)) ≫
              (projectiveLineGluingData k).ι (projectiveLineXIndex k) = ξ
          simp only [← Category.assoc, hfy, hOverlap] at hglue
          exact hglue.trans hxi
      have hDataTop : oppositeTopData = oppositeTop := by
        cases b
        · simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
            projectiveLinePuncturedChart, projectiveLineInversionIso, Functor.mapIso_inv,
            Scheme.Spec_map, Functor.mapIso_hom, CategoryTheory.GlueData.ofGlueData',
            dite_eq_ite, CategoryTheory.GlueData'.f', projectiveLineXIndex, Bool.false_eq_true,
            ↓reduceIte, projectiveLineYIndex, ULift.up.injEq, Bool.true_eq_false, ↓reduceDIte,
            Iso.op_hom, RingEquiv.toCommRingCatIso_hom, AlgEquiv.toRingEquiv_toRingHom,
            Quiver.Hom.unop_op, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
            Category.id_comp, oppositeTopData, overlapMapXY, overlapMap, overlapEval, oppositeTop]
          exact comp_eqToHom_comp_eqToHom_comp _ _ _ _
        · simp only [projectiveLineGluingData, projectiveLineGluingData', ne_eq,
            projectiveLinePuncturedChart, projectiveLineInversionIso, Functor.mapIso_inv,
            Scheme.Spec_map, Functor.mapIso_hom, CategoryTheory.GlueData.ofGlueData',
            dite_eq_ite, CategoryTheory.GlueData'.f', projectiveLineXIndex, ↓reduceIte,
            projectiveLineYIndex, ULift.up.injEq, Bool.true_eq_false, Bool.false_eq_true,
            ↓reduceDIte, Iso.op_inv, RingEquiv.toCommRingCatIso_inv, RingEquiv.symm_mk,
            AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm,
            LaurentPolynomial.invert_symm, Quiver.Hom.unop_op, Category.assoc,
            eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, oppositeTopData,
            overlapMapYX, overlapMap, overlapEval, oppositeTop]
          exact comp_eqToHom_comp_eqToHom_comp _ _ _ _
      have hopposite : oppositeTop ≫ oppositeChart = ξ := by
        rw [← hDataTop]
        exact hDataLift
      let fK' : Polynomial k →+* K := (Spec.preimage oppositeTop).hom
      have hcK' : fK' Polynomial.X = cK⁻¹ := by
        cases b <;> simp [fK', oppositeTop, overlapMap, overlapEval,
          Spec.preimage_comp, Spec.preimage_map, projectiveLinePuncturedChart,
          projectiveLineInversionIso, LaurentPolynomial.eval₂_T, cUnit, cK]
      have hbase' : oppositeTop ≫ projectiveLineAffineStructureMorphism k =
          Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ φ := by
        calc
          oppositeTop ≫ projectiveLineAffineStructureMorphism k =
              oppositeTop ≫ (oppositeChart ≫ p) := by rw [hoppositeChartP]
          _ = ξ ≫ p := by rw [← Category.assoc, hopposite]
          _ = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ φ := hsq.w
      have hbaseRing' : CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫
          CommRingCat.ofHom fK' = CommRingCat.ofHom fA ≫
          CommRingCat.ofHom (algebraMap A K) := by
        simpa only [Spec.preimage_comp, Spec.preimage_map, fA, fK',
          CommRingCat.ofHom_hom] using congrArg Spec.preimage hbase'
      have hcoeff' : (algebraMap A K).comp fA = fK'.comp Polynomial.C := by
        have hh := congrArg CommRingCat.Hom.hom hbaseRing'
        exact hh.symm
      obtain ⟨l, hl₁, hl₂⟩ := hDirect oppositeTop oppositeChart hopposite
        hoppositeChartP fK' rfl hcoeff' cA (by simpa [hcK'] using hcA)
      exact ⟨⟨l, hl₁, hl₂⟩⟩

/-- The structure morphism of the projective line is quasi-compact. -/
@[stacks 01KG "quasi-compactness"]
theorem projectiveLine_quasiCompact (k : Type u) [CommRing k] :
    QuasiCompact (projectiveLine k ↘ Spec (.of k)) := by
  have : CompactSpace (projectiveLine k) := projectiveLine_compactSpace k
  infer_instance

/-- The structure morphism of the projective line is universally closed. -/
@[stacks 01KG "universal closedness"]
theorem projectiveLine_universallyClosed (k : Type u) [CommRing k] :
    UniversallyClosed (projectiveLine k ↘ Spec (.of k)) := by
  rw [UniversallyClosed.eq_valuativeCriterion]
  exact ⟨projectiveLine_valuativeCriterion_existence k, projectiveLine_quasiCompact k⟩

end AlgebraicGeometry
