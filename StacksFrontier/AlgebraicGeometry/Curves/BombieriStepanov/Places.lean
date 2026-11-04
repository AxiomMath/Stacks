module

public import StacksFrontier.NumberTheory.BombieriStepanov.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochMeromorphic
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic

/-!
# The places of a curve

Let `X` be an integral locally Noetherian scheme whose local rings at the points of codimension one
are discrete valuation rings. Each such point `x` gives an additive valuation `ord_x` on the
function field `R(X)`, read off `AlgebraicGeometry.Scheme.ord`. For `X` a proper curve over a
field `k`, the points of codimension one with these valuations and their residue degrees satisfy
the degree formula for principal divisors: `∑_x [κ(x) : k] · ord_x(f) = 0` for `f ≠ 0`. This is
Riemann–Roch for the structure sheaf in divisor form,
`AlgebraicGeometry.curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle_of_isCurve`. There
`deg(𝒪_X) = 0`, and the divisor of the meromorphic section `f` of `𝒪_X` has coefficient
`ord_x(f)` at `x` (`Stacks.Chow.orderOfVanishing_unitModule_eq_ord`).

## Main definitions

* `Stacks.BombieriStepanov.schemeVal`: the valuation `ord_x` of `R(X)` at a point with a discrete
  valuation ring as local ring.
* `Stacks.BombieriStepanov.curveVal`: the family of these valuations at the points of codimension
  one.

## Main results

* `Stacks.BombieriStepanov.ordZ_schemeVal`: `ordZ` of `schemeVal x` is `ord_x`.
* `Stacks.BombieriStepanov.hasDegreeFormula_curveVal`: the degree formula on a proper curve.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

section Valuation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The order of vanishing of the constant function `1` is zero at every point. -/
theorem scheme_ord_one (x : X) : X.ord (1 : X.functionField) x = 0 := by
  have h := Scheme.ord_mul (x := x) (one_ne_zero (α := X.functionField))
    (one_ne_zero (α := X.functionField))
  rw [mul_one] at h
  omega

open Classical in
/-- The valuation `ord_x` of the function field at a point whose local ring is a discrete
valuation ring. -/
def schemeVal (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    AddValuation X.functionField (WithTop ℤ) :=
  AddValuation.of (fun f => if f = 0 then ⊤ else ((X.ord f x : ℤ) : WithTop ℤ))
    (by simp) (by simp [scheme_ord_one])
    (by
      intro f g
      by_cases hf : f = 0
      · simp [hf]
      by_cases hg : g = 0
      · simp [hg]
      by_cases hfg : f + g = 0
      · simp [hfg]
      simp only [hf, hg, hfg, if_false]
      rw [← WithTop.coe_min]
      exact WithTop.coe_le_coe.2 (Scheme.ord_add hfg))
    (by
      intro f g
      by_cases hf : f = 0
      · simp [hf]
      by_cases hg : g = 0
      · simp [hg]
      simp only [mul_eq_zero, hf, hg, or_self, if_false]
      rw [Scheme.ord_mul hf hg]
      rfl)

open Classical in
/-- On a nonzero function the valuation `schemeVal x` takes the finite value `ord_x(f)`. -/
theorem schemeVal_apply (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f : X.functionField} (hf : f ≠ 0) : schemeVal x f = ((X.ord f x : ℤ) : WithTop ℤ) := by
  simp [schemeVal, hf]

open Classical in
/-- The integer-valued order `ordZ` of the valuation `schemeVal x` is the order of vanishing
`ord_x`. -/
theorem ordZ_schemeVal (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (f : X.functionField) : ordZ (schemeVal x) f = X.ord f x := by
  by_cases hf : f = 0
  · simp [ordZ, schemeVal, hf]
  · rw [ordZ, schemeVal_apply x hf]
    rfl

end Valuation

section DegreeFormula

/-- The places of a scheme: its points of codimension one. On a curve these are its closed
points. -/
abbrev CurvePlace (X : Scheme.{u}) : Type u := {x : X // coheight x = 1}

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))

/-- The valuations `ord_x` at the places of `X`. -/
def curveVal (P : CurvePlace X) : AddValuation X.functionField (WithTop ℤ) :=
  haveI := hdvr P.1 P.2
  schemeVal P.1

/-- The integer-valued order `ordZ` of the valuation at a place `P` is `ord_P`. -/
theorem ordZ_curveVal (P : CurvePlace X) (f : X.functionField) :
    ordZ (curveVal hdvr P) f = X.ord f P.1 := by
  have := hdvr P.1 P.2
  exact ordZ_schemeVal P.1 f

variable (k : Type u) [Field k] (p : X ⟶ Spec (.of k))

/-- The degree `[κ(x) : k]` of a place. -/
def curveDeg (P : CurvePlace X) : ℕ := p.residueDegree P.1

/-- An integer-valued function on `X` that vanishes off the points of codimension one has the
same unconditional sum over the places of `X` as over all of `X`. -/
private theorem finsum_curvePlace_eq_finsum :
    ∀ F : X → ℤ, (∀ x, coheight x ≠ 1 → F x = 0) →
      ∑ᶠ P : CurvePlace X, F P.1 = ∑ᶠ x, F x := by
  classical
  intro F hF
  rw [finsum_subtype_eq_finsum_cond (fun x : X => coheight x = 1)]
  refine finsum_congr fun x => ?_
  rw [finsum_eq_if]
  split_ifs with hx
  · rfl
  · exact (hF x hx).symm

variable [IsProper p] [IsCurve k p]

/-- **The divisor of a rational function as a cycle of relative dimension zero.** A nonzero `f`
is a meromorphic section of `𝒪_X`, and on a proper curve Riemann–Roch for the structure sheaf
gives a degree-zero cycle whose coefficient at each point `x` is `ord_x(f)`. -/
private theorem exists_cycle_coeff_eq_ord (hdim : topologicalKrullDim X ≤ 1) :
    ∀ f : X.functionField, f ≠ 0 → ∃ c : Stacks.Chow.CycleGroup
      (Stacks.Chow.fieldChowSituation k) p 0,
      (∀ x : X, (c.1 : AlgebraicCycle X ℤ) x = X.ord f x) ∧
      Stacks.Chow.cycleDegree (Stacks.Chow.fieldChowSituation k) p
        (IsLocalRing.closedPoint k) c = 0 := by
  classical
  intro f hf
  set s := (Stacks.Ample.unitStalkEquiv X (genericPoint X)).symm f with hs
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact (LinearEquiv.map_ne_zero_iff _).2 hf
  have h := curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle_of_isCurve k p hdim
    (Stacks.Ample.unitModule X) s hs0
  refine ⟨_, fun x => ?_, h.symm.trans ?_⟩
  · by_cases hx : coheight x = 1
    · have hgen := Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne x hx
      conv_lhs => rw [← hgen]
      rw [Stacks.Chow.meromorphicDivisorCycle_genericPoint,
        Stacks.Chow.orderOfVanishing_unitModule_eq_ord, hgen]
    · rw [Stacks.Chow.meromorphicDivisorCycle_eq_zero, Scheme.ord_eq_zero_of_coheight_neq_one hx]
      intro Z hZ
      exact hx (hZ ▸ Stacks.Divisors.PrimeDivisor.coheight_genericPoint Z)
  · simp [curveDegree]

/-- **The degree formula on a proper curve.** A nonzero rational function `f` has finitely many
zeros and poles, and `∑_x [κ(x) : k] · ord_x(f) = 0`. -/
theorem hasDegreeFormula_curveVal : HasDegreeFormula (curveVal hdvr) (curveDeg k p) := by
  classical
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one p).le
  -- the divisor cycle of `f`, viewed as a meromorphic section of `𝒪_X`
  have hcyc := exists_cycle_coeff_eq_ord k p hdim
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hord : ∀ f : X.functionField, ∀ x : X, coheight x ≠ 1 → X.ord f x = 0 :=
    fun f x hx => Scheme.ord_eq_zero_of_coheight_neq_one hx f
  -- the sum over places is the sum over all points
  have hsub := finsum_curvePlace_eq_finsum (X := X)
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨c, hc, -⟩ := hcyc f hf
    have hfin := (Function.locallyFinsupp.locallyFiniteSupport (c.1 : AlgebraicCycle X ℤ)
      ).finite_inter_support_of_isCompact isCompact_univ
    rw [Set.univ_inter] at hfin
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun P hP => ?_
    simp only [Function.mem_support, ordZ_curveVal] at hP
    simp only [Set.mem_preimage, Function.mem_support]
    show (c.1 : AlgebraicCycle X ℤ) P.1 ≠ 0
    rw [hc]
    exact hP
  · obtain ⟨c, hc, hdeg⟩ := hcyc f hf
    have hdeg1 := Stacks.Chow.cycleDegree_apply (Stacks.Chow.fieldChowSituation k) p
      (IsLocalRing.closedPoint k) c
    have hdeg2 := hdeg1.symm.trans hdeg
    have hdeg' := (Stacks.Chow.properPushforward_apply (Stacks.Chow.fieldChowSituation k) p
      (𝟙 _) p (Category.comp_id p) 0 c (IsLocalRing.closedPoint k)).symm.trans hdeg2
    clear hdeg hdeg1 hdeg2
    simp only [ordZ_curveVal, curveDeg]
    rw [hsub (fun x => (p.residueDegree x : ℤ) * X.ord f x)
      (fun x hx => by rw [hord f x hx, mul_zero])]
    refine Eq.trans ?_ hdeg'
    refine finsum_congr fun x => ?_
    rw [finsum_eq_if, if_pos (by
      simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact Subsingleton.elim _ _), hc x]
    by_cases hx0 : X.ord f x = 0
    · rw [hx0]
      simp
    have hcx : (c.1 : AlgebraicCycle X ℤ) x ≠ 0 := by rw [hc x]; exact hx0
    have hrel := (Stacks.Chow.mem_cyclesOfDimension_iff_forall_point
      (Stacks.Chow.fieldChowSituation k) p 0 c.1).1 c.2 x hcx
    rw [if_pos, mul_comm]
    rw [hrel, Stacks.Chow.relativeDimension_id]
    exact (Stacks.Chow.fieldChowSituation_dimensionFunction_eq_zero k (p x)).symm

end DegreeFormula

end Stacks.BombieriStepanov

end
