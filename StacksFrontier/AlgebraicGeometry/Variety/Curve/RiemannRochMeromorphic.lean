module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochInvertibleDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree of an invertible module is the degree of the divisor of a meromorphic section

Let `k` be a field, let `X` be an integral scheme proper over `k` of topological dimension one and
let `ℳ` be an invertible `𝒪_X`-module. For every nonzero **meromorphic** section `s` of `ℳ` — an
element of the stalk of `ℳ` at the generic point of `X` —

`deg(ℳ) = deg(div(s))`,

that is, `χ(X, ℳ) − χ(X, 𝒪_X) = ∑_x ord_x(s) · [κ(x) : k]`, the sum being over the closed points
of `X`.

`AlgebraicGeometry.curveDegree k p hdim ℳ 1` is the left-hand side, `χ(X, ℳ) − 1 · χ(X, 𝒪_X)`,
and `Stacks.Chow.cycleDegree` of the zero cycle `Stacks.Chow.meromorphicDivisorCycle`, which is
`∑_x ord_x(s) · [x]`, is the right-hand side.

## Main results

* `AlgebraicGeometry.schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one`: an integral
  scheme of topological dimension one over a field has delta-dimension one.
* `AlgebraicGeometry.curveChernDegree_eq_cycleDegree_meromorphicDivisorCycle`: the degree of
  `c₁(ℳ) ∩ [X]` is the degree of `div(s)`.
* `AlgebraicGeometry.curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle`: the degree formula
  at a meromorphic section, `deg(ℳ) = deg(div(s))`.
* `AlgebraicGeometry.curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle_of_isCurve`: the same
  on a proper curve.
* `AlgebraicGeometry.eulerCharacteristic_eq_cycleDegree_meromorphicDivisorCycle_add`:
  Riemann-Roch in divisor form, `χ(X, ℳ) = deg(div(s)) + χ(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 0BRY](https://stacks.math.columbia.edu/tag/0BRY)
* [Stacks Project, Tag 0BRZ](https://stacks.math.columbia.edu/tag/0BRZ)
* [Stacks Project, Tag 0AZ3](https://stacks.math.columbia.edu/tag/0AZ3)
* [Stacks Project, Tag 0AZ2](https://stacks.math.columbia.edu/tag/0AZ2)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow Stacks.Divisors

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]

/-! ### Delta-dimension one -/

/-- **An integral scheme of topological dimension one, proper over a field, has delta-dimension
one.** -/
theorem schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one [IsIntegral X]
    (hone : topologicalKrullDim X = 1) :
    schemeDeltaDimension (fieldChowSituation k) p = ((1 : ℤ) : EInt) :=
  Stacks.Chow.schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq (n := 1) p
    (by rw [hone]; rfl)

/-! ### The Chern side is the degree of the divisor cycle -/

/-- **The Chern side of the degree formula is the degree of the divisor of a meromorphic
section.** On an integral `X` of delta-dimension one, proper over `k`, and for `ℳ` invertible with
a nonzero section `s` of the stalk of `ℳ` at the generic point,

`deg(c₁(ℳ) ∩ [X]_1) = deg(div(s))`. -/
theorem curveChernDegree_eq_cycleDegree_meromorphicDivisorCycle [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (hdelta : schemeDeltaDimension (fieldChowSituation k) p = ((1 : ℤ) : EInt)) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    curveChernDegree k p hdim (firstChernComponentCycleRule (fieldChowSituation k) p 0 M) =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        ((meromorphicDivisorCycle (fieldChowSituation k) p hdelta
            (fun x ↦
              have := Stacks.Divisors.isInvertible_presheaf M
              isTrivializedNear_of_isInvertible M x) s).val :
          CycleGroup (fieldChowSituation k) p 0) := by
  have hcap : firstChernClassCapOfInvertible (fieldChowSituation k) p 0 M
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p (𝟙 X) 1) =
      QuotientAddGroup.mk
        ((meromorphicDivisorCycle (fieldChowSituation k) p hdelta
            (fun x ↦
              have := Stacks.Divisors.isInvertible_presheaf M
              isTrivializedNear_of_isInvertible M x) s).val :
          CycleGroup (fieldChowSituation k) p 0) :=
    firstChernClassCapOfInvertible_fundamentalCycle_eq_mk (fieldChowSituation k) p hdelta M s hs
  rw [curveChernDegree_eq_chowDegree_firstChernClassCapOfInvertible, hcap]
  exact chowDegree_mk (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) p
    (IsLocalRing.closedPoint k) _

/-! ### The degree formula at a meromorphic section -/

/-- **The degree of an invertible module is the degree of the divisor of any nonzero meromorphic
section.** For `X` integral and proper over `k` of delta-dimension one and `ℳ` invertible of rank
one, and `s` a nonzero element of the stalk of `ℳ` at the generic point of `X`,

`deg(ℳ) = deg(div(s))`, that is, `χ(X, ℳ) − χ(X, 𝒪_X) = ∑_x ord_x(s) · [κ(x) : k]`. -/
theorem curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (hdelta : schemeDeltaDimension (fieldChowSituation k) p = ((1 : ℤ) : EInt)) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    curveDegree k p hdim M 1 =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        ((meromorphicDivisorCycle (fieldChowSituation k) p hdelta
            (fun x ↦
              have := Stacks.Divisors.isInvertible_presheaf M
              isTrivializedNear_of_isInvertible M x) s).val :
          CycleGroup (fieldChowSituation k) p 0) :=
  (curveDegree_eq_curveChernDegree_of_isInvertible k p hdim M).trans
    (curveChernDegree_eq_cycleDegree_meromorphicDivisorCycle k p hdim hdelta M s hs)

/-- **The degree formula at a meromorphic section on a proper curve.** For `X` a proper curve
over `k`, `ℳ` invertible of rank one and `s` a nonzero element of the stalk of `ℳ` at the generic
point of `X`, `deg(ℳ) = deg(div(s))`. -/
theorem curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle_of_isCurve [IsCurve k p]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1]
    (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    curveDegree k p hdim M 1 =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
        ((meromorphicDivisorCycle (fieldChowSituation k) p
            (schemeDeltaDimension_eq_one_of_topologicalKrullDim_eq_one k p
              (IsCurve.topologicalKrullDim_eq_one p))
            (fun x ↦
              have := Stacks.Divisors.isInvertible_presheaf M
              isTrivializedNear_of_isInvertible M x) s).val :
          CycleGroup (fieldChowSituation k) p 0) :=
  curveDegree_one_eq_cycleDegree_meromorphicDivisorCycle k p hdim _ M s hs

/-! ### Riemann-Roch in divisor form -/

/-- **Riemann-Roch in divisor form.** For `X` integral and proper over `k` of delta-dimension
one, `ℳ` invertible of rank one and `s` a nonzero meromorphic section of `ℳ`,

`χ(X, ℳ) = deg(div(s)) + χ(X, 𝒪_X)`. -/
@[sga "7 X 1.4" "special case"]
theorem eulerCharacteristic_eq_cycleDegree_meromorphicDivisorCycle_add [IsIntegral X]
    [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (hdelta : schemeDeltaDimension (fieldChowSituation k) p = ((1 : ℤ) : EInt)) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1] [M.IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf).IsCoherent]
    (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    eulerCharacteristic k p M =
      cycleDegree (fieldChowSituation k) p (IsLocalRing.closedPoint k)
          ((meromorphicDivisorCycle (fieldChowSituation k) p hdelta
              (fun x ↦
                have := Stacks.Divisors.isInvertible_presheaf M
                isTrivializedNear_of_isInvertible M x) s).val :
            CycleGroup (fieldChowSituation k) p 0) +
        eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf) :=
  (eulerCharacteristic_eq_curveChernDegree_add_of_isInvertible_of_isProper k p hdim M).trans
    (congrArg (· + eulerCharacteristic k p (SheafOfModules.unit X.ringCatSheaf))
      (curveChernDegree_eq_cycleDegree_meromorphicDivisorCycle k p hdim hdelta M s hs))

end AlgebraicGeometry

end
