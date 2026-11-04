module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksCore.Tactic.StacksAttribute

/-!
# The divisor differential on pointwise Milnor K-chains

Let `(S, δ)` be the base situation of chapter 42 and `p : X ⟶ S` locally of finite type. Stacks
0GU3 presents the Chow group of `X` in degree `k` as the cokernel of a map

`⨁_{Δ(x) = k + 1} K₁(κ(x)) ⟶ ⨁_{Δ(y) = k} K₀(κ(y))`,

both sums locally finite; the target is the group of `k`-cycles, by Stacks 0GU2. This file
constructs that map.

A point `x` of relative dimension `k + 1` spans the integral closed subscheme `closure {x}`, of
delta-dimension `k + 1`, and the degree-one Milnor K-group of `κ(x)` is `κ(x)ˣ`, which is the
group of nonzero rational functions on `closure {x}` (Stacks 01RV). The component of the
differential at `x` is therefore the principal divisor of that rational function, pushed forward
to `X`, and the differential is the locally finite sum of these over all such `x`, which is a
`k`-cycle by Stacks 02RW.

## Main definitions

* `Stacks.Chow.PointwiseKOneGroup` — the locally finite direct sum of the degree-one Milnor
  K-groups of the residue fields at the points of relative dimension `k + 1`.
* `Stacks.Chow.rationalFunctionsEquivResidueFieldOfGenericPoint`,
  `Stacks.Chow.rationalFunctionUnitsEquivOfGenericPoint` — the rational functions on an integral
  closed subscheme are the residue field of the ambient scheme at its generic point.
* `Stacks.Chow.integralComponentFunction` — the nonzero rational function on `closure {x}` with a
  prescribed value at `x`.
* `Stacks.Chow.pointwiseDivisorTerm` — the contribution of a single point to the differential.
* `Stacks.Chow.pointwiseDivisorSum` — the `k`-cycle which is the divisor of a pointwise chain.
* `Stacks.Chow.IsPointwiseDivisorDifferential` — the coordinatewise divisor formula
  characterising the differential.
* `Stacks.Chow.pointwiseDivisorDifferential` — the differential itself.

## Main results

* `Stacks.Chow.principalDivisorPushforward_one`,
  `Stacks.Chow.principalDivisorPushforward_mul` — the pushed-forward principal divisor is
  additive in the rational function.
* `Stacks.Chow.pointwiseDivisorSum_apply` — the coefficient of the divisor of a pointwise chain
  is the locally finite sum of the contributions of all the points of relative dimension `k + 1`.
* `Stacks.Chow.principalDivisorFamilyCoefficient_eq_of_genericPointOf` — the divisor formula does
  not depend on the presentation of the supporting points as integral closed subschemes.
* `Stacks.Chow.pointwiseDivisorDifferential_spec`,
  `Stacks.Chow.exists_pointwiseDivisorDifferential` — Stacks 0GU3: the differential satisfies the
  divisor formula.

## Implementation notes

The index type of the family of subschemes attached to a chain `a` is the set of points where `a`
is nonzero, so it varies with `a`. Additivity is therefore proved after rewriting the coefficient
as a locally finite sum over *all* points of relative dimension `k + 1`, a point at which the
chain vanishes contributing the zero cycle.

The characterising property quantifies over an arbitrary family of integral closed subschemes
whose generic points are the supporting points of `a`, rather than only over the canonical family
`closure {x}`: an integral closed subscheme is the reduced induced structure on the closure of its
generic point, so the two agree, and the quantified form is the one a consumer of the differential
can supply.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0BE3](https://stacks.math.columbia.edu/tag/0BE3)
* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Additivity of the pushed-forward principal divisor -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)

/-- Pushing a cycle forward along the closed immersion of a closed subscheme is additive: the
coefficient at a point of the subscheme is transported, and every other coefficient is zero. -/
theorem closedSubschemeCyclePushforward_add (W : X.IdealSheafData)
    (c d : AlgebraicCycle W.subscheme ℤ) :
    closedSubschemeCyclePushforward C p W (c + d) =
      closedSubschemeCyclePushforward C p W c + closedSubschemeCyclePushforward C p W d := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ Set.range W.subschemeι.base
  · obtain ⟨z, rfl⟩ := hx
    simp
  · simp [closedSubschemeCyclePushforward_apply_of_notMem_range C p W _ hx]

/-- Pushing the zero cycle forward along the closed immersion of a closed subscheme gives the
zero cycle. -/
@[simp]
theorem closedSubschemeCyclePushforward_zero (W : X.IdealSheafData) :
    closedSubschemeCyclePushforward C p W 0 = 0 := by
  have h := closedSubschemeCyclePushforward_add C p W 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

/-- **Stacks 0BE3.** The principal divisor of the constant rational function `1` is the zero
cycle, since the principal divisor turns products into sums. -/
@[simp]
theorem principalCycle_one (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] :
    principalCycle Y 1 = 0 := by
  have h := principalCycle_mul Y (f := 1) (g := 1) one_ne_zero one_ne_zero
  rw [one_mul] at h
  exact add_eq_left.mp h.symm

/-- A unit of the ring of rational functions on an integral scheme has nonzero image in the
function field. -/
theorem rationalFunctionsEquivFunctionField_ne_zero (Y : Scheme.{u}) [IsIntegral Y]
    (g : (rationalFunctions Y)ˣ) :
    (rationalFunctionsEquivFunctionField Y).1 (g : rationalFunctions Y) ≠ 0 :=
  fun h ↦ g.ne_zero ((rationalFunctionsEquivFunctionField Y).1.injective
    (h.trans (map_zero _).symm))

section PushforwardAdditive

variable [LocallyOfFiniteType p]

/-- The pushforward of the principal divisor of the constant rational function `1` on an integral
closed subscheme is the zero cycle. -/
@[simp]
theorem principalDivisorPushforward_one (V : X.IdealSheafData) (hV : IsIntegral V.subscheme) :
    principalDivisorPushforward C p V hV 1 = 0 := by
  let _ := hV
  let _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  rw [principalDivisorPushforward_eq,
    show ((1 : (rationalFunctions V.subscheme)ˣ) : rationalFunctions V.subscheme) = 1 from rfl,
    map_one, principalCycle_one, closedSubschemeCyclePushforward_zero]

/-- **Stacks 02RP.** The pushforward of the principal divisor of a product of nonzero rational
functions on an integral closed subscheme is the sum of the two pushforwards. -/
theorem principalDivisorPushforward_mul (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g h : (rationalFunctions V.subscheme)ˣ) :
    principalDivisorPushforward C p V hV (g * h) =
      principalDivisorPushforward C p V hV g + principalDivisorPushforward C p V hV h := by
  let _ := hV
  let _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ p)
  rw [principalDivisorPushforward_eq, principalDivisorPushforward_eq,
    principalDivisorPushforward_eq,
    show ((g * h : (rationalFunctions V.subscheme)ˣ) : rationalFunctions V.subscheme) =
      (g : rationalFunctions V.subscheme) * (h : rationalFunctions V.subscheme) from rfl,
    map_mul, principalCycle_mul _ (rationalFunctionsEquivFunctionField_ne_zero V.subscheme g)
      (rationalFunctionsEquivFunctionField_ne_zero V.subscheme h),
    closedSubschemeCyclePushforward_add]

end PushforwardAdditive

/-! ### Rational functions on the integral closed subscheme attached to a point -/

/-- **Stacks 01RV.** The field of rational functions on an integral closed subscheme `W` of `X`
whose generic point is `x` is the residue field of `X` at `x`: the rational functions on an
integral scheme are the residue field at its generic point, and a closed immersion identifies the
residue field at a point of the subscheme with the one at its image. -/
def rationalFunctionsEquivResidueFieldOfGenericPoint (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) {x : X} (hx : genericPointOf W hW = x) :
    rationalFunctions W.subscheme ≃+* X.residueField x :=
  letI := hW
  ((rationalFunctionsEquivResidueField W.subscheme).1.trans
    (RingEquiv.ofBijective (W.subschemeι.residueFieldMap (genericPoint W.subscheme)).hom
      (bijective_residueFieldMap_of_isClosedImmersion W.subschemeι _)).symm).trans
    (X.residueFieldCongr hx).commRingCatIsoToRingEquiv

/-- **Stacks 01RV.** The nonzero rational functions on an integral closed subscheme `W` of `X`
whose generic point is `x` are the units of the residue field of `X` at `x`. -/
def rationalFunctionUnitsEquivOfGenericPoint (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) {x : X} (hx : genericPointOf W hW = x) :
    (rationalFunctions W.subscheme)ˣ ≃* (X.residueField x)ˣ :=
  Units.mapEquiv (rationalFunctionsEquivResidueFieldOfGenericPoint W hW hx).toMulEquiv

/-- The nonzero rational function on the integral closed subscheme `closure {x}` whose value at
the generic point `x` is a prescribed unit of the residue field of `X` there. -/
def integralComponentFunction (x : X) (u : (X.residueField x)ˣ) :
    (rationalFunctions (integralComponentAt x).subscheme)ˣ :=
  (rationalFunctionUnitsEquivOfGenericPoint (integralComponentAt x)
    (isIntegral_integralComponentAt x) (genericPointOf_integralComponentAt x)).symm u

/-- The value at `x` of the rational function on `closure {x}` attached to a unit of the residue
field at `x` is that unit. -/
@[simp]
theorem integralComponentFunction_value (x : X) (u : (X.residueField x)ˣ) :
    rationalFunctionUnitsEquivOfGenericPoint (integralComponentAt x)
        (isIntegral_integralComponentAt x) (genericPointOf_integralComponentAt x)
        (integralComponentFunction x u) = u :=
  (rationalFunctionUnitsEquivOfGenericPoint _ _ _).apply_symm_apply u

/-- The rational function on `closure {x}` attached to the unit `1` is the constant function
`1`. -/
@[simp]
theorem integralComponentFunction_one (x : X) : integralComponentFunction x 1 = 1 := by
  simp [integralComponentFunction]

/-- Reading a unit of the residue field at `x` as a rational function on `closure {x}` is
multiplicative. -/
@[simp]
theorem integralComponentFunction_mul (x : X) (u v : (X.residueField x)ˣ) :
    integralComponentFunction x (u * v) =
      integralComponentFunction x u * integralComponentFunction x v := by
  simp [integralComponentFunction]

/-! ### Pointwise Milnor K₁-chains -/

/-- **Stacks 0GU3.** The group of locally finite families of degree-one Milnor K-classes at the
points of relative dimension `k + 1`: the source of the divisor differential. -/
abbrev PointwiseKOneGroup (k : ℤ) : Type u :=
  ↥(locallyFiniteDirectSum X (pointsOfDimension C p (k + 1))
    fun x ↦ MilnorKTheory (X.residueField x.1) 1)

/-- The nonzero rational function on `closure {x}` attached to the degree-one Milnor K-class of a
pointwise chain at a point `x` of relative dimension `k + 1`. -/
def pointwiseComponentFunction (k : ℤ) (a : PointwiseKOneGroup C p k)
    (x : pointsOfDimension C p (k + 1)) :
    (rationalFunctions (integralComponentAt x.1).subscheme)ˣ :=
  integralComponentFunction x.1
    (Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x.1) (a.1 x)))

/-- Where the chain vanishes, the attached rational function is the constant function `1`. -/
theorem pointwiseComponentFunction_of_eq_zero (k : ℤ) (a : PointwiseKOneGroup C p k)
    {x : pointsOfDimension C p (k + 1)} (hx : a.1 x = 0) :
    pointwiseComponentFunction C p k a x = 1 := by
  simp [pointwiseComponentFunction, hx]

/-- The rational function attached to a sum of pointwise chains is the product of the rational
functions attached to the summands. -/
theorem pointwiseComponentFunction_add (k : ℤ) (a b : PointwiseKOneGroup C p k)
    (x : pointsOfDimension C p (k + 1)) :
    pointwiseComponentFunction C p k (a + b) x =
      pointwiseComponentFunction C p k a x * pointwiseComponentFunction C p k b x := by
  simp [pointwiseComponentFunction, show (a + b).1 x = a.1 x + b.1 x from rfl]

/-- The closures of the points at which a pointwise chain is nonzero form a locally finite
family: every point of `X` has an affine, hence quasi-compact, open neighbourhood containing only
finitely many of those points, and the closure of a point meets an open set only if the point
itself does. -/
theorem locallyFinite_closure_pointwiseSupport (k : ℤ) (a : PointwiseKOneGroup C p k) :
    LocallyFinite fun j : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} ↦
      closure ({j.1.1} : Set X) := by
  intro z
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  refine ⟨(U : Set X), U.2.mem_nhds hzU, ?_⟩
  refine Set.Finite.of_finite_image
    (f := fun j : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} ↦ j.1)
    ((a.2 U hUaff.isCompact).subset ?_) (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨j, ⟨w, hwcl, hwU⟩, rfl⟩
  obtain ⟨v, hvU, hv⟩ := mem_closure_iff.mp hwcl (U : Set X) U.2 hwU
  exact ⟨by rw [← Set.mem_singleton_iff.mp hv]; exact hvU, j.2⟩

/-! ### The divisor of a pointwise Milnor K₁-chain -/

variable [LocallyOfFiniteType p]

/-- The contribution of the point `x` to the divisor of a pointwise Milnor K₁-chain: the
pushforward to `X` of the principal divisor on `closure {x}` of the rational function attached to
the Milnor K-class of the chain at `x`. -/
def pointwiseDivisorTerm (k : ℤ) (a : PointwiseKOneGroup C p k)
    (x : pointsOfDimension C p (k + 1)) : AlgebraicCycle X ℤ :=
  principalDivisorPushforward C p (integralComponentAt x.1) (isIntegral_integralComponentAt x.1)
    (pointwiseComponentFunction C p k a x)

/-- A point where the chain vanishes contributes nothing to its divisor. -/
theorem pointwiseDivisorTerm_of_eq_zero (k : ℤ) (a : PointwiseKOneGroup C p k)
    {x : pointsOfDimension C p (k + 1)} (hx : a.1 x = 0) :
    pointwiseDivisorTerm C p k a x = 0 := by
  rw [pointwiseDivisorTerm, pointwiseComponentFunction_of_eq_zero C p k a hx,
    principalDivisorPushforward_one]

/-- A point where the chain vanishes contributes the coefficient zero at every point of `X`. -/
theorem pointwiseDivisorTerm_apply_of_eq_zero (k : ℤ) (a : PointwiseKOneGroup C p k)
    {x : pointsOfDimension C p (k + 1)} (hx : a.1 x = 0) (y : X) :
    pointwiseDivisorTerm C p k a x y = 0 := by
  rw [pointwiseDivisorTerm_of_eq_zero C p k a hx]
  rfl

/-- The contribution of a point to the divisor of a pointwise chain is supported on the closure
of that point. -/
theorem support_pointwiseDivisorTerm_subset (k : ℤ) (a : PointwiseKOneGroup C p k)
    (x : pointsOfDimension C p (k + 1)) :
    Function.support (pointwiseDivisorTerm C p k a x) ⊆ closure ({x.1} : Set X) := by
  simp only [pointwiseDivisorTerm]
  simpa only [coe_support_integralComponentAt] using
    support_principalDivisorPushforward_subset C p (integralComponentAt x.1)
      (isIntegral_integralComponentAt x.1) (pointwiseComponentFunction C p k a x)

/-- Away from the closure of a point, that point contributes nothing to the divisor. -/
theorem pointwiseDivisorTerm_apply_of_notMem_closure (k : ℤ) (a : PointwiseKOneGroup C p k)
    (x : pointsOfDimension C p (k + 1)) {y : X} (hy : y ∉ closure ({x.1} : Set X)) :
    pointwiseDivisorTerm C p k a x y = 0 := by
  by_contra h
  exact hy (support_pointwiseDivisorTerm_subset C p k a x h)

/-- The contribution of a point to the divisor is additive in the chain. -/
theorem pointwiseDivisorTerm_add (k : ℤ) (a b : PointwiseKOneGroup C p k)
    (x : pointsOfDimension C p (k + 1)) :
    pointwiseDivisorTerm C p k (a + b) x =
      pointwiseDivisorTerm C p k a x + pointwiseDivisorTerm C p k b x := by
  rw [pointwiseDivisorTerm, pointwiseComponentFunction_add, principalDivisorPushforward_mul]
  rfl

/-- At a fixed point of `X` only finitely many points of relative dimension `k + 1` contribute to
the divisor of a pointwise chain. -/
theorem finite_support_pointwiseDivisorTerm (k : ℤ) (a : PointwiseKOneGroup C p k) (y : X) :
    (Function.support fun x : pointsOfDimension C p (k + 1) ↦
      pointwiseDivisorTerm C p k a x y).Finite := by
  obtain ⟨t, ht, hfin⟩ := locallyFinite_closure_pointwiseSupport C p k a y
  refine (Set.Finite.image
    (fun j : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} ↦ j.1) hfin).subset ?_
  intro x hx
  have hax : a.1 x ≠ 0 := fun h ↦ hx (pointwiseDivisorTerm_apply_of_eq_zero C p k a h y)
  have hy : y ∈ closure ({x.1} : Set X) := by
    by_contra hnot
    exact hx (pointwiseDivisorTerm_apply_of_notMem_closure C p k a x hnot)
  exact ⟨⟨x, hax⟩, ⟨y, hy, mem_of_mem_nhds ht⟩, rfl⟩

/-- **Stacks 02RW.** The locally finite sum of the contributions of the points of relative
dimension `k + 1` to the divisor of a pointwise Milnor K₁-chain is a `k`-cycle. -/
theorem exists_pointwiseDivisorSum (k : ℤ) (a : PointwiseKOneGroup C p k) :
    ∃ α : CycleGroup C p k, ∀ y : X, α.1 y =
      principalDivisorFamilyCoefficient C p
        (fun j : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} ↦
          integralComponentAt j.1.1)
        (fun j ↦ isIntegral_integralComponentAt j.1.1)
        (fun j ↦ pointwiseComponentFunction C p k a j.1) y :=
  exists_principalDivisorFamilySum C p k _ _
    (fun j ↦ by
      rw [schemeDeltaDimension_integralComponentAt C p]
      exact congrArg _ ((mem_pointsOfDimension C p).mp j.1.2))
    (by
      simpa only [coe_support_integralComponentAt] using
        locallyFinite_closure_pointwiseSupport C p k a)
    _

/-- The `k`-cycle which is the divisor of a pointwise Milnor K₁-chain. -/
def pointwiseDivisorSum (k : ℤ) (a : PointwiseKOneGroup C p k) : CycleGroup C p k :=
  (exists_pointwiseDivisorSum C p k a).choose

/-- The coefficients of the divisor of a pointwise chain are given by the divisor formula for the
family of closures of the points at which the chain is nonzero. -/
theorem pointwiseDivisorSum_spec (k : ℤ) (a : PointwiseKOneGroup C p k) (y : X) :
    (pointwiseDivisorSum C p k a).1 y =
      principalDivisorFamilyCoefficient C p
        (fun j : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} ↦
          integralComponentAt j.1.1)
        (fun j ↦ isIntegral_integralComponentAt j.1.1)
        (fun j ↦ pointwiseComponentFunction C p k a j.1) y :=
  (exists_pointwiseDivisorSum C p k a).choose_spec y

/-- The coefficient of the divisor of a pointwise chain at a point of `X` is the locally finite
sum, over *all* points of relative dimension `k + 1`, of their contributions: a point at which
the chain vanishes contributes nothing. -/
theorem pointwiseDivisorSum_apply (k : ℤ) (a : PointwiseKOneGroup C p k) (y : X) :
    (pointwiseDivisorSum C p k a).1 y =
      ∑ᶠ x : pointsOfDimension C p (k + 1), pointwiseDivisorTerm C p k a x y := by
  rw [pointwiseDivisorSum_spec]
  have hsub : (Function.support fun x : pointsOfDimension C p (k + 1) ↦
      pointwiseDivisorTerm C p k a x y) ⊆ {x | a.1 x ≠ 0} := by
    intro x hx
    by_contra hax
    exact hx (pointwiseDivisorTerm_apply_of_eq_zero C p k a (not_not.mp hax) y)
  have h := finsum_set_coe_eq_finsum_mem
    (f := fun x : pointsOfDimension C p (k + 1) ↦ pointwiseDivisorTerm C p k a x y)
    {x : pointsOfDimension C p (k + 1) | a.1 x ≠ 0}
  rw [finsum_mem_def, Set.indicator_eq_self.mpr hsub] at h
  exact h

/-- The divisor of a pointwise Milnor K₁-chain is additive. -/
theorem pointwiseDivisorSum_add (k : ℤ) (a b : PointwiseKOneGroup C p k) :
    pointwiseDivisorSum C p k (a + b) =
      pointwiseDivisorSum C p k a + pointwiseDivisorSum C p k b := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  show (pointwiseDivisorSum C p k (a + b)).1 y =
    (pointwiseDivisorSum C p k a).1 y + (pointwiseDivisorSum C p k b).1 y
  rw [pointwiseDivisorSum_apply, pointwiseDivisorSum_apply, pointwiseDivisorSum_apply,
    ← finsum_add_distrib (finite_support_pointwiseDivisorTerm C p k a y)
      (finite_support_pointwiseDivisorTerm C p k b y)]
  refine finsum_congr fun x ↦ ?_
  rw [pointwiseDivisorTerm_add]
  rfl

/-- The divisor of the zero chain is the zero cycle. -/
@[simp]
theorem pointwiseDivisorSum_zero (k : ℤ) : pointwiseDivisorSum C p k 0 = 0 := by
  have h := pointwiseDivisorSum_add C p k 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

/-- The divisor formula does not depend on how the points carrying a pointwise chain are
presented as integral closed subschemes: an integral closed subscheme is the reduced induced
structure on the closure of its generic point, and a rational function on it is determined by its
value there. -/
theorem principalDivisorFamilyCoefficient_eq_of_genericPointOf (k : ℤ)
    (a : PointwiseKOneGroup C p k)
    (W : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hGeneric : ∀ j, genericPointOf (W j) (hW j) = j.1.1)
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ)
    (hCompat : ∀ j, rationalFunctionUnitsEquivOfGenericPoint (W j) (hW j) (hGeneric j) (g j) =
      Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField j.1.1) (a.1 j.1)))
    (y : X) :
    principalDivisorFamilyCoefficient C p W hW g y =
      principalDivisorFamilyCoefficient C p
        (fun j : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} ↦
          integralComponentAt j.1.1)
        (fun j ↦ isIntegral_integralComponentAt j.1.1)
        (fun j ↦ pointwiseComponentFunction C p k a j.1) y := by
  have hWfun : W = fun j ↦ integralComponentAt j.1.1 :=
    funext fun j ↦ (integralComponentAt_genericPointOf (W j) (hW j)).symm.trans
      (congrArg integralComponentAt (hGeneric j))
  subst hWfun
  have hgj : ∀ j, g j = pointwiseComponentFunction C p k a j.1 := fun j ↦
    (rationalFunctionUnitsEquivOfGenericPoint (integralComponentAt j.1.1) (hW j)
        (hGeneric j)).injective
      ((hCompat j).trans (integralComponentFunction_value j.1.1 _).symm)
  show (∑ᶠ j, principalDivisorPushforward C p _ _ (g j) y) = _
  exact finsum_congr fun j ↦ by rw [hgj j]

/-! ### The divisor differential -/

/-- **Stacks 0GU3.** The coordinatewise divisor formula characterising the differential from
pointwise Milnor K₁-chains to pointwise Milnor K₀-chains: for every chain `a`, every presentation
of the points at which `a` is nonzero as integral closed subschemes `W j` carrying nonzero
rational functions `g j` whose values at the generic points are the Milnor K₁-classes of `a`, and
every point `y` of relative dimension `k`, the degree-zero coordinate of `d a` at `y` is the
coefficient at `y` of the sum of the pushed-forward principal divisors of the `g j`. -/
def IsPointwiseDivisorDifferential (k : ℤ)
    (d : PointwiseKOneGroup C p k →+ PointwiseCycleGroup C p k) : Prop :=
  ∀ (a : PointwiseKOneGroup C p k)
    (W : {x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0} → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hGeneric : ∀ j, genericPointOf (W j) (hW j) = j.1.1)
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ),
    (∀ j, rationalFunctionUnitsEquivOfGenericPoint (W j) (hW j) (hGeneric j) (g j) =
      Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField j.1.1) (a.1 j.1))) →
    ∀ y : pointsOfDimension C p k,
      milnorKTheoryZeroAddEquiv (X.residueField y.1) ((d a).1 y) =
        principalDivisorFamilyCoefficient C p W hW g y.1

/-- **Stacks 0GU3.** The divisor differential from pointwise Milnor K₁-chains at the points of
relative dimension `k + 1` to pointwise Milnor K₀-chains at the points of relative dimension `k`:
each Milnor K₁-class is read as a nonzero rational function on the closure of its point, and the
differential is the locally finite sum of the pushed-forward principal divisors, transported to
the pointwise description of cycles of Stacks 0GU2. -/
@[stacks 0GU3 "pointwise_divisor_differential",
  stacks 0EAY "the second of the two arrows of the remark's displayed diagram, in the case \
i = 1: the map ⊕_{δ(x) = j} K^M_1(κ(x)) ⟶ ⊕_{δ(x) = j - 1} K^M_0(κ(x)), which on the \
identifications K^M_1(κ(x)) = κ(x)^* and K^M_0(κ(x)) = ℤ of the remark is the order of vanishing"]
def pointwiseDivisorDifferential (k : ℤ) :
    PointwiseKOneGroup C p k →+ PointwiseCycleGroup C p k :=
  (pointwiseCycleEquiv C p k).toAddMonoidHom.comp
    { toFun := pointwiseDivisorSum C p k
      map_zero' := pointwiseDivisorSum_zero C p k
      map_add' := pointwiseDivisorSum_add C p k }

/-- **Stacks 0GU3.** The divisor differential satisfies the coordinatewise divisor formula. -/
@[stacks 0GU3 "pointwise_divisor_differential"]
theorem pointwiseDivisorDifferential_spec (k : ℤ) :
    IsPointwiseDivisorDifferential C p k (pointwiseDivisorDifferential C p k) := by
  intro a W hW hGeneric g hCompat y
  have hcoord : milnorKTheoryZeroAddEquiv (X.residueField y.1)
      ((pointwiseDivisorDifferential C p k a).1 y) = (pointwiseDivisorSum C p k a).1 y :=
    pointwiseCycleEquiv_apply C p k (pointwiseDivisorSum C p k a) y
  rw [hcoord, pointwiseDivisorSum_spec]
  exact (principalDivisorFamilyCoefficient_eq_of_genericPointOf C p k a W hW hGeneric g
    hCompat y.1).symm

/-- **Stacks 0GU3.** There is a homomorphism from pointwise Milnor K₁-chains to pointwise Milnor
K₀-chains satisfying the coordinatewise divisor formula. -/
@[stacks 0GU3 "pointwise_divisor_differential"]
theorem exists_pointwiseDivisorDifferential (k : ℤ) :
    ∃ d : PointwiseKOneGroup C p k →+ PointwiseCycleGroup C p k,
      IsPointwiseDivisorDifferential C p k d :=
  ⟨pointwiseDivisorDifferential C p k, pointwiseDivisorDifferential_spec C p k⟩

end Stacks.Chow

end
