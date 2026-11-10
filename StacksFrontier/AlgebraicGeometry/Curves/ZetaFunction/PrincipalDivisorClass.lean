module

public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.VanishingIdealStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorMiddleExactness

/-!
# Principal divisors on a curve and the Picard group

Let `C` be a smooth proper curve over an algebraically closed field `Ω`, with function field
`K`. A nonzero `f ∈ K` has a divisor `div f = ∑ ord_x(f) x` on the closed points, and a divisor
`D` on the closed points has a class `[D] ∈ Pic(C)` (`Stacks.Zeta.divisorClass`). This file
proves the two halves of the exact sequence `K^× → Div(C) → Pic(C)`:

* `[div f] = 0` (`Stacks.Zeta.divisorClass_divOf`), and
* `[D] = 0` only if `D = div f` for some `f ≠ 0`
  (`Stacks.Zeta.exists_divOf_eq_of_divisorClass_eq_zero`),

by passing through the Weil divisor class group: the first Chern class `Pic(C) → Cl(C)` is
injective on the normal scheme `C` (Tag 0BE8), sends `[x]` to the class of the prime divisor `x`
(the order of a local equation of the reduced point is `1` at `x` and `0` elsewhere), and
`Cl(C)` is the Weil divisors modulo the principal ones. As consequences, `div f` has degree `0`
and a function without zeros or poles is a constant
(`Stacks.Zeta.exists_eq_algebraMap_of_divOf_eq_zero`).

## Main definitions

* `Stacks.Zeta.divOf`: the divisor of a rational function on the closed points.

## Main results

* `Stacks.Zeta.divisorClass_divOf`, `Stacks.Zeta.exists_divOf_eq_of_divisorClass_eq_zero`.
* `Stacks.Zeta.degree_divOf`: `deg (div f) = 0`.
* `Stacks.Zeta.exists_eq_algebraMap_of_divOf_eq_zero`: `div f = 0` forces `f ∈ Ω`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order

universe u

namespace Stacks.Zeta

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

/-! ### Closed points and prime divisors -/

/-- The prime divisor of a closed point. -/
def primeDivisorOfClosedPoint (x : ClosedPoint C) : PrimeDivisor C :=
  PrimeDivisor.ofCoheightOne x.1 (coheight_eq_one_of_isClosed g x.2)

/-- The generic point of a prime divisor of a curve is a closed point. -/
def closedPointOfPrimeDivisor (Z : PrimeDivisor C) : ClosedPoint C :=
  ⟨Z.genericPoint, Stacks.EtaleCohomology.isClosed_singleton_of_coheight_eq_one g
    (PrimeDivisor.coheight_genericPoint Z)⟩

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
/-- Distinct prime divisors have distinct generic points. -/
theorem closedPointOfPrimeDivisor_injective :
    Function.Injective (closedPointOfPrimeDivisor g) := fun _ _ h =>
  PrimeDivisor.genericPoint_injective (congrArg Subtype.val h)

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
/-- The generic point of the prime divisor of a closed point `x` is `x`. -/
theorem closedPointOfPrimeDivisor_primeDivisorOfClosedPoint
    (x : ClosedPoint C) :
    closedPointOfPrimeDivisor g (primeDivisorOfClosedPoint g x) = x :=
  Subtype.ext (PrimeDivisor.genericPoint_ofCoheightOne _ _)

/-! ### Divisors on closed points as Weil divisors -/

/-- A divisor on the closed points, read as a Weil divisor. -/
def toWeil (D : ClosedPoint C →₀ ℤ) : WeilDivisor C :=
  ⟨fun Z => D (closedPointOfPrimeDivisor g Z), by
    refine mem_weilDivisor_of_forall_exists_open fun x => ⟨Set.univ, isOpen_univ, trivial, ?_⟩
    refine ((D.support.finite_toSet.preimage
      (closedPointOfPrimeDivisor_injective g).injOn)).subset fun Z hZ => ?_
    simpa using hZ.2⟩

/-- The Weil divisors of the closed points: an additive map. -/
def toWeilHom : (ClosedPoint C →₀ ℤ) →+ WeilDivisor C where
  toFun := toWeil g
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
/-- The multiplicity of `toWeil g D` at a prime divisor `Z` is the coefficient of `D` at the
generic point of `Z`. -/
@[simp]
theorem toWeil_val_apply (D : ClosedPoint C →₀ ℤ) (Z : PrimeDivisor C) :
    (toWeil g D).val Z = D (closedPointOfPrimeDivisor g Z) := rfl

/-! ### The first Chern class of a point -/

omit [IsAlgClosed Ω] [IsProper g] [IsCurve Ω g] [IsLocallyNoetherian C] in
include g in
/-- A smooth curve over a field is a normal scheme. -/
theorem isNormal_of_curve : IsNormal C :=
  isNormal_of_isRegular C (isRegular_of_smooth_over_field g)

/-- The first Chern class `Pic(C) → Cl(C)`. -/
def firstChern (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C] :
    Stacks.Picard.ofScheme C →+ weilDivisorClassGroup C :=
  picardToWeilDivisorClassGroup C

omit [IsLocallyNoetherian C] in
/-- The order of the image of a unit of a local ring is zero. -/
theorem ord_algebraMap_isUnit [IsIntegral C] [IsLocallyNoetherian C] {x : C}
    (hx : coheight x = 1) [IsDiscreteValuationRing (C.presheaf.stalk x)]
    {c : C.presheaf.stalk x} (hc : IsUnit c) :
    C.ord (algebraMap (C.presheaf.stalk x) C.functionField c) x = 0 := by
  obtain ⟨d, hd⟩ := hc.exists_right_inv
  have hc0 : c ≠ 0 := hc.ne_zero
  have hd0 : d ≠ 0 := fun h => by simp [h] at hd
  have h1 := Stacks.BombieriStepanov.ord_algebraMap_nonneg hx hc0
  have h2 := Stacks.BombieriStepanov.ord_algebraMap_nonneg hx hd0
  have hsum := Scheme.ord_mul (x := x)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hc0)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hd0)
  rw [← map_mul, hd, map_one, Stacks.BombieriStepanov.scheme_ord_one] at hsum
  omega

omit [IsAlgClosed Ω] [IsProper g] in
/-- **The first Chern class of a point class** is the class of the prime divisor of the
point. -/
theorem firstChern_pointClass (x : ClosedPoint C) :
    firstChern C (pointClass g x) = (toWeil g (Finsupp.single x 1) : weilDivisorClassGroup C) := by
  classical
  have := isEffectiveCartierDivisor_pointIdeal g x
  refine (weilDivisorClassOfPicardClass_picardClass C _).trans ?_
  refine weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord (pointIdeal x) _ fun Z c hc => ?_
  have hZ1 := PrimeDivisor.coheight_genericPoint Z
  have := Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one g _ hZ1
  rw [toWeil_val_apply]
  by_cases hZx : closedPointOfPrimeDivisor g Z = x
  · subst hZx
    rw [Finsupp.single_eq_same]
    have hmax : IdealSheafData.stalk (pointIdeal (closedPointOfPrimeDivisor g Z))
        Z.genericPoint = IsLocalRing.maximalIdeal (C.presheaf.stalk Z.genericPoint) :=
      Stacks.Divisors.stalk_vanishingIdeal_singleton_of_isClosed _ _
    rw [hmax] at hc
    have hirr : Irreducible c := (IsDiscreteValuationRing.irreducible_iff_uniformizer c).2 hc
    exact (Stacks.BombieriStepanov.ord_algebraMap_irreducible hZ1 hirr).symm
  · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hZx)]
    have hnot : Z.genericPoint ∉ (pointIdeal x).support := by
      intro h
      have h' : Z.genericPoint ∈ ((pointIdeal x).support : Set C) := h
      rw [pointIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h'
      exact hZx (Subtype.ext h')
    have htop := (Stacks.Divisors.stalk_eq_top_iff_notMem_support (pointIdeal x)
      Z.genericPoint).2 hnot
    rw [htop, eq_comm, Ideal.span_singleton_eq_top] at hc
    exact (ord_algebraMap_isUnit hZ1 hc).symm

omit [IsAlgClosed Ω] [IsProper g] in
/-- **The first Chern class of a divisor class** is the class of the divisor. -/
theorem firstChern_divisorClass (D : ClosedPoint C →₀ ℤ) :
    firstChern C (divisorClass g D) = (toWeil g D : weilDivisorClassGroup C) := by
  have key : (firstChern C).comp (divisorClass g) =
      (QuotientAddGroup.mk' (principalWeilDivisors C)).comp (toWeilHom g) := by
    refine Finsupp.addHom_ext fun x n => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, divisorClass_single, map_zsmul,
      firstChern_pointClass, QuotientAddGroup.mk'_apply]
    rw [← QuotientAddGroup.mk_zsmul]
    congr 1
    refine Subtype.ext (funext fun Z => ?_)
    change n * (Finsupp.single x 1) (closedPointOfPrimeDivisor g Z) =
      (Finsupp.single x n) (closedPointOfPrimeDivisor g Z)
    classical
    by_cases h : x = closedPointOfPrimeDivisor g Z
    · simp [h]
    · simp [h]
  exact DFunLike.congr_fun key D

/-! ### Divisors of rational functions -/

omit [IsAlgClosed Ω] in
include g in
/-- A nonzero rational function has nonzero order at only finitely many closed points. -/
theorem finite_setOf_ord_ne_zero {f : C.functionField} (hf : f ≠ 0) :
    {x : ClosedPoint C | C.ord f x.1 ≠ 0}.Finite := by
  have hdvr : ∀ x : C, coheight x = 1 → IsDiscreteValuationRing (C.presheaf.stalk x) :=
    fun x hx => Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one g x hx
  have hfin := (Stacks.BombieriStepanov.hasDegreeFormula_curveVal hdvr Ω g).finite_support f hf
  refine (hfin.preimage (f := fun x : ClosedPoint C =>
    (⟨x.1, coheight_eq_one_of_isClosed g x.2⟩ : Stacks.BombieriStepanov.CurvePlace C))
    (fun a _ b _ h => Subtype.ext (by simpa using congrArg Subtype.val h))).subset fun x hx => ?_
  simpa [Stacks.BombieriStepanov.ordZ_curveVal] using hx

/-- The divisor `div f = ∑ ord_x(f) x` of a nonzero rational function, on the closed points. -/
def divOf {f : C.functionField} (hf : f ≠ 0) : ClosedPoint C →₀ ℤ :=
  Finsupp.ofSupportFinite (fun x => C.ord f x.1) (finite_setOf_ord_ne_zero g hf)

omit [IsAlgClosed Ω] in
/-- The coefficient of `div f` at a closed point `x` is the order of `f` at `x`. -/
@[simp]
theorem divOf_apply {f : C.functionField} (hf : f ≠ 0) (x : ClosedPoint C) :
    divOf g hf x = C.ord f x.1 := rfl

omit [IsAlgClosed Ω] in
/-- Read as a Weil divisor, `div f` is the principal Weil divisor of `f`. -/
theorem toWeil_divOf {f : C.functionField} (hf : f ≠ 0) :
    toWeil g (divOf g hf) = principalDivisor C (Units.mk0
      ((Stacks.Chow.rationalFunctionsEquivFunctionField C).val.symm f)
      (by simpa using hf)) := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [toWeil_val_apply, principalDivisor_apply, divOf_apply]
  simp only [Units.val_mk0, RingEquiv.apply_symm_apply]
  rfl

omit [IsAlgClosed Ω] in
/-- **A principal divisor has trivial class.** -/
theorem divisorClass_divOf {f : C.functionField} (hf : f ≠ 0) :
    divisorClass g (divOf g hf) = 0 := by
  have := isNormal_of_curve g
  have hinj : Function.Injective (firstChern C) := picardToWeilDivisorClassGroup_injective C
  refine hinj ?_
  rw [map_zero, firstChern_divisorClass, toWeil_divOf, mk_eq_zero_iff]
  exact ⟨_, rfl⟩

omit [IsAlgClosed Ω] in
/-- **A divisor with trivial class is principal.** -/
theorem exists_divOf_eq_of_divisorClass_eq_zero {D : ClosedPoint C →₀ ℤ}
    (hD : divisorClass g D = 0) : ∃ (f : C.functionField) (hf : f ≠ 0), divOf g hf = D := by
  have h := congrArg (firstChern C) hD
  rw [firstChern_divisorClass, map_zero, mk_eq_zero_iff] at h
  obtain ⟨u, hu⟩ := h
  set f := (Stacks.Chow.rationalFunctionsEquivFunctionField C).val (u : _)
  have hf : f ≠ 0 :=
    (u.isUnit.map (Stacks.Chow.rationalFunctionsEquivFunctionField C).val.toRingHom).ne_zero
  refine ⟨f, hf, Finsupp.ext fun x => ?_⟩
  have := congrArg (fun W : WeilDivisor C => W.val (primeDivisorOfClosedPoint g x)) hu
  simp only [principalDivisor_apply, toWeil_val_apply,
    closedPointOfPrimeDivisor_primeDivisorOfClosedPoint] at this
  rw [divOf_apply, ← this]
  simp only [primeDivisorOfClosedPoint, PrimeDivisor.genericPoint_ofCoheightOne]
  rfl

/-- **A principal divisor has degree zero.** -/
theorem degree_divOf {f : C.functionField} (hf : f ≠ 0) :
    ((divOf g hf).sum fun _ n => n) = 0 := by
  rw [← picardDegree_divisorClass g, divisorClass_divOf, map_zero]

end Stacks.Zeta

end
