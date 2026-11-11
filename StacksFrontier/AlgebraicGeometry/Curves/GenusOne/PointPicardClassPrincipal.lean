module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.PointPicardClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClassGroupPicard

/-!
# A function vanishing at a single point of an open subcurve

Let `X` be a smooth curve over a field `k`, `U ⊆ X` an open subset and `x ∈ U` a closed point.
If a regular function `a` on `U` vanishes on `U` exactly at `x`, then `n [𝒪_X(x)]` is a
combination of the classes `[𝒪_X(p)]` of closed points `p ∉ U`, where `n ≥ 1` is the order of `a`
at `x`: the principal divisor of `a` is `n x` plus a divisor supported outside `U`.

The argument runs in the closed-point class group `(X_0 →₀ ℤ)/div(k(X)^*)` of the curve, which is
the Picard group of `X` by [Stacks, Tag 0BE9]
(`Stacks.EtaleCohomology.closedPointClassGroupAddEquivSchemePicard`); the class of a closed point
corresponds to `[𝒪_X(x)]`.

## Main definitions

* `AlgebraicGeometry.IsCurve.closedPointClassGroupAddEquivOfScheme`: `Cl(X) ≃+ Pic(X)`, with the
  Picard group in the model `Stacks.Picard.ofScheme X` of `pointPicardClass`.

## Main results

* `AlgebraicGeometry.IsCurve.closedPointClassGroupAddEquivOfScheme_single`: the class of a closed
  point goes to `[𝒪_X(x)]`.
* `AlgebraicGeometry.IsCurve.exists_nsmul_pointPicardClass_mem_closure`: the statement above.

## References

* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.IsCurve

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]

omit [Smooth f] in
include f in
/-- A curve over a field is a locally Noetherian scheme. -/
theorem isLocallyNoetherian_of_isCurve : IsLocallyNoetherian X :=
  haveI : LocallyOfFiniteType f := IsVariety.toLocallyOfFiniteType (k := k)
  haveI : IsLocallyNoetherian (Spec (.of k)) := inferInstance
  LocallyOfFiniteType.isLocallyNoetherian f

omit [Smooth f] in
include f in
/-- A curve over a field is a Noetherian scheme. -/
theorem isNoetherian_of_isCurve : IsNoetherian X :=
  haveI := isLocallyNoetherian_of_isCurve k f
  haveI : QuasiCompact f := IsVariety.toQuasiCompact (k := k)
  haveI : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  IsNoetherian.mk

section ClassGroup

variable [IsLocallyNoetherian X] [IsNoetherian X]

/-- **The closed-point class group of a smooth curve is its Picard group**, with the Picard group
in the model `Stacks.Picard.ofScheme X`: Tag 0BE9 followed by the identification of the two
models of `Pic(X)`. -/
def closedPointClassGroupAddEquivOfScheme :
    closedPointClassGroup X ≃+ Stacks.Picard.ofScheme X :=
  (closedPointClassGroupAddEquivSchemePicard f).trans
    (Stacks.SheafOfModules.picardGroupShrinkAddEquiv X.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)).symm

/-- **The class of a closed point is `[𝒪_X(x)]`.** -/
theorem closedPointClassGroupAddEquivOfScheme_single (x : closedPoints X) :
    closedPointClassGroupAddEquivOfScheme k f
        (QuotientAddGroup.mk (Finsupp.single x 1) : closedPointClassGroup X) =
      pointPicardClass k f x.2 := by
  rw [closedPointClassGroupAddEquivOfScheme, AddEquiv.trans_apply,
    closedPointClassGroupAddEquivSchemePicard_single]
  exact (AddEquiv.symm_apply_eq _).2 rfl

omit [IsNoetherian X] in
/-- The order at a closed point `x` of a regular function on an open `U ∋ x` which vanishes at `x`
and is nonzero is a positive integer. -/
theorem exists_ord_germToFunctionField_eq (U : X.Opens) [Nonempty U] {x : X} (hxU : x ∈ U)
    (hx : IsClosed ({x} : Set X)) (a : Γ(X, U)) (ha0 : X.germToFunctionField U a ≠ 0)
    (hax : x ∉ X.basicOpen a) :
    ∃ n : ℕ, 0 < n ∧ X.ord (X.germToFunctionField U a) x = n := by
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_of_isClosed k f hx
  set b := X.presheaf.germ U x hxU a with hb
  have hb0 : b ≠ 0 := by
    intro h
    apply ha0
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hxU a, ← hb, h, map_zero]
  have hbu : ¬ IsUnit b := fun h => hax ((Scheme.mem_basicOpen X a x hxU).mpr h)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  obtain ⟨n, u, hnu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (hnu ▸ (by simp : IsUnit ((u : X.presheaf.stalk x) * ϖ ^ 0))) hbu
    · exact hn
  have hord : Ring.ord (X.presheaf.stalk x) b = n := by
    rw [hnu, Ring.ord_mul_of_isUnit_left u.isUnit,
      Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ,
      nsmul_eq_mul, mul_one]
  have hco : Order.coheight x = 1 :=
    coheight_eq_one (f := f) (ne_genericPoint_of_mem_closedPoints_of_isCurve f ⟨x, hx⟩)
  refine ⟨n, hn, ?_⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hxU a]
  exact Stacks.Chow.ord_algebraMap_eq_ringOrd hco hb0 hord

end ClassGroup

/-- **A function on `U` vanishing on `U` exactly at `x`.** If a regular function `a` on an open
`U` of a smooth curve vanishes on `U` only at the closed point `x ∈ U`, then for some `n ≥ 1` the
class `n [𝒪_X(x)]` lies in the subgroup generated by the classes `[𝒪_X(p)]` of the closed points
`p ∉ U`. -/
theorem exists_nsmul_pointPicardClass_mem_closure (U : X.Opens) {x : X} (hxU : x ∈ U)
    (hx : IsClosed ({x} : Set X)) (a : Γ(X, U))
    (ha : (X.basicOpen a : Set X) = (U : Set X) \ {x}) :
    ∃ n : ℕ, 0 < n ∧ n • pointPicardClass k f hx ∈
      AddSubgroup.closure
        {c | ∃ (p : X) (hp : IsClosed ({p} : Set X)), p ∉ U ∧ c = pointPicardClass k f hp} := by
  classical
  have := isLocallyNoetherian_of_isCurve k f
  have := isNoetherian_of_isCurve k f
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  -- the generic point lies in `U \ {x}`, so `a` is nonzero in the function field
  have hη : genericPoint X ∈ X.basicOpen a := by
    have hηU : genericPoint X ∈ U :=
      (genericPoint_spec X).specializes (Set.mem_univ x) |>.mem_open U.isOpen hxU
    have hηx : genericPoint X ≠ x :=
      (ne_genericPoint_of_mem_closedPoints_of_isCurve f ⟨x, hx⟩).symm
    have : genericPoint X ∈ (U : Set X) \ {x} := ⟨hηU, hηx⟩
    rw [← ha] at this
    exact this
  have ha0 : X.germToFunctionField U a ≠ 0 := by
    intro h
    have h0 : a = 0 := Scheme.germToFunctionField_injective X U (h.trans (map_zero _).symm)
    rw [h0, Scheme.basicOpen_zero] at hη
    exact hη
  have hax : x ∉ X.basicOpen a := by
    intro h
    have : x ∈ (U : Set X) \ {x} := ha ▸ h
    exact this.2 rfl
  obtain ⟨n, hn, hord⟩ := exists_ord_germToFunctionField_eq k f U hxU hx a ha0 hax
  refine ⟨n, hn, ?_⟩
  set φ : Additive (X.functionField)ˣ := Additive.ofMul (Units.mk0 _ ha0)
  set D := closedPointDivisorOfUnit X φ
  set x' : closedPoints X := ⟨x, hx⟩
  set E : closedPoints X →₀ ℤ := (n : ℤ) • Finsupp.single x' 1 - D
  -- `E` is supported outside `U`
  have hE : ∀ p ∈ E.support, (p : X) ∉ U := by
    intro p hp hpU
    apply Finsupp.mem_support_iff.mp hp
    simp only [E, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
      Finsupp.single_apply, smul_eq_mul, D, closedPointDivisorOfUnit_apply, φ, toMul_ofMul,
      Units.val_mk0]
    by_cases hpx : p = x'
    · subst hpx
      simp only [↓reduceIte]
      exact sub_eq_zero.mpr ((mul_one _).trans hord.symm)
    · simp only [Ne.symm hpx, ↓reduceIte, mul_zero, zero_sub, neg_eq_zero]
      have hpu : (p : X) ∈ X.basicOpen a := by
        change (p : X) ∈ (X.basicOpen a : Set X)
        rw [ha]
        exact ⟨hpU, fun h => hpx (Subtype.ext h)⟩
      have hunit := (Scheme.mem_basicOpen X a p hpU).mp hpu
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hpU a]
      exact Scheme.ord_algebraMap_of_isUnit
        (coheight_eq_one (f := f) (ne_genericPoint_of_mem_closedPoints_of_isCurve f p)) hunit
  set Φ := closedPointClassGroupAddEquivOfScheme k f
  have hD : (QuotientAddGroup.mk D : closedPointClassGroup X) = 0 :=
    (QuotientAddGroup.eq_zero_iff D).mpr (AddMonoidHom.mem_range.mpr ⟨φ, rfl⟩)
  have hkey : n • pointPicardClass k f hx = Φ (QuotientAddGroup.mk E) := by
    have h1 : (QuotientAddGroup.mk E : closedPointClassGroup X) =
        (n : ℤ) • (QuotientAddGroup.mk (Finsupp.single x' 1) : closedPointClassGroup X) := by
      simp only [E, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_zsmul, hD, sub_zero]
    rw [h1, map_zsmul, closedPointClassGroupAddEquivOfScheme_single, natCast_zsmul]
  rw [hkey]
  -- `E` is a combination of single points outside `U`
  have hsum : E = E.support.sum fun p => E p • Finsupp.single p 1 := by
    conv_lhs => rw [← Finsupp.sum_single E]
    simp only [Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsum, ← QuotientAddGroup.mk'_apply, map_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun p hp => ?_
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk_zsmul, map_zsmul,
    closedPointClassGroupAddEquivOfScheme_single]
  have hmem : pointPicardClass k f p.2 ∈
      {c | ∃ (q : X) (hq : IsClosed ({q} : Set X)), q ∉ U ∧ c = pointPicardClass k f hq} :=
    ⟨p.1, p.2, hE p hp, rfl⟩
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _

end AlgebraicGeometry.IsCurve

end
