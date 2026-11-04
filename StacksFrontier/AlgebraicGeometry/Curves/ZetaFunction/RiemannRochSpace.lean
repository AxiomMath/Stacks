module

public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.GlobalSectionsGenericStalk
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PrincipalDivisorClass
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# The Riemann–Roch spaces `L(D)` of a curve

Let `C` be a smooth proper curve over an algebraically closed field `Ω`, with function field
`K`. For a divisor `D` on the closed points, `L(D) = {f ∈ K : f = 0 ∨ ord_x(f) + D(x) ≥ 0 ∀ x}`
is an `Ω`-subspace of `K`. This file identifies its dimension with `h⁰` of an invertible module of
class `[D]`:

* for a regular meromorphic section `s` of an invertible module `L`, the divisor `div s` of `s`
  on the closed points has class `[L]` (`Stacks.Zeta.divisorClass_sectionDivisor`), and
  `H⁰(C, L) ≅ L(div s)` as `Ω`-vector spaces (`Stacks.Zeta.finrank_rrSpace_sectionDivisor`), by
  `Stacks.Zeta.genericCoord`;
* multiplication by `f⁻¹` identifies `L(D)` with `L(D + div f)`.

## Main definitions

* `Stacks.Zeta.rrSpace`: the space `L(D)`.
* `Stacks.Zeta.sectionDivisor`: the divisor of a regular meromorphic section on the closed points.

## Main results

* `Stacks.Zeta.mem_rrSpace`: membership in `L(D)` in terms of orders at closed points.
* `Stacks.Zeta.divisorClass_sectionDivisor`: the divisor of a regular meromorphic section of `L`
  has class `[L]`.
* `Stacks.Zeta.finrank_rrSpace_sectionDivisor`: `dim L(div s) = h⁰(C, L)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace

universe u

namespace Stacks.Zeta

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}} (g : C ⟶ Spec (.of Ω))
  [IsProper g] [Smooth g] [IsCurve Ω g] [IsLocallyNoetherian C]

/-- The `Ω`-algebra structure of the function field. -/
abbrev ffAlg : Algebra Ω C.functionField := Stacks.BombieriStepanov.functionFieldAlgebra g

omit [IsAlgClosed Ω] [IsProper g] [IsLocallyNoetherian C] in
include g in
/-- The stalk of `C` at a closed point is a discrete valuation ring. -/
theorem dvr_closedPoint (x : ClosedPoint C) : IsDiscreteValuationRing (C.presheaf.stalk x.1) :=
  IsCurve.isDiscreteValuationRing_stalk_of_isClosed Ω g x.2

omit [IsAlgClosed Ω] [IsProper g] in
/-- A nonzero constant has order zero at every closed point. -/
theorem ord_algebraMap_const {c : Ω} (hc : c ≠ 0) (x : ClosedPoint C) :
    letI := ffAlg g
    C.ord (algebraMap Ω C.functionField c) x.1 = 0 := by
  let := ffAlg g
  have := dvr_closedPoint g x
  rw [Stacks.BombieriStepanov.algebraMap_functionFieldAlgebra g x.1 c]
  refine ord_algebraMap_isUnit (coheight_eq_one_of_isClosed g x.2) ?_
  exact (IsUnit.mk0 c hc).map (fieldToStalk g x.1).hom

/-- **The Riemann–Roch space** `L(D)`. -/
def rrSpace (D : ClosedPoint C →₀ ℤ) :
    letI := ffAlg g
    Submodule Ω C.functionField :=
  letI := ffAlg g
  { carrier := {f | f = 0 ∨ ∀ x : ClosedPoint C, 0 ≤ C.ord f x.1 + D x}
    zero_mem' := Or.inl rfl
    add_mem' := by
      rintro f f' (rfl | hf) (rfl | hf')
      · simp
      · rw [zero_add]; exact Or.inr hf'
      · rw [add_zero]; exact Or.inr hf
      by_cases h0 : f + f' = 0
      · exact Or.inl h0
      refine Or.inr fun x => ?_
      have := dvr_closedPoint g x
      have := Scheme.ord_add (x := x.1) h0
      have h1 := hf x
      have h2 := hf' x
      omega
    smul_mem' := by
      rintro c f (rfl | hf)
      · simp
      by_cases hc : c = 0
      · simp [hc]
      by_cases hf0 : f = 0
      · rw [hf0, smul_zero]; exact Or.inl rfl
      refine Or.inr fun x => ?_
      have hc' : algebraMap Ω C.functionField c ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap Ω C.functionField).injective).2 hc
      rw [Algebra.smul_def, Scheme.ord_mul hc' hf0, ord_algebraMap_const g hc x, zero_add]
      exact hf x }

omit [IsAlgClosed Ω] [IsProper g] in
/-- A function `f` lies in `L(D)` if and only if `f = 0` or `ord_x(f) + D(x) ≥ 0` at every closed
point `x`. -/
theorem mem_rrSpace {D : ClosedPoint C →₀ ℤ} {f : C.functionField} :
    letI := ffAlg g
    f ∈ rrSpace g D ↔ f = 0 ∨ ∀ x : ClosedPoint C, 0 ≤ C.ord f x.1 + D x := Iff.rfl

/-! ### The divisor of a meromorphic section -/

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
/-- The prime divisor of the closed point of a prime divisor `Z` is `Z`. -/
theorem primeDivisorOfClosedPoint_closedPointOfPrimeDivisor (Z : PrimeDivisor C) :
    primeDivisorOfClosedPoint g (closedPointOfPrimeDivisor g Z) = Z :=
  PrimeDivisor.genericPoint_injective (PrimeDivisor.genericPoint_ofCoheightOne _ _)

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] [IsLocallyNoetherian C] in
/-- Distinct closed points give distinct prime divisors. -/
theorem primeDivisorOfClosedPoint_injective :
    Function.Injective (primeDivisorOfClosedPoint g (C := C)) := fun x y h => by
  rw [← closedPointOfPrimeDivisor_primeDivisorOfClosedPoint g x,
    ← closedPointOfPrimeDivisor_primeDivisorOfClosedPoint g y, h]

section Section

variable (L : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
  (s : MeromorphicSection C.sheaf L) (hs : IsRegularMeromorphicSection C.sheaf L s)

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
include g in
/-- A regular meromorphic section has nonzero order of vanishing at only finitely many closed
points. -/
theorem finite_orderOfVanishing_ne_zero :
    {x : ClosedPoint C |
      orderOfVanishingMeromorphic C L s hs (primeDivisorOfClosedPoint g x) ≠ 0}.Finite := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace g
  have hfin := (weilDivisorOfMeromorphicSection C L s hs).2.finite_nonempty_of_compact
  refine (hfin.preimage (primeDivisorOfClosedPoint_injective g).injOn).subset fun x hx => ?_
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  show (if orderOfVanishingMeromorphic C L s hs (primeDivisorOfClosedPoint g x) = 0 then ∅
    else (primeDivisorOfClosedPoint g x).support).Nonempty
  rw [if_neg hx, PrimeDivisor.support_eq_closure]
  exact ⟨_, subset_closure rfl⟩

/-- The divisor of a regular meromorphic section, on the closed points. -/
def sectionDivisor : ClosedPoint C →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun x => orderOfVanishingMeromorphic C L s hs (primeDivisorOfClosedPoint g x))
    (finite_orderOfVanishing_ne_zero g L s hs)

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
/-- The coefficient of `sectionDivisor` at a closed point `x` is the order of vanishing of `s` at
the prime divisor of `x`. -/
theorem sectionDivisor_apply (x : ClosedPoint C) :
    sectionDivisor g L s hs x =
      orderOfVanishingMeromorphic C L s hs (primeDivisorOfClosedPoint g x) := rfl

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
/-- The Weil divisor associated to `sectionDivisor` is the Weil divisor of the section `s`. -/
theorem toWeil_sectionDivisor :
    toWeil g (sectionDivisor g L s hs) = weilDivisorOfMeromorphicSection C L s hs :=
  Subtype.ext (funext fun Z => by
    rw [toWeil_val_apply, sectionDivisor_apply,
      primeDivisorOfClosedPoint_closedPointOfPrimeDivisor, weilDivisorOfMeromorphicSection_apply])

omit [IsAlgClosed Ω] [IsProper g]
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L] in
/-- **The divisor of a meromorphic section of `L` has the class of `L`.** -/
theorem divisorClass_sectionDivisor
    (hL : Stacks.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L) :
    divisorClass g (sectionDivisor g L s hs) =
      Stacks.SheafOfModules.picardClass C.sheaf.obj C.ringCatSheaf.property L hL := by
  have := isNormal_of_curve g
  have hinj : Function.Injective (firstChern C) := picardToWeilDivisorClassGroup_injective C
  refine hinj ?_
  rw [firstChern_divisorClass, toWeil_sectionDivisor,
    ← weilDivisorClassOfInvertibleSheaf_eq C L s hs]
  exact (weilDivisorClassOfPicardClass_picardClass C L).symm

/-- The structure map `Ω → Γ(C, 𝒪_C)`. -/
abbrev globalAlgebraMap : Ω →+* Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of Ω)).inv ≫ g.appTop).hom

/-- The coordinate `ρ` as an `Ω`-linear map on global sections. -/
def coordLinear :
    letI := ffAlg g
    (ModuleCat.restrictScalars (globalAlgebraMap g)).obj
        ((_root_.SheafOfModules.evaluation C.ringCatSheaf (op (⊤ : C.Opens))).obj L) →ₗ[Ω]
      C.functionField :=
  letI := ffAlg g
  { toFun := fun t => genericCoord C L s hs t
    map_add' := fun t t' => genericCoord_add C L s hs t t'
    map_smul' := fun c t => by
      have h := genericCoord_smul C L s hs (globalAlgebraMap g c) (show Γ(L, ⊤) from t)
      exact h }

omit [IsAlgClosed Ω] [IsProper g] [Smooth g] in
/-- The coordinate `coordLinear` is injective. -/
theorem coordLinear_injective : Function.Injective (coordLinear g L s hs) :=
  genericCoord_injective C L s hs

omit [IsAlgClosed Ω] [IsProper g] in
/-- **The range of the coordinate is `L(div s)`.** -/
theorem range_coordLinear :
    letI := ffAlg g
    LinearMap.range (coordLinear g L s hs) = rrSpace g (sectionDivisor g L s hs) := by
  let := ffAlg g
  have := isNormal_of_curve g
  have hdvr : ∀ Z : PrimeDivisor C, IsDiscreteValuationRing (C.presheaf.stalk Z.genericPoint) :=
    fun Z => Stacks.BombieriStepanov.isDiscreteValuationRing_stalk_of_coheight_eq_one g _
      (PrimeDivisor.coheight_genericPoint Z)
  ext a
  rw [LinearMap.mem_range, mem_rrSpace]
  constructor
  · rintro ⟨t, rfl⟩
    by_cases h0 : coordLinear g L s hs t = 0
    · exact Or.inl h0
    refine Or.inr fun x => ?_
    have := hdvr (primeDivisorOfClosedPoint g x)
    have := (genericCoord_mem C L s hs t (primeDivisorOfClosedPoint g x)).resolve_left h0
    have hgp : (primeDivisorOfClosedPoint g x).genericPoint = x.1 :=
      PrimeDivisor.genericPoint_ofCoheightOne _ _
    rw [hgp] at this
    exact this
  · intro ha
    obtain ⟨t, ht⟩ := exists_genericCoord_eq C L s hs hdvr a fun Z => by
      rcases ha with h0 | ha
      · exact Or.inl h0
      refine Or.inr ?_
      have := ha (closedPointOfPrimeDivisor g Z)
      rwa [sectionDivisor_apply, primeDivisorOfClosedPoint_closedPointOfPrimeDivisor] at this
    exact ⟨t, ht⟩

omit [IsAlgClosed Ω] [IsProper g] in
/-- **`H⁰(C, L) ≅ L(div s)`.** -/
theorem finrank_rrSpace_sectionDivisor :
    letI := ffAlg g
    Module.finrank Ω (rrSpace g (sectionDivisor g L s hs)) =
      Module.finrank Ω (cohomologyOverField Ω g L 0) := by
  let := ffAlg g
  rw [← range_coordLinear, LinearMap.finrank_range_of_inj (coordLinear_injective g L s hs)]
  exact (cohomologyOverFieldZeroIsoSections Ω g L).toLinearEquiv.finrank_eq.symm

end Section

end Stacks.Zeta

end
