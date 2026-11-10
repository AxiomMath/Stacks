module

public import StacksFrontier.AlgebraicGeometry.GenericPointGluing.AffineDecomposition
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Stalks
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksWeaklyAssociated

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped nonZeroDivisors

universe u

namespace Stacks.AlgebraicGeometry.GenericPointSheaf

open Stacks.AlgebraicGeometry.GenericPointGluing

variable {X : Scheme.{u}} {U : X.Opens}

/-- Under the hypothesis that the weakly associated points of `X` are generic points, the
nonzerodivisors of the ring of sections on an affine open are exactly the elements lying in no
prime coming from a generic point in that open. -/
theorem mem_nonZeroDivisors_iff_forall_notMem
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hU : IsAffineOpen U) (r : Γ(X, U)) :
    r ∈ Γ(X, U)⁰ ↔ ∀ η : {η : genericPoints X // η.1 ∈ U},
      r ∉ (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal := by
  refine ⟨fun hr η hrη ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hrη
    (primeIdealOf_mem_minimalPrimes hU η) hr, fun hr ↦ ?_⟩
  refine mem_nonZeroDivisors_iff_left.mpr fun z hz ↦ ?_
  by_contra hz0
  have hproper : (Γ(X, U) ∙ z).annihilator ≠ ⊤ :=
    (Ideal.ne_top_iff_one _).mpr fun h1 ↦
      hz0 (by simpa using (Submodule.mem_annihilator_span_singleton z 1).mp h1)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hproper
  let p : PrimeSpectrum Γ(X, U) := ⟨q, hq.1.1⟩
  have hpU : hU.fromSpec.base p ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self p
  let y : U := ⟨hU.fromSpec.base p, hpU⟩
  have hyp : hU.primeIdealOf y = p :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf y)
  have hw : Stacks.Divisors.IsWeaklyAssociatedPoint
      (SheafOfModules.unit X.ringCatSheaf) y := by
    apply (AlgebraicGeometry.isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint
      (SheafOfModules.unit X.ringCatSheaf) U hU y y.2).mp
    change IsWeaklyAssociatedPrime Γ(X, U) Γ(X, U) (hU.primeIdealOf y).asIdeal
    rw [hyp]
    exact ⟨z, hq⟩
  refine hr ⟨⟨(y : X), hass hw⟩, y.2⟩ ?_
  rw [show (hU.primeIdealOf ⟨(y : X), y.2⟩).asIdeal = q from congrArg PrimeSpectrum.asIdeal hyp]
  exact hq.1.2 ((Submodule.mem_annihilator_span_singleton z r).mpr
    (by simpa [smul_eq_mul, mul_comm] using hz))

/-- On an affine open of a scheme whose weakly associated points are generic points, with
finitely many irreducible components, the product of the local rings of `X` at the generic
points lying in that open is a localization of its ring of sections at the nonzerodivisors.
This is the general, non-reduced, form of
`Stacks.AlgebraicGeometry.GenericPointGluing.isLocalization_nonZeroDivisors_pi_stalk`. -/
theorem isLocalization_nonZeroDivisors_pi_stalk
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hU : IsAffineOpen U) (hfin : (irreducibleComponents (U : Set X)).Finite) :
    letI : ∀ η : {η : genericPoints X // η.1 ∈ U},
        Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
      fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
    IsLocalization (nonZeroDivisors Γ(X, U))
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) :=
  @isLocalization_nonZeroDivisors_pi Γ(X, U) _
    {η : genericPoints X // η.1 ∈ U} (finite_genericPoints_subtype X hfin)
    (fun η ↦ (hU.primeIdealOf ⟨η.1.1, η.2⟩).asIdeal)
    (fun η ↦ (hU.primeIdealOf ⟨η.1.1, η.2⟩).2)
    (fun η ↦ X.presheaf.stalk η.1.1)
    (fun _ ↦ inferInstance)
    (fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩)
    (fun η ↦ hU.isLocalization_stalk ⟨η.1.1, η.2⟩)
    (primeIdealOf_mem_minimalPrimes hU) (primeIdealOf_injective hU)
    (mem_nonZeroDivisors_iff_forall_notMem hass hU)

/-- The meromorphic functions on an affine open are the product of the local rings of `X` at
the generic points lying in that open, whenever the weakly associated points of `X` are
generic points and the open has finitely many irreducible components. Both sides are total
quotient rings of `Γ(X, U)`, so the isomorphism is the uniqueness of localizations. -/
noncomputable def totalQuotientObjAlgEquivPiStalk
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hU : IsAffineOpen U) (hfin : (irreducibleComponents (U : Set X)).Finite) :
    letI : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) :=
      (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
    letI : ∀ η : {η : genericPoints X // η.1 ∈ U},
        Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
      fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
    (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) ≃ₐ[Γ(X, U)]
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) :=
  @IsLocalization.algEquiv Γ(X, U) _ (nonZeroDivisors Γ(X, U))
    (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) _
    ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra)
    (AlgebraicGeometry.isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen X U hU)
    (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) _
    (@Pi.algebra {η : genericPoints X // η.1 ∈ U} Γ(X, U)
      (fun η : {η : genericPoints X // η.1 ∈ U} ↦ (X.presheaf.stalk η.1.1 : Type u)) _ _
      (fun η : {η : genericPoints X // η.1 ∈ U} ↦
        X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩))
    (isLocalization_nonZeroDivisors_pi_stalk hass hU hfin)

/-- The isomorphism of `totalQuotientObjAlgEquivPiStalk` is the canonical one: on the image of
`Γ(X, U)` in the meromorphic functions it is the family of germ maps at the generic points
lying in `U`. Together with `IsLocalization.algHom_ext` this pins it down, so any morphism of
presheaves whose component at an affine open restricts to the germ family on `Γ(X, U)` agrees
with it there. -/
theorem totalQuotientObjAlgEquivPiStalk_apply_algebraMap
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hU : IsAffineOpen U) (hfin : (irreducibleComponents (U : Set X)).Finite)
    (r : Γ(X, U)) (η : {η : genericPoints X // η.1 ∈ U}) :
    letI : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) :=
      (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
    letI : ∀ η : {η : genericPoints X // η.1 ∈ U},
        Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
      fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
    totalQuotientObjAlgEquivPiStalk hass hU hfin
        ((X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom r) η
      = X.presheaf.germ U η.1.1 η.2 r := by
  let : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (Opposite.op U)).hom.toAlgebra
  let : ∀ η : {η : genericPoints X // η.1 ∈ U},
      Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
    fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  exact congrFun ((totalQuotientObjAlgEquivPiStalk hass hU hfin).commutes r) η

end Stacks.AlgebraicGeometry.GenericPointSheaf
