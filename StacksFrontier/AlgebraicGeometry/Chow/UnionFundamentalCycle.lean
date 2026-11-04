module

public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.LocalBound
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CycleCoefficientSupport
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.FibreDifference
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnion
import all StacksFrontier.AlgebraicGeometry.Blowup.Colength.LocalBound
import all StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange

/-!
# The fundamental cycle of a scheme-theoretic union

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a scheme
locally of finite type over `S`. Two ideal sheaves `I` and `J` on `X` cut out closed subschemes
`X₁` and `X₂`; their scheme-theoretic **union** is cut out by the meet `I ⊓ J` and their
scheme-theoretic **intersection** by the join `I ⊔ J`, the order on ideal sheaves being inclusion
of ideals. This file computes the cycle of the union:

  `[X₁ ∪ X₂]_k = [X₁]_k + [X₂]_k`  provided no point of `X₁ ∩ X₂` has delta-dimension `k`.

The hypothesis is exactly what is needed and cannot be dropped: a component common to `X₁` and
`X₂` of delta-dimension `k` would be counted once on the left and twice on the right.

## Main results

* `Stacks.Chow.idealStalk_inf_eq_of_notMem_support`: away from the support of `J`, the ideal
  sheaf of the union has the same stalk as the ideal sheaf of `X₁`.
* `Stacks.Chow.componentMultiplicity_eq_of_idealStalk_eq`: the multiplicity of a component at a
  point depends on the ideal sheaf only through its stalk there.
* `Stacks.Chow.exists_genericPoints_subschemeι_eq_iff`: a point of `X` is the image of a generic
  point of the closed subscheme cut out by `I` exactly when it lies in `I.support` and has no
  proper generalisation inside `I.support`.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_inf`: the fundamental cycle of a union is the sum
  of the fundamental cycles.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Stalks of a meet of ideal sheaves -/

section Stalk

variable {X : Scheme.{u}}

/-- The stalk of an ideal sheaf at a point is monotone in the ideal sheaf. -/
theorem idealStalk_mono {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    IdealSheafData.stalk I x ≤ IdealSheafData.stalk J x := by
  obtain ⟨V, hxV⟩ := Stacks.Divisors.exists_affineOpens_mem x
  rw [IdealSheafData.stalk_eq_map_germ I x V hxV, IdealSheafData.stalk_eq_map_germ J x V hxV]
  exact Ideal.map_mono (h V)

/-- The stalk of a product of ideal sheaves is the product of the stalks. -/
theorem idealStalk_mul (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I * J) x =
      IdealSheafData.stalk I x * IdealSheafData.stalk J x := by
  obtain ⟨V, hxV⟩ := Stacks.Divisors.exists_affineOpens_mem x
  rw [IdealSheafData.stalk_eq_map_germ (I * J) x V hxV,
    IdealSheafData.stalk_eq_map_germ I x V hxV, IdealSheafData.stalk_eq_map_germ J x V hxV,
    show (I * J).ideal V = I.ideal V * J.ideal V from rfl, Ideal.map_mul]

/-- The product of two ideal sheaves is below their meet. -/
theorem mul_le_inf (I J : X.IdealSheafData) : I * J ≤ I ⊓ J := by
  refine le_inf (fun U ↦ ?_) (fun U ↦ ?_) <;>
    simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  · exact Ideal.mul_le_left
  · exact Ideal.mul_le_right

/-- The ideal sheaf `I ⊓ J` of the scheme-theoretic union has the same stalk at `x` as `I`
whenever `x` is outside the support of `J`. -/
theorem idealStalk_inf_eq_of_notMem_support (I J : X.IdealSheafData) {x : X}
    (hx : x ∉ (J.support : Set X)) :
    IdealSheafData.stalk (I ⊓ J) x = IdealSheafData.stalk I x := by
  refine le_antisymm (idealStalk_mono inf_le_left x) ?_
  calc IdealSheafData.stalk I x = IdealSheafData.stalk (I * J) x := by
        rw [idealStalk_mul, idealStalk_eq_top_of_notMem_support J hx, Ideal.mul_top]
    _ ≤ IdealSheafData.stalk (I ⊓ J) x := idealStalk_mono (mul_le_inf I J) x

/-- The ideal sheaf `I ⊓ J` of the scheme-theoretic union has the same stalk at `x` as `J`
whenever `x` is outside the support of `I`. -/
theorem idealStalk_inf_eq_of_notMem_support' (I J : X.IdealSheafData) {x : X}
    (hx : x ∉ (I.support : Set X)) :
    IdealSheafData.stalk (I ⊓ J) x = IdealSheafData.stalk J x := by
  rw [inf_comm]
  exact idealStalk_inf_eq_of_notMem_support J I hx

end Stalk

/-! ### The multiplicity of a component through the stalk of the ideal sheaf -/

/-- If `ξ` and `η` are generic points of components of the closed subschemes cut out by `I` and by
`J`, both lying over the same point `x` of `X`, and if the two ideal sheaves have the same stalk at
`x`, then the two components have the same multiplicity. -/
theorem componentMultiplicity_eq_of_idealStalk_eq {X : Scheme.{u}} {I J : X.IdealSheafData}
    {x : X} (ξ : genericPoints I.subscheme) (η : genericPoints J.subscheme)
    (hξ : I.subschemeι.base ξ.1 = x) (hη : J.subschemeι.base η.1 = x)
    (h : IdealSheafData.stalk I x = IdealSheafData.stalk J x) :
    componentMultiplicity I.subschemeι ξ = componentMultiplicity J.subschemeι η := by
  have hlen : ∀ {K : X.IdealSheafData} (ζ : genericPoints K.subscheme),
      componentMultiplicity K.subschemeι ζ =
      ((Module.length (X.presheaf.stalk (K.subschemeι.base ζ.1))
        (X.presheaf.stalk (K.subschemeι.base ζ.1) ⧸
          IdealSheafData.stalk K (K.subschemeι.base ζ.1))).toNat : ℤ) := fun {K} ζ ↦ by
    rw [componentMultiplicity_eq_length_stalk,
      ← Stacks.Blowup.Colength.length_idealStalk_quotient_eq_subschemeStalk K ζ.1]
  rw [hlen ξ, hlen η, hξ, hη, h]

/-! ### Generic points of a closed subscheme, read in the ambient scheme -/

/-- A point of `X` is the image of a generic point of the closed subscheme cut out by `I` exactly
when it lies in the support of `I` and has no proper generalisation there. -/
theorem exists_genericPoints_subschemeι_eq_iff {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    (∃ ξ : genericPoints I.subscheme, I.subschemeι.base ξ.1 = x) ↔
      x ∈ (I.support : Set X) ∧
        ∀ y : X, y ∈ (I.support : Set X) → x ∈ closure ({y} : Set X) → y = x := by
  have hrange : Set.range I.subschemeι.base = (I.support : Set X) := I.range_subschemeι
  have hind : Topology.IsInducing I.subschemeι.base :=
    I.subschemeι.isClosedEmbedding.isEmbedding.isInducing
  constructor
  · rintro ⟨ξ, hξ⟩
    refine ⟨by rw [← hrange]; exact ⟨ξ.1, hξ⟩, fun y hy hxy ↦ ?_⟩
    rw [← hrange] at hy
    obtain ⟨ζ, hζ⟩ := hy
    have hspec : I.subschemeι.base ζ ⤳ I.subschemeι.base ξ.1 := by
      rw [hζ, hξ]
      exact specializes_iff_mem_closure.mpr hxy
    have hzeta : ζ = ξ.1 :=
      (mem_genericPoints_iff_no_strict_generalization ξ.1).mp ξ.2 ζ
        (hind.specializes_iff.mp hspec)
    rw [← hζ, hzeta, hξ]
  · rintro ⟨hxI, hmax⟩
    rw [← hrange] at hxI
    obtain ⟨ξ, hξ⟩ := hxI
    refine ⟨⟨ξ, (mem_genericPoints_iff_no_strict_generalization ξ).mpr fun ζ hζ ↦ ?_⟩, hξ⟩
    have hspec : I.subschemeι.base ζ ⤳ I.subschemeι.base ξ := hind.specializes_iff.mpr hζ
    have hmem : I.subschemeι.base ζ ∈ (I.support : Set X) := by
      rw [← hrange]; exact ⟨ζ, rfl⟩
    have heq : I.subschemeι.base ζ = x :=
      hmax _ hmem (by rw [← hξ]; exact specializes_iff_mem_closure.mp hspec)
    exact I.subschemeι.isClosedEmbedding.injective (heq.trans hξ.symm)

/-- Off the support of `J` a point is the image of a generic point of the union exactly when it is
the image of a generic point of the closed subscheme cut out by `I`. -/
theorem exists_genericPoints_inf_iff_of_notMem_support {X : Scheme.{u}} (I J : X.IdealSheafData)
    {x : X} (hx : x ∉ (J.support : Set X)) :
    (∃ ξ : genericPoints (I ⊓ J).subscheme, (I ⊓ J).subschemeι.base ξ.1 = x) ↔
      ∃ ξ : genericPoints I.subscheme, I.subschemeι.base ξ.1 = x := by
  have hsupp : ((I ⊓ J).support : Set X) = (I.support : Set X) ∪ (J.support : Set X) := by
    rw [Stacks.IdealSheafData.support_inf]; rfl
  rw [exists_genericPoints_subschemeι_eq_iff, exists_genericPoints_subschemeι_eq_iff, hsupp]
  constructor
  · rintro ⟨hxu, hmax⟩
    exact ⟨hxu.resolve_right hx, fun y hy hxy ↦ hmax y (Or.inl hy) hxy⟩
  · rintro ⟨hxI, hmax⟩
    refine ⟨Or.inl hxI, fun y hy hxy ↦ ?_⟩
    rcases hy with hy | hy
    · exact hmax y hy hxy
    · exact absurd (J.support.isClosed.closure_subset
        (closure_mono (Set.singleton_subset_iff.mpr hy) hxy)) hx

/-! ### The fundamental cycle of a union -/

section Union

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-- The coefficient of the cycle of the union at a point outside the support of `J` is the
coefficient of the cycle of the closed subscheme cut out by `I`. -/
theorem cycleAssociatedToClosedSubscheme_inf_apply_of_notMem_support (I J : X.IdealSheafData)
    (k : ℤ) {x : X} (hx : x ∉ (J.support : Set X)) :
    (cycleAssociatedToClosedSubscheme C f (I ⊓ J).subschemeι k).1 x =
      (cycleAssociatedToClosedSubscheme C f I.subschemeι k).1 x := by
  by_cases hdim : relativeDimension C.dimensionFunction f x = k
  · by_cases hex : ∃ ξ : genericPoints I.subscheme, I.subschemeι.base ξ.1 = x
    · obtain ⟨η, hη⟩ := hex
      obtain ⟨ξ, hξ⟩ := (exists_genericPoints_inf_iff_of_notMem_support I J hx).mpr ⟨η, hη⟩
      have hl := cycleAssociatedToClosedSubscheme_apply C f (I ⊓ J).subschemeι k ξ
        (by rw [hξ]; exact hdim)
      have hr := cycleAssociatedToClosedSubscheme_apply C f I.subschemeι k η
        (by rw [hη]; exact hdim)
      rw [hξ] at hl
      rw [hη] at hr
      rw [hl, hr]
      exact componentMultiplicity_eq_of_idealStalk_eq ξ η hξ hη
        (idealStalk_inf_eq_of_notMem_support I J hx)
    · have hl : ¬ ∃ ξ : genericPoints (I ⊓ J).subscheme,
          (I ⊓ J).subschemeι.base ξ.1 = x := fun h ↦
        hex ((exists_genericPoints_inf_iff_of_notMem_support I J hx).mp h)
      rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C f (I ⊓ J).subschemeι k x
          (fun ⟨ξ, hξ, _⟩ ↦ hl ⟨ξ, hξ⟩),
        cycleAssociatedToClosedSubscheme_apply_eq_zero C f I.subschemeι k x
          (fun ⟨ξ, hξ, _⟩ ↦ hex ⟨ξ, hξ⟩)]
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C f (I ⊓ J).subschemeι k x
      (fun ⟨_, _, h⟩ ↦ hdim h),
    cycleAssociatedToClosedSubscheme_apply_eq_zero C f I.subschemeι k x
      (fun ⟨_, _, h⟩ ↦ hdim h)]

/-- The coefficient of the cycle of the union at a point outside the support of `I` is the
coefficient of the cycle of the closed subscheme cut out by `J`. -/
theorem cycleAssociatedToClosedSubscheme_inf_apply_of_notMem_support' (I J : X.IdealSheafData)
    (k : ℤ) {x : X} (hx : x ∉ (I.support : Set X)) :
    (cycleAssociatedToClosedSubscheme C f (I ⊓ J).subschemeι k).1 x =
      (cycleAssociatedToClosedSubscheme C f J.subschemeι k).1 x := by
  rw [inf_comm]
  exact cycleAssociatedToClosedSubscheme_inf_apply_of_notMem_support C f J I k hx

/-- If no point of the scheme-theoretic intersection of the closed subschemes cut out by `I` and
`J` has delta-dimension `k`, then the `k`-cycle of their scheme-theoretic union is the sum of
their `k`-cycles. -/
theorem cycleAssociatedToClosedSubscheme_inf (I J : X.IdealSheafData) (k : ℤ)
    (hIJ : ∀ x ∈ ((I ⊔ J).support : Set X),
      relativeDimension C.dimensionFunction f x ≠ k) :
    cycleAssociatedToClosedSubscheme C f (I ⊓ J).subschemeι k =
      cycleAssociatedToClosedSubscheme C f I.subschemeι k +
        cycleAssociatedToClosedSubscheme C f J.subschemeι k := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  show (cycleAssociatedToClosedSubscheme C f (I ⊓ J).subschemeι k).1 x =
    (cycleAssociatedToClosedSubscheme C f I.subschemeι k).1 x +
      (cycleAssociatedToClosedSubscheme C f J.subschemeι k).1 x
  by_cases hdim : relativeDimension C.dimensionFunction f x = k
  · have hnot : x ∉ (I.support : Set X) ∨ x ∉ (J.support : Set X) := by
      by_contra! hcon
      exact hIJ x (by rw [Scheme.IdealSheafData.support_sup]; exact hcon) hdim
    rcases hnot with hI | hJ
    · rw [cycleAssociatedToClosedSubscheme_inf_apply_of_notMem_support' C f I J k hI,
        cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f I.subschemeι k
          (by rwa [I.range_subschemeι]),
        zero_add]
    · rw [cycleAssociatedToClosedSubscheme_inf_apply_of_notMem_support C f I J k hJ,
        cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C f J.subschemeι k
          (by rwa [J.range_subschemeι]),
        add_zero]
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f
      (I ⊓ J).subschemeι k hdim,
    cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f I.subschemeι k
      hdim,
    cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C f J.subschemeι k
      hdim, add_zero]

end Union

end Stacks.Chow

end
