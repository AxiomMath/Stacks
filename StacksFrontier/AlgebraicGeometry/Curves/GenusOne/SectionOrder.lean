module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSection
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.StalkOrder
public import StacksFrontier.AlgebraicGeometry.SectionProduct.StalkMultiple

/-!
# The order at a point of the homogeneous elements of a section ring

Let `L` be an invertible module on a scheme `X` and `x` a point whose local ring is a discrete
valuation ring. A homogeneous element `s` of degree `n` of the section ring `Γ_*(X, L)` has a
germ in the stalk of `L ^⊗ n` at `x`, which is free of rank one, and so an order
(`Stacks.StalkOrder.stalkOrd`). This file proves that the order is additive under the product of
the section ring, that it is an ultrametric valuation on each graded piece, and, when `X` is
integral, that it is finite on nonzero elements.

## Main definitions

* `Stacks.StalkOrder.sectionOrd`: the order at `x` of a homogeneous element.

## Main results

* `Stacks.StalkOrder.stalkOrd_mapFun_of_stalkMul`: a morphism of invertible modules whose stalk
  map has image exactly the `r`-multiples adds the valuation of `r` to orders.
* `Stacks.StalkOrder.sectionOrd_mul`: **the order of a product is the sum of the orders.**
* `Stacks.StalkOrder.sectionOrd_eq_top_iff`: on an integral scheme the order is infinite only at
  zero.

## Implementation notes

Multiplication by a section `s` of degree `n` is `Stacks.GradedSections.mulMap s m`. The germ of
`s` is `r • g` for a free generator `g`, so the stalk map of `s` has image exactly the
`r`-multiples, and `Stacks.SectionProduct.stalkMulLE_mulMap` and
`Stacks.SectionProduct.stalkMulGE_mulMap` carry this to `mulMap s m`. No formula for the monoidal
structure on sections is needed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.ModuleStalk Stacks.SectionProduct
open Stacks.GradedSections (powSections mul mulMap)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.StalkOrder

variable {X : Scheme.{u}} {x : X} [IsDomain (X.presheaf.stalk x)]
  [IsDiscreteValuationRing (X.presheaf.stalk x)]

/-- **A morphism whose stalk map has image exactly the `r`-multiples adds the valuation of `r`
to orders**, between invertible modules. -/
theorem stalkOrd_mapFun_of_stalkMul {M N : X.Modules} [Stacks.Ample.IsInvertibleModule X M]
    [Stacks.Ample.IsInvertibleModule X N] (φ : M ⟶ N) {r : X.presheaf.stalk x}
    (hle : StalkMulLE φ x r) (hge : StalkMulGE φ x r)
    (w : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkOrd N x (mapFun φ x w) =
      IsDiscreteValuationRing.addVal (X.presheaf.stalk x) r + stalkOrd M x w := by
  obtain ⟨g, hg, hfree⟩ := exists_generator M x
  obtain ⟨h, hh, hhfree⟩ := exists_generator N x
  obtain ⟨a, rfl⟩ := hg w
  obtain ⟨z₀, hz₀⟩ := hle g
  rw [mapFun_smul, hz₀, stalkOrd_smul_generator hg hfree, smul_smul, stalkOrd_smul]
  by_cases hr : r = 0
  · rw [hr, mul_zero, IsDiscreteValuationRing.addVal_zero, top_add, top_add]
  -- `z₀` is a generator of `N_x`, so its order is zero.
  obtain ⟨w₀, hw₀⟩ := hge h
  obtain ⟨c, rfl⟩ := hg w₀
  rw [mapFun_smul, hz₀, smul_smul] at hw₀
  obtain ⟨d, hd⟩ := hh z₀
  have hcd : c * d = 1 := by
    have h₁ : (c * r * d - r) • h = 0 := by
      rw [sub_smul, ← smul_smul, ← hd, hw₀, sub_self]
    have h₂ : r * (c * d - 1) = 0 := by linear_combination hhfree _ h₁
    exact sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_left hr)
  have hd0 : IsDiscreteValuationRing.addVal (X.presheaf.stalk x) d = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_of_unit (IsUnit.of_mul_eq_one_right c hcd).unit
  rw [hd, stalkOrd_smul_generator hh hhfree, hd0, add_zero,
    IsDiscreteValuationRing.addVal_mul, add_comm]

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- The germ at `x` of the global section of a homogeneous element of degree `n`. -/
abbrev sectionGerm {n : ℕ} (s : powSections L n) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (natTensorPow L n).presheaf x :=
  ((natTensorPow L n).presheaf.Γgerm x).hom (globalSection X _ s)

variable (x) in
/-- **The order at `x` of a homogeneous element of the section ring**: the order of the germ at
`x` of its global section, in the stalk of the tensor power. -/
def sectionOrd {n : ℕ} (s : powSections L n) : ℕ∞ :=
  stalkOrd (natTensorPow L n) x (sectionGerm L s)

/-- **The order of a product is the sum of the orders.** -/
theorem sectionOrd_mul {n m : ℕ} (s : powSections L n) (t : powSections L m) :
    sectionOrd x L (mul s t) = sectionOrd x L s + sectionOrd x L t := by
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L n
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L m
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L (n + m)
  obtain ⟨g, hg, hfree⟩ := exists_generator (natTensorPow L n) x
  obtain ⟨r, hr⟩ := hg (((natTensorPow L n).presheaf.Γgerm x).hom (globalSection X _ s))
  have hle : StalkMulLE s x r := (stalkMulLE_unit_iff _ s x r).mpr ⟨g, hr⟩
  have hge : StalkMulGE s x r := (stalkMulGE_unit_iff _ s x r).mpr fun z => by
    obtain ⟨c, rfl⟩ := hg z
    exact ⟨c, by rw [hr, smul_smul, smul_smul, mul_comm]⟩
  unfold sectionOrd sectionGerm
  rw [Γgerm_globalSection_mul, stalkOrd_mapFun_of_stalkMul _ (stalkMulLE_mulMap L s hle m)
    (stalkMulGE_mulMap L s hge m)]
  congr 1
  rw [hr, stalkOrd_smul_generator hg hfree]

/-- **The order of a sum is at least the smaller order**, in one degree. -/
theorem min_le_sectionOrd_add {n : ℕ} (s t : powSections L n) :
    min (sectionOrd x L s) (sectionOrd x L t) ≤ sectionOrd x L (s + t) := by
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L n
  unfold sectionOrd sectionGerm
  have h : globalSection X (natTensorPow L n) (s + t) =
      globalSection X (natTensorPow L n) s + globalSection X (natTensorPow L n) t :=
    map_add (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L n)) s t
  rw [h, map_add]
  exact min_le_stalkOrd_add _ _

/-- **Scaling by a function adds the valuation of its germ.** -/
theorem sectionOrd_unitScalarEquiv_symm_comp (c : Γ(X, ⊤)) {n : ℕ} (s : powSections L n) :
    sectionOrd x L ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm c ≫ s) =
      IsDiscreteValuationRing.addVal (X.presheaf.stalk x) ((X.presheaf.Γgerm x).hom c) +
        sectionOrd x L s := by
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L n
  unfold sectionOrd sectionGerm
  have h1 : Stacks.SectionRingGeometric.unitScalar X
      ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm c) = c :=
    (Stacks.SectionRingGeometric.unitScalarEquiv X).apply_symm_apply c
  have h : globalSection X (natTensorPow L n)
      ((Stacks.SectionRingGeometric.unitScalarEquiv X).symm c ≫ s) =
      c • globalSection X (natTensorPow L n) s := by
    show Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ _ =
      c • Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ s
    rw [Stacks.SectionRingGeometric.globalSection_unitComp, h1]
  rw [h, Γgerm_smul, stalkOrd_smul]

/-- **On an integral scheme the order of a homogeneous element is infinite only at zero**: a
global section of an invertible module whose germ vanishes at one point is zero. -/
theorem sectionOrd_eq_top_iff [IsIntegral X] {n : ℕ} (s : powSections L n) :
    sectionOrd x L s = ⊤ ↔ s = 0 := by
  have := Stacks.SectionProduct.isInvertibleModule_natTensorPow (X := X) L n
  unfold sectionOrd sectionGerm
  rw [stalkOrd_eq_top_iff]
  constructor
  · intro h
    have hs : globalSection X (natTensorPow L n) s = 0 := by
      let M : X.Modules := natTensorPow L n
      have : Stacks.SheafOfModules.IsInvertible X.presheaf
          (structureSheafRing X.toRingedSpace).property M :=
        Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ this
      exact Stacks.ChernCap42.eq_zero_of_germ_eq_zero M _ h
    exact (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _).map_eq_zero_iff.mp hs
  · rintro rfl
    have h : globalSection X (natTensorPow L n) 0 = 0 :=
      map_zero (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L n))
    rw [h, map_zero]

end Stacks.StalkOrder

end
