module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic

/-!
# The order of an element of the stalk of an invertible module at a discrete valuation point

Let `X` be a scheme, `M` an invertible `𝒪_X`-module and `x` a point at which the local ring
`𝒪_{X,x}` is a discrete valuation ring. The stalk `M_x` is free of rank one over `𝒪_{X,x}`, so
every element `z` of it is `r • g` for a generator `g`, and the valuation of `r` does not depend
on the generator. This file defines that number, the *order* of `z`, without choosing a
generator: it is the largest valuation of an element `r` of which `z` is a multiple.

## Main definitions

* `Stacks.StalkOrder.stalkOrd`: the order of an element of `M_x`.

## Main results

* `Stacks.StalkOrder.exists_generator`: `M_x` is free of rank one, with a generator.
* `Stacks.StalkOrder.stalkOrd_smul_generator`: the order of `r • g` is the valuation of `r`.
* `Stacks.StalkOrder.stalkOrd_eq_top_iff`, `Stacks.StalkOrder.stalkOrd_smul`,
  `Stacks.StalkOrder.min_le_stalkOrd_add`, `Stacks.StalkOrder.stalkOrd_neg`: the order is a
  valuation on `M_x`.
* `Stacks.StalkOrder.exists_isUnit_lt_stalkOrd_sub`: two elements of the same finite order agree
  to first order up to a unit.

## Implementation notes

The generator is the germ of the basis section of a trivialization through `x`, which
`Stacks.SectionProduct.exists_trivialization_at` provides for any invertible module; that it is
a free generator is read off the trivialization.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.ModuleStalk

universe u

namespace Stacks.StalkOrder

variable {X : Scheme.{u}}

/-- **The stalk of an invertible module is free of rank one**: it has an element `g` of which every
element is a multiple, and only the zero multiple of `g` vanishes. -/
theorem exists_generator (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (x : X) :
    ∃ g : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x,
      (∀ z, ∃ r : X.presheaf.stalk x, z = r • g) ∧
        ∀ r : X.presheaf.stalk x, r • g = 0 → r = 0 := by
  obtain ⟨V, hxV, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at M x
  refine ⟨(M.presheaf.germ V x hxV).hom (Stacks.NonvanishingOpen.basis t),
    fun z => Stacks.SectionProduct.exists_smul_germ_basis t hxV z, fun r hr => ?_⟩
  obtain ⟨W, hxW, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  have hxVW : x ∈ V ⊓ W := ⟨hxV, hxW⟩
  set c' : Γ(X, V ⊓ W) := X.presheaf.map (homOfLE inf_le_right).op c with hc'
  set b' : Γ(M, V ⊓ W) := M.presheaf.map (homOfLE inf_le_left).op
    (Stacks.NonvanishingOpen.basis t) with hb'
  have hgerm : (M.presheaf.germ (V ⊓ W) x hxVW).hom (c' • b') =
      (M.presheaf.germ (V ⊓ W) x hxVW).hom 0 := by
    rw [germ_smul, hc', hb', TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      map_zero]
    exact hr
  obtain ⟨W', hxW', i₁, i₂, he⟩ :=
    TopCat.Presheaf.germ_eq M.presheaf x hxVW hxVW _ _ hgerm
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  have hzero : X.presheaf.map i₁.op c' = 0 := by
    have h1 := congrArg (Stacks.NonvanishingOpen.triv t (i₁ ≫ homOfLE inf_le_left)) he
    have h0 : Stacks.NonvanishingOpen.triv t (i₁ ≫ homOfLE inf_le_left)
        ((M.presheaf.map i₁.op) 0) = 0 := by
      rw [map_zero]
      exact map_zero (t.θ _ _)
    rw [h0] at h1
    rw [← h1, Scheme.Modules.map_smul, Stacks.NonvanishingOpen.triv_smul, hb',
      ← M.presheaf.map_comp_apply, ← op_comp, Stacks.NonvanishingOpen.triv_res_basis, mul_one]
  have : (X.presheaf.germ W x hxW).hom c =
      (X.presheaf.germ W' x hxW').hom (X.presheaf.map i₁.op c') := by
    rw [TopCat.Presheaf.germ_res_apply, hc', TopCat.Presheaf.germ_res_apply]
  rw [this, hzero, map_zero]

variable (M : X.Modules) (x : X)

/-- **The order of an element `z` of the stalk `M_x`**: the supremum of the valuations of the
elements `r` of `𝒪_{X,x}` of which `z` is a multiple. -/
def stalkOrd [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) : ℕ∞ :=
  ⨆ (r : X.presheaf.stalk x) (_ : ∃ w, z = r • w),
    IsDiscreteValuationRing.addVal (X.presheaf.stalk x) r

variable [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
  {M x}

/-- **The order of `r • g` is the valuation of `r`**, for a free generator `g` of `M_x`. -/
theorem stalkOrd_smul_generator {g : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x}
    (hg : ∀ z, ∃ r : X.presheaf.stalk x, z = r • g)
    (hfree : ∀ r : X.presheaf.stalk x, r • g = 0 → r = 0) (r : X.presheaf.stalk x) :
    stalkOrd M x (r • g) = IsDiscreteValuationRing.addVal (X.presheaf.stalk x) r := by
  refine le_antisymm (iSup₂_le fun s ⟨w, hw⟩ => ?_) (le_iSup₂_of_le r ⟨g, rfl⟩ le_rfl)
  obtain ⟨c, rfl⟩ := hg w
  rw [smul_smul, ← sub_eq_zero, ← sub_smul] at hw
  have hrs : r = s * c := sub_eq_zero.mp (hfree _ hw)
  rw [hrs, IsDiscreteValuationRing.addVal_mul]
  exact le_self_add

/-- The order of an element, read off a free generator: if `z = r • g` then its order is the
valuation of `r`. -/
theorem stalkOrd_eq_addVal {g : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x}
    (hg : ∀ z, ∃ r : X.presheaf.stalk x, z = r • g)
    (hfree : ∀ r : X.presheaf.stalk x, r • g = 0 → r = 0)
    {z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x} {r : X.presheaf.stalk x}
    (hz : z = r • g) :
    stalkOrd M x z = IsDiscreteValuationRing.addVal (X.presheaf.stalk x) r := by
  rw [hz, stalkOrd_smul_generator hg hfree]

variable [Stacks.Ample.IsInvertibleModule X M]

/-- **The order of an element is infinite exactly when the element is zero.** -/
theorem stalkOrd_eq_top_iff (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkOrd M x z = ⊤ ↔ z = 0 := by
  obtain ⟨g, hg, hfree⟩ := exists_generator M x
  obtain ⟨r, rfl⟩ := hg z
  rw [stalkOrd_smul_generator hg hfree, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact ⟨fun h => by rw [h, zero_smul], fun h => hfree r h⟩

/-- **The order is additive under scalar multiplication.** -/
theorem stalkOrd_smul (c : X.presheaf.stalk x)
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkOrd M x (c • z) =
      IsDiscreteValuationRing.addVal (X.presheaf.stalk x) c + stalkOrd M x z := by
  obtain ⟨g, hg, hfree⟩ := exists_generator M x
  obtain ⟨r, rfl⟩ := hg z
  rw [smul_smul, stalkOrd_smul_generator hg hfree, stalkOrd_smul_generator hg hfree,
    IsDiscreteValuationRing.addVal_mul]

/-- **The order of a sum is at least the smaller of the two orders.** -/
theorem min_le_stalkOrd_add (z z' : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    min (stalkOrd M x z) (stalkOrd M x z') ≤ stalkOrd M x (z + z') := by
  obtain ⟨g, hg, hfree⟩ := exists_generator M x
  obtain ⟨r, rfl⟩ := hg z
  obtain ⟨r', rfl⟩ := hg z'
  simp only [← add_smul, stalkOrd_smul_generator hg hfree]
  exact IsDiscreteValuationRing.addVal_add

/-- The order of the negative of an element is its order. -/
theorem stalkOrd_neg (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkOrd M x (-z) = stalkOrd M x z := by
  have h1 : IsDiscreteValuationRing.addVal (X.presheaf.stalk x) (-1) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_of_unit (-1 : (X.presheaf.stalk x)ˣ)
  rw [← neg_one_smul (X.presheaf.stalk x) z, stalkOrd_smul, h1, zero_add]

/-- **Two elements of the same order differ by a unit**: in a free module of rank one over a
discrete valuation ring, elements of equal valuation are associated. -/
theorem exists_unit_smul_eq {z z' : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x}
    (h : stalkOrd M x z = stalkOrd M x z') :
    ∃ v : (X.presheaf.stalk x)ˣ, z = (v : X.presheaf.stalk x) • z' := by
  obtain ⟨g, hg, hfree⟩ := exists_generator M x
  obtain ⟨r, rfl⟩ := hg z
  obtain ⟨r', rfl⟩ := hg z'
  simp only [stalkOrd_smul_generator hg hfree] at h
  obtain ⟨v, hv⟩ := ((IsDiscreteValuationRing.addVal_eq_iff_associated r' r).mp h.symm)
  exact ⟨v, by rw [smul_smul, ← hv, mul_comm]⟩

/-- **An injective linear map out of the stalk preserves orders**, provided its target is the stalk
of an invertible module and the map is bijective. -/
theorem stalkOrd_map_of_bijective {N : X.Modules} [Stacks.Ample.IsInvertibleModule X N]
    (ψ : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x →ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x) (hψ : Function.Bijective ψ)
    (z : TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x) :
    stalkOrd N x (ψ z) = stalkOrd M x z := by
  obtain ⟨g, hg, hfree⟩ := exists_generator M x
  obtain ⟨r, rfl⟩ := hg z
  have hg' : ∀ w, ∃ s : X.presheaf.stalk x, w = s • ψ g := fun w => by
    obtain ⟨v, rfl⟩ := hψ.2 w
    obtain ⟨s, rfl⟩ := hg v
    exact ⟨s, map_smul ψ s g⟩
  have hfree' : ∀ s : X.presheaf.stalk x, s • ψ g = 0 → s = 0 := fun s hs =>
    hfree s (hψ.1 (by rw [map_smul, hs, map_zero]))
  rw [map_smul, stalkOrd_smul_generator hg' hfree', stalkOrd_smul_generator hg hfree]

end Stacks.StalkOrder

end
