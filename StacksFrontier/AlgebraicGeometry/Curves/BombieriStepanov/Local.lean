module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Places

/-!
# Orders at a point whose local ring is a discrete valuation ring

Let `X` be an integral locally Noetherian scheme and `x` a point of codimension one whose local
ring `𝒪_{X,x}` is a discrete valuation ring. This file collects the facts about
`ord_x = AlgebraicGeometry.Scheme.ord · x` used to read the places of a curve. A rational
function with `ord_x ≥ 0` comes from `𝒪_{X,x}`. Elements of `𝒪_{X,x}` have `ord_x ≥ 0`, and
elements of the maximal ideal have `ord_x ≥ 1`. Two rational functions of the same order differ by
a unit of `𝒪_{X,x}`.

## Main results

* `Stacks.BombieriStepanov.exists_algebraMap_eq_of_ord_nonneg`
* `Stacks.BombieriStepanov.ord_algebraMap_nonneg`, `Stacks.BombieriStepanov.one_le_ord_algebraMap`
* `Stacks.BombieriStepanov.exists_unit_mul_eq_of_ord_eq`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {x : X} (hx : coheight x = 1)

include hx

/-- At a point of codimension one the order homomorphism of `X` is the valuation `Ring.ordFrac` of
the local ring `𝒪_{X,x}` on its fraction field. -/
theorem ordHom_eq_ordFrac :
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    X.ordHom x hx = Ring.ordFrac (X.presheaf.stalk x) := rfl

/-- Elements of the local ring have nonnegative order. -/
theorem ord_algebraMap_nonneg {a : X.presheaf.stalk x} (ha : a ≠ 0) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have ha' : algebraMap _ X.functionField a ≠ 0 := by simpa using ha
  rw [Scheme.le_ord_iff hx ha', ordHom_eq_ordFrac hx]
  exact Ring.ordFrac_ge_one_of_ne_zero ha

variable [IsDiscreteValuationRing (X.presheaf.stalk x)]

/-- A uniformizer has order one. -/
theorem ord_algebraMap_irreducible {π : X.presheaf.stalk x} (hπ : Irreducible π) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField π) x = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hπ' : algebraMap _ X.functionField π ≠ 0 := by simpa using hπ.ne_zero
  rw [Scheme.ord_eq_iff hx hπ', ordHom_eq_ordFrac hx, Ring.ordFrac_irreducible hπ]
  rfl

/-- Elements of the maximal ideal have order at least one. -/
theorem one_le_ord_algebraMap {a : X.presheaf.stalk x} (ha : a ≠ 0)
    (hm : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    1 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  rw [hspan, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, rfl⟩ := hm
  have hb : b ≠ 0 := left_ne_zero_of_mul ha
  have hπ0 : algebraMap _ X.functionField π ≠ 0 := by simpa using hπ.ne_zero
  have hb0 : algebraMap _ X.functionField b ≠ 0 := by simpa using hb
  rw [map_mul, Scheme.ord_mul hb0 hπ0, ord_algebraMap_irreducible hx hπ]
  have := ord_algebraMap_nonneg hx hb
  omega

/-- Two nonzero rational functions of the same order differ by a unit of the local ring. -/
theorem exists_unit_mul_eq_of_ord_eq {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : X.ord f x = X.ord g x) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField u * g = f := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hf' := (Scheme.ord_eq_iff hx hf).1 rfl
  have hg' := (Scheme.ord_eq_iff hx hg).1 h.symm
  rw [ordHom_eq_ordFrac hx] at hf' hg'
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := X.presheaf.stalk x) g f
    (hg'.trans hf'.symm)
  exact ⟨u, by rw [← hu, Units.smul_def, Algebra.smul_def]⟩

/-- A rational function of nonnegative order comes from the local ring. -/
theorem exists_algebraMap_eq_of_ord_nonneg {y : X.functionField} (hy : 0 ≤ X.ord y x) :
    ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, map_zero _⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have hπ0 : algebraMap _ X.functionField π ≠ 0 := by simpa using hπ.ne_zero
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hy
  have hpow : ∀ n : ℕ,
      X.ord ((algebraMap (X.presheaf.stalk x) X.functionField π) ^ n) x = n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hπ0) hπ0, ih, ord_algebraMap_irreducible hx hπ]
      push_cast
      ring
  obtain ⟨u, hu⟩ := exists_unit_mul_eq_of_ord_eq hx hy0 (pow_ne_zero n hπ0)
    (by rw [hpow n, hn])
  exact ⟨u * π ^ n, by rw [map_mul, map_pow, hu]⟩

end Stacks.BombieriStepanov

end
