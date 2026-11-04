module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.FunctionField
public import StacksFrontier.RingTheory.OrderOfVanishing.RingEquivTransport

/-!
# Invariance of the order of vanishing under an isomorphism of schemes

Let `φ : V ≅ W` be an isomorphism of locally Noetherian integral schemes, let `f` be a rational
function on `V` and let `z` be a point of `V`. The order of vanishing of `f` at `z` and the order
of vanishing of the transported rational function at `φ z` agree.

## Main results

* `Stacks.Chow.ord_functionFieldRingEquivOfIso`: the order of vanishing of a rational function
  is unchanged by transporting both the function and the point along an isomorphism of schemes.

## References

* [Stacks Project, Tag 02RL](https://stacks.math.columbia.edu/tag/02RL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Invariance of the algebraic order of vanishing -/

/-- `Ring.ordFrac` is transported by a ring isomorphism of one-dimensional Noetherian domains
together with a compatible isomorphism of their fraction fields. -/
theorem ordFrac_eq_of_ringEquiv {R S K L : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 S] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra S L]
    [IsFractionRing S L] (e : R ≃+* S) (E : K ≃+* L)
    (h : ∀ r : R, E (algebraMap R K r) = algebraMap S L (e r)) (f : K) :
    Ring.ordFrac S (E f) = Ring.ordFrac R f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  rw [map_div₀, h, h]
  have key : ∀ x : R, x ≠ 0 → e x ∈ nonZeroDivisors S := fun x hx ↦
    mem_nonZeroDivisors_of_ne_zero (by simpa using hx)
  have hb' := key b (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  by_cases ha : a = 0
  · simp [ha]
  have ha' := key a ha
  rw [← IsFractionRing.mk'_mk_eq_div hb, ← IsFractionRing.mk'_mk_eq_div hb',
    Ring.ordFrac_eq_div S ⟨e a, ha'⟩ ⟨e b, hb'⟩,
    Ring.ordFrac_eq_div R ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩ ⟨b, hb⟩,
    Ring.ordMonoidWithZeroHom_eq_ord ha',
    Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr ha),
    Ring.ordMonoidWithZeroHom_eq_ord hb', Ring.ordMonoidWithZeroHom_eq_ord hb,
    ← Stacks.OrderOfVanishing.ord_eq_of_ringEquiv e a,
    ← Stacks.OrderOfVanishing.ord_eq_of_ringEquiv e b]

/-! ### Invariance of the order of vanishing on a scheme -/

variable {V W : Scheme.{u}}

/-- **The order of vanishing is an isomorphism invariant.** For an isomorphism `φ : V ≅ W` of
locally Noetherian integral schemes, the order of vanishing at `φ z` of the rational function
transported along `φ` equals the order of vanishing of the original rational function at `z`. -/
theorem ord_functionFieldRingEquivOfIso (φ : V ≅ W) [IsIntegral V] [IsIntegral W]
    [IsLocallyNoetherian V] [IsLocallyNoetherian W] (f : V.functionField) (z : V) :
    W.ord (functionFieldRingEquivOfIso φ f) (φ.hom.base z) = V.ord f z := by
  have hcoh : coheight (φ.hom.base z) = coheight z := coheight_eq_of_isOpenImmersion φ.hom
  by_cases hz : coheight z = 1
  · have hφz : coheight (φ.hom.base z) = 1 := hcoh.trans hz
    let _ : Ring.KrullDimLE 1 (V.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    let _ : Ring.KrullDimLE 1 (W.presheaf.stalk (φ.hom.base z)) :=
      krullDimLE_of_coheight_le hφz.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hφz, Scheme.ord_eq_ordHom_of_coheight_eq_one hz]
    exact congrArg (fun t ↦ Multiplicative.toAdd (WithZero.unzeroD 1 t))
      (ordFrac_eq_of_ringEquiv (stalkRingEquivOfIso φ z) (functionFieldRingEquivOfIso φ)
        (functionFieldRingEquivOfIso_algebraMap φ z) f)
  · have hφz : coheight (φ.hom.base z) ≠ 1 := fun h ↦ hz (hcoh.symm.trans h)
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hφz, Scheme.ord_eq_zero_of_coheight_neq_one hz]

end Stacks.Chow

end
