module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.DeterminantLine

/-!
# The determinant of an exact periodic complex from four symbol scalars

Let `(N, φ, ψ)` be an exact two-periodic complex of finite length over a local ring. Take
generating admissible sequences `xs` of `im ψ` and `ts` of `im φ`, and two further sequences
`ss` of `im ψ` and `ys` of `im φ` whose symbols are the multiples `g` and `h` of the first two.
If the two determinant maps carry `xs ⊗ ys` and `ts ⊗ ss` to a common element of the determinant
line up to the scalars `f_φ` and `f_ψ`, then `f_φ h` and `f_ψ g` differ by the signed periodic
determinant. Equivalently the periodic determinant is `± f_φ h / (f_ψ g)`.

## Main results

* `AlgebraicGeometry.periodicDeterminant_mul_eq_mul_of_symbol_smul` is the comparison.

## Implementation notes

The element of the determinant line that the two sides share is left implicit: instead of naming
it, the hypothesis equates the two scaled determinant-map values directly, which is how it arises
from a sequence that lies in both spans. The two determinant maps are
`AlgebraicGeometry.periodicGamma` for the two short exact sequences cut out by the images, and
their tensor factors come in opposite orders, so the comparison picks up the sign
`(-1) ^ (length (im φ) * length (im ψ))` recorded in `AlgebraicGeometry.IsPeriodicDeterminant`.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/

@[expose] public section

open scoped TensorProduct

open Module.FiniteLength

universe u v

namespace AlgebraicGeometry

/-- Over a field, the tensor of a vector spanning a line with any nonzero vector is nonzero. -/
private theorem tmul_ne_zero_of_span_eq_top {k : Type u} [Field k] {A B : Type v}
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B] {a : A} {b : B}
    (ha : (k ∙ a) = ⊤) (ha0 : a ≠ 0) (hb : b ≠ 0) :
    a ⊗ₜ[k] b ≠ 0 := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton k A a) := by
    rw [← LinearMap.ker_eq_bot]
    ext c
    simp only [Submodule.mem_bot, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact ⟨fun hc ↦ (smul_eq_zero.mp hc).resolve_right ha0, fun hc ↦ by rw [hc, zero_smul]⟩
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k A a) := fun x ↦ by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (ha ▸ Submodule.mem_top (x := x))
    exact ⟨c, rfl⟩
  let e : k ≃ₗ[k] A := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have hea : e 1 = a := by
    show LinearMap.toSpanSingleton k A a 1 = a
    simp
  intro hz
  apply hb
  have key : TensorProduct.lid k B
      (TensorProduct.congr e.symm (LinearEquiv.refl k B) (a ⊗ₜ[k] b)) = b := by
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      e.symm_apply_eq.mpr hea.symm, TensorProduct.lid_tmul, one_smul]
  rw [← key, hz, map_zero, map_zero]

/-- For an exact two-periodic complex of finite length, let `xs`, `ts` be generating admissible
sequences of `im ψ` and `im φ`, and let `ss`, `ys` be sequences of `im ψ` and `im φ` with
`symbol ss = g • symbol xs` and `symbol ys = h • symbol ts`. If `f_φ` times the determinant map
applied to `xs ⊗ ys` equals `f_ψ` times the opposite determinant map applied to `ts ⊗ ss`, then
`f_φ h` is the signed periodic determinant times `f_ψ g`. -/
theorem periodicDeterminant_mul_eq_mul_of_symbol_smul
    {A : Type u} {N : Type v} [CommRing A] [IsLocalRing A] [AddCommGroup N] [Module A N]
    (φ ψ : N →ₗ[A] N) (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hN : IsFiniteLength A N)
    (xs ss : AdmissibleSequence A (LinearMap.range ψ))
    (ts ys : AdmissibleSequence A (LinearMap.range φ))
    (hxs : Submodule.span A (Set.range xs.1) = ⊤)
    (hts : Submodule.span A (Set.range ts.1) = ⊤)
    (g h fφ fψ : IsLocalRing.ResidueField A)
    (hys : symbol ys = h • symbol ts)
    (hss : symbol ss = g • symbol xs)
    (hz : fφ • periodicGamma φ ψ hψφ hN (symbol xs ⊗ₜ symbol ys)
        = fψ • periodicGamma ψ φ hφψ hN (symbol ts ⊗ₜ symbol ss)) :
    fφ * h =
      ((-1 : IsLocalRing.ResidueField A) ^
          (moduleLength A (LinearMap.range φ) * moduleLength A (LinearMap.range ψ)) *
        (periodicDeterminant φ ψ hφψ hψφ hN : IsLocalRing.ResidueField A)) * (fψ * g) := by
  have hr (M : Submodule A N) : IsFiniteLength A M := hN.of_injective M.subtype_injective
  have hspx : (IsLocalRing.ResidueField A) ∙ symbol xs = ⊤ := span_symbol_eq_top (hr _) xs hxs
  have htm : symbol xs ⊗ₜ[IsLocalRing.ResidueField A] symbol ts ≠ 0 :=
    tmul_ne_zero_of_span_eq_top hspx (symbol_ne_zero_of_span_eq_top (hr _) xs hspx)
      (symbol_ne_zero_of_span_eq_top (hr _) ts (span_symbol_eq_top (hr _) ts hts))
  have hbij : Function.Bijective (periodicGamma φ ψ hψφ hN) := by
    unfold periodicGamma
    exact determinantExactSequenceMap_bijective _ _ _ _ _ _ _ _
  have hw : periodicGamma φ ψ hψφ hN
      (symbol xs ⊗ₜ[IsLocalRing.ResidueField A] symbol ts) ≠ 0 := fun hh ↦
    htm (hbij.1 (by rw [hh, map_zero]))
  have hdet := periodicDeterminant_spec φ ψ hφψ hψφ hN
  change periodicGamma ψ φ hφψ hN ∘ₗ
      (TensorProduct.comm (IsLocalRing.ResidueField A)
        (determinant A (LinearMap.range ψ))
        (determinant A (LinearMap.range φ))).toLinearMap =
    (((-1 : IsLocalRing.ResidueField A) ^
      (moduleLength A (LinearMap.range φ) * moduleLength A (LinearMap.range ψ))) *
      (periodicDeterminant φ ψ hφψ hψφ hN : IsLocalRing.ResidueField A)) •
      periodicGamma φ ψ hψφ hN at hdet
  have hval := LinearMap.congr_fun hdet (symbol xs ⊗ₜ[IsLocalRing.ResidueField A] symbol ts)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul] at hval
  rw [hys, hss, TensorProduct.tmul_smul, TensorProduct.tmul_smul, map_smul, map_smul,
    smul_smul, smul_smul, hval, smul_smul] at hz
  refine smul_left_injective _ hw ?_
  dsimp only
  rw [hz]
  congr 1
  ring

end AlgebraicGeometry

end
