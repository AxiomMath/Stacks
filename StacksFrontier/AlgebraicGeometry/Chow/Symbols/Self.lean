module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Sign
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Basic

/-!
# The symbol of an element with itself

For a finite module of dimension one over a Noetherian local ring, the symbol of a
nonzerodivisor with itself is a sign determined by the length of the quotient module.

## Main results

* `AlgebraicGeometry.moduleSymbol_self_eq_negOne_pow_length`: the symbol `(a, a)` equals
  `(-1) ^ length (M / aM)`.

## References

* [Stacks Project, Tag 0AY9](https://stacks.math.columbia.edu/tag/0AY9)
-/

@[expose] public section

noncomputable section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- The image of the endomorphism induced by `f` on the quotient by the image of `f ∘ f` has the
same length as the quotient by the image of `f`. -/
private theorem moduleLength_range_mapQ_self
    {A : Type u} {M : Type v} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] (f : M →ₗ[A] M)
    (hf : Function.Injective f) :
    moduleLength A
        (LinearMap.range
          (Submodule.mapQ (LinearMap.range (f ∘ₗ f))
            (LinearMap.range (f ∘ₗ f)) f (by
              rintro y ⟨x, rfl⟩
              exact ⟨f x, rfl⟩))) =
      moduleLength A (M ⧸ LinearMap.range f) := by
  let p : Submodule A M := LinearMap.range (f ∘ₗ f)
  let q : M ⧸ p →ₗ[A] M ⧸ p := Submodule.mapQ p p f (by
    rintro y ⟨x, rfl⟩
    exact ⟨f x, rfl⟩)
  let g : M →ₗ[A] M ⧸ p := q.comp (Submodule.mkQ p)
  have hker : LinearMap.ker g = LinearMap.range f := by
    apply le_antisymm
    · intro x hx
      change Submodule.Quotient.mk (f x) = 0 at hx
      obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
      exact ⟨y, hf (by simpa using hy)⟩
    · rintro x ⟨y, rfl⟩
      change Submodule.Quotient.mk (f (f y)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y, rfl⟩
  have hrange : LinearMap.range g = LinearMap.range q := by
    simpa [g] using LinearMap.range_comp_of_range_eq_top q (Submodule.range_mkQ p)
  change (Module.length A (LinearMap.range q)).toNat =
    (Module.length A (M ⧸ LinearMap.range f)).toNat
  rw [← hrange, ← hker]
  exact congrArg ENat.toNat g.quotKerEquivRange.length_eq.symm

/-- The symbol of a nonzerodivisor `a` with itself is `(-1) ^ length (M / aM)`. -/
@[stacks 0AY9]
theorem moduleSymbol_self_eq_negOne_pow_length
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a : A) (ha : IsSMulRegular M a)
    (hdim : Module.supportDim A M = 1) :
    moduleSymbol a a ha ha hdim =
      (-1 : (IsLocalRing.ResidueField A)ˣ) ^
        moduleLength A (M ⧸ (LinearMap.lsmul A M a).range) := by
  let φ : M →ₗ[A] M := LinearMap.lsmul A M a
  let hcomm := range_lsmul_comp_comm (M := M) a a
  let θ := periodicQuotientPhi φ φ hcomm
  let θ' := Submodule.mapQ (LinearMap.range (φ ∘ₗ φ))
    (LinearMap.range (φ ∘ₗ φ)) φ (by
      rintro y ⟨x, rfl⟩
      exact ⟨φ x, rfl⟩)
  have hmap : θ = θ' := by
    ext x
    simp [θ, θ', periodicQuotientPhi]
  have hθ : Function.Exact θ θ :=
    exact_mul_left_right (M := M) a a ha
  have hfinite : IsFiniteLength A (M ⧸ LinearMap.range (φ ∘ₗ φ)) :=
    isFiniteLength_quotient_mul (M := M) a a ha ha hdim
  change periodicDeterminant θ θ hθ hθ hfinite = _
  rw [periodicDeterminant_self_eq_negOne_pow_range_length θ hθ hfinite, hmap]
  congr 1
  simpa [φ, θ'] using moduleLength_range_mapQ_self φ ha

end AlgebraicGeometry
