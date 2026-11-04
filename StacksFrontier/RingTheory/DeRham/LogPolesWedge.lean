module

public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.RingTheory.DeRham.LogPolesComplex
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksCore.Tactic.StacksAttribute

/-!
# The wedge product on the de Rham complex of log poles

Let `A → R` be a ring map and let `t ∈ R` cut out the effective Cartier divisor
`Y = Spec (R ⧸ (t))` in `X = Spec R`, and assume the de Rham complex of log poles is defined for
`Y ⊆ X` over `S = Spec A`. An `𝒪_X`-bilinear extension of the wedge product
`Ω^p_{X/S} × Ω^q_{X/S} → Ω^{p+q}_{X/S}` to `Ω^•_{X/S}(log Y)` is unique, without assuming the
Leibniz rule.

## Main definitions

* `Stacks.LogPoles.logFormsR`: the log forms as `𝒪_X`-modules, that is as `R`-modules rather
  than the `A`-modules `Stacks.LogPoles.logFormsX` that the complex is built from.
* `Stacks.LogPoles.logInclR`: the inclusion `Ω^p_{X/S} → Ω^p_{X/S}(log Y)` as an `R`-linear map.
* `Stacks.LogPoles.logMulT`: multiplication by `t`, as an `R`-linear map from the log forms to
  the forms with no pole.

## Main results

* `Stacks.LogPoles.logInclR_logMulT`: `t · α = ι (logMulT α)`, that is, `t` times a log form is
  the form with no pole `t ω + dt ∧ η`.
* `Stacks.LogPoles.isSMulRegular_logFormsR`: `t` is a nonzerodivisor on the log forms.
* `Stacks.LogPoles.smul_logWedge_eq`: `t² (α ∧ β) = (tα) ∧ (tβ)` for an `𝒪_X`-bilinear
  extension, with both factors on the right forms with no pole.
* `Stacks.LogPoles.logWedge_unique`: two `𝒪_X`-bilinear products on `Ω^•_{X/S}(log Y)` that both
  restrict to the wedge product on the forms with no pole are equal.
* `Stacks.LogPoles.logFormsR_carrier_eq` and
  `Stacks.LogPoles.restrictScalars_logRel_carrier`: the `𝒪_X`-modules of log forms have the same
  carriers as the terms of the complex.

## References

* [Stacks Project, Tag 0FUP](https://stacks.math.columbia.edu/tag/0FUP), clause (1)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), the complex
* [Stacks Project, Tag 0FUA](https://stacks.math.columbia.edu/tag/0FUA), its name
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace Stacks.LogPoles

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-! ### The log forms as `𝒪_X`-modules -/

/-- The log forms as `𝒪_X`-modules, that is as `R`-modules: the functions in degree zero and the
pair model `(Ω^{p+1} × Ω^p) / logRel` in degree `p + 1`, the relations being the kernel of the
`R`-linear map `Stacks.LogPoles.logPairMap`. -/
def logFormsR (A : Type u) [CommRing A] [Algebra A R] (t : R) : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R ↥(⋀[R]^0 (Ω[R⁄A]))
  | p + 1 => ModuleCat.of R ((⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) ⧸ (logRel A t p))

/-- The `𝒪_X`-modules of log forms have the same carriers as the terms of the complex of log
poles. -/
theorem logFormsR_carrier_eq (t : R) (p : ℕ) :
    (logFormsR A t p : Type u) = (logFormsX A t p : Type u) := by
  cases p with
  | zero => rfl
  | succ q => rfl

/-- The inclusion `Ω^p_{X/S} → Ω^p_{X/S}(log Y)` of the forms with no pole, as an `R`-linear
map: the identity in degree zero and `ω ↦ (ω, 0)` in degree `p + 1`. -/
def logInclR (t : R) : (p : ℕ) → (⋀[R]^p (Ω[R⁄A]) →ₗ[R] logFormsR A t p)
  | 0 => LinearMap.id
  | p + 1 => (logRel A t p).mkQ.comp (LinearMap.inl R _ _)

/-- In degree `p + 1` the inclusion of the forms with no pole sends `ω` to the class of the
pair `(ω, 0)`. -/
@[simp]
theorem logInclR_succ_apply (t : R) (p : ℕ) (ω : ⋀[R]^(p + 1) (Ω[R⁄A])) :
    logInclR (A := A) t (p + 1) ω =
      Submodule.Quotient.mk (p := logRel A t p) (ω, 0) := rfl

/-- The `R`-submodule of relations and the `A`-submodule the complex of log poles quotients by
have the same carrier. -/
theorem restrictScalars_logRel_carrier (t : R) (p : ℕ) :
    (Submodule.restrictScalars A (logRel A t p) :
        Set (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A]))) =
      (logRel A t p : Set (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A]))) := rfl

/-- In degree zero the inclusion of the forms with no pole is the identity. -/
theorem logInclR_zero_apply (t : R) (ω : ⋀[R]^0 (Ω[R⁄A])) :
    logInclR (A := A) t 0 ω = ω := rfl

/-! ### Multiplication by the equation lands in the forms with no pole -/

/-- Multiplication by `t`, carrying a log form to a form with no pole, as an `R`-linear map: in
the pair model `t · (ω + dlog t ∧ η) = t ω + dt ∧ η`, which is `Stacks.LogPoles.logPairMap`. -/
def logMulT (A : Type u) [CommRing A] [Algebra A R] (t : R) :
    (p : ℕ) → (logFormsR A t p →ₗ[R] ⋀[R]^p (Ω[R⁄A]))
  | 0 => t • LinearMap.id
  | p + 1 => Submodule.liftQ _ (logPairMap A t p) le_rfl

/-- In degree `p + 1` multiplication by `t` sends the class of a pair `x` to its image
under `Stacks.LogPoles.logPairMap`. -/
@[simp]
theorem logMulT_succ_apply (t : R) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logMulT A t (p + 1) (Submodule.Quotient.mk (p := logRel A t p) x) =
      logPairMap A t p x := rfl

/-- `t` times a log form is the form with no pole `t ω + dt ∧ η`. -/
theorem logInclR_logMulT (t : R) (p : ℕ) (α : logFormsR A t p) :
    logInclR (A := A) t p (logMulT A t p α) = t • α := by
  cases p with
  | zero => rfl
  | succ q =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (logRel A t q) α
      rw [logMulT_succ_apply, logInclR_succ_apply]
      refine (Submodule.Quotient.eq (logRel A t q)).mpr ?_
      rw [mem_logRel_iff, logPairMap]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.fst_apply,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
        Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub]
      simp only [add_sub_cancel_left, zero_sub, map_neg, map_smul]
      abel

/-- If `t` is a nonzerodivisor on the forms, a pair whose `t`-multiple is a relation is itself a
relation. -/
theorem mem_logRel_of_smul_mem {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ)
    {z : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hz : t • z ∈ logRel A t p) :
    z ∈ logRel A t p := by
  rw [mem_logRel_iff] at hz ⊢
  refine ht (p + 1) ?_
  show t • (t • z.1 + exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p z.2) =
    t • (0 : ⋀[R]^(p + 1) (Ω[R⁄A]))
  rw [smul_zero, smul_add, smul_smul]
  simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_smul] using hz

/-- If `t` is a nonzerodivisor on the forms, it is a nonzerodivisor on the log forms. -/
theorem isSMulRegular_logFormsR {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) (p : ℕ) :
    IsSMulRegular (logFormsR A t p) t := by
  cases p with
  | zero => exact ht 0
  | succ q =>
      intro α β hαβ
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (logRel A t q) α
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (logRel A t q) β
      have h2 : t • x - t • y ∈ logRel A t q :=
        (Submodule.Quotient.eq (logRel A t q)).mp hαβ
      have h3 : t • (x - y) ∈ logRel A t q := by rwa [smul_sub]
      exact (Submodule.Quotient.eq (logRel A t q)).mpr (mem_logRel_of_smul_mem ht q h3)

/-! ### Uniqueness of the extension of the wedge product -/

/-- For an `𝒪_X`-bilinear extension `w` of the wedge product, `t² w(α, β)` is the inclusion of
the ordinary wedge product of `Stacks.LogPoles.logMulT α` and `Stacks.LogPoles.logMulT β`. -/
theorem smul_logWedge_eq {t : R}
    (w : (p q : ℕ) →
      logFormsR A t p →ₗ[R] logFormsR A t q →ₗ[R] logFormsR A t (p + q))
    (hw : ∀ (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A])),
      w p q (logInclR t p ω) (logInclR t q η) =
        logInclR t (p + q) (exteriorPower.wedgeMul p q ω η))
    (p q : ℕ) (α : logFormsR A t p) (β : logFormsR A t q) :
    (t * t) • w p q α β =
      logInclR t (p + q) (exteriorPower.wedgeMul p q
        (logMulT A t p α) (logMulT A t q β)) := by
  have hscale : w p q (t • α) (t • β) = (t * t) • w p q α β := by
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul]
  rw [← hscale, ← logInclR_logMulT t p α, ← logInclR_logMulT t q β, hw]

/-- If `t` is a nonzerodivisor on the forms, two `𝒪_X`-bilinear products on the de Rham complex
of log poles that both restrict to the wedge product on the forms with no pole are equal. -/
@[stacks 0FUP "clause (1), the uniqueness half, strengthened by dropping the Leibniz hypothesis: \
an O_X-bilinear extension of the wedge to the log poles complex of 0FMW is unique. Existence, \
and clauses (2), (3), (4), are not proved here"]
theorem logWedge_unique {t : R}
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (w₁ w₂ : (p q : ℕ) →
      logFormsR A t p →ₗ[R] logFormsR A t q →ₗ[R] logFormsR A t (p + q))
    (h₁ : ∀ (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A])),
      w₁ p q (logInclR t p ω) (logInclR t q η) =
        logInclR t (p + q) (exteriorPower.wedgeMul p q ω η))
    (h₂ : ∀ (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A])) (η : ⋀[R]^q (Ω[R⁄A])),
      w₂ p q (logInclR t p ω) (logInclR t q η) =
        logInclR t (p + q) (exteriorPower.wedgeMul p q ω η)) :
    w₁ = w₂ := by
  funext p q
  refine LinearMap.ext fun α ↦ LinearMap.ext fun β ↦ ?_
  have hreg : IsSMulRegular (logFormsR A t (p + q)) (t * t) :=
    (isSMulRegular_logFormsR ht (p + q)).mul (isSMulRegular_logFormsR ht (p + q))
  refine hreg ?_
  show (t * t) • (w₁ p q) α β = (t * t) • (w₂ p q) α β
  rw [smul_logWedge_eq w₁ h₁ p q α β, smul_logWedge_eq w₂ h₂ p q α β]

end Stacks.LogPoles

end
