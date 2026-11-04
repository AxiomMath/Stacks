module

public import StacksFrontier.RingTheory.DeRham.LogPolesHom
public import StacksFrontier.RingTheory.DeRham.LogPolesSequence

/-!
# The Leibniz formula for the differential of the forms with a logarithmic pole

Let `A → R` be a ring map, let `I ⊆ R` be an ideal and let `t ∈ I`. Stacks Tag 0FMW describes
the forms with a logarithmic pole along the divisor cut out by `I` as

`Ω^p_{X/S}(log Y) = Hom_R(I, 𝒦^p)`,

`𝒦^p` being the forms vanishing on the divisor; that description is
`Stacks.LogPoles.homIdealEquivLogFormsR`. This file supplies the formula by which the de Rham
differential acts in that description, and the sense in which the formula determines it.

For an `R`-linear map `φ` out of `I` the **Leibniz form** of `φ` is

`logLeibniz φ a b = a · d(φ b) − db ∧ φ a`.

Two facts about it are proved. First, it is `R`-bilinear — `Stacks.LogPoles.logLeibnizBilin` —
which is a statement about an arbitrary ideal and an arbitrary `φ` and uses nothing about log
poles. Second, on the diagonal at `t` it computes `t` times the differential of the log form
that `φ` presents: if `φ t` is the form `t · (ω + dlog t ∧ η)` of the pair model, then
`logLeibniz φ t t` is `t · (dω − dlog t ∧ dη)`.

## Main definitions

* `Stacks.LogPoles.logLeibniz`: the Leibniz form `a · d(φ b) − db ∧ φ a` of an `R`-linear map
  out of an ideal.
* `Stacks.LogPoles.logLeibnizBilin`: **the Leibniz form is `R`-bilinear.**

## Main results

* `Stacks.LogPoles.smul_logPairMap_logPairD`: **the Leibniz identity of the pair model**,
  `t · (t · dα) = t · d(t · α) − dt ∧ (t · α)` for `α` a log form `(ω, η)`.
* `Stacks.LogPoles.logLeibniz_diag`: the Leibniz form on the diagonal at `t` is `t` times the
  differential of the log form presented by `φ`.
* `Stacks.LogPoles.eq_logPairMap_logPairD_of_smul_eq`: and it determines that differential, `t`
  being a nonzerodivisor on the forms.
* `Stacks.LogPoles.existsUnique_smul_eq_leibniz`: for a form `v` vanishing on the divisor there
  is exactly one form `w` with `t · w = t · dv − dt ∧ v`.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
-/

@[expose] public noncomputable section

open KaehlerDifferential

universe u

namespace Stacks.LogPoles

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-! ### The Leibniz form of a linear map out of an ideal -/

/-- **The Leibniz form** `a · d(φ b) − db ∧ φ a` of an `R`-linear map `φ` from an ideal `I` into
the relative `p`-forms. On the diagonal at a generator `t` of `I` it is `t` times the de Rham
differential of the log form `t⁻¹ φ t`. -/
def logLeibniz {I : Ideal R} {p : ℕ} (φ : ↥I →ₗ[R] ⋀[R]^p (Ω[R⁄A])) (a b : ↥I) :
    ⋀[R]^(p + 1) (Ω[R⁄A]) :=
  (a : R) • deRhamDifferential (A := A) p (φ b) -
    exteriorPower.wedgeLeft (D A R (b : R)) p (φ a)

/-- The Leibniz form `logLeibniz φ a b` equals `a · d(φ b) − db ∧ φ a`. -/
theorem logLeibniz_eq_sub {I : Ideal R} {p : ℕ} (φ : ↥I →ₗ[R] ⋀[R]^p (Ω[R⁄A])) (a b : ↥I) :
    logLeibniz φ a b =
      (a : R) • deRhamDifferential (A := A) p (φ b) -
        exteriorPower.wedgeLeft (D A R (b : R)) p (φ a) := rfl

/-- A linear map out of an ideal satisfies `a · φ b = b · φ a`: both sides are `φ (a b)`. -/
theorem smul_apply_comm {I : Ideal R} {M : Type u} [AddCommGroup M] [Module R M]
    (φ : ↥I →ₗ[R] M) (a b : ↥I) : (a : R) • φ b = (b : R) • φ a := by
  have h : ((a : R) • b : ↥I) = ((b : R) • a : ↥I) := Subtype.ext (mul_comm _ _)
  rw [← map_smul, ← map_smul, h]

/-- **The Leibniz form is `R`-bilinear.** -/
def logLeibnizBilin {I : Ideal R} {p : ℕ} (φ : ↥I →ₗ[R] ⋀[R]^p (Ω[R⁄A])) :
    ↥I →ₗ[R] ↥I →ₗ[R] ⋀[R]^(p + 1) (Ω[R⁄A]) :=
  LinearMap.mk₂ R (logLeibniz φ)
    (fun a₁ a₂ b ↦ by
      simp only [logLeibniz, Submodule.coe_add, add_smul, map_add]
      abel)
    (fun c a b ↦ by
      simp only [logLeibniz, SetLike.val_smul, smul_eq_mul, map_smul, mul_smul, smul_sub])
    (fun a b₁ b₂ ↦ by
      simp only [logLeibniz, map_add, Submodule.coe_add, exteriorPower.wedgeLeft_add,
        LinearMap.add_apply, smul_add]
      abel)
    (fun c a b ↦ by
      have key : (a : R) • exteriorPower.wedgeLeft (D A R c) p (φ b) =
          (b : R) • exteriorPower.wedgeLeft (D A R c) p (φ a) := by
        simpa only [map_smul] using
          congrArg (exteriorPower.wedgeLeft (D A R c) p) (smul_apply_comm φ a b)
      simp only [logLeibniz, SetLike.val_smul, smul_eq_mul, map_smul, deRhamDifferential_smul,
        Derivation.leibniz, exteriorPower.wedgeLeft_add, exteriorPower.wedgeLeft_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_sub, smul_comm (a : R) c]
      rw [key]
      abel)

/-- The bilinear map `logLeibnizBilin φ` evaluated at `a` and `b` is `logLeibniz φ a b`. -/
@[simp]
theorem logLeibnizBilin_apply {I : Ideal R} {p : ℕ} (φ : ↥I →ₗ[R] ⋀[R]^p (Ω[R⁄A])) (a b : ↥I) :
    logLeibnizBilin φ a b = logLeibniz φ a b := rfl

/-! ### The Leibniz identity of the pair model -/

/-- Multiplication by `t` on the pair model, on an element: `(ω, η) ↦ t ω + dt ∧ η`. -/
theorem logPairMap_apply (A : Type u) [CommRing A] [Algebra A R] (t : R) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairMap A t p x = t • x.1 + exteriorPower.wedgeLeft (D A R t) p x.2 := rfl

/-- **The Leibniz identity of the pair model.** Writing `t · α` for `logPairMap`, the
multiplication `(ω, η) ↦ t ω + dt ∧ η` of a log form by `t`, and `dα` for the differential
`(ω, η) ↦ (dω, −dη)`, one has

`t · (t · dα) = t · d(t · α) − dt ∧ (t · α)`. -/
theorem smul_logPairMap_logPairD (A : Type u) [CommRing A] [Algebra A R] (t : R) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    t • logPairMap A t (p + 1) (logPairD A p x) =
      t • deRhamDifferential (A := A) (p + 1) (logPairMap A t p x) -
        exteriorPower.wedgeLeft (D A R t) (p + 1) (logPairMap A t p x) := by
  rw [logPairMap_apply, logPairMap_apply, logPairD_apply]
  simp only [map_add, map_neg, map_smul, deRhamDifferential_smul,
    deRhamDifferential_wedgeLeft_D, exteriorPower.wedgeLeft_wedgeLeft, smul_add, smul_neg,
    add_zero]
  abel

/-- **The Leibniz form computes the differential of the log forms.** If `φ` is an `R`-linear map
out of an ideal containing `t` whose value at `t` is the log form `α = (ω, η)` multiplied by `t`,
then the Leibniz form of `φ` on the diagonal at `t` is `t` times `dα`. -/
theorem logLeibniz_diag {I : Ideal R} {p : ℕ} (φ : ↥I →ₗ[R] ⋀[R]^(p + 1) (Ω[R⁄A])) (τ : ↥I)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) (hφ : φ τ = logPairMap A (τ : R) p x) :
    logLeibniz φ τ τ = (τ : R) • logPairMap A (τ : R) (p + 1) (logPairD A p x) := by
  rw [logLeibniz_eq_sub, hφ, smul_logPairMap_logPairD]

/-! ### The divisibility behind the existence of the differential -/

/-- An `R`-linear map carries `I · M` into `I · N`. -/
theorem map_mem_smul_top {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (I : Ideal R) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : f x ∈ I • (⊤ : Submodule R N) := by
  have h : Submodule.map f (I • (⊤ : Submodule R M)) ≤ I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h ⟨x, hx, rfl⟩

/-- **The divisibility that makes the differential of the log forms exist.** Wedging with `dt`
carries the forms vanishing on the divisor cut out by `t` into `t · Ω^{p+2}`: a form vanishing
on the divisor is `t ω + dt ∧ η`, and `dt ∧ (t ω + dt ∧ η) = t · (dt ∧ ω)`. -/
theorem wedgeLeft_D_mem_smul_top_of_mem_logSubmodule (t : R) (p : ℕ)
    {v : ⋀[R]^(p + 1) (Ω[R⁄A])} (hv : v ∈ logSubmodule A R (Ideal.span {t}) p) :
    exteriorPower.wedgeLeft (D A R t) (p + 1) v ∈
      Ideal.span {t} • (⊤ : Submodule R (⋀[R]^(p + 1 + 1) (Ω[R⁄A]))) := by
  rw [logSubmodule_span_singleton] at hv
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨η, rfl⟩ := hv₁
  rw [map_add, exteriorPower.wedgeLeft_wedgeLeft, zero_add]
  exact map_mem_smul_top _ _ hv₂

/-- **The Leibniz form determines the differential of the log forms.** If `t` is a
nonzerodivisor on the forms of degree `p + 2` then `t · dα` is the unique form `w` with
`t · w = t · d(t · α) − dt ∧ (t · α)`. -/
theorem eq_logPairMap_logPairD_of_smul_eq (A : Type u) [CommRing A] [Algebra A R] {t : R}
    {p : ℕ} (ht : IsSMulRegular (↥(⋀[R]^(p + 1 + 1) (Ω[R⁄A]))) t)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) (w : ⋀[R]^(p + 1 + 1) (Ω[R⁄A]))
    (hw : t • w = t • deRhamDifferential (A := A) (p + 1) (logPairMap A t p x) -
      exteriorPower.wedgeLeft (D A R t) (p + 1) (logPairMap A t p x)) :
    w = logPairMap A t (p + 1) (logPairD A p x) :=
  ht (hw.trans (smul_logPairMap_logPairD A t p x).symm)

/-- The differential of a log form, multiplied by `t`, again vanishes on the divisor. -/
theorem logPairMap_logPairD_mem_ker (A : Type u) [CommRing A] [Algebra A R] (t : R) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairMap A t (p + 1) (logPairD A p x) ∈
      LinearMap.ker (KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t})
        (p + 1 + 1)) :=
  (range_logPairMap (A := A) t (p + 1)).le ⟨_, rfl⟩

/-- **The differential of the log forms exists and is unique, said without the pair model.** Let
`v` be a relative `(p+1)`-form vanishing on the divisor cut out by `t`. Then there is exactly one
form `w` with

`t · w = t · dv − dt ∧ v`,

namely `t` times the differential of the log form `t⁻¹ v`; and `w` again vanishes on the divisor
by `Stacks.LogPoles.logPairMap_logPairD_mem_ker`. -/
theorem existsUnique_smul_eq_leibniz (A : Type u) [CommRing A] [Algebra A R] {t : R} {p : ℕ}
    (ht : IsSMulRegular (↥(⋀[R]^(p + 1 + 1) (Ω[R⁄A]))) t) {v : ⋀[R]^(p + 1) (Ω[R⁄A])}
    (hv : v ∈ LinearMap.ker (KaehlerDifferential.mapExteriorPower A R
      (R ⧸ Ideal.span {t}) (p + 1))) :
    ∃! w : ⋀[R]^(p + 1 + 1) (Ω[R⁄A]),
      t • w = t • deRhamDifferential (A := A) (p + 1) v -
        exteriorPower.wedgeLeft (D A R t) (p + 1) v := by
  obtain ⟨x, rfl⟩ := (range_logPairMap (A := A) t p).ge hv
  exact ⟨logPairMap A t (p + 1) (logPairD A p x), smul_logPairMap_logPairD A t p x,
    fun w hw ↦ eq_logPairMap_logPairD_of_smul_eq A ht x w hw⟩

end Stacks.LogPoles

end
