module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LocalEquationIndependence
public import StacksFrontier.LinearAlgebra.ExteriorPower.ReduceMod
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# The kernel of the restriction of differential forms to a closed subscheme

Let `A → R` be a ring map and let `I ⊆ R` be an ideal, cutting out the closed subscheme
`Spec (R ⧸ I) ⊆ Spec R`. Restriction of forms along that closed immersion is

`⋀^n Ω[R⁄A] → ⋀^n_{R ⧸ I} Ω[R ⧸ I⁄A]`,

the map `KaehlerDifferential.mapExteriorPower`. This file shows that it is surjective and
computes its kernel: in degree `n + 1` the kernel is `Stacks.LogPoles.logSubmodule`, spanned by
the forms `dt ∧ η` for `t ∈ I` together with the `I`-multiples of all forms, and in degree zero
it is `I` itself. The ideal `I` is arbitrary.

This is the step "if a form `η` over `U` restricts to zero on `Y ∩ U`, then
`η = df ∧ η' + f η''`" in the proof of Stacks Tag 0FMW.

## Main definitions

* `Stacks.LogPoles.reduceForms`: reduction of forms modulo `I`, that is the base change of
  `⋀^n Ω[R⁄A]` along `R → R ⧸ I`.

## Main results

* `Stacks.LogPoles.ker_reduceForms`: the kernel of reduction is `I • ⊤`.
* `Stacks.LogPoles.mapExteriorPower_eq_map_reduceForms`: restriction factors as reduction
  followed by the functorial map of the conormal surjection.
* `Stacks.LogPoles.surjective_mapExteriorPower_quotient`: **restriction is surjective**, so every
  form on the closed subscheme is a restriction.
* `Stacks.LogPoles.ker_mapExteriorPower_quotient_succ`: **the kernel of restriction** in positive
  degree is the logarithmic submodule of the ideal.
* `Stacks.LogPoles.ker_mapExteriorPower_quotient_zero`: the kernel in degree zero is `I`.
* `Stacks.LogPoles.exists_smul_wedgeLeft_D_of_mapExteriorPower_eq_zero`: for a principal ideal
  `(t)`, if `η` restricts to zero then `dt ∧ η` is `t` times a form.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), whose proof performs
  this computation
* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO), the right exactness of
  exterior powers used here
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Stacks.LogPoles

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-- **Reduction of forms modulo an ideal.** The base change of `⋀^n Ω[R⁄A]` along `R → R ⧸ I`,
landing in the `n`-th exterior power over `R ⧸ I` of the reduction of the differentials. -/
def reduceForms (I : Ideal R) (n : ℕ) :
    ⋀[R]^n (Ω[R⁄A]) →ₗ[R] ⋀[R ⧸ I]^n ((R ⧸ I) ⊗[R] Ω[R⁄A]) :=
  ExteriorAlgebra.exteriorPowerBaseChangeMap R (R ⧸ I) Ω[R⁄A] n

/-- Reduction of forms modulo `I` agrees with `exteriorPower.quotSmulTopEquiv` applied to the class
of a form in the quotient by `I • ⊤`. -/
theorem reduceForms_apply (I : Ideal R) (n : ℕ) (x : ⋀[R]^n (Ω[R⁄A])) :
    reduceForms (A := A) I n x =
      exteriorPower.quotSmulTopEquiv I n (Submodule.Quotient.mk x) := by
  have h1 : (TensorProduct.quotTensorEquivQuotSMul (⋀[R]^n (Ω[R⁄A])) I).symm
      (Submodule.Quotient.mk x) = (1 : R ⧸ I) ⊗ₜ[R] x :=
    (LinearEquiv.symm_apply_eq _).mpr
      (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I x).symm
  rw [exteriorPower.quotSmulTopEquiv, LinearEquiv.trans_apply, h1,
    LinearEquiv.restrictScalars_apply, ExteriorAlgebra.exteriorPowerBaseChange_tmul, one_smul]
  rfl

/-- Reduction of forms modulo an ideal is surjective. -/
theorem surjective_reduceForms (I : Ideal R) (n : ℕ) :
    Function.Surjective (reduceForms (A := A) I n) := by
  intro y
  obtain ⟨z, hz⟩ := (exteriorPower.quotSmulTopEquiv (M := Ω[R⁄A]) I n).surjective y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨x, by rw [reduceForms_apply, hz]⟩

/-- The kernel of reduction of forms modulo `I` is `I • ⊤`. -/
theorem ker_reduceForms (I : Ideal R) (n : ℕ) :
    LinearMap.ker (reduceForms (A := A) I n) =
      I • (⊤ : Submodule R (⋀[R]^n (Ω[R⁄A]))) := by
  refine SetLike.ext fun x ↦ ?_
  rw [LinearMap.mem_ker, reduceForms_apply, LinearEquiv.map_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero]

/-- Reduction of forms modulo `I` carries `e ∧ ξ` to `(1 ⊗ e) ∧ ξ̄`, where `ξ̄` is the reduction
of `ξ`. -/
theorem reduceForms_wedgeLeft (I : Ideal R) (n : ℕ) (e : Ω[R⁄A]) (ξ : ⋀[R]^n (Ω[R⁄A])) :
    reduceForms (A := A) I (n + 1) (exteriorPower.wedgeLeft e n ξ) =
      exteriorPower.wedgeLeft ((1 : R ⧸ I) ⊗ₜ[R] e) n (reduceForms (A := A) I n ξ) := by
  have hmap : (reduceForms (A := A) I (n + 1)).comp (exteriorPower.wedgeLeft e n) =
      ((exteriorPower.wedgeLeft ((1 : R ⧸ I) ⊗ₜ[R] e) n).restrictScalars R).comp
        (reduceForms (A := A) I n) := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span R n (Ω[R⁄A])) ?_
    rintro x ⟨v, rfl⟩
    have hcons : (fun i : Fin (n + 1) ↦
          (1 : R ⧸ I) ⊗ₜ[R] (Fin.cons e v : Fin (n + 1) → Ω[R⁄A]) i) =
        (Fin.cons ((1 : R ⧸ I) ⊗ₜ[R] e)
          (fun i ↦ (1 : R ⧸ I) ⊗ₜ[R] v i) : Fin (n + 1) → (R ⧸ I) ⊗[R] Ω[R⁄A]) :=
      funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
    simp only [LinearMap.coe_comp, Function.comp_apply, exteriorPower.wedgeLeft_ιMulti,
      reduceForms, ExteriorAlgebra.exteriorPowerBaseChangeMap_ιMulti,
      LinearMap.coe_restrictScalars, hcons]
  exact congrArg (fun f : ⋀[R]^n (Ω[R⁄A]) →ₗ[R] _ ↦ f ξ) hmap

/-- Restriction of forms to the closed subscheme factors as reduction modulo `I` followed by the
functorial map of the conormal surjection `(R ⧸ I) ⊗ Ω[R⁄A] → Ω[R ⧸ I⁄A]`. -/
theorem mapExteriorPower_eq_map_reduceForms (I : Ideal R) (n : ℕ) :
    KaehlerDifferential.mapExteriorPower A R (R ⧸ I) n =
      ((exteriorPower.map n
          (KaehlerDifferential.mapBaseChange A R (R ⧸ I))).restrictScalars R).comp
        (reduceForms (A := A) I n) := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span R n (Ω[R⁄A])) ?_
  rintro x ⟨v, rfl⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    KaehlerDifferential.mapExteriorPower_ιMulti, reduceForms,
    ExteriorAlgebra.exteriorPowerBaseChangeMap_ιMulti, exteriorPower.map_apply_ιMulti]
  refine congrArg _ (funext fun i ↦ ?_)
  rw [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]

/-- **Restriction of forms to a closed subscheme is surjective**: every form on `Spec (R ⧸ I)`
is the restriction of a form on `Spec R`. -/
theorem surjective_mapExteriorPower_quotient (I : Ideal R) (n : ℕ) :
    Function.Surjective (KaehlerDifferential.mapExteriorPower A R (R ⧸ I) n) := by
  rw [mapExteriorPower_eq_map_reduceForms]
  intro y
  obtain ⟨z, hz⟩ := exteriorPower.map_surjective (n := n)
    (KaehlerDifferential.mapBaseChange_surjective A R (R ⧸ I)
      (Ideal.Quotient.mk_surjective)) y
  obtain ⟨x, rfl⟩ := surjective_reduceForms (A := A) I n z
  exact ⟨x, hz⟩

/-- The image of `logSubmodule A R I k` under reduction modulo `I` is the kernel of the map
induced on `(k + 1)`-st exterior powers by `(R ⧸ I) ⊗ Ω[R⁄A] → Ω[R ⧸ I⁄A]`. -/
theorem map_reduceForms_logSubmodule (I : Ideal R) (k : ℕ) :
    Submodule.map (reduceForms (A := A) I (k + 1)) (logSubmodule A R I k) =
      Submodule.restrictScalars R
        (LinearMap.ker (exteriorPower.map (k + 1)
          (KaehlerDifferential.mapBaseChange A R (R ⧸ I)))) := by
  set f := KaehlerDifferential.mapBaseChange A R (R ⧸ I) with hf
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr (sup_le ?_ ?_)) ?_
  · refine Submodule.span_le.mpr ?_
    rintro ω ⟨x, hx, η, rfl⟩
    have hfx : f ((1 : R ⧸ I) ⊗ₜ[R] KaehlerDifferential.D A R x) = 0 := by
      rw [hf, KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
        show (algebraMap R (R ⧸ I)) x = 0 from (Ideal.Quotient.eq_zero_iff_mem).mpr hx, map_zero]
    refine SetLike.mem_coe.mpr (Submodule.mem_comap.mpr ?_)
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, reduceForms_wedgeLeft,
      show exteriorPower.map (k + 1) f
          (exteriorPower.wedgeLeft ((1 : R ⧸ I) ⊗ₜ[R] KaehlerDifferential.D A R x) k
            (reduceForms (A := A) I k η)) =
        exteriorPower.wedgeLeft (f ((1 : R ⧸ I) ⊗ₜ[R] KaehlerDifferential.D A R x)) k
          (exteriorPower.map k f (reduceForms (A := A) I k η)) from
      DFunLike.congr_fun (exteriorPower.map_comp_wedgeLeft' f _ k) _, hfx,
      exteriorPower.wedgeLeft_zero, LinearMap.zero_apply]
  · intro z hz
    have h0 : reduceForms (A := A) I (k + 1) z = 0 := by
      rw [← LinearMap.mem_ker, ker_reduceForms]; exact hz
    refine Submodule.mem_comap.mpr ?_
    rw [h0]
    exact Submodule.zero_mem _
  · intro z hz
    have hker : z ∈ LinearMap.range
        (ExtPow.beta (R := R ⧸ I) (M₁ := (R ⧸ I) ⊗[R] Ω[R⁄A]) (M₂ := ↥(LinearMap.ker f)) k
          (LinearMap.ker f).subtype) := by
      rw [(exterior_power_presentation
        (M₁ := (R ⧸ I) ⊗[R] Ω[R⁄A]) (M₂ := ↥(LinearMap.ker f))
        (LinearMap.ker f).subtype f
        (KaehlerDifferential.mapBaseChange_surjective A R (R ⧸ I)
          (Ideal.Quotient.mk_surjective)) (Submodule.range_subtype _) k).2]
      exact hz
    obtain ⟨w, rfl⟩ := hker
    clear hz
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul u ξ =>
        obtain ⟨c, hc⟩ : ∃ c, KaehlerDifferential.kerCotangentToTensor A R (R ⧸ I) c =
            (u : (R ⧸ I) ⊗[R] Ω[R⁄A]) :=
          (KaehlerDifferential.range_kerCotangentToTensor A R (R ⧸ I)
            (Ideal.Quotient.mk_surjective)).ge
            (show (u : (R ⧸ I) ⊗[R] Ω[R⁄A]) ∈
              Submodule.restrictScalars R (LinearMap.ker f) from u.2)
        obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ c
        obtain ⟨η, rfl⟩ := surjective_reduceForms (A := A) I k ξ
        have hxI : (x : R) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp <| by
          rw [← Ideal.Quotient.algebraMap_eq]
          exact RingHom.mem_ker.mp x.2
        refine ⟨exteriorPower.wedgeLeft (KaehlerDifferential.D A R (x : R)) k η,
          Submodule.mem_sup_left (Submodule.subset_span ⟨(x : R), hxI, η, rfl⟩), ?_⟩
        rw [reduceForms_wedgeLeft]
        refine Subtype.ext ?_
        rw [exteriorPower.coe_wedgeLeft, ExtPow.beta_tmul,
          show ((LinearMap.ker f).subtype u : (R ⧸ I) ⊗[R] Ω[R⁄A]) =
              (1 : R ⧸ I) ⊗ₜ[R] KaehlerDifferential.D A R (x : R) by
            rw [Submodule.subtype_apply, ← hc,
              KaehlerDifferential.kerCotangentToTensor_toCotangent]]

/-- **The kernel of the restriction of forms to a closed subscheme**, in positive degree: a form
restricts to zero on `Spec (R ⧸ I)` exactly when it is a sum of a form with a factor `dx` for
some `x ∈ I` and a form with coefficients in `I`. -/
theorem ker_mapExteriorPower_quotient_succ (I : Ideal R) (k : ℕ) :
    LinearMap.ker (KaehlerDifferential.mapExteriorPower A R (R ⧸ I) (k + 1)) =
      logSubmodule A R I k := by
  rw [mapExteriorPower_eq_map_reduceForms, LinearMap.ker_comp, LinearMap.ker_restrictScalars,
    ← map_reduceForms_logSubmodule (A := A) I k, Submodule.comap_map_eq, ker_reduceForms]
  exact sup_eq_left.mpr le_sup_right

/-- The kernel of the restriction of functions to a closed subscheme, in degree zero. -/
theorem ker_mapExteriorPower_quotient_zero (I : Ideal R) :
    LinearMap.ker (KaehlerDifferential.mapExteriorPower A R (R ⧸ I) 0) =
      I • (⊤ : Submodule R (⋀[R]^0 (Ω[R⁄A]))) := by
  have hinj : Function.Injective
      (exteriorPower.map 0 (KaehlerDifferential.mapBaseChange A R (R ⧸ I))) := by
    refine Function.Injective.of_comp (f := exteriorPower.zeroEquiv (R ⧸ I) Ω[R ⧸ I⁄A]) ?_
    rw [show (exteriorPower.zeroEquiv (R ⧸ I) Ω[R ⧸ I⁄A]) ∘
        (exteriorPower.map 0 (KaehlerDifferential.mapBaseChange A R (R ⧸ I))) =
        ((exteriorPower.zeroEquiv (R ⧸ I) Ω[R ⧸ I⁄A] : _ →ₗ[R ⧸ I] _).comp
          (exteriorPower.map 0 (KaehlerDifferential.mapBaseChange A R (R ⧸ I)))) from rfl,
      exteriorPower.zeroEquiv_naturality]
    exact (exteriorPower.zeroEquiv (R ⧸ I) ((R ⧸ I) ⊗[R] Ω[R⁄A])).injective
  rw [mapExteriorPower_eq_map_reduceForms, LinearMap.ker_comp, LinearMap.ker_restrictScalars,
    LinearMap.ker_eq_bot.mpr hinj, Submodule.restrictScalars_bot, Submodule.comap_bot,
    ker_reduceForms]

section Principal

/-- Every element of `(t) • ⊤` in an `R`-module is of the form `t • y`. -/
theorem exists_smul_of_mem_span_singleton_smul_top {N : Type u} [AddCommGroup N] [Module R N]
    (t : R) {x : N} (hx : x ∈ Ideal.span {t} • (⊤ : Submodule R N)) : ∃ y, x = t • y := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha n _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨c • n, by rw [smul_smul, mul_comm]⟩
  · rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, by rw [smul_add]⟩

/-- **A form restricting to zero on the divisor has `dt`-wedge divisible by `t`.**  If `η`
restricts to zero on `Spec (R ⧸ (t))` then `dt ∧ η` is `t` times a form. -/
theorem exists_smul_wedgeLeft_D_of_mapExteriorPower_eq_zero (t : R) (p : ℕ)
    {η : ⋀[R]^p (Ω[R⁄A])}
    (h : KaehlerDifferential.mapExteriorPower A R (R ⧸ Ideal.span {t}) p η = 0) :
    ∃ y : ⋀[R]^(p + 1) (Ω[R⁄A]),
      exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p η = t • y := by
  cases p with
  | zero =>
      rw [← LinearMap.mem_ker, ker_mapExteriorPower_quotient_zero] at h
      obtain ⟨y, rfl⟩ := exists_smul_of_mem_span_singleton_smul_top t h
      exact ⟨exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) 0 y, by rw [map_smul]⟩
  | succ q =>
      rw [← LinearMap.mem_ker, ker_mapExteriorPower_quotient_succ,
        logSubmodule_span_singleton] at h
      obtain ⟨a, ⟨ζ, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp h
      obtain ⟨y, rfl⟩ := exists_smul_of_mem_span_singleton_smul_top t hb
      refine ⟨exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) (q + 1) y, ?_⟩
      rw [map_add, map_smul, exteriorPower.wedgeLeft_wedgeLeft, zero_add]

end Principal

end Stacks.LogPoles

end
