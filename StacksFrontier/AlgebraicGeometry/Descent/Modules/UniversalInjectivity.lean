module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Defs
public import StacksFrontier.RingTheory.UniversallyExact

/-!
# Universal injectivity of a ring map tests every module universe

Universal injectivity of a ring map `R → A` is defined by injectivity of `id ⊗ f` on test
modules drawn from the universe of `R`. The argument below removes that restriction: once
`R ⊗ Q → A ⊗ Q` is injective for every test module in `R`'s universe, it is injective for
every `R`-module whatsoever.

## Main results

* `Algebra.rTensor_injective_of_universallyInjective`: a universally injective ring map stays
  injective after tensoring with an `R`-module in an arbitrary universe.

## Implementation notes

The universe restriction is lifted through the characterisation of universal exactness by
finitely presented test modules. A finitely presented module over `R` is small relative to
`R`'s universe, so the hypothesis already covers the finitely presented test modules of any
universe; the characterisation then upgrades that to all test modules. Both ends are
transported along `ULift.moduleEquiv`, since the source and target of the ring map live in
different universes while the characterisation needs them in one.

## References

* [Stacks Project, Tag 058K](https://stacks.math.columbia.edu/tag/058K)
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- Transporting `f ⊗ id_P` along the `ULift` equivalences and an equivalence `P ≃ₗ[R] P'`
gives `f ⊗ id_P'`. -/
private theorem congr_moduleEquiv_rTensor_apply.{t, w'}
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    {P : Type w} {P' : Type w'} [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (e : P ≃ₗ[R] P') (z : ULift.{t} R ⊗[R] P) :
    _root_.TensorProduct.congr (ULift.moduleEquiv.{u, v, t} (R := R) (M := A)) e
        (LinearMap.rTensor P
          ((ULift.moduleEquiv.{u, v, t} (R := R) (M := A)).symm.toLinearMap.comp
            ((Algebra.linearMap R A).comp
              (ULift.moduleEquiv.{u, u, t} (R := R) (M := R)).toLinearMap)) z) =
      LinearMap.rTensor P' (Algebra.linearMap R A)
        (_root_.TensorProduct.congr (ULift.moduleEquiv.{u, u, t} (R := R) (M := R)) e z) := by
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-- A universally injective ring map `R → A` has `f ⊗ id_Q` injective for every `R`-module
`Q`, in any universe, not only for test modules in the universe of `R`. -/
theorem Algebra.rTensor_injective_of_universallyInjective
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (Q : Type w) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((Algebra.linearMap R A).rTensor Q) := by
  let eR : ULift.{max (max u v) w} R ≃ₗ[R] R :=
    ULift.moduleEquiv.{u, u, max (max u v) w} (R := R) (M := R)
  let eA : ULift.{max (max u v) w} A ≃ₗ[R] A :=
    ULift.moduleEquiv.{u, v, max (max u v) w} (R := R) (M := A)
  let f : R →ₗ[R] A := Algebra.linearMap R A
  let f' : ULift.{max (max u v) w} R →ₗ[R] ULift.{max (max u v) w} A :=
    eA.symm.toLinearMap.comp (f.comp eR.toLinearMap)
  let g : ULift.{max (max u v) w} A →ₗ[R]
      (ULift.{max (max u v) w} A ⧸ LinearMap.range f') :=
    (LinearMap.range f').mkQ
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : (LinearMap.rTensor R f) (x ⊗ₜ[R] (1 : R)) =
        (LinearMap.rTensor R f) (y ⊗ₜ[R] (1 : R)) := by simp [hxy]
    simpa using congrArg (_root_.TensorProduct.lid R R) (h R hxy')
  have hf' : Function.Injective f' := fun x y hxy =>
    eR.injective (hf (eA.symm.injective hxy))
  have hfg : Function.Exact f' g := by
    rw [LinearMap.exact_iff]
    simp [g]
  have hg : Function.Surjective g := Submodule.mkQ_surjective _
  have htfae := Function.Exact.universallyExact_tfae (R := R) hfg hf' hg
  have h₂ : ∀ (Q' : Type (max (max u v) w)) [AddCommGroup Q'] [Module R Q']
      [Module.FinitePresentation R Q'],
      Function.Injective (f'.rTensor Q') ∧ Function.Exact (f'.rTensor Q') (g.rTensor Q') ∧
        Function.Surjective (g.rTensor Q') := by
    intro Q' _ _ _
    refine ⟨?_, rTensor_exact Q' hfg hg, LinearMap.rTensor_surjective Q' hg⟩
    obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (R := R) (M := Q')
    have hsmall : Small.{u} Q' := small_of_surjective (e.symm.surjective.comp K.mkQ_surjective)
    let eQ : Shrink.{u} Q' ≃ₗ[R] Q' := Shrink.linearEquiv R Q'
    let d₀ : (ULift.{max (max u v) w} R ⊗[R] Q') ≃ₗ[R] (R ⊗[R] Shrink.{u} Q') :=
      _root_.TensorProduct.congr eR eQ.symm
    let d₁ : (ULift.{max (max u v) w} A ⊗[R] Q') ≃ₗ[R] (A ⊗[R] Shrink.{u} Q') :=
      _root_.TensorProduct.congr eA eQ.symm
    have key := congr_moduleEquiv_rTensor_apply R A eQ.symm
    exact fun x y hxy => d₀.injective (h (Shrink.{u} Q') (by rw [← key x, ← key y, hxy]))
  have hall : ∀ (Q' : Type (max (max u v) w)) [AddCommGroup Q'] [Module R Q'],
      Function.Injective (f'.rTensor Q') := (htfae.out 2 1).mp h₂
  let eQ : ULift.{max (max u v) w} Q ≃ₗ[R] Q :=
    ULift.moduleEquiv.{u, w, max (max u v) w} (R := R) (M := Q)
  let d₀ : (ULift.{max (max u v) w} R ⊗[R] ULift.{max (max u v) w} Q) ≃ₗ[R] (R ⊗[R] Q) :=
    _root_.TensorProduct.congr eR eQ
  let d₁ : (ULift.{max (max u v) w} A ⊗[R] ULift.{max (max u v) w} Q) ≃ₗ[R] (A ⊗[R] Q) :=
    _root_.TensorProduct.congr eA eQ
  have key := congr_moduleEquiv_rTensor_apply R A eQ
  intro x y hxy
  obtain ⟨x', rfl⟩ := d₀.surjective x
  obtain ⟨y', rfl⟩ := d₀.surjective y
  refine congrArg d₀ (hall _ (d₁.injective ?_))
  rw [key, key, hxy]

/-- A universally injective ring map `R → A` has `m ↦ 1 ⊗ m` injective on every `R`-module,
in any universe. -/
theorem Algebra.mk_one_injective_of_universallyInjective
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (h : Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{u}
      (Algebra.linearMap R A))
    (Q : Type w) [AddCommGroup Q] [Module R Q] :
    Function.Injective (_root_.TensorProduct.mk R A Q (1 : A)) := by
  have hfactor : (_root_.TensorProduct.mk R A Q (1 : A)) =
      (LinearMap.rTensor Q (Algebra.linearMap R A)).comp
        (_root_.TensorProduct.lid R Q).symm.toLinearMap := by
    ext q
    simp [LinearMap.rTensor_tmul, _root_.TensorProduct.lid_symm_apply]
  rw [hfactor]
  exact (Algebra.rTensor_injective_of_universallyInjective R A h Q).comp
    (_root_.TensorProduct.lid R Q).symm.injective

end
