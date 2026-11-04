module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Reflexivity transfers along an equivalence of rings

Mathlib's `Module.equiv` transports `Module.IsReflexive` along a linear equivalence of modules
over a *fixed* ring.  This file supplies the version for two different rings: if `σ : R ≃+* S`
is an equivalence of rings and `e : M ≃+ N` an additive equivalence satisfying
`e (r • m) = σ r • e m`, then `M` is a reflexive `R`-module if and only if `N` is a reflexive
`S`-module.

## Main results

* `Module.IsReflexive.of_ringEquiv`: reflexivity transfers along a semilinear additive
  equivalence over an equivalence of rings.

## Implementation notes

The hypothesis is phrased as an `AddEquiv` together with the scalar compatibility rather than as
a semilinear equivalence `M ≃ₛₗ[(σ : R →+* S)] N`, because the latter's type mentions the
`RingHomInvPair` instances that `σ` supplies: a caller would have to put them in scope before it
could even write the statement.  They are introduced inside the proof instead, where
`LinearEquiv.arrowCongr` dualizes the semilinear equivalence twice and the two evaluation maps
are identified by `funext`.
-/

@[expose] public section

namespace Module.IsReflexive

/-- **Reflexivity transfers along an equivalence of rings.**  Let `σ : R ≃+* S` be an
equivalence of rings, `M` an `R`-module and `N` an `S`-module, and let `e : M ≃+ N` be an
additive equivalence with `e (r • m) = σ r • e m`.  If `M` is a reflexive `R`-module then `N` is
a reflexive `S`-module.

Applying the statement to `σ.symm` and `e.symm` gives the converse, so this is an equivalence. -/
public theorem of_ringEquiv {R S M N : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    (σ : R ≃+* S) (e : M ≃+ N) (he : ∀ (r : R) (m : M), e (r • m) = σ r • e m)
    [Module.IsReflexive R M] : Module.IsReflexive S N := by
  let _ := RingHomInvPair.of_ringEquiv σ
  let _ := RingHomInvPair.of_ringEquiv_symm σ
  let e' : M ≃ₛₗ[(σ : R →+* S)] N := { __ := e, map_smul' := he }
  let d : Module.Dual R M ≃ₛₗ[(σ : R →+* S)] Module.Dual S N :=
    LinearEquiv.arrowCongr e' σ.toSemilinearEquiv
  let dd : Module.Dual R (Module.Dual R M) ≃ₛₗ[(σ : R →+* S)]
      Module.Dual S (Module.Dual S N) :=
    LinearEquiv.arrowCongr d σ.toSemilinearEquiv
  have h : ⇑(Module.Dual.eval S N) = dd ∘ Module.Dual.eval R M ∘ e'.symm := by
    funext n
    ext l
    simp [dd, d, LinearEquiv.arrowCongr_apply, LinearEquiv.arrowCongr_symm_apply]
  constructor
  rw [h]
  exact dd.bijective.comp ((Module.bijective_dual_eval R M).comp e'.symm.bijective)

end Module.IsReflexive

end
