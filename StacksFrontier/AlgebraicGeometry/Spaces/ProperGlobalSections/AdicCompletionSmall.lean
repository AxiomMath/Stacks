module

public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.Algebra.Module.Shrink

/-!
# Exactness of adic completion for finite modules in a larger universe

Mathlib's `AdicCompletion.map_injective` and `AdicCompletion.map_exact` are stated for modules in
the universe of the ring.  A finite module over a ring in universe `u` is `u`-small, so both
statements transport to finite modules in any universe through `Shrink`.  This is used for the
global sections of coherent modules on an algebraic space, which are finite over the base ring but
live one universe higher.
-/

@[expose] public section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  {M N P : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

omit [IsNoetherianRing R] in
/-- Transport of `AdicCompletion.map` along linear equivalences of the source and the target. -/
theorem map_eq_congr_comp {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N']
    [Module R N'] (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) (f : M →ₗ[R] N) :
    map I f = (congr I eN).toLinearMap ∘ₗ map I (eN.symm.toLinearMap ∘ₗ f ∘ₗ eM.toLinearMap) ∘ₗ
      (congr I eM).symm.toLinearMap := by
  change map I f = map I eN.toLinearMap ∘ₗ map I (eN.symm.toLinearMap ∘ₗ f ∘ₗ eM.toLinearMap) ∘ₗ
    map I eM.symm.toLinearMap
  rw [map_comp, map_comp]
  congr 1
  ext y
  simp

/-- Adic completion of an injection of finite modules over a Noetherian ring is injective, in any
universe. -/
theorem map_injective_of_finite [Module.Finite R N] {f : M →ₗ[R] N}
    (hf : Function.Injective f) : Function.Injective (map I f) := by
  have : Module.Finite R M := Module.Finite.of_injective f hf
  have : Small.{u} M := Module.Finite.small.{u} R M
  have : Small.{u} N := Module.Finite.small.{u} R N
  let eM := Shrink.linearEquiv.{u} R M
  let eN := Shrink.linearEquiv.{u} R N
  have hf' : Function.Injective (eN.symm.toLinearMap ∘ₗ f ∘ₗ eM.toLinearMap) :=
    eN.symm.injective.comp (hf.comp eM.injective)
  rw [map_eq_congr_comp I eM eN f]
  exact (congr I eN).injective.comp ((map_injective I hf').comp (congr I eM).symm.injective)

/-- Adic completion is exact on short exact sequences of finite modules over a Noetherian ring,
in any universe. -/
theorem map_exact_of_finite [Module.Finite R N] {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (map I f) (map I g) := by
  have : Module.Finite R M := Module.Finite.of_injective f hf
  have : Module.Finite R P := Module.Finite.of_surjective g hg
  have : Small.{u} M := Module.Finite.small.{u} R M
  have : Small.{u} N := Module.Finite.small.{u} R N
  have : Small.{u} P := Module.Finite.small.{u} R P
  let eM := Shrink.linearEquiv.{u} R M
  let eN := Shrink.linearEquiv.{u} R N
  let eP := Shrink.linearEquiv.{u} R P
  let f' := eN.symm.toLinearMap ∘ₗ f ∘ₗ eM.toLinearMap
  let g' := eP.symm.toLinearMap ∘ₗ g ∘ₗ eN.toLinearMap
  have hf' : Function.Injective f' := eN.symm.injective.comp (hf.comp eM.injective)
  have hg' : Function.Surjective g' := eP.symm.surjective.comp (hg.comp eN.surjective)
  have hfg' : Function.Exact f' g' := by
    refine Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := eM.symm) (e₂ := eN.symm)
      (e₃ := eP.symm) ?_ ?_ hfg
    · ext x; simp [f']
    · ext x; simp [g']
  have H := map_exact (I := I) hf' hfg' hg'
  rw [map_eq_congr_comp I eM eN f, map_eq_congr_comp I eN eP g,
    LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.conj_exact_iff_exact,
    LinearEquiv.precomp_exact_iff_exact]
  exact H

/-- Adic completion of a left exact sequence of finite modules over a Noetherian ring is exact at
the middle term, in any universe. -/
theorem map_exact_of_finite_of_injective [Module.Finite R N] [Module.Finite R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact (map I f) (map I g) := by
  have hsub : Function.Injective (LinearMap.range g).subtype := Subtype.val_injective
  have hfg' : Function.Exact f g.rangeRestrict := by
    rw [← hsub.comp_exact_iff_exact]
    exact hfg
  have H := map_exact_of_finite I hf hfg' g.surjective_rangeRestrict
  have hg : map I g = map I (LinearMap.range g).subtype ∘ₗ map I g.rangeRestrict := by
    rw [map_comp]
    rfl
  rw [hg, (map_injective_of_finite I hsub).comp_exact_iff_exact]
  exact H

end AdicCompletion
