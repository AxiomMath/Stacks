module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change bijectivity from a pushout square of commutative rings

A pushout square of commutative rings

```
R ──α──▶ M
│ρ        │γ
▼         ▼
S ──β──▶ T
```

identifies `T` with `S ⊗_R M`.  This file states that identification for module structures
that are given *independently* of the ring maps but agree with them, which is the form in which
it is consumed on the sections of sheaves of modules over étale charts, where the module
structures are restrictions of scalars defined elsewhere.

## Main results

* `RingHom.bijective_liftBaseChange_of_isPushout`: if the square is a pushout in
  `CommRingCat` then the `S`-linear extension `S ⊗_R M ⟶ T` of `γ` is bijective.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-- **A pushout square of commutative rings is a base change, for any compatible module
structures.**  Let `α : R → M`, `ρ : R → S`, `γ : M → T`, `β : S → T` form a pushout square in
`CommRingCat`.  Equip `S` with an `R`-algebra structure whose structure map is `ρ`, `M` with an
`R`-module structure acting through `α`, and `T` with an `S`-module structure acting through `β`
and a compatible `R`-module structure.  Then for an `R`-linear map `τ : M → T` with underlying
function `γ`, the `S`-linear extension `S ⊗_R M ⟶ T` of `τ` is bijective.

The module structures are hypotheses rather than the ones the ring maps induce, so that the
statement applies to restrictions of scalars defined elsewhere; they are identified with the
induced ones and `CommRingCat.isPushout_iff_isPushout` does the rest. -/
theorem RingHom.bijective_liftBaseChange_of_isPushout {R S M T : Type u} [CommRing R]
    [CommRing S] [CommRing M] [CommRing T] (ρ : R →+* S) (α : R →+* M) (β : S →+* T)
    (γ : M →+* T)
    (hsq : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom ρ) (CommRingCat.ofHom γ)
      (CommRingCat.ofHom β))
    [iRS : Algebra R S] [iRM : Module R M] [iST : Module S T] [iRT : Module R T]
    [hRST : IsScalarTower R S T] (hRS : algebraMap R S = ρ)
    (hRM : ∀ (r : R) (m : M), r • m = α r * m)
    (hST : ∀ (s : S) (t : T), s • t = β s * t) (τ : M →ₗ[R] T) (hτ : ∀ m, τ m = γ m) :
    Function.Bijective (τ.liftBaseChange S) := by
  have hRT : ∀ (r : R) (t : T), r • t = β (ρ r) * t := fun r t => by
    rw [← hRS, ← hST, algebraMap_smul]
  obtain rfl : iRS = ρ.toAlgebra := Algebra.algebra_ext _ _ fun r => congrArg (· r) hRS
  obtain rfl : iRM = (α.toAlgebra).toModule := Module.ext (funext₂ hRM)
  obtain rfl : iST = (β.toAlgebra).toModule := Module.ext (funext₂ hST)
  obtain rfl : iRT = ((β.comp ρ).toAlgebra).toModule := Module.ext (funext₂ hRT)
  let : Algebra R S := ρ.toAlgebra
  let : Algebra R M := α.toAlgebra
  let : Algebra S T := β.toAlgebra
  let : Algebra M T := γ.toAlgebra
  let : Algebra R T := (β.comp ρ).toAlgebra
  have : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := T) fun _ => rfl
  have hw : ∀ r, γ (α r) = β (ρ r) := fun r =>
    congrArg (fun f => f.hom r) hsq.w
  have : IsScalarTower R M T :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := M) (A := T) fun r => (hw r).symm
  have hpush : Algebra.IsPushout R S M T :=
    (CommRingCat.isPushout_iff_isPushout (R := R) (S := M) (R' := S) (S' := T)).1 hsq.flip
  have hbc := hpush.out
  have hτ' : τ = (IsScalarTower.toAlgHom R M T).toLinearMap := LinearMap.ext hτ
  subst hτ'
  have heq : (IsScalarTower.toAlgHom R M T).toLinearMap.liftBaseChange S =
      (hbc.equiv : S ⊗[R] M →ₗ[S] T) := by
    ext m
    simp [IsBaseChange.equiv_tmul]
  rw [heq]
  exact hbc.equiv.bijective
