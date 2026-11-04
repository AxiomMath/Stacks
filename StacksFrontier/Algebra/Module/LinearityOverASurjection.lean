module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Linearity over a surjective algebra map

Let `S` be an `R`-algebra whose structure map `algebraMap R S` is **surjective** — the case of
interest being a quotient of `R`, or the stalk of a quotient of a sheaf of rings. For `S`-modules
whose `R`-actions are the restrictions of their `S`-actions, every `R`-linear map is already
`S`-linear; that is `LinearMap.extendScalarsOfSurjective`, which Mathlib has.

This file covers the case that one cannot, because the two actions are **not instances on the same
spelling of the module**. An identification of an `S`-module `Q` with an `R`-module `P` is then not
linear over either ring: it is additive and **semilinear**, carrying `a • p` to
`algebraMap R S a • Θ p`. This is exactly what the stalk of a descended sheaf of modules provides.
The two stalks are the same type — descent along a quotient of the ring sheaf leaves the underlying
presheaf of abelian groups untouched — but the `R`-action is an instance at the spelling of the
original sheaf and the `S`-action at the spelling of the descended one, so neither
`LinearMap.extendScalarsOfSurjective` nor `IsScalarTower` can be stated for them. What relates them
is the identity, read as a semilinear additive equivalence.

Composing such a `Θ` with an `R`-linear equivalence `P ≃ₗ[R] N` onto a module that *is* an
`S`-module compatibly produces an honest `S`-linear equivalence `Q ≃ₗ[S] N`. So an identification
proved over the original ring is upgraded to one over the quotient, which is the only way the
`R`-linear work already done can be reused.

## Main definitions

* `Stacks.Module.LinearEquiv.ofSemilinearAddEquiv`: an `S`-linear equivalence out of a semilinear
  additive identification followed by an `R`-linear equivalence.

## Main results

* `Stacks.Module.symm_smul_of_semilinear`: a semilinear additive equivalence has semilinear
  inverse, in the direction that reads a scalar of `S` as a scalar of `R`.
* `Stacks.Module.comp_symm_smul_of_semilinear`: the homogeneity of a semilinear identification
  followed by an `R`-linear equivalence.

## Implementation notes

**Only the target carries two compatible actions, and there `IsScalarTower R S ·` says so.** It
gives `algebraMap R S a • n = a • n` by `algebraMap_smul`, which is the compatibility used. No
`Module.compHom` is introduced anywhere: nothing here equips a module over one ring with an action
of the other, which is precisely what makes the statements usable at a stalk.

**Surjectivity is used once, to name a preimage.** It is not weakened to local surjectivity: at a
stalk the quotient map of sheaves of rings is surjective on the nose, local surjectivity having
already been spent in passing to the stalk.
-/

@[expose] public section

namespace Stacks.Module

universe u v w

section Semilinear

variable {R : Type u} {S : Type v} {P Q N : Type w}
  [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module S Q]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- **A semilinear additive equivalence has semilinear inverse.** If `Θ` carries `a • p` to
`algebraMap R S a • Θ p`, then `Θ.symm` carries `algebraMap R S a • q` to `a • Θ.symm q`. -/
theorem symm_smul_of_semilinear (Θ : P ≃+ Q)
    (hΘ : ∀ (a : R) (p : P), Θ (a • p) = algebraMap R S a • Θ p) (a : R) (q : Q) :
    Θ.symm (algebraMap R S a • q) = a • Θ.symm q := by
  refine Θ.injective ?_
  rw [Θ.apply_symm_apply, hΘ, Θ.apply_symm_apply]

/-- **The homogeneity of a semilinear identification followed by an `R`-linear equivalence.**
Reading a scalar of `S` as the image of a scalar of `R`, the inverse semilinearity of `Θ` turns it
into a scalar of `R`, where the `R`-linearity of `e` applies, and `algebraMap_smul` turns it back.
This is the `map_smul'` field of `LinearEquiv.ofSemilinearAddEquiv`. -/
theorem comp_symm_smul_of_semilinear (hs : Function.Surjective (algebraMap R S)) (Θ : P ≃+ Q)
    (hΘ : ∀ (a : R) (p : P), Θ (a • p) = algebraMap R S a • Θ p) (e : P ≃ₗ[R] N) (s : S) (q : Q) :
    e (Θ.symm (s • q)) = s • e (Θ.symm q) := by
  obtain ⟨a, rfl⟩ := hs s
  rw [symm_smul_of_semilinear Θ hΘ, e.map_smul, algebraMap_smul]

/-- **An `S`-linear equivalence out of a semilinear identification.** Let `Θ : P ≃+ Q` be an
additive equivalence from an `R`-module to an `S`-module which carries `a • p` to
`algebraMap R S a • Θ p`, and let `e : P ≃ₗ[R] N` be an `R`-linear equivalence onto a module that
is already an `S`-module compatibly. If `algebraMap R S` is surjective then `e ∘ Θ⁻¹` is
`S`-linear.

This is the shape the stalk of a descended sheaf of modules presents: `Q` is the stalk with its
action of the stalk of the quotient ring sheaf, `P` the same stalk with its action of the stalk of
the original ring sheaf, `Θ` the identity between them — semilinear, not linear — and `e` an
identification of the latter proved over the original ring. -/
def LinearEquiv.ofSemilinearAddEquiv (hs : Function.Surjective (algebraMap R S)) (Θ : P ≃+ Q)
    (hΘ : ∀ (a : R) (p : P), Θ (a • p) = algebraMap R S a • Θ p) (e : P ≃ₗ[R] N) : Q ≃ₗ[S] N where
  __ := Θ.symm.trans e.toAddEquiv
  map_smul' := comp_symm_smul_of_semilinear hs Θ hΘ e

/-- `LinearEquiv.ofSemilinearAddEquiv hs Θ hΘ e` sends `q` to `e (Θ.symm q)`. -/
@[simp]
theorem LinearEquiv.ofSemilinearAddEquiv_apply (hs : Function.Surjective (algebraMap R S))
    (Θ : P ≃+ Q) (hΘ : ∀ (a : R) (p : P), Θ (a • p) = algebraMap R S a • Θ p) (e : P ≃ₗ[R] N)
    (q : Q) : LinearEquiv.ofSemilinearAddEquiv hs Θ hΘ e q = e (Θ.symm q) := rfl

/-- The inverse of `LinearEquiv.ofSemilinearAddEquiv hs Θ hΘ e` sends `n` to `Θ (e.symm n)`. -/
@[simp]
theorem LinearEquiv.ofSemilinearAddEquiv_symm_apply (hs : Function.Surjective (algebraMap R S))
    (Θ : P ≃+ Q) (hΘ : ∀ (a : R) (p : P), Θ (a • p) = algebraMap R S a • Θ p) (e : P ≃ₗ[R] N)
    (n : N) : (LinearEquiv.ofSemilinearAddEquiv hs Θ hΘ e).symm n = Θ (e.symm n) := rfl

end Semilinear

end Stacks.Module

end
