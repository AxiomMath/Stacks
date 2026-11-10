module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The length of a localization does not depend on the model

Let `R` be a commutative ring, `S` a submonoid, `M` an `R`-module, `T` a localization of `R` at
`S` and `N` a localization of `M` at `S` as a `T`-module. The length of `N` over `T` is then an
invariant of `(R, S, M)` alone: it agrees with the length of the *formal* localization
`LocalizedModule S M` over the *formal* localization `Localization S`.

This is the statement a consumer needs whenever a length is computed in one model and used in
another — for instance when the length formula of [Stacks, Tag 02QH],
`Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient`,
produces a sum of lengths over `Localization.AtPrime q` of
`LocalizedModule q.primeCompl M`, and the geometric object those lengths are about is the stalk of
a module at the point corresponding to `q`, which is a localization of `M` in its own right.

Mathlib has no statement pairing `IsLocalizedModule` with `Module.length`: its
`Mathlib.RingTheory.Length` never mentions the former. The localized-length statements in this
development are all quotient-specific (`Module.length_localizedModule_le`,
`length_localizedModule_quotient_span_eq`) or about semilocal decompositions, so none of them is
this.

## Main results

* `Module.length_eq_of_isLocalization_of_isLocalizedModule` — the statement above.

## Implementation notes

Exactly one scalar transport is unavoidable: neither `LocalizedModule S M` carries a `T`-action
natively nor `N` a `Localization S`-action, so one of the two modules has to be given the other
ring's action before the two lengths can be compared at all. The transport is taken on `N`, along
the comparison isomorphism `IsLocalization.algEquiv S (Localization S) T` of the two ring models,
by `Module.compHom`; the two resulting scalar towers are the only thing proved by hand, and each
is one `Algebra.smul_def` away from `IsScalarTower.smul_assoc` for the given tower over `R`.

With `N` an `Localization S`-module, `LinearEquiv.extendScalarsOfIsLocalization` upgrades the
`R`-linear comparison of the two module models — `IsLocalizedModule.linearEquiv` applied to the
formal localization map and to `f` — to a `Localization S`-linear one. That is what makes this
proof short: the alternative, `Module.length_eq_of_surjective_of_addEquiv`, needs the
semilinearity of that comparison over the ring isomorphism proved by hand, which is an
`IsLocalization.mk'` induction. Having the scalars extended instead, `LinearEquiv.length_eq`
gives the equality over `Localization S` and `Module.length_eq_of_surjective` restores the
scalars to `T`, the comparison map being surjective because it is an isomorphism.

## References

* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public section

universe u

/-- **The length of a localization is independent of the model.** If `T` is a localization of `R`
at `S` and `N` is a localization of the `R`-module `M` at `S`, read as a `T`-module, then the
length of `N` over `T` is the length of the formal localization `LocalizedModule S M` over the
formal localization `Localization S`. -/
theorem Module.length_eq_of_isLocalization_of_isLocalizedModule
    {R : Type*} [CommRing R] (S : Submonoid R) (T : Type*) [CommRing T] [Algebra R T]
    [IsLocalization S T] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module T N] [IsScalarTower R T N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    Module.length (Localization S) (LocalizedModule S M) = Module.length T N := by
  let _ : Algebra (Localization S) T :=
    (IsLocalization.algEquiv S (Localization S) T).toRingEquiv.toRingHom.toAlgebra
  have hmap : (algebraMap (Localization S) T).comp (algebraMap R (Localization S))
      = algebraMap R T := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (IsLocalization.algEquiv S (Localization S) T).toAlgHom.comp_algebraMap
  have hsurj : Function.Surjective (algebraMap (Localization S) T) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (IsLocalization.algEquiv S (Localization S) T).surjective
  let _ : Module (Localization S) N := Module.compHom N (algebraMap (Localization S) T)
  have : IsScalarTower (Localization S) T N :=
    ⟨fun x t n => by
      change (x • t) • n = (algebraMap (Localization S) T x) • (t • n)
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower R (Localization S) N :=
    ⟨fun r x n => by
      have h1 : algebraMap (Localization S) T (r • x)
          = algebraMap R T r * algebraMap (Localization S) T x := by
        rw [Algebra.smul_def, map_mul, ← RingHom.comp_apply, hmap]
      change (algebraMap (Localization S) T (r • x)) • n
        = r • ((algebraMap (Localization S) T x) • n)
      rw [h1, ← Algebra.smul_def, smul_assoc]⟩
  exact (LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S M) f)).length_eq.trans
    (Module.length_eq_of_surjective hsurj)

end
