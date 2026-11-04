module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Exterior powers of a localized module

Let `S` be a multiplicative subset of a commutative ring `R`, let `Rₛ` be a localization of `R`
at `S`, and let `f : M →ₗ[R] M'` exhibit `M'` as the localization of the `R`-module `M` at `S`.
**Then the induced map `⋀ⁿ_R(M) → ⋀ⁿ_{Rₛ}(M')` exhibits the `Rₛ`-module `⋀ⁿ_{Rₛ}(M')` as the
localization of `⋀ⁿ_R(M)` at `S`.**

This is the exterior counterpart of `IsLocalization.isLocalizedModule_tensorMap`, which is
[Stacks, Tag 00DL], and it is stated in the same style: for an *abstract* localization `Rₛ` of
`R` and an *abstract* localization map `f`, not for the concrete `Localization S` and
`LocalizedModule.mkLinearMap`.

## Main definitions

* `IsLocalization.exteriorPowerAlt`: the `R`-alternating map
  `v ↦ f (v 0) ∧ ⋯ ∧ f (v (n-1))` with values in `⋀ⁿ_{Rₛ}(M')`.
* `IsLocalization.exteriorPowerMap`: **the canonical comparison**
  `⋀ⁿ_R(M) →ₗ[R] ⋀ⁿ_{Rₛ}(M')`, the `R`-linear map it induces.

## Main results

* `IsLocalization.isLocalizedModule_of_exteriorPower`: **any** `R`-linear map
  `⋀ⁿ_R(M) → ⋀ⁿ_{Rₛ}(M')` carrying a wedge of elements to the wedge of their images under `f`
  is a localization map.
* `IsLocalization.isLocalizedModule_exteriorPowerMap`: the canonical comparison is a
  localization map.

## Implementation notes

**The target is an exterior power over `Rₛ`, not over `R`**, so `exteriorPower.map` cannot be
used: it produces `⋀ⁿ_R(M) →ₗ[R] ⋀ⁿ_R(M')`, an exterior power over the wrong ring.  The
comparison is therefore built directly from the universal property of the exterior power through
`exteriorPower.alternatingMapLinearEquiv`, exactly as `ExteriorAlgebra.exteriorPowerBaseChangeMap`
is.

**No new mathematics.** `DeRhamBaseChange.isBaseChange_exteriorPower` already says that a
degree-`n` map compatible with `exteriorPower.ιMulti` and with a base change in degree one is
itself a base change — and it says it for an abstract target, not only for `Rₛ ⊗[R] M` — so all
that is needed is to pass through `isLocalizedModule_iff_isBaseChange` in both directions.  In
particular no flatness, finiteness or characteristic hypothesis appears.

Nothing is said here about the multiplication of the exterior algebra, nor about the graded
algebra `⋀_{Rₛ}(M')` as a whole; only the individual homogeneous pieces are compared.

## References

* [Stacks Project, Tag 00DL](https://stacks.math.columbia.edu/tag/00DL)
* [Stacks Project, Tag 0C6F](https://stacks.math.columbia.edu/tag/0C6F)
-/


@[expose] public noncomputable section

open scoped TensorProduct

variable {R : Type*} [CommRing R]
  (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [Module Rₛ M'] [IsScalarTower R Rₛ M']
  (f : M →ₗ[R] M') (n : ℕ)

/-- The `R`-alternating map `v ↦ f (v 0) ∧ ⋯ ∧ f (v (n-1))` with values in the `n`-th exterior
power of `M'` over `Rₛ`. -/
def IsLocalization.exteriorPowerAlt : M [⋀^Fin n]→ₗ[R] ↥(⋀[Rₛ]^n M') where
  toMultilinearMap :=
    ((exteriorPower.ιMulti Rₛ n).toMultilinearMap.restrictScalars R).compLinearMap fun _ ↦ f
  map_eq_zero_of_eq' _v _i _j hv hij :=
    (exteriorPower.ιMulti Rₛ n).map_eq_zero_of_eq _ (congrArg f hv) hij

/-- **The canonical comparison `⋀ⁿ_R(M) → ⋀ⁿ_{Rₛ}(M')`** induced by a map `f : M →ₗ[R] M'` into
an `Rₛ`-module. -/
def IsLocalization.exteriorPowerMap : ↥(⋀[R]^n M) →ₗ[R] ↥(⋀[Rₛ]^n M') :=
  exteriorPower.alternatingMapLinearEquiv (IsLocalization.exteriorPowerAlt Rₛ f n)

/-- The canonical comparison `IsLocalization.exteriorPowerMap` sends the wedge
`v 0 ∧ ⋯ ∧ v (n-1)` to the wedge `f (v 0) ∧ ⋯ ∧ f (v (n-1))`. -/
@[simp]
theorem IsLocalization.exteriorPowerMap_ιMulti (v : Fin n → M) :
    IsLocalization.exteriorPowerMap Rₛ f n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti Rₛ n fun i ↦ f (v i) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- **The `n`-th exterior power of a localization is a localization of the `n`-th exterior
power**, for any comparison map carrying a wedge to the wedge of the images.

The hypothesis on `Φ` determines it: the wedges `exteriorPower.ιMulti R n v` span `⋀ⁿ_R(M)`. -/
theorem IsLocalization.isLocalizedModule_of_exteriorPower (S : Submonoid R)
    [IsLocalization S Rₛ] [IsLocalizedModule S f]
    (Φ : ↥(⋀[R]^n M) →ₗ[R] ↥(⋀[Rₛ]^n M'))
    (hΦ : ∀ v : Fin n → M, Φ (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti Rₛ n fun i ↦ f (v i)) :
    IsLocalizedModule S Φ :=
  (isLocalizedModule_iff_isBaseChange S Rₛ Φ).2
    (DeRhamBaseChange.isBaseChange_exteriorPower
      ((isLocalizedModule_iff_isBaseChange S Rₛ f).1 inferInstance) Φ hΦ)

/-- **The canonical comparison is a localization map.** -/
instance IsLocalization.isLocalizedModule_exteriorPowerMap (S : Submonoid R)
    [IsLocalization S Rₛ] [IsLocalizedModule S f] :
    IsLocalizedModule S (IsLocalization.exteriorPowerMap Rₛ f n) :=
  IsLocalization.isLocalizedModule_of_exteriorPower Rₛ f n S _
    (IsLocalization.exteriorPowerMap_ιMulti Rₛ f n)

end
