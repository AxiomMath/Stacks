module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.Length.LocalizationModelIndependence

/-!
# The localized length at a prime of a stalk is the multiplicity at the corresponding point

Let `X` be a scheme, `ξ` a point, `A = 𝒪_{X, ξ}` the local ring there, `F` a quasi-coherent
`𝒪_X`-module and `q` a prime of `A`. The length formula of [Stacks, Tag 02QH] produces, for each
minimal prime `q` of `A`, the length over `A_q` of the localization of `F_ξ` at `q`; part (4) of
[Stacks, Tag 02SW] states the corresponding coefficient as the multiplicity of `F` at the generic
point `η` of the irreducible component that `q` indexes, which is the length of `F_η` over
`𝒪_{X, η}`. This file identifies the two.

Both are "the localization of `F_ξ` at `q`, over the localization of `A` at `q`", in two models:
on the left the formal `Localization.AtPrime q` and `LocalizedModule q.primeCompl F_ξ`, on the
right the geometric `𝒪_{X, η}` and `F_η`. That the geometric pair really is such a localization is
two library statements — `Stacks.Chow.isLocalization_stalk_of_specializes` on the ring and
`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes` on the module — and
the model-independence of the length is
`Module.length_eq_of_isLocalization_of_isLocalizedModule`.

The only hypothesis is quasi-coherence of `F`, which is what the module-side statement needs. No
Noetherian, integral or dimension assumption appears, and no chart is chosen.

## Main results

* `Stacks.Chow.length_localizedModule_stalk_eq_length_stalk` — the displayed identity.
* `Stacks.Chow.length_localizedModule_stalk_eq_sheafMultiplicity` — the same with the right-hand
  side as `Stacks.Chow.sheafMultiplicity`, the coefficient of the cycle of `F`, which is the form
  part (4) consumes.

## Implementation notes

This is the general-module counterpart of
`Stacks.Chow.length_localizedModule_quotient_idealStalk_eq_length_stalk`, which does the same for
`A ⧸ I`. That statement is not instantiated here and cannot be: its two helpers are `private` and
reduce everything to *rings* — a quotient ring viewed as a module over itself — which a general
module cannot be put into. The model-independence used instead is stated once, for arbitrary
commutative rings and modules, in `StacksFrontier.RingTheory.Length.LocalizationModelIndependence`;
the geometry enters only through the two localization facts above.

The prime that the module-side statement is indexed by is the chart-free
`(IsLocalRing.maximalIdeal 𝒪_{X, η}).under 𝒪_{X, ξ}`, and it is `q` because the ring-side
statement makes `𝒪_{X, η}` a localization of `A` at `q`: that is Mathlib's
`IsLocalization.AtPrime.under_maximalIdeal`. That equality of primes cannot be moved into the
`IsLocalizedModule` hypothesis by `rewrite` — the two sides carry different `Ideal.IsPrime`
instance arguments, so the motive is not type correct — and
`Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_of_eq` exists for exactly that
transport.

The scalar tower the model-independence asks for,
`IsScalarTower 𝒪_{X, ξ} 𝒪_{X, η} F_η`, holds by `rfl`:
`Stacks.ModuleStalkSpecialization.stalkSpecializesModule` is *defined* as
`Module.compHom` of the stalk module along `TopCat.Presheaf.stalkSpecializes`, which is the same
ring map the `Algebra` instance is built from, so `algebraMap r • m` and `stalkSpecializes r • m`
are the same term. So no `IsLocalization.mk'` induction proving the semilinearity of the module
comparison over the ring comparison is needed.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **The length, over the localization of `𝒪_{X, ξ}` at a prime `q`, of the localization of
`F_ξ` there is the length of `F_η` over `𝒪_{X, η}`**, for `η` the point of `X` corresponding to
`q`. Both sides are the localization of `F_ξ` at `q` over the localization of `𝒪_{X, ξ}` at `q`,
in two models, and the length does not depend on the model. The only hypothesis is
quasi-coherence of `F`. -/
theorem length_localizedModule_stalk_eq_length_stalk (F : X.Modules) [F.IsQuasicoherent]
    {ξ : X} (q : PrimeSpectrum (X.presheaf.stalk ξ)) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk ξ)) =
      Module.length (X.presheaf.stalk (X.fromSpecStalk ξ q))
        (F.presheaf.stalk (X.fromSpecStalk ξ q)) := by
  have h : X.fromSpecStalk ξ q ⤳ ξ := by
    have hr : X.fromSpecStalk ξ q ∈ Set.range ⇑(X.fromSpecStalk ξ) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  let _ : Algebra (X.presheaf.stalk ξ) (X.presheaf.stalk (X.fromSpecStalk ξ q)) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc : IsLocalization.AtPrime
      (X.presheaf.stalk (X.fromSpecStalk ξ q)) q.asIdeal :=
    isLocalization_stalk_of_specializes h q rfl
  let _ := Stacks.ModuleStalkSpecialization.stalkModule F ξ
  let _ := Stacks.ModuleStalkSpecialization.stalkModule F (X.fromSpecStalk ξ q)
  let _ := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F h
  have hmod : IsLocalizedModule.AtPrime q.asIdeal
      (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_of_eq
      (IsLocalization.AtPrime.under_maximalIdeal _ _)
      (Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F h)
  have htow : IsScalarTower (X.presheaf.stalk ξ) (X.presheaf.stalk (X.fromSpecStalk ξ q))
      (F.presheaf.stalk (X.fromSpecStalk ξ q)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.length_eq_of_isLocalization_of_isLocalizedModule q.asIdeal.primeCompl
    (X.presheaf.stalk (X.fromSpecStalk ξ q))
    (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h)

/-- **The same identity with the right-hand side as the multiplicity of `F` at the corresponding
point**, which is the coefficient of the cycle of `F` there and the form part (4) of
[Stacks, Tag 02SW] consumes. -/
theorem length_localizedModule_stalk_eq_sheafMultiplicity (F : X.Modules) [F.IsQuasicoherent]
    {ξ : X} (q : PrimeSpectrum (X.presheaf.stalk ξ)) :
    ((Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl (F.presheaf.stalk ξ))).toNat : ℤ) =
      sheafMultiplicity F (X.fromSpecStalk ξ q) :=
  congrArg (fun z : ℕ∞ => (z.toNat : ℤ))
    (length_localizedModule_stalk_eq_length_stalk F q)

end Stacks.Chow

end
