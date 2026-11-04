module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Derivations of a localization

A derivation of a ring `S` with values in a module over a localization `S'` of `S` extends
uniquely to a derivation of `S'`. This file proves that, in the form of a bijection
`Derivation R S' N ≃ Derivation R S N`, and records the uniqueness half separately in the
weakest form in which it is used: an additive map of `S'` satisfying the Leibniz rule and
vanishing on the image of `S` vanishes.

This is the algebraic input to the affine computation of the sheaf of relative differentials of
a morphism of schemes, [Stacks Project, Tag 01UM]: a derivation of the sections of `𝒪_X` over an
affine open `W` spreads out over the basic opens of `W` because the sections over a basic open
are a localization, and it does so uniquely. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafAffine`.

## Main definitions

* `Stacks.Smooth.derivationLocalizationLift` is the extension of a derivation of `S` to the
  localization `S'`, and `Stacks.Smooth.derivationLocalizationEquiv` packages it as a bijection
  between derivations of `S'` and derivations of `S` with values in an `S'`-module.

## Main results

* `Stacks.Smooth.eq_zero_of_leibniz_of_apply_algebraMap_eq_zero`: an additive map `S' →+ N`
  satisfying the Leibniz rule and vanishing on the image of `S` is zero. This is the uniqueness
  statement, in the form that applies to the sectionwise differential of a sheaf derivation,
  which is not packaged as a `Derivation` over a base ring.
* `Stacks.Smooth.derivation_ext_of_isLocalization` is the same statement for two derivations of
  `S'` agreeing on the image of `S`.
* `Stacks.Smooth.derivationLocalizationLift_apply` says that the extension restricts to the
  given derivation along `S → S'`.

## Implementation notes

Surjectivity of the restriction map is obtained from the universal property of Kähler
differentials together with `KaehlerDifferential.isLocalizedModule_map`, which says that
`Ω[S'⁄R]` is the localization of `Ω[S⁄R]`; the extension is therefore
`IsLocalizedModule.lift`, read back as a derivation. Injectivity is proved directly from the
Leibniz rule: for `y : S'` there are `x : S` and `s : p` with `y * s = x`, so
`s • d y = d x = 0`, and `s` acts invertibly on an `S'`-module.

The scalar tower `R → S' → N` is not assumed: it follows from the towers `R → S → S'` and
`S → S' → N`, and is produced by `Stacks.Smooth.isScalarTower_of_isLocalization`.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
-/

@[expose] public section

universe u

namespace Stacks.Smooth

section Primitive

variable {S N : Type*} (S' : Type*) [CommRing S] [CommRing S'] [AddCommGroup N] [Algebra S S']
  [Module S N] [Module S' N] [IsScalarTower S S' N]

/-- An element of a submonoid `p` of `S` acts on an `S'`-module as a unit, when `S'` is the
localization of `S` at `p`. -/
theorem isUnit_algebraMap_moduleEnd (p : Submonoid S) [IsLocalization p S'] (x : p) :
    IsUnit (algebraMap S (Module.End S N) (x : S)) := by
  have h : (algebraMap S (Module.End S N)) (x : S)
      = Algebra.lsmul S S N (algebraMap S S' (x : S)) := by ext n; simp
  rw [h]
  exact (IsLocalization.map_units S' x).map (Algebra.lsmul S S N : S' →ₐ[S] Module.End S N)

/-- An element of a submonoid `p` of `S` acts injectively on an `S'`-module, when `S'` is the
localization of `S` at `p`. -/
theorem smul_injective_of_isLocalization (p : Submonoid S) [IsLocalization p S'] (x : p) :
    Function.Injective fun n : N ↦ (x : S) • n := by
  have h := (Module.End.isUnit_iff _).mp (isUnit_algebraMap_moduleEnd S' (N := N) p x)
  exact fun n₁ n₂ hn ↦ h.1 (by simpa [Module.algebraMap_end_apply] using hn)

/-- **A derivation of a localization is determined by its restriction to the base.** A map from
`S'` to an `S'`-module which satisfies the Leibniz rule and vanishes on the image of `S`
vanishes identically.

Additivity is not needed, and the map is not required to be bundled: this is the form of
uniqueness used on the sections of a sheaf of modules, where the relevant map is a difference
of two sectionwise differentials rather than a `Derivation` over a base ring. -/
theorem eq_zero_of_leibniz_of_apply_algebraMap_eq_zero (p : Submonoid S) [IsLocalization p S']
    (d : S' → N) (hmul : ∀ x y : S', d (x * y) = x • d y + y • d x)
    (h : ∀ b : S, d (algebraMap S S' b) = 0) (y : S') : d y = 0 := by
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj p y
  have hleib := hmul y (algebraMap S S' (s : S))
  rw [hs, h x, h s, smul_zero, zero_add] at hleib
  refine smul_injective_of_isLocalization S' p s ?_
  change (s : S) • d y = (s : S) • (0 : N)
  rw [← IsScalarTower.algebraMap_smul S' (s : S) (d y), ← hleib, smul_zero]

end Primitive

section Localization

variable {R S N : Type*} (S' : Type*) [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
  [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
  [Module S N] [Module S' N] [IsScalarTower S S' N] [Module R N] [IsScalarTower R S N]

/-- The scalar tower `R → S' → N` attached to the towers `R → S → S'` and `S → S' → N`, for `S'`
a localization of `S`. -/
theorem isScalarTower_of_isLocalization (p : Submonoid S) [IsLocalization p S'] :
    IsScalarTower R S' N :=
  IsScalarTower.of_algebraMap_smul fun r n ↦ by
    rw [IsScalarTower.algebraMap_apply R S S', IsScalarTower.algebraMap_smul,
      IsScalarTower.algebraMap_smul]

omit [Algebra R S] [IsScalarTower R S S'] [IsScalarTower R S N] in
/-- A derivation of a localization vanishing on the image of the base vanishes. -/
theorem derivation_eq_zero_of_apply_algebraMap_eq_zero (p : Submonoid S) [IsLocalization p S']
    (d : Derivation R S' N) (h : ∀ b : S, d (algebraMap S S' b) = 0) : d = 0 :=
  Derivation.ext fun y ↦
    (eq_zero_of_leibniz_of_apply_algebraMap_eq_zero S' p d d.leibniz h y).trans
      (Derivation.zero_apply y).symm

omit [Algebra R S] [IsScalarTower R S S'] [IsScalarTower R S N] in
/-- Two derivations of a localization agreeing on the image of the base agree. -/
theorem derivation_ext_of_isLocalization (p : Submonoid S) [IsLocalization p S']
    {d₁ d₂ : Derivation R S' N}
    (h : ∀ b : S, d₁ (algebraMap S S' b) = d₂ (algebraMap S S' b)) : d₁ = d₂ :=
  sub_eq_zero.mp (derivation_eq_zero_of_apply_algebraMap_eq_zero S' p (d₁ - d₂)
    fun b ↦ by simp [h b])

/-- **The extension of a derivation to a localization.** For `S'` a localization of `S` and `N`
an `S'`-module, an `R`-derivation of `S` with values in `N` extends to an `R`-derivation of
`S'`. -/
noncomputable def derivationLocalizationLift (p : Submonoid S) [IsLocalization p S']
    (δ : Derivation R S N) : Derivation R S' N :=
  have := isScalarTower_of_isLocalization (R := R) (N := N) S' p
  KaehlerDifferential.linearMapEquivDerivation R S'
    ((IsLocalizedModule.lift p (KaehlerDifferential.map R R S S')
      δ.liftKaehlerDifferential (isUnit_algebraMap_moduleEnd S' p)).extendScalarsOfIsLocalization
        p S')

/-- The extension of a derivation to a localization restricts to the given derivation. -/
theorem derivationLocalizationLift_apply (p : Submonoid S) [IsLocalization p S']
    (δ : Derivation R S N) (b : S) :
    derivationLocalizationLift S' p δ (algebraMap S S' b) = δ b := by
  have := isScalarTower_of_isLocalization (R := R) (N := N) S' p
  have h : (IsLocalizedModule.lift p (KaehlerDifferential.map R R S S')
        δ.liftKaehlerDifferential (isUnit_algebraMap_moduleEnd S' (N := N) p))
          (KaehlerDifferential.map R R S S' (KaehlerDifferential.D R S b)) = δ b := by
    rw [← LinearMap.comp_apply, IsLocalizedModule.lift_comp]
    exact Derivation.liftKaehlerDifferential_comp_D δ b
  rw [derivationLocalizationLift, KaehlerDifferential.linearMapEquivDerivation_apply_apply,
    ← KaehlerDifferential.map_D R R S S' b, LinearMap.extendScalarsOfIsLocalization_apply', h]

/-- **Derivations of a localization are the derivations of the base.** For `S'` a localization of
`S` and `N` an `S'`-module, restriction along `S → S'` is a bijection from the `R`-derivations of
`S'` with values in `N` onto the `R`-derivations of `S` with values in `N`. -/
noncomputable def derivationLocalizationEquiv (p : Submonoid S) [IsLocalization p S'] :
    Derivation R S' N ≃ Derivation R S N where
  toFun d := d.compAlgebraMap S
  invFun := derivationLocalizationLift S' p
  left_inv _ := derivation_ext_of_isLocalization S' p fun b ↦ by
    rw [derivationLocalizationLift_apply]; rfl
  right_inv δ := by ext b; exact derivationLocalizationLift_apply S' p δ b

end Localization

end Stacks.Smooth

end
