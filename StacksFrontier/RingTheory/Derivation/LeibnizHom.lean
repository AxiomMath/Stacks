module

public import StacksFrontier.RingTheory.Derivation.Extension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additive maps obeying the Leibniz rule, and their localizations

A derivation of a commutative ring `A` over `ℤ` is nothing more than an additive map
`f : A →+ A` satisfying `f (x * y) = x * f y + y * f x`: the `ℤ`-linearity is automatic from
additivity, and `f 1 = 0` is forced by the Leibniz rule itself, since `f 1 = f (1 * 1) = 2 * f 1`.
This file records that equivalence in the direction that is actually needed — from a bare additive
map to a bundled `Derivation ℤ A A` — and transports the extension theory of
`StacksFrontier.RingTheory.Derivation.Extension` across it.

The point of working with unbundled maps is that vector fields on a scheme are glued from families
of additive maps `Γ(Y, W) →+ Γ(Y, W)` obeying the Leibniz rule, one for each open `W`; the base
ring over which such a map is linear plays no role in any of the gluing arguments, and insisting on
a bundled `Derivation k` there forces a `k`-algebra structure on every ring of sections before the
mathematics asks for one. Once the map is recognised as a `Derivation ℤ`, the localization results
apply verbatim: a Leibniz map on `A` induces exactly one on any localization `L` of `A`, and two
Leibniz maps on `L` agreeing on the image of `A` are equal. The latter is the statement that lets a
vector field be identified from its behaviour on a dense affine, where the ring of sections of a
smaller open is a localization of the larger one.

## Main definitions

* `Stacks.DerivationExtension.ofLeibnizHom` — an additive map obeying the Leibniz rule, viewed as
  a derivation over `ℤ`.
* `Stacks.DerivationExtension.locLeibnizHom` — the induced Leibniz map on a localization.

## Main results

* `Stacks.DerivationExtension.locLeibnizHom_algebraMap` and
  `Stacks.DerivationExtension.eq_locLeibnizHom` — `locLeibnizHom` extends the given map along
  `A → L`, and is the only Leibniz map of `L` which does.
* `Stacks.DerivationExtension.eq_of_leibniz_of_localization` — **two Leibniz additive maps on a
  localization which agree on the image of the base are equal.**

## References

* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.DerivationExtension

section Bundle

variable {A : Type u} [CommRing A]

/-- An additive map of a commutative ring obeying the Leibniz rule is a derivation over `ℤ`. -/
@[sga "3 VIIA 1.2.0" "partial"]
public def ofLeibnizHom (f : A →+ A)
    (hf : ∀ x y : A, f (x * y) = x * f y + y * f x) : Derivation ℤ A A where
  toLinearMap := f.toIntLinearMap
  map_one_eq_zero' := by
    change f 1 = 0
    have h := hf 1 1
    rw [mul_one, one_mul] at h
    linear_combination -h
  leibniz' a b := by
    change f (a * b) = a • f b + b • f a
    simpa only [smul_eq_mul] using hf a b

/-- `ofLeibnizHom f hf` is `f` as a function. -/
@[simp] public theorem ofLeibnizHom_apply (f : A →+ A)
    (hf : ∀ x y : A, f (x * y) = x * f y + y * f x) (a : A) : ofLeibnizHom f hf a = f a := rfl

end Bundle

section Localization

variable {A : Type u} [CommRing A] (f : A →+ A)
  (hf : ∀ x y : A, f (x * y) = x * f y + y * f x) (M : Submonoid A)
  (L : Type v) [CommRing L] [Algebra A L] [IsLocalization M L]

/-- The Leibniz additive map induced on a localization by one on the base. -/
public def locLeibnizHom : L →+ L :=
  (locDeriv (ofLeibnizHom f hf) M L).toLinearMap.toAddMonoidHom

/-- `locLeibnizHom f hf M L` is the underlying function of `locDeriv (ofLeibnizHom f hf) M L`. -/
@[simp] public theorem locLeibnizHom_apply (z : L) :
    locLeibnizHom f hf M L z = locDeriv (ofLeibnizHom f hf) M L z := rfl

/-- It obeys the Leibniz rule. -/
public theorem locLeibnizHom_mul (z w : L) : locLeibnizHom f hf M L (z * w)
    = z * locLeibnizHom f hf M L w + w * locLeibnizHom f hf M L z := by
  simp only [locLeibnizHom_apply, Derivation.leibniz, smul_eq_mul]

/-- It extends `f` along `A → L`. -/
@[simp] public theorem locLeibnizHom_algebraMap (a : A) :
    locLeibnizHom f hf M L (algebraMap A L a) = algebraMap A L (f a) := by
  simp only [locLeibnizHom_apply, locDeriv_algebraMap, ofLeibnizHom_apply]

/-- **Uniqueness.** Any Leibniz additive map of `L` extending `f` along `A → L` is this one. -/
public theorem eq_locLeibnizHom (g : L →+ L)
    (hg : ∀ z w : L, g (z * w) = z * g w + w * g z)
    (h : ∀ a : A, g (algebraMap A L a) = algebraMap A L (f a)) :
    g = locLeibnizHom f hf M L := by
  have key : ofLeibnizHom g hg = locDeriv (ofLeibnizHom f hf) M L :=
    derivation_ext_of_algebraMap M L _ _ fun a => by simpa using h a
  exact AddMonoidHom.ext fun z => by simpa using DFunLike.congr_fun key z

end Localization

section Transitivity

variable {A : Type u} [CommRing A] {L : Type v} [CommRing L] [Algebra A L]

/-- **Two Leibniz maps on a localization that extend Leibniz maps on the base agreeing there are
equal.** No extension datum on the base is needed: the hypothesis is only that the two maps agree
on the image of `A`, and a Leibniz map of a localization is determined by its values there. -/
public theorem eq_of_leibniz_of_localization (M : Submonoid A) [IsLocalization M L]
    (g₁ g₂ : L →+ L)
    (hg₁ : ∀ z w : L, g₁ (z * w) = z * g₁ w + w * g₁ z)
    (hg₂ : ∀ z w : L, g₂ (z * w) = z * g₂ w + w * g₂ z)
    (h : ∀ a : A, g₁ (algebraMap A L a) = g₂ (algebraMap A L a)) :
    g₁ = g₂ := by
  have key : ofLeibnizHom g₁ hg₁ = ofLeibnizHom g₂ hg₂ :=
    derivation_ext_of_algebraMap M L _ _ fun a => by simpa using h a
  exact AddMonoidHom.ext fun z => by simpa using DFunLike.congr_fun key z

end Transitivity

end Stacks.DerivationExtension

end
