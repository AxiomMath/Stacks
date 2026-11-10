module

public import Mathlib.RingTheory.Localization.Basic
public import StacksFrontier.RingTheory.Derivation.Extension

/-!
# The quotient rule for a derivation extended to a localization

Let `A` be a commutative ring, `D : A → A` a derivation — modelled as `Derivation ℤ A A` — and
`L` a localization of `A` at a submonoid `S`. The unique extension of `D` to `L`, which is
`Stacks.DerivationExtension.locDeriv`, is given on fractions by the quotient rule
`D (a / t) = (t * D a - a * D t) / t²`. That formula is what makes the extension computable, and
it is the only thing about the extension that an explicit construction on a complex of
localizations needs.

The uniqueness statement is strengthened at the same time: a derivation out of `L` is determined
by its values on the image of `A` even when its target is an `L`-algebra rather than `L` itself.
That version applies to the comparison of the extensions of `D` to two nested localizations of
`A`, where one derivation has to be composed with the transition map before the two can be
compared.

A derivation relative to a base ring other than `ℤ` extends the same way: if `A` is an
`R`-algebra and `D : Derivation R A A`, the extension of `D` to a localization `L` of `A` is
again an `R`-derivation, because the scalar action of `r : R` on `L` is multiplication by the
image of `algebraMap R A r`, an element the extension kills. `Derivation.localization` packages
that, and in particular produces a derivation of `Localization P` for any `P : Submonoid A`.

## Main definitions

* `Derivation.localization` — the extension of an `R`-derivation `D : Derivation R A A` to a
  localization `L` of `A`, as an `R`-derivation `Derivation R L L`.

## Main results

* `Stacks.DerivationExtension.locDeriv_mk'` — **the quotient rule.**
* `Stacks.DerivationExtension.derivation_ext_of_algebraMap_of_tower` — a derivation of `L` into
  an `L`-algebra is determined by its values on the image of `A`.
* `Stacks.DerivationExtension.algHom_locDeriv` — **the extension is natural**: an `A`-algebra map
  between two localizations of `A` intertwines the two extensions of `D`.
* `Derivation.localization_algebraMap`, `Derivation.localization_mk'` and
  `Derivation.localization_mk` — `Derivation.localization` extends `D` along `A → L`, and obeys
  the quotient rule, in the `IsLocalization.mk'` and the `Localization.mk` spellings.
* `Derivation.ext_of_isLocalization` and `Derivation.eq_localization` — **uniqueness**: two
  `R`-derivations of `L` agreeing on the image of `A` are equal, so `Derivation.localization` is
  the only `R`-derivation of `L` extending `D`.

## Implementation notes

`Stacks.DerivationExtension.derivation_ext_of_algebraMap_of_tower` strictly generalizes
`Stacks.DerivationExtension.derivation_ext_of_algebraMap` of
`StacksFrontier/RingTheory/Derivation/Extension.lean`, which is the case `N = L`; both results
belong next to `Stacks.DerivationExtension.locDeriv` in that file, and merging them there would
let the special case be deleted.

`Derivation.localization` is not a second construction: it is
`Stacks.DerivationExtension.locDeriv` applied to `D.restrictScalars ℤ`, repackaged as an
`R`-derivation once `Stacks.DerivationExtension.locDeriv_smul` has supplied the missing
`R`-linearity. Every statement about it therefore reduces to the corresponding statement about
`locDeriv`, and the case `R = ℤ` recovers `locDeriv` itself.

## References

* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
-/

@[expose] public section

namespace Stacks.DerivationExtension

variable {A : Type*} [CommRing A] {S : Submonoid A}

/-- Differentiating `x * q = y` with a derivation `G` into an `L`-algebra `N`. -/
private theorem algebraMap_mul_deriv_of_mul_eq {L N : Type*} [CommRing L] [CommRing N]
    [Algebra L N] (G : Derivation ℤ L N) {x q y : L} (h : x * q = y) :
    algebraMap L N q * G x = G y - algebraMap L N x * G q := by
  have hh : G (x * q) = G y := by rw [h]
  rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def] at hh
  linear_combination hh

/-- **The quotient rule.** The unique extension of a derivation `D` of `A` to a localization `L`
of `A` sends the fraction `a / t` to `(t * D a - a * D t) / t²`. -/
theorem locDeriv_mk' (D : Derivation ℤ A A) (L : Type*) [CommRing L] [Algebra A L]
    [IsLocalization S L] (a : A) (t : S) :
    locDeriv D S L (IsLocalization.mk' L a t) =
      IsLocalization.mk' L ((t : A) * D a - a * D (t : A)) (t * t) := by
  set x := IsLocalization.mk' L a t
  set q : L := algebraMap A L (t : A) with hq
  have ht : IsUnit q := IsLocalization.map_units L t
  have hs : x * q = algebraMap A L a := IsLocalization.mk'_spec L a t
  have hq' : locDeriv D S L q = algebraMap A L (D (t : A)) := locDeriv_algebraMap D S L t
  have hder := algebraMap_mul_deriv_of_mul_eq (locDeriv D S L) hs
  simp only [Algebra.algebraMap_self, RingHom.id_apply, locDeriv_algebraMap, hq'] at hder
  have hmul : locDeriv D S L x * q * q =
      algebraMap A L ((t : A) * D a - a * D (t : A)) := by
    calc locDeriv D S L x * q * q
        = (algebraMap A L (D a) - x * algebraMap A L (D (t : A))) * q := by
          linear_combination hder * q
      _ = algebraMap A L ((t : A) * D a - a * D (t : A)) := by
          simp only [map_sub, map_mul, sub_mul]
          rw [← hs]
          ring
  refine (ht.pow 2).mul_left_cancel ?_
  calc q ^ 2 * locDeriv D S L x
      = locDeriv D S L x * q * q := by ring
    _ = algebraMap A L ((t : A) * D a - a * D (t : A)) := hmul
    _ = IsLocalization.mk' L ((t : A) * D a - a * D (t : A)) (t * t) *
          algebraMap A L ((t * t : S) : A) :=
        (IsLocalization.mk'_spec L ((t : A) * D a - a * D (t : A)) (t * t)).symm
    _ = q ^ 2 * IsLocalization.mk' L ((t : A) * D a - a * D (t : A)) (t * t) := by
        rw [hq, Submonoid.coe_mul, map_mul]
        ring

/-- **A derivation out of a localization is determined on the image of the base ring**, even when
its target is a larger algebra. This is `derivation_ext_of_algebraMap` with the target allowed to
be any `L`-algebra, which is what comparing the extensions to two nested localizations needs. -/
theorem derivation_ext_of_algebraMap_of_tower {L : Type*} [CommRing L] [Algebra A L]
    [IsLocalization S L] {N : Type*} [CommRing N] [Algebra L N] [Algebra A N]
    [IsScalarTower A L N] (D E : Derivation ℤ L N)
    (h : ∀ a : A, D (algebraMap A L a) = E (algebraMap A L a)) : D = E := by
  refine Derivation.ext fun x => ?_
  obtain ⟨⟨a, t⟩, hx⟩ := IsLocalization.surj S x
  refine ((IsLocalization.map_units L t).map (algebraMap L N)).mul_left_cancel ?_
  rw [algebraMap_mul_deriv_of_mul_eq D hx, algebraMap_mul_deriv_of_mul_eq E hx, h a, h (t : A)]

/-- **The extension of a derivation to a localization is natural.** If `L` and `N` are
localizations of `A` at submonoids `S` and `T` and `g : L →ₐ[A] N` is the canonical comparison,
then `g` carries the extension of `D` to `L` to the extension of `D` to `N`. No relation between
`S` and `T` is needed beyond the existence of `g`, which already forces every element of `S` to
become a unit in `N`. -/
theorem algHom_locDeriv {T : Submonoid A} (D : Derivation ℤ A A) (L N : Type*) [CommRing L]
    [CommRing N] [Algebra A L] [Algebra A N] [IsLocalization S L] [IsLocalization T N]
    (g : L →ₐ[A] N) (x : L) :
    g (locDeriv D S L x) = locDeriv D T N (g x) := by
  let _ : Algebra L N := g.toRingHom.toAlgebra
  have _ : IsScalarTower A L N := IsScalarTower.of_algHom g
  have h : (IsScalarTower.toAlgHom L L N).toLinearMap.compDer (locDeriv D S L) =
      Derivation.compAlgebraMap (R := ℤ) L (locDeriv D T N) := by
    refine derivation_ext_of_algebraMap_of_tower (S := S) _ _ fun a => ?_
    change algebraMap L N (locDeriv D S L (algebraMap A L a)) =
      locDeriv D T N (algebraMap L N (algebraMap A L a))
    rw [locDeriv_algebraMap]
    simp only [← IsScalarTower.algebraMap_apply]
    rw [locDeriv_algebraMap]
  exact DFunLike.congr_fun h x

section Base

variable {R : Type*} [CommRing R] [Algebra R A] (D : Derivation R A A) (P : Submonoid A)
  (L : Type*) [CommRing L] [Algebra A L] [IsLocalization P L] [Algebra R L]
  [IsScalarTower R A L]

/-- The extension to a localization of a derivation that is linear over a base ring `R` is again
`R`-linear: the scalar `r : R` acts on `L` as multiplication by the image of `algebraMap R A r`,
and the extension sends that image to the image of `D (algebraMap R A r) = 0`. -/
lemma locDeriv_smul (r : R) (x : L) :
    locDeriv (D.restrictScalars ℤ) P L (r • x) = r • locDeriv (D.restrictScalars ℤ) P L x := by
  have hc : algebraMap R L r = algebraMap A L (algebraMap R A r) :=
    IsScalarTower.algebraMap_apply R A L r
  have hD : locDeriv (D.restrictScalars ℤ) P L (algebraMap A L (algebraMap R A r)) = 0 := by
    rw [locDeriv_algebraMap]
    simp [Derivation.restrictScalars_apply, D.map_algebraMap]
  rw [Algebra.smul_def r x, hc, Derivation.leibniz, hD, smul_zero, add_zero, smul_eq_mul, ← hc,
    ← Algebra.smul_def]

end Base

end Stacks.DerivationExtension

namespace Derivation

open Stacks.DerivationExtension

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)
  (P : Submonoid A) (L : Type*) [CommRing L] [Algebra A L] [IsLocalization P L] [Algebra R L]
  [IsScalarTower R A L]

/-- **The extension of a derivation to a localization.** An `R`-derivation `D` of an `R`-algebra
`A` extends to an `R`-derivation of any localization `L` of `A` at a submonoid `P`; on fractions
it is given by the quotient rule `D (a / s) = (s * D a - a * D s) / s²`. Taking
`L = Localization P` gives a derivation of `Localization P`. -/
noncomputable def localization : Derivation R L L :=
  Derivation.mk'
    { toFun := locDeriv (D.restrictScalars ℤ) P L
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => locDeriv_smul D P L r x }
    fun a b => (locDeriv (D.restrictScalars ℤ) P L).leibniz a b

/-- As a function, `Derivation.localization` is the extension
`Stacks.DerivationExtension.locDeriv` of `D` viewed as an additive derivation; the `R`-derivation
structure adds only the `R`-linearity. -/
lemma coe_localization :
    ⇑(D.localization P L) = locDeriv (D.restrictScalars ℤ) P L := rfl

/-- **`Derivation.localization` extends `D`**: it agrees with `D` on the image of `A` in the
localization. -/
@[simp] theorem localization_algebraMap (a : A) :
    D.localization P L (algebraMap A L a) = algebraMap A L (D a) :=
  locDeriv_algebraMap (D.restrictScalars ℤ) P L a

/-- **The quotient rule.** `Derivation.localization` sends the fraction `a / s` to
`(s * D a - a * D s) / s²`. -/
theorem localization_mk' (a : A) (s : P) :
    D.localization P L (IsLocalization.mk' L a s) =
      IsLocalization.mk' L ((s : A) * D a - a * D (s : A)) (s * s) :=
  locDeriv_mk' (D.restrictScalars ℤ) L a s

/-- **The quotient rule** in `Localization.mk` form: the extension of `D` to `Localization P`
sends `Localization.mk a s` to `Localization.mk ((s : A) * D a - a * D s) (s * s)`. -/
theorem localization_mk (a : A) (s : P) :
    D.localization P (Localization P) (Localization.mk a s) =
      Localization.mk ((s : A) * D a - a * D (s : A)) (s * s) := by
  rw [Localization.mk_eq_mk']
  exact localization_mk' D P (Localization P) a s

omit [Algebra R A] [IsScalarTower R A L] in
include P in
/-- **A derivation of a localization is determined on the base ring.** Two `R`-derivations of a
localization `L` of `A` that agree on the image of `A` are equal, because every element of `L` is
a fraction and the denominators are units. -/
theorem ext_of_isLocalization (D₁ D₂ : Derivation R L L)
    (h : ∀ a : A, D₁ (algebraMap A L a) = D₂ (algebraMap A L a)) : D₁ = D₂ :=
  Derivation.ext fun x => DFunLike.congr_fun
    (derivation_ext_of_algebraMap P L (D₁.restrictScalars ℤ) (D₂.restrictScalars ℤ) h) x

/-- **Uniqueness of the extension.** `Derivation.localization` is the only `R`-derivation of the
localization agreeing with `D` on the image of `A`. -/
theorem eq_localization (D' : Derivation R L L)
    (h : ∀ a : A, D' (algebraMap A L a) = algebraMap A L (D a)) : D' = D.localization P L :=
  ext_of_isLocalization P L D' (D.localization P L) fun a => by
    rw [h a, localization_algebraMap]

omit [Algebra R A] [IsScalarTower R A L] in
include P in
/-- An `R`-derivation of a localization of `A` vanishing on the image of `A` is zero; this is
`Derivation.ext_of_isLocalization` for the zero derivation. -/
theorem eq_zero_of_isLocalization (D' : Derivation R L L)
    (h : ∀ a : A, D' (algebraMap A L a) = 0) : D' = 0 :=
  ext_of_isLocalization P L D' 0 fun a => by simp [h a]

end Derivation

end
