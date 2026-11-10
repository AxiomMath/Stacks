module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.Derivation.Extension
public import StacksFrontier.RingTheory.Derivation.SubalgebraStable

/-!
# Extending a derivation to the integral closure in a localization

Let `A` be a commutative ring, let `L` be a localization of `A` and let `A'` be the integral
closure of `A` in `L`. A derivation of `A` extends uniquely to a derivation of `L` by Tag 07PE
(`Stacks.DerivationExtension.locDeriv`), and the question is whether that extension carries `A'`
into `A'`. It does as soon as `A'` is generated over `A` by elements satisfying a polynomial
relation with invertible formal derivative, and then the extension restricts to the *unique*
derivation of `A'` over the base field prolonging the given one.

**No locality hypothesis on `A` is used.** That is the point: the local statement
`Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra` rests on "an element of a
local ring with nonzero residue is a unit", and `Stacks.Curves.IsNodalAlgebra` is defined only
for local rings, so neither transfers to the coordinate ring of an affine open. What replaces
the unit argument here is the hypothesis that the inverse of the derivative is given.

## Main results

* `Stacks.DerivationExtension.locDeriv_mem_integralClosure_of_adjoin` — the stabilization of the
  integral closure under `locDeriv`, the statement that the whole question reduces to.
* `Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_adjoin` — the extension of
  a `k`-derivation to `A'` and its uniqueness.
* `Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_quadratic` — the same with
  a single generator satisfying a monic quadratic relation, which is the shape in which the
  normalization of a curve singularity presents itself.

## Implementation notes

The base ring of `Stacks.DerivationExtension.locDeriv` is `ℤ`, so the `k`-linearity of the
restriction is recovered from `D (algebraMap k A c) = 0` rather than inherited. The localization
is kept as a general `L` with `[IsLocalization (nonZeroDivisors A) L]` instead of being
specialised to `FractionRing A`: `Algebra ℤ (FractionRing A)` has a diamond
(`Ring.toIntAlgebra` against the localization's own algebra instance) which makes `leibniz` and
`map_one_eq_zero` fail to typecheck for `locDeriv` at that ring.

The two hypotheses are exactly the two things the elementary argument needs, and nothing here
verifies them: it is the generation of `A'` over `A` by elements with an invertible derivative
that carries the geometric content, and it is false for a general ring extension.

## References

* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open Polynomial

universe u v w

namespace Stacks.DerivationExtension

section Stabilize

variable {A : Type v} {L : Type w} [CommRing A] [CommRing L] [Algebra A L]

/-- **The extension of a derivation to a localization preserves the integral closure, given
generators with invertible derivative.** If the integral closure `A'` of `A` in a localization
`L` is generated as an `A`-algebra by a set `S`, and every `y ∈ S` satisfies a polynomial
relation over `A` whose formal derivative at `y` is invertible in `A'`, then the derivation
`Stacks.DerivationExtension.locDeriv D M L` of Tag 07PE carries `A'` into `A'`. -/
public theorem locDeriv_mem_integralClosure_of_adjoin (D : Derivation ℤ A A) (M : Submonoid A)
    [IsLocalization M L] (S : Set L) (hS : Algebra.adjoin A S = integralClosure A L)
    (hgen : ∀ y ∈ S, ∃ p : A[X], aeval y p = 0 ∧
      ∃ w ∈ integralClosure A L, w * aeval y (derivative p) = 1)
    {z : L} (hz : z ∈ integralClosure A L) :
    locDeriv D M L z ∈ integralClosure A L :=
  Derivation.apply_mem_of_adjoin_eq_of_isUnit_aeval_derivative (locDeriv D M L)
    (integralClosure A L)
    (fun a => by
      rw [locDeriv_algebraMap]
      exact (integralClosure A L).algebraMap_mem (D a))
    S hS hgen hz

end Stabilize

section Extend

variable {k : Type u} {A : Type v} {L : Type w} [Field k] [CommRing A] [Algebra k A]
variable [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
variable [Algebra k L] [IsScalarTower k A L]

omit [IsLocalization (nonZeroDivisors A) L] in
/-- The image in the localization of the image of `a : A` in the integral closure. -/
theorem coe_algebraMap_integralClosure (a : A) :
    ((algebraMap A ↥(integralClosure A L) a : ↥(integralClosure A L)) : L) =
      algebraMap A L a := rfl

omit [IsLocalization (nonZeroDivisors A) L] in
/-- A `k`-scalar multiple in the localization, written multiplicatively. -/
private theorem smul_eq_algebraMap_mul (c : k) (z : L) :
    c • z = algebraMap A L (algebraMap k A c) * z := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k A L]

/-- **A `k`-derivation of `A` extends uniquely to the integral closure of `A` in a localization,
given generators with invertible derivative.** `A` is an arbitrary `k`-algebra — in particular it
need not be local, which is what distinguishes this from
`Stacks.Curves.existsUnique_extend_integralClosure_of_isNodalAlgebra`. -/
public theorem existsUnique_extend_integralClosure_of_adjoin (D : Derivation k A A) (S : Set L)
    (hS : Algebra.adjoin A S = integralClosure A L)
    (hgen : ∀ y ∈ S, ∃ p : A[X], aeval y p = 0 ∧
      ∃ w ∈ integralClosure A L, w * aeval y (derivative p) = 1) :
    ∃! D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L),
      ∀ a : A, D' (algebraMap A ↥(integralClosure A L) a) =
        algebraMap A ↥(integralClosure A L) (D a) := by
  classical
  let DK := locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L
  have hDKa : ∀ a : A, DK (algebraMap A L a) = algebraMap A L (D a) := fun a =>
    locDeriv_algebraMap (D.restrictScalars ℤ) (nonZeroDivisors A) L a
  have hDKk : ∀ c : k, DK (algebraMap A L (algebraMap k A c)) = 0 := by
    intro c
    rw [hDKa, Derivation.map_algebraMap, map_zero]
  have hstab : ∀ t : ↥(integralClosure A L), DK (t : L) ∈ integralClosure A L := fun t =>
    locDeriv_mem_integralClosure_of_adjoin (D.restrictScalars ℤ) (nonZeroDivisors A) S hS hgen t.2
  -- the restriction of `DK` to the integral closure
  let D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L) :=
    { toFun := fun t => ⟨DK (t : L), hstab t⟩
      map_add' := fun t s => Subtype.ext (map_add DK (t : L) (s : L))
      map_smul' := fun c t => by
        apply Subtype.ext
        change DK (c • (t : L)) = c • DK (t : L)
        rw [smul_eq_algebraMap_mul (A := A), smul_eq_algebraMap_mul (A := A), DK.leibniz, hDKk]
        simp only [smul_eq_mul, mul_zero, add_zero]
      map_one_eq_zero' := by
        apply Subtype.ext
        change DK ((1 : ↥(integralClosure A L)) : L) = ((0 : ↥(integralClosure A L)) : L)
        rw [Subalgebra.coe_one, Subalgebra.coe_zero, DK.map_one_eq_zero]
      leibniz' := fun t s => by
        apply Subtype.ext
        change DK ((t : L) * (s : L)) = (t : L) * DK (s : L) + (s : L) * DK (t : L)
        rw [DK.leibniz]
        simp only [smul_eq_mul] }
  have hD'coe : ∀ t : ↥(integralClosure A L),
      ((D' t : ↥(integralClosure A L)) : L) = DK (t : L) := fun _ => rfl
  have hD'ext : ∀ a : A, D' (algebraMap A ↥(integralClosure A L) a) =
      algebraMap A ↥(integralClosure A L) (D a) := by
    intro a
    apply Subtype.ext
    rw [hD'coe, coe_algebraMap_integralClosure, coe_algebraMap_integralClosure, hDKa]
  -- the generators, read inside the integral closure
  have hgen' : ∀ t : ↥(integralClosure A L), (t : L) ∈ S →
      ∃ p : A[X], aeval t p = 0 ∧
        ∃ w : ↥(integralClosure A L), w * aeval t (derivative p) = 1 := by
    intro t ht
    obtain ⟨p, hp, w, hw, hwu⟩ := hgen (t : L) ht
    have hcoe : ∀ q : A[X], ((aeval t q : ↥(integralClosure A L)) : L) = aeval (t : L) q :=
      fun q => (Polynomial.aeval_algHom_apply (integralClosure A L).val t q).symm
    refine ⟨p, Subtype.ext ?_, ⟨w, hw⟩, Subtype.ext ?_⟩
    · rwa [Subalgebra.coe_zero, hcoe]
    · rwa [Subalgebra.coe_one, Subalgebra.coe_mul, hcoe]
  refine ⟨D', hD'ext, fun E hE => ?_⟩
  exact Derivation.ext_of_adjoin_eq_of_isUnit_aeval_derivative (integralClosure A L) S hS E D'
    (fun a => by rw [hE, hD'ext]) hgen'

/-- **The case of no singularity.** If `A` is already integrally closed in the localization, the
extension is the identity statement and the hypotheses above hold with an empty generating set.
This is the half of the affine statement of Tag 0E68 that carries no content: over an affine open
meeting no node the normalization changes nothing. -/
public theorem existsUnique_extend_integralClosure_of_eq_bot (D : Derivation k A A)
    (hbot : integralClosure A L = ⊥) :
    ∃! D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L),
      ∀ a : A, D' (algebraMap A ↥(integralClosure A L) a) =
        algebraMap A ↥(integralClosure A L) (D a) := by
  refine existsUnique_extend_integralClosure_of_adjoin D ∅ ?_ (by simp)
  rw [Algebra.adjoin_empty, hbot]

/-- **The monogenic quadratic case.** The integral closure is `A [t]` for a single `t` with
`t ^ 2 = a + c t`, and `2 t - c` is invertible there: then every `k`-derivation of `A` extends
uniquely to the integral closure. This is the ring-theoretic shape in which the normalization of
a curve at an ordinary double point presents itself, with the invertibility of `2 t - c` — which
the proof of Tag 0E68 obtains from the residues at the two branches — supplied as data. -/
public theorem existsUnique_extend_integralClosure_of_quadratic (D : Derivation k A A) (t : L)
    (a c : A) (hS : Algebra.adjoin A {t} = integralClosure A L)
    (hrel : t * t = algebraMap A L a + algebraMap A L c * t)
    (w : L) (hw : w ∈ integralClosure A L)
    (hwu : w * (t + t - algebraMap A L c) = 1) :
    ∃! D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L),
      ∀ b : A, D' (algebraMap A ↥(integralClosure A L) b) =
        algebraMap A ↥(integralClosure A L) (D b) := by
  refine existsUnique_extend_integralClosure_of_adjoin D {t} hS ?_
  rintro _ rfl
  refine ⟨X ^ 2 - C c * X - C a, ?_, w, hw, ?_⟩
  · simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C]
    linear_combination hrel
  · rw [show derivative (X ^ 2 - C c * X - C a) = C 2 * X - C c by
      simp only [derivative_sub, derivative_mul, derivative_pow, derivative_X, derivative_C]
      ring_nf]
    simp only [map_sub, map_mul, aeval_X, aeval_C, map_ofNat]
    linear_combination hwu

end Extend

section FractionRing

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- **The same at the total ring of fractions**, which is the ring in which the rest of the
development takes the normalization of a curve singularity. `A` is not assumed local. -/
public theorem existsUnique_extend_integralClosure_fractionRing_of_adjoin
    (D : Derivation k A A) (S : Set (FractionRing A))
    (hS : Algebra.adjoin A S = integralClosure A (FractionRing A))
    (hgen : ∀ y ∈ S, ∃ p : A[X], aeval y p = 0 ∧
      ∃ w ∈ integralClosure A (FractionRing A), w * aeval y (derivative p) = 1) :
    ∃! D' : Derivation k ↥(integralClosure A (FractionRing A))
        ↥(integralClosure A (FractionRing A)),
      ∀ a : A, D' (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
        algebraMap A ↥(integralClosure A (FractionRing A)) (D a) :=
  existsUnique_extend_integralClosure_of_adjoin D S hS hgen

end FractionRing

end Stacks.DerivationExtension

end
