module

public import StacksFrontier.RingTheory.Derivation.IntegralClosureExtension

/-!
# A derivation of the integral closure in a localization is determined on the base

Let `A` be a commutative ring, let `L` be a localization of `A` at its nonzerodivisors and let
`A' = integralClosure A L`. Two `k`-derivations of `A'` which agree on the image of `A` are
equal.

The reason is that `A'` sits between `A` and `L`, so every `z : A'` satisfies an equation
`s • z = a` with `a : A` and `s` a nonzerodivisor of `A`; the Leibniz rule turns that equation
into `s • D' z = D a - z • D s`, which determines `D' z` because the image of `s` in `A'` can be
cancelled — it is a unit already in `L`, and `A' → L` is injective.

Nothing here is local and nothing here is about curves: no hypothesis relates `A'` to `A`
beyond its being the integral closure in a localization. That matters because the extension of
a derivation to `A'` is produced by different arguments on different parts of a curve — by
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_eq_bot` where the
normalization changes nothing, and by the conductor of
`Stacks.Curves.existsUnique_extend_integralClosure_branchResidues_of_isNodalAlgebra` at a node —
and the two have to be recognised as the same derivation wherever both apply.

## Main results

* `Stacks.DerivationExtension.mul_left_cancel_algebraMap_integralClosure` — the image in the
  integral closure of a nonzerodivisor of the base can be cancelled.
* `Stacks.DerivationExtension.extend_integralClosure_unique` — **two `k`-derivations of the
  integral closure agreeing on the base are equal.**
* `Stacks.DerivationExtension.eq_of_leibniz_of_algebraMap` — the same with no base ring, for
  additive maps obeying the Leibniz rule.
* `Stacks.DerivationExtension.extend_integralClosure_unique_fractionRing` — the same at the total
  ring of fractions.
* `Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_stable` — the extension
  exists, and is then unique, as soon as the canonical extension to the localization carries
  integral elements to integral elements.

## References

* [Stacks Project, Tag 07PE](https://stacks.math.columbia.edu/tag/07PE)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.DerivationExtension

section Cancel

variable {A : Type v} {L : Type w} [CommRing A] [CommRing L] [Algebra A L]
variable [IsLocalization (nonZeroDivisors A) L]

/-- **The image of a nonzerodivisor of `A` in the integral closure can be cancelled.** It becomes
a unit in `L` and the integral closure is a subring of `L`. -/
public theorem mul_left_cancel_algebraMap_integralClosure {s : A} (hs : s ∈ nonZeroDivisors A)
    {x y : ↥(integralClosure A L)}
    (h : algebraMap A ↥(integralClosure A L) s * x
        = algebraMap A ↥(integralClosure A L) s * y) :
    x = y := by
  refine Subtype.ext ((IsLocalization.map_units L ⟨s, hs⟩).mul_left_cancel ?_)
  simpa using congrArg Subtype.val h

/-- **A Leibniz additive map on the integral closure is determined by its restriction to the
base.** This is `Stacks.DerivationExtension.extend_integralClosure_unique` with no base ring at
all: the gluing of vector fields on a scheme consumes additive maps obeying the Leibniz rule
rather than bundled derivations, and the argument never uses linearity over anything. -/
public theorem eq_of_leibniz_of_algebraMap
    (f g : ↥(integralClosure A L) →+ ↥(integralClosure A L))
    (hf : ∀ x y : ↥(integralClosure A L), f (x * y) = x * f y + y * f x)
    (hg : ∀ x y : ↥(integralClosure A L), g (x * y) = x * g y + y * g x)
    (h : ∀ a : A, f (algebraMap A ↥(integralClosure A L) a)
      = g (algebraMap A ↥(integralClosure A L) a)) :
    f = g := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors A) (z : L)
  have hzA : z * algebraMap A ↥(integralClosure A L) (s : A)
      = algebraMap A ↥(integralClosure A L) a := by
    refine Subtype.ext ?_
    simpa using hz
  have hf' := hf z (algebraMap A ↥(integralClosure A L) (s : A))
  have hg' := hg z (algebraMap A ↥(integralClosure A L) (s : A))
  rw [hzA] at hf' hg'
  refine mul_left_cancel_algebraMap_integralClosure s.2 ?_
  have hfa := h a
  rw [hf', h (s : A), hg'] at hfa
  linear_combination hfa

end Cancel

section Unique

variable {k : Type u} {A : Type v} {L : Type w} [Field k] [CommRing A] [Algebra k A]
variable [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
variable [Algebra k L] [IsScalarTower k A L]

/-- **A `k`-derivation of the integral closure of `A` in a localization is determined by its
restriction to `A`.** No hypothesis on `A` or on the integral closure is needed. -/
public theorem extend_integralClosure_unique (D : Derivation k A A)
    (E₁ E₂ : Derivation k ↥(integralClosure A L) ↥(integralClosure A L))
    (h₁ : ∀ a : A, E₁ (algebraMap A ↥(integralClosure A L) a)
      = algebraMap A ↥(integralClosure A L) (D a))
    (h₂ : ∀ a : A, E₂ (algebraMap A ↥(integralClosure A L) a)
      = algebraMap A ↥(integralClosure A L) (D a)) :
    E₁ = E₂ := by
  refine Derivation.ext fun z => ?_
  have := eq_of_leibniz_of_algebraMap E₁.toLinearMap.toAddMonoidHom E₂.toLinearMap.toAddMonoidHom
    (fun x y => by simp [E₁.leibniz x y]) (fun x y => by simp [E₂.leibniz x y])
    (fun a => (h₁ a).trans (h₂ a).symm)
  exact DFunLike.congr_fun this z

end Unique

section FractionRing

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- **The same at the total ring of fractions**, which is the ring in which the normalization of
a curve is taken. -/
public theorem extend_integralClosure_unique_fractionRing (D : Derivation k A A)
    (E₁ E₂ : Derivation k ↥(integralClosure A (FractionRing A))
      ↥(integralClosure A (FractionRing A)))
    (h₁ : ∀ a : A, E₁ (algebraMap A ↥(integralClosure A (FractionRing A)) a)
      = algebraMap A ↥(integralClosure A (FractionRing A)) (D a))
    (h₂ : ∀ a : A, E₂ (algebraMap A ↥(integralClosure A (FractionRing A)) a)
      = algebraMap A ↥(integralClosure A (FractionRing A)) (D a)) :
    E₁ = E₂ :=
  extend_integralClosure_unique D E₁ E₂ h₁ h₂

end FractionRing

section Stable

variable {k : Type u} {A : Type v} {L : Type w} [Field k] [CommRing A] [Algebra k A]
variable [CommRing L] [Algebra A L] [IsLocalization (nonZeroDivisors A) L]
variable [Algebra k L] [IsScalarTower k A L]

/-- **A `k`-derivation of `A` extends to the integral closure, uniquely, as soon as its canonical
extension to the localization preserves it.** The extension to `L` is `locDeriv` of Tag 07PE, so
the whole question of extending a derivation to a normalization is the single condition that
`locDeriv D` carry integral elements to integral elements.

This is `Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_adjoin` with the
stabilization taken as the hypothesis instead of being deduced from a generating set with
invertible derivative. The point of separating them is that the generators are not available
globally: on an affine open of a nodal curve the derivative `2 t - c` of the quadratic relation is
a unit only at the points above the nodes, and it genuinely vanishes elsewhere — on
`A = {h ∈ k[s] : h 1 = h (-1)}` with `A' = k[s]`, where `t = s` and `s ^ 2 = 1`, the derivative
`2 s` vanishes at the smooth point `s = 0`. Stabilization, unlike the generators, is a local
condition and can be checked one maximal ideal at a time. -/
public theorem existsUnique_extend_integralClosure_of_stable (D : Derivation k A A)
    (hstab : ∀ z : ↥(integralClosure A L),
      locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L (z : L) ∈ integralClosure A L) :
    ∃! D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L),
      ∀ a : A, D' (algebraMap A ↥(integralClosure A L) a)
        = algebraMap A ↥(integralClosure A L) (D a) := by
  classical
  let DK := locDeriv (D.restrictScalars ℤ) (nonZeroDivisors A) L
  have hDKa : ∀ a : A, DK (algebraMap A L a) = algebraMap A L (D a) := fun a =>
    locDeriv_algebraMap (D.restrictScalars ℤ) (nonZeroDivisors A) L a
  have hDKk : ∀ c : k, DK (algebraMap A L (algebraMap k A c)) = 0 := by
    intro c
    rw [hDKa, Derivation.map_algebraMap, map_zero]
  have hsm : ∀ (c : k) (z : L), c • z = algebraMap A L (algebraMap k A c) * z := by
    intro c z
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k A L]
  let D' : Derivation k ↥(integralClosure A L) ↥(integralClosure A L) :=
    { toFun := fun t => ⟨DK (t : L), hstab t⟩
      map_add' := fun t s => Subtype.ext (map_add DK (t : L) (s : L))
      map_smul' := fun c t => by
        apply Subtype.ext
        show DK (c • (t : L)) = c • DK (t : L)
        rw [hsm c (t : L), hsm c (DK (t : L)), DK.leibniz, hDKk]
        simp only [smul_eq_mul, mul_zero, add_zero]
      map_one_eq_zero' := Subtype.ext DK.map_one_eq_zero
      leibniz' := fun t s => by
        apply Subtype.ext
        show DK ((t : L) * (s : L)) = (t : L) * DK (s : L) + (s : L) * DK (t : L)
        rw [DK.leibniz]
        simp only [smul_eq_mul] }
  have hD'ext : ∀ a : A, D' (algebraMap A ↥(integralClosure A L) a)
      = algebraMap A ↥(integralClosure A L) (D a) := fun a => Subtype.ext (hDKa a)
  exact ⟨D', hD'ext, fun E hE => extend_integralClosure_unique D E D' hE hD'ext⟩

end Stable

end Stacks.DerivationExtension

end
