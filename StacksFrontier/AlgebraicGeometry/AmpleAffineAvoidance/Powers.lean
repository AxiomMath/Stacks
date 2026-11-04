module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.FromAmple

/-!
# Two homogeneous sections of a common degree

`StacksFrontier/AlgebraicGeometry/AmpleAffineAvoidance/Basic.lean` divides one section of an
invertible module by another. The two sections it divides have to be sections of the *same*
module, and the two that part (3) of Stacks Tag 01ZY produces are not: graded prime avoidance
returns a homogeneous element `a` of `Γ_*(X, L)` of some degree `d ≥ 1`, while ampleness returns,
at each point, a homogeneous `b` of some unrelated degree `n ≥ 1`. This file replaces each by a
power of itself, in the common degree `d n`, which changes neither nonvanishing locus.

## The route

`Stacks.AmpleFiniteAvoidance.nvLocus_mul` — `X_{st} = X_s ∩ X_t`, the product lemma — gives
`X_{s^k} = X_s` for `k ≥ 1` by a two-line induction. The degree bookkeeping is arranged so that no
transport appears in the induction: `Stacks.GradedSections.mul` lands in degree `n + m` on the
nose, and `n * (k + 1 + 1)` reduces to `n * (k + 1) + n` definitionally, so the inductive step is
literally a product. The one transport is at the base case, where `n` and `n * (0 + 1)` are equal
but not definitionally so; `Stacks.AmpleAffineAvoidance.nvLocus_comp_eqToHom` says a transport of
a homogeneous element along an equality of degrees leaves its nonvanishing locus alone, which is
`Stacks.Ample.nonvanishingLocus_congr` at an `eqToIso`.

Passing from "every positive multiple of the degree" to "the common degree `d n`" is then
divisibility: `Stacks.AmpleAffineAvoidance.exists_pow_of_dvd` substitutes the factorisation of the
target degree, so the statement in the awkward shape `n * (k + 1)` is never rewritten in the type.

## Main results

* `Stacks.AmpleAffineAvoidance.exists_pow_succ`: `X_{s^{k+1}} = X_s`.
* `Stacks.AmpleAffineAvoidance.exists_pow_of_dvd`: a homogeneous element of degree `n` has a power
  in every positive degree divisible by `n`, with the same nonvanishing locus.
* `Stacks.AmpleAffineAvoidance.exists_common_degree`: **two homogeneous elements of positive
  degrees have powers of one common degree**, with the two original nonvanishing loci.

## Implementation notes

The local monoidal instances are the exact list that
`StacksFrontier/AlgebraicGeometry/AmpleFiniteAvoidance/Basic.lean` installs, and for the same
reason: `Stacks.GradedSections.powSections` and `Stacks.GradedSections.mul` are stated for an
abstract monoidal category. As in that file, `Stacks.SectionRingGeometric.schemeSectionCommRing`
is deliberately *not* installed — nothing here mentions the ring structure of `Γ_*(X, L)`, only
the degreewise product, so the hazard it causes for `GradedRing` synthesis is avoided by not
needing a ring at all.

The results are existential rather than a `pow` definition. A definition would have to name the
degree `n * (k + 1)`, and every consumer would then carry that arithmetic in its types; the
existential lets the degree be destructured once, at the point of use.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)

## What is not done

No tag attribute is attached. Nothing here is about the ring structure of the section ring, about
its grading, or about ampleness; and no power is identified with a power of the *ring* element
`DirectSum.of _ d a` — only the degreewise product is used, so no formula for the components of a
product of inhomogeneous elements is needed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.GradedSections Stacks.SectionProduct Stacks.AmpleFiniteAvoidance

universe u

namespace Stacks.AmpleAffineAvoidance

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

omit [IsInvertibleModule X L] in
/-- Transporting a homogeneous element along an equality of degrees leaves its nonvanishing
locus alone. -/
theorem nvLocus_comp_eqToHom {n m : ℕ} (h : n = m) (s : powSections L n) :
    nvLocus L (s ≫ eqToHom (congrArg (Stacks.TensorPowers.natTensorPow L) h)) = nvLocus L s := by
  rw [nvLocus, globalSection_comp]
  exact nonvanishingLocus_congr
    (eqToIso (congrArg (Stacks.TensorPowers.natTensorPow L) h)) _

/-- **The powers of a homogeneous element have its nonvanishing locus.** -/
theorem exists_pow_succ {n : ℕ} (s : powSections L n) (k : ℕ) :
    ∃ t : powSections L (n * (k + 1)), nvLocus L t = nvLocus L s := by
  induction k with
  | zero =>
      have h : n = n * (0 + 1) := by omega
      exact ⟨s ≫ eqToHom (congrArg (Stacks.TensorPowers.natTensorPow L) h),
        nvLocus_comp_eqToHom L h s⟩
  | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨Stacks.GradedSections.mul t s, ?_⟩
      rw [nvLocus_mul, ht, Set.inter_self]

/-- **A homogeneous element has a power in every positive degree it divides.** -/
theorem exists_pow_of_dvd {n m : ℕ} (s : powSections L n) (h : n ∣ m) (hm : 1 ≤ m) :
    ∃ t : powSections L m, nvLocus L t = nvLocus L s := by
  obtain ⟨k, rfl⟩ := h
  match k with
  | 0 => simp at hm
  | j + 1 => exact exists_pow_succ L s j

/-- **Two homogeneous elements of positive degree have powers of a common degree.** -/
theorem exists_common_degree {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (a : powSections L d) (b : powSections L n) :
    ∃ (m : ℕ) (a' b' : powSections L m), 1 ≤ m ∧ nvLocus L a' = nvLocus L a ∧
      nvLocus L b' = nvLocus L b := by
  have hm : 1 ≤ d * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨a', ha'⟩ := exists_pow_of_dvd L a (Dvd.intro n rfl) hm
  obtain ⟨b', hb'⟩ := exists_pow_of_dvd L b (Dvd.intro_left d rfl) hm
  exact ⟨d * n, a', b', hm, ha', hb'⟩

end Stacks.AmpleAffineAvoidance

end
