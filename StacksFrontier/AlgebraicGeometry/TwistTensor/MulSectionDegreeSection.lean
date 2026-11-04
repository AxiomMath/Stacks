module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Bijectivity
public import StacksFrontier.AlgebraicGeometry.TwistTensor.MultiplicationAssociativity

/-!
# Equation 01MO on the global sections attached to two homogeneous elements

Let `S` be a graded ring with grading `𝒮`. A homogeneous element of degree `n` has a canonical
global section `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` of the `n`-th twist on
`Proj S`, whose value at a point is the fraction `a / 1`. This file records that the canonical
multiplication of the twists, Equation 01MO, carries the pair of sections attached to two
homogeneous elements to the section attached to their product:

`𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)`,  `a / 1 ⊗ b / 1 ↦ ab / 1`.

Pointwise that is `LocalizedModule.mk_mul_mk`, so the proof is the extensionality of local
sections of a twist together with the pointwise formula
`Stacks.AlgebraicGeometry.TwistTensor.mulSection_apply` for the product.

## Why it is stated here

It is the **twist half** of the sections-side compatibility that the monomial symbol system of
[Stacks, Tag 0C2K] needs; see
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistSuccessor.lean`. The successor
comparison of `AlgebraicGeometry.projectiveLineTwistPowerSystem` is Equation 01MO at `(d, 1)`,
and the symbol of a product of functions has to be the product of their symbols as binary forms;
reading that off asks exactly for the statement below, in the degrees `(d, 1)`.

The statement is made for an arbitrary pair of natural-number degrees and an arbitrary graded
ring, where it costs nothing more. It is not stated for integer degrees: `degreeSection` is
attached to an element homogeneous of a natural-number degree, and a negative twist has no such
section to multiply.

`Stacks.AlgebraicGeometry.ThetaGlobal.twistMulModules_degreeSection` is the same content at the
`d`-divisible degrees `(d · n, d · m)` and through the retyping `twistMulModules` of the
comparison family `Stacks.AlgebraicGeometry.ThetaGlobal.theta`; this one is at
`Stacks.AlgebraicGeometry.TwistTensor.mulSection`, the product of two local sections, which is
the form a power system's successor comparison presents, and it needs no
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.DegreeOneCover` hypothesis because it is about
the multiplication *map* and not about its being an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.TwistTensor.mulSection_degreeSection` — **the product of the global
  sections attached to two homogeneous elements is the global section attached to their
  product**, modulo the transport along `n + m = n + m` read in `ℤ`.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace Stacks.AlgebraicGeometry.TwistTensor

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Equation 01MO carries the pair of global sections attached to two homogeneous elements to
the global section attached to their product.** The product element is supplied separately
together with the equation pinning it down, so that the caller chooses the degree in which it is
homogeneous; the transport is along `(n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ)`, which is the one the
successor comparison of a power system of twists carries.

Pointwise the two sides are `a / 1 · b / 1` and `ab / 1`. -/
public theorem mulSection_degreeSection (n m : ℕ) (a : 𝒮 n) (b : 𝒮 m) (ab : 𝒮 (n + m))
    (hab : (ab : S) = (a : S) * (b : S)) :
    (eqToHom (congrArg (twist 𝒮)
          (show (n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ) by push_cast; ring))).val.app
        (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
        (mulSection 𝒮 (n : ℤ) (m : ℤ) (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
          (degreeSection 𝒮 n a) (degreeSection 𝒮 m b)) =
      degreeSection 𝒮 (n + m) ab := by
  refine twist_section_ext 𝒮 (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) _ _ fun z => ?_
  refine Eq.trans (eqToHom_twist_val_app_apply 𝒮
    (show (n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ) by push_cast; ring)
    (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) _ z) ?_
  refine Eq.trans (mulSection_apply 𝒮 (n : ℤ) (m : ℤ)
    (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) _ _ z) ?_
  rw [ProjTwistSections.degreeSection_apply, ProjTwistSections.degreeSection_apply,
    ProjTwistSections.degreeSection_apply, hab]
  exact Eq.trans LocalizedModule.mk_mul_mk
    (congrArg (LocalizedModule.mk ((a : S) * (b : S))) (mul_one 1))

end Stacks.AlgebraicGeometry.TwistTensor

end
