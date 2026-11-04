module

public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Cover
public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Criterion

/-!
# Relative rigidity of the graded twists for a nested pair of affine opens

Let `A` be a quasi-coherent graded `𝒪_S`-algebra in the sheaf-theoretic form of Situation 01NN
and let `U ⊆ V` be a nested pair of affine opens of `S`. This file proves that a multiplicative
family of endomorphisms of the twists on `Proj Γ(U, A)` which fixes the global section of `𝒪(k)`
attached to `A.res h c` for every homogeneous `c` of degree `k` of the graded ring of sections
over the *larger* open consists of identity morphisms.

That hypothesis is the one Tag 01NO's twist comparison supplies:
`Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection` computes the
six-factor comparison map on a pulled-back homogeneous global section and lands on exactly
`degreeSection (A.grading U) k ⟨A.res h c, (A.res h).map_mem c.2⟩`. The absolute statement
`Stacks.AlgebraicGeometry.TwistRigidity.eq_id` cannot consume it: that one needs the family to
fix `degreeSection (A.grading U) k c` for **every** `c : A.grading U k`, which by definition is
every element of `Γ(U, A_k)`, and `Γ(V, A_k) → Γ(U, A_k)` is not surjective. The hypothesis is
not weakenable by inspection either, since
`Stacks.AlgebraicGeometry.TwistRigidity.app_eq_self_of_isFraction` consumes an arbitrary
homogeneous numerator as well as an arbitrary denominator.

## Main results

* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.generates_res`: **restriction along a nested
  pair of affine opens generates pointwise.** This is the geometric input.
* `Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res`: **relative rigidity.**

## The route

The two halves are separated completely. The abstract half, in
`StacksFrontier/AlgebraicGeometry/RelativeTwistRigidity/Criterion.lean`, weakens
`Stacks.AlgebraicGeometry.TwistRigidity.eq_id`'s hypothesis from all homogeneous elements to the
image of a graded ring homomorphism `ψ : ℬ →+*ᵍ 𝒜`, given that `ψ` *generates* `𝒜` pointwise:
every homogeneous `a` becomes an image of `ψ` after multiplication by a degree-zero image of `ψ`
nonvanishing at a prescribed point of `Proj 𝒜`. The geometric half, in the sibling `Cover.lean`,
provides that for `ψ = A.res h`, and this file is the one-line join.

**The covering step was needed, and it happens on the base, not on `Proj`.** `U` need not be a
basic open of `V`, so no single function of `V` inverts into surjectivity. But `U` is covered by
the basic opens of `V` that it contains, those cut out a family of functions spanning the unit
ideal of `Γ(S, U)`, and the degree-`0` elements they give in the graded ring of sections over `U`
therefore cannot all lie in one relevant homogeneous prime. So at each point of `Proj Γ(U, A)`
one of them is nonvanishing, and the multiplier is chosen anew at each point. No covering of
`Proj Γ(U, A)` is involved, and in particular nothing is needed about how the relative Proj over
`U` is glued from the relative Projs over the members of the cover — which is what a
Proj-level covering argument would have required.

## Implementation notes

The hypothesis the consumer must discharge, `FixesResDegreeSections (A.res h) α`, is spelled with
the subtype element `⟨A.res h c, (A.res h).map_mem c.2⟩`, character-for-character the right-hand
side of `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.composite_degreeSection`.

Everything in this file is at the concrete instance of the graded ring, where the elaboration
budget is tight; see the implementation notes of `Criterion.lean` for the measurement. The goal
of `generates_res` is a statement about ring elements and a prime ideal only, with no sheaf in
it, which is why it can be proved in tactic mode at all; `eq_id_res` is a single term.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)

## What is not done here

The cocycle for Tag 01NO's twist comparisons is not assembled, and neither is
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData`. What this file supplies is the
uniqueness input they need: the comparison maps are determined, so a composite of two of them
against the inverse of the third is forced to be the identity once it is known to be
multiplicative and to fix the restricted homogeneous sections. Multiplicativity of that composite
is not proved here. The twist datum itself is available —
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` builds one from a
quasi-coherent graded algebra with no further hypothesis — so what is owed is the multiplicativity,
not the datum.

No tag is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.TwistRigidity

namespace Stacks.AlgebraicGeometry.RelativeTwistRigidity

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible]
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U V : S.Opens) (h : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V)

include hU hV

/-- **Restriction along a nested pair of affine opens generates pointwise.** For every degree
`k`, every homogeneous element `a` of the graded ring of sections over `U` and every point `x` of
`Proj Γ(U, A)`, there are a degree-`0` element `d` and a degree-`k` element `c` of the graded ring
of sections over `V` such that the restriction of `d` does not vanish at `x` and `a` times the
restriction of `d` is the restriction of `c`.

The multiplier is chosen at each point: `A.res h` itself is not surjective in any degree. -/
public theorem generates_res : Generates (A.res h) := by
  intro k a x
  obtain ⟨f, hf, hnv⟩ := exists_basicOpen_strHom_notMem A h hU hV x
  obtain ⟨N, c, hc⟩ := exists_pow_mul_eq_res A h hU hV f hf k a
  refine ⟨⟨A.strHom V (f ^ N), A.strHom_mem V _⟩, c, ?_, ?_⟩
  · rw [res_apply A, A.resRingHom_strHom, map_pow, map_pow]
    exact Submonoid.pow_mem (Ideal.primeCompl x.asHomogeneousIdeal.toIdeal) hnv N
  · rw [res_apply A, A.resRingHom_strHom, map_pow]
    exact hc

/-- **Relative rigidity.** A multiplicative family of endomorphisms of the twists on
`Proj Γ(U, A)` which fixes, for every degree `k`, the global section of `𝒪(k)` attached to the
restriction of each homogeneous element of degree `k` of the graded ring of sections over a
larger affine open is the identity in every integer degree.

Nothing is assumed about the homogeneous sections attached to the elements of `Γ(U, A_k)` that
are not restrictions, and those are the vast majority: the restriction map is not surjective. -/
public theorem eq_id_res
    {α : ∀ n : ℤ, twistingSheaf (A.grading U) n ⟶ twistingSheaf (A.grading U) n}
    (hmul : IsMultiplicative α) (hfix : FixesResDegreeSections (A.res h) α) (n : ℤ) :
    α n = 𝟙 (twistingSheaf (A.grading U) n) :=
  eq_id hmul (generates_res A U V h hU hV) hfix n

end Stacks.AlgebraicGeometry.RelativeTwistRigidity

end
