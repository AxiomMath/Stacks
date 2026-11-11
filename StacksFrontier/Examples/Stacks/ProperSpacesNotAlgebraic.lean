module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesNonEffectiveSurface
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.K3Surface
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite

/-!
# The stack of proper algebraic spaces is not algebraic: the assembly (Stacks 0D1R)

Stacks 0D1R: the stack in groupoids `p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶
Sch_fppf` whose category of sections over a scheme `S` is the category of flat, proper, finitely
presented algebraic spaces over `S` is not an algebraic stack. The base is the absolute big fppf
site `Sch_fppf`, i.e. the big fppf site of `Spec ℤ`, which in this library is
`AlgebraicGeometry.integerBase`.

The source's proof: if it were an algebraic stack, every formal object would be effective
(Stacks 07X8); the discussion before the lemma shows that this is not the case after base change
to `Spec ℂ` (and, by its footnote, after base change to `Spec k` for any field `k` of
characteristic zero). This file assembles that proof:

* the deduction from a non-effective formal object over `Spec k` to non-algebraicity over
  `Spec ℤ`, through the base change `Spec k ⟶ Spec ℤ`
  (`AlgebraicGeometry.not_isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase`);
* the existence of a non-effective formal object over `Spec k`, for every field `k` of
  characteristic zero: the versal formal deformation of the Fermat quartic surface
  `x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴ = 0` in `ℙ³_k`, a K3 surface
  (`AlgebraicGeometry.properFlatSpacesNonEffectiveInput`, from
  `AlgebraicGeometry.ProperFlatSpaceOfScheme.exists_not_isEffective_of_surface`);
* Stacks 0D1R itself, `AlgebraicGeometry.not_isAlgebraicStack_cartesianProperFlatBasedCategory`,
  with `k = ℚ`.

## Main definitions

* `AlgebraicGeometry.ProperFlatSpacesNonEffectiveInput`: `p'_{fp, flat, proper}` over `Spec k`
  has a formal object that is not effective.

## Main results

* `AlgebraicGeometry.properFlatSpacesNonEffectiveInput`: the input holds over every field of
  characteristic zero in the site.
* `AlgebraicGeometry.not_isAlgebraicStack_cartesianProperFlatBasedCategory`: **Stacks 0D1R**.

* `AlgebraicGeometry.not_isAlgebraicStack_cartesianProperFlatBasedCategory_of_nonEffectiveInput`:
  a non-effective formal object over `Spec k`, with `Spec k ⟶ S` a morphism of the site, shows
  that `p'_{fp, flat, proper}` over `S` is not algebraic.
* `not_isAlgebraicStack_cartesianProperFlatBasedCategory_integerBase_of_nonEffectiveInput`, in
  the namespace `AlgebraicGeometry`: the statement of Stacks 0D1R over `Spec ℤ`, from the input
  over a field of characteristic zero.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

/-- **The input of Stacks 0D1R from "the discussion above".** The stack `p'_{fp, flat, proper}`
over the big fppf site of `Spec k` has a formal object (Stacks 07X3) that is not effective
(Stacks 07X7). In the source, for `k = ℂ` (or any field of characteristic zero), this formal
object is the universal deformation of a general smooth quartic surface `X ⊂ ℙ³_k` over
`k⟦x₁, …, x₂₀⟧`. -/
def ProperFlatSpacesNonEffectiveInput (B : BigFppfSite.{u}) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) : Prop :=
  ∃ ξ : Deformation.Artin.FormalObject B (Spec (.of k)) hk
      (cartesianProperFlatProjection B (Spec (.of k)) hk),
    ¬ Deformation.Artin.FormalObject.IsEffective B (Spec (.of k)) hk
      (cartesianProperFlatProjection B (Spec (.of k)) hk)
      (cartesianProperFlatProjection_isFiberedInGroupoids B (Spec (.of k)) hk) ξ

/-- **The assembly of Stacks 0D1R over an arbitrary base.** If `p'_{fp, flat, proper}` over
`Spec k` has a non-effective formal object and `Spec k ⟶ S` is a morphism of the big fppf site,
then `p'_{fp, flat, proper}` over `S` is not an algebraic stack. -/
theorem not_isAlgebraicStack_cartesianProperFlatBasedCategory_of_nonEffectiveInput
    (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    {S : Scheme.{u}} (hS : B.Contains S) (f : B.obj hk ⟶ B.obj hS)
    (h : ProperFlatSpacesNonEffectiveInput B k hk) :
    ¬ Stack.IsAlgebraicStack.{u, w} B S hS (cartesianProperFlatBasedCategory B S hS) :=
  let ⟨ξ, hξ⟩ := h
  not_isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase f ξ hξ

/-- **Stacks 0D1R, assembled from its one remaining input.** The stack
`p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶ Sch_fppf` of flat, proper, finitely
presented algebraic spaces, over the big fppf site of `Spec ℤ`, is not an algebraic stack, provided
`p'_{fp, flat, proper}` over `Spec k` has a non-effective formal object for some field `k` of
characteristic zero contained in the site (`AlgebraicGeometry.ProperFlatSpacesNonEffectiveInput`,
the content of the discussion before the lemma).

The input is `AlgebraicGeometry.properFlatSpacesNonEffectiveInput`; the unconditional statement
is `AlgebraicGeometry.not_isAlgebraicStack_cartesianProperFlatBasedCategory`. The
characteristic-zero hypothesis is not used by the deduction itself; it records the setting in
which the source establishes the input. -/
theorem not_isAlgebraicStack_cartesianProperFlatBasedCategory_integerBase_of_nonEffectiveInput
    (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) (k : Type u) [Field k] [CharZero k]
    (hk : B.Contains (Spec (.of k))) (h : ProperFlatSpacesNonEffectiveInput B k hk) :
    ¬ Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (cartesianProperFlatBasedCategory B integerBase hZ) :=
  not_isAlgebraicStack_cartesianProperFlatBasedCategory_of_nonEffectiveInput B k hk hZ
    (ObjectProperty.homMk (specULiftZIsTerminal.from _)) h

/-- **The input of Stacks 0D1R** ("the discussion above" in [Stacks, Section 0D1Q]): for every
field `k` of characteristic zero with `Spec k` in the site, `p'_{fp, flat, proper}` over `Spec k`
has a non-effective formal object, namely the versal formal deformation of the Fermat quartic
surface in `ℙ³_k`, a smooth quartic (K3) surface. -/
theorem properFlatSpacesNonEffectiveInput (B : BigFppfSite.{u}) (k : Type u) [Field k]
    [CharZero k] (hk : B.Contains (Spec (.of k))) : ProperFlatSpacesNonEffectiveInput B k hk :=
  haveI : NeZero (2 : k) := ⟨two_ne_zero⟩
  ProperFlatSpaceOfScheme.exists_not_isEffective_of_surface B k hk (FermatQuartic.toSpec k)
    (FermatQuartic.isProjective_toSpec k) (FermatQuartic.relativeDimension_toSpec k)
    (FermatQuartic.equidimensional_fermatQuartic k)
    (FermatQuartic.topologicalKrullDim_fermatQuartic k)
    (FermatQuartic.isZero_cohomology_one_unit k)
    (FermatQuartic.nonempty_dualizingModule_iso_unit k)
    (FermatQuartic.subsingleton_ext_relativeDifferentials_unit k)

/-- **Stacks 0D1R.** The stack in groupoids
`p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶ Sch_fppf` whose category of sections over
a scheme `S` is the category of flat, proper, finitely presented algebraic spaces over `S`, over
the big fppf site of `Spec ℤ` (any big fppf site `B`, as in Stacks 021R), is not an algebraic
stack.

As in the source, the proof is: an algebraic stack has effective formal objects (07X8), but over
`Spec ℚ` the versal formal deformation of a smooth quartic surface (here the Fermat quartic) is a
non-effective formal object (`AlgebraicGeometry.properFlatSpacesNonEffectiveInput`), and
algebraicity over `Spec ℤ` would give algebraicity over `Spec ℚ`. The source argues over `ℂ`; by
its footnote any field of characteristic zero works, and `ℚ` (lifted to the universe `u`) is
used here. -/
@[stacks 0D1R]
theorem not_isAlgebraicStack_cartesianProperFlatBasedCategory (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) :
    ¬ Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (cartesianProperFlatBasedCategory B integerBase hZ) :=
  haveI : CharZero (ULift.{u} ℚ) := (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).toRingHom.charZero
  have hQ : B.Contains (Spec (.of (ULift.{u} ℚ))) :=
    BigFppfSite.contains_spec_of_mk_lt_cutoff B (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)
  not_isAlgebraicStack_cartesianProperFlatBasedCategory_integerBase_of_nonEffectiveInput B hZ
    (ULift.{u} ℚ) hQ (properFlatSpacesNonEffectiveInput B (ULift.{u} ℚ) hQ)

end AlgebraicGeometry

end
