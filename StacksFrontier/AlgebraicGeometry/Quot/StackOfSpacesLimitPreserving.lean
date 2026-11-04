module

public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# The stack `Spaces'_{fp, flat, proper}` is limit preserving, from the size-free descent results

Stacks 0D1I asserts that the stack `p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶ Sch_fppf`
of Stacks 0D1D is limit preserving in the sense of Stacks 07XL. Its proof combines Stacks 07SK
(algebraic spaces of finite presentation over `T = lim Tᵢ` form the colimit of those over the
`Tᵢ`) with the descent of flatness and properness through the limit, Stacks 08K0 and 08K1.

This file assembles that proof from the five propositions of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SiteConventionDescentInputs.lean`, which state those
three results in the form in which they hold under the chapter's convention of Section 70.2 (tag
07SD) with no bound on the size of the index; the convention itself holds for the systems of
Stacks 07XL by `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_isLimit`. The five
propositions are proved, and Stacks 0D1I registered, in
`StacksFrontier/AlgebraicGeometry/Quot/StackOfSpacesLimitPreservingUnconditional.lean`.

## Main results

* `AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory_of_descent`.

## Implementation notes

The base of the source's stack is `Sch_fppf`, the big fppf site of `Spec(ℤ)`; as for Stacks 0D1D
and 0D1E in this library, the base here is the big fppf site of an arbitrary scheme `S` of the
site, which recovers the source at `S = Spec(ℤ)`. The index categories of Stacks 07XL are taken in
the scheme universe, which is the smallness the source's directed sets have.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The stack `Spaces'_{fp, flat, proper}` of finitely presented, flat and proper families of
algebraic spaces is limit preserving (Stacks 07XL), given Stacks 07SK, 08K0 and 08K1 in the form in
which they hold under the convention of Section 70.2 (tag 07SD) with no bound on the index. -/
theorem isLimitPreserving_cartesianProperFlatFiberedCategory_of_descent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hM : Space.ModelsDescendUnderConvention B S hS B.contains_terminal)
    (hF : Space.MorphismsDescendUnderConvention B S hS B.contains_terminal)
    (hE : Space.EqualitiesDescendUnderConvention B S hS B.contains_terminal)
    (hflat : Space.PropertyDescendsUnderConvention B S hS B.contains_terminal
      (fun f => Space.IsFlat B S hS f) (fun f => Space.IsLocallyOfFinitePresentation B S hS f))
    (hproper : Space.PropertyDescendsUnderConvention B S hS B.contains_terminal
      (fun f => Space.IsProper B S hS f) (fun f => Space.IsLocallyOfFiniteType B S hS f)) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
      (cartesianProperFlatFiberedCategory B S hS) := by
  intro I _ _ D c hc
  have hp := cartesianProperFlatProjection_isFiberedInGroupoids B S hS
  have : (cartesianProperFlatProjection B S hS).IsFibered := hp.isFibered
  exact
    { faithful := Deformation.Artin.faithful_of_descentEq _ hp _ _
        (StackOfSpacesLimit.descentEq B.contains_terminal D hc hE)
      full := Deformation.Artin.full_of_descentHom _ hp _ _
        (StackOfSpacesLimit.descentHom B.contains_terminal D hc hF hE)
      essSurj := Deformation.Artin.essSurj_of_descentObj _ hp _ _
        (StackOfSpacesLimit.descentObj B.contains_terminal D hc hM hflat hproper) }

end AlgebraicGeometry

end
