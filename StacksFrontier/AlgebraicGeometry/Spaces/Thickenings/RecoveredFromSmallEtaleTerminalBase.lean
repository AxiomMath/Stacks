module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap

/-!
# Recovery of morphisms from the small étale ringed topos over the terminal base

`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` is the assertion of [Stacks, Tag 04KL]
*over a base*: a locally ringed morphism `ψ` of the small étale ringed topoi of two algebraic
spaces `P` and `Q` over `S`, 2-compatible with a pair of structure morphisms `pP : P ⟶ A` and
`pQ : Q ⟶ A`, is induced by exactly one morphism `P ⟶ Q`.  Over a general `S` it is not proved
in this development, and the statements of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap` take it as an
argument.

This file discharges it **over the terminal base** `Spec ℤ` — here `Spec (ULift ℤ)`, the
terminal scheme of the universe of the site, which is the base [Stacks, Tag 04KL] itself is
stated at.  Over that base `AlgebraicGeometry.AlgebraicSpaces` is the absolute category of
algebraic spaces, so the conclusion of the relative statement is literally the conclusion of
Tag 04KL and the 2-compatibility with `pP` and `pQ` is an unused hypothesis.

The hypothesis `hZ` that the site contains the terminal scheme is no restriction on the site:
`AlgebraicGeometry.contains_specULiftZ` of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute` proves it for every
`AlgebraicGeometry.BigFppfSite`.  What restricts the statements below is only that the base
scheme is the terminal one.

## Main results

* `AlgebraicGeometry.Space.isRecoveredFromSmallEtale_specULiftZ`: **`IsRecoveredFromSmallEtale`
  holds over the terminal base**, with nothing granted.
* `AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged_specULiftZ`:
  consequently [Stacks, Tag 05ZN] over the terminal base, with only the locally ringed
  condition on `(f_{spaces,étale}, α)` still taken as an argument.  That condition is a
  property of the *morphism* and is not the locally ringed clause of [Stacks, Tag 05ZM], which
  is proved; see the implementation note on that statement.

## Implementation notes

**Why this is not a weakening of the counterexample.**  The implementation notes of
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` and of
`StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Main` record that the relative form is
*false* over a general base: for `S = P = Q = A = Spec ℚ(i)` and `σ` the nontrivial automorphism,
`(σ_small, σ♯)` is a locally ringed automorphism of the small étale ringed topos that is not
2-isomorphic to the identity, while the identity is the only morphism over `S`.  That
counterexample needs a base with a nontrivial automorphism; over the terminal base there is
nothing to commute with, and the direction of the deduction is from the absolute statement to
the relative one rather than the reverse.  What remains owed for a general base is the
[Stacks, Tag 04SG] transport
(`AlgebraicGeometry.spacesOverSmallerBaseEquivalence`), which no declaration performs.

**Which form the proof of [Stacks, Tag 05ZT] needs.**  The source of Tag 05ZT builds the ambient
space over `Spec ℤ` and only then transports the `f^{-1}𝒪_B`-algebra structure through the
isomorphism to obtain the morphism to the base, invoking Tag 05ZN *at the absolute base* with
`Y = Y' = B` and the trivial thickening.  So it is the statement below, and not
`IsRecoveredFromSmallEtale` over a general base, that Tag 05ZT needs; the general-base form is
not on the path.

**Nothing is registered here.**  No `@[stacks 04KL]` attribute: the absolute statement already
carries it on `AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_isLocallyRinged`, and the
reformulation below is a consequence of it with hypotheses added, not a second proof of the tag.
No `@[stacks 05ZN]` either: that lemma is stated by the source over an arbitrary base algebraic
space, and a statement restricted to the terminal base is not that statement.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u})
  (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- **Over the terminal base, morphisms of algebraic spaces are recovered from their small étale
ringed topoi**, with nothing granted.

This is `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` — [Stacks, Tag 04KL] over a base —
at the base `Spec (ULift ℤ)`.  There the category of algebraic spaces over the base is the
absolute one, so the conclusion is that of Tag 04KL and the 2-compatibility with the two
structure morphisms to `A` is not used. -/
theorem isRecoveredFromSmallEtale_specULiftZ :
    IsRecoveredFromSmallEtale B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ := by
  intro _ P Q _ _ ψ hψ _
  refine (existsUnique_congr fun k => ?_).mp
    (existsUnique_spaceHom_twoIso_of_isLocallyRinged B hZ ψ hψ)
  exact ⟨fun ⟨t⟩ => ⟨t.symm⟩, fun ⟨t⟩ => ⟨t.symm⟩⟩

variable {T X' Y' : AlgebraicSpaces B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ}
  {G : Subfunctor X'.1} {H : Subfunctor Y'.1}

/-- **[Stacks, Tag 05ZN] over the terminal base**, with the recovery of morphisms no longer
granted.

Let `G ⊂ X'` and `H ⊂ Y'` be thickenings of algebraic spaces over `T`, let `f` be a morphism of
the two closed subspaces, and let `Φ = (f_{spaces,étale}, α)` be a locally ringed morphism of the
small étale ringed topoi of `X'` and `Y'` compatible with the two inclusions and with the two
structure morphisms to `T`.  Then there is exactly one `f' : X' ⟶ Y'` inducing `Φ`, and it makes
`(f, f')` a morphism of thickenings over `T`.

This is `AlgebraicGeometry.Space.existsUnique_thickeningHom_of_isLocallyRinged` with its
`IsRecoveredFromSmallEtale` argument supplied by
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_specULiftZ`.  Only the locally ringed
condition on `Φ` is still an argument.

**What `hlocal` is, and what it is not.**  It is
`AlgebraicGeometry.RingedToposHom.IsLocallyRinged`, the cartesian-units-square condition of
[Stacks, Tag 04HA] on the *morphism* `Φ`.  The locally ringed clause of [Stacks, Tag 05ZM] is
proved, as `AlgebraicGeometry.Space.thickeningFundamentalHom_isLocallyRinged` and
`AlgebraicGeometry.Space.thickeningFundamentalHomInverse_isLocallyRinged` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRingedTopos`, but it is the assertion
that the comparison of the fundamental equivalence and its inverse are locally ringed, which is
a different assertion and does not discharge `hlocal`: it constrains the units square of that
comparison, not of an arbitrary morphism `Φ` out of the thickened topos.  What the
[Stacks, Tag 05ZT] route needs of `Φ` there is that the structure map `f^{-1}𝒪_B ⟶ 𝒜` reflects
units.

**How that is to be supplied, and why `hlocal` is still an argument.**  The criterion for it is
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_reflectsUnitsObj_comp` of
`StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare`: units need
only be reflected for the composite `f^{-1}𝒪_B ⟶ 𝒜 ⟶ 𝒪_X`, reflection of units passing to a
left factor (`AlgebraicGeometry.RingedTopos.reflectsUnitsObj_of_comp`).  That composite is the
structure map of the morphism `X ⟶ B` of algebraic spaces, whose morphism of small étale ringed
topoi is locally ringed by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_isLocallyRinged` ([Stacks, Tag 04KJ]), and
`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged` turns that into the
hypothesis at the geometric points of the small étale site, which are a conservative family
(`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints`).  The square-zero
hypothesis of [Stacks, Tag 05ZT] is not what reflects units for `Φ` itself; it is what makes
`𝒜 ⟶ 𝒪_X` a local homomorphism (`isLocalHom_of_surjective_of_forall_sq_eq_zero` of
`StacksFrontier.RingTheory.Henselian.Pair.Nilpotent`) and what makes the source a locally ringed
site.

`hlocal` is not discharged in the statement below, and cannot be: `Φ` there is an arbitrary
morphism of the two small étale ringed topoi, for which the cartesian units square is genuinely
a condition and not a theorem.  It is the *concrete* `Φ` of Tag 05ZT that the criterion applies
to, and that `Φ` needs a square-zero extension `𝒜` of the structure sheaf of an algebraic
space, which this development does not have —
`StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension` packages only the scheme-level
notion. -/
theorem existsUnique_thickeningHom_of_isLocallyRinged_specULiftZ
    (hG : IsThickening B _ hZ X' G) (hH : IsThickening B _ hZ Y' H)
    (pX' : X' ⟶ T) (pY' : Y' ⟶ T)
    (f : IsThickening.space B _ hZ hG ⟶ IsThickening.space B _ hZ hH)
    (Φ : RingedToposHom (smallEtaleRingedTopos B _ hZ X')
      (smallEtaleRingedTopos B _ hZ Y'))
    (hlocal : Φ.IsLocallyRinged)
    (hsquare : Nonempty (SmallEtaleTwoIso B _ hZ
      (smallEtaleComp B _ hZ Φ
        (smallEtaleRingedToposHom B _ hZ (IsThickening.inclusion B _ hZ hG)))
      (smallEtaleRingedToposHom B _ hZ (f ≫ IsThickening.inclusion B _ hZ hH))))
    (halgebra : Nonempty (SmallEtaleTwoIso B _ hZ
      (smallEtaleComp B _ hZ (smallEtaleRingedToposHom B _ hZ pY') Φ)
      (smallEtaleRingedToposHom B _ hZ pX'))) :
    ∃! f' : X' ⟶ Y', InducesSmallEtaleRingedToposHom B _ hZ f' Φ ∧
      IsThickening.inclusion B _ hZ hG ≫ f' = f ≫ IsThickening.inclusion B _ hZ hH ∧
      f' ≫ pY' = pX' :=
  existsUnique_thickeningHom_of_isLocallyRinged B _ hZ
    (isRecoveredFromSmallEtale_specULiftZ B hZ) hG hH pX' pY' f Φ hlocal hsquare halgebra

end AlgebraicGeometry.Space

end
