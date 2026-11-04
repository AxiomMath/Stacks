module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeRestriction

/-!
# Lefschetz for the fundamental group: the equivalence over the neighbourhoods of a zero scheme

Let `k` be a field, let `X` be a proper scheme over `k`, let `L` be an ample invertible
`𝒪_X`-module, let `s ∈ Γ(X, L)`, let `Y = Z(s)` be the zero scheme of `s`, and let `𝒱` be the
open subschemes of `X` containing `Y`, ordered by reverse inclusion. [Stacks, Tag 0ELD] asserts
that if

`depth(𝒪_{X, x}) + dim({x}‾) > 2`

at every point `x` of `X` outside `Y`, then the restriction functor

`colim_𝒱 FÉt_V ⟶ FÉt_Y`

is an equivalence. That is a single conclusion. It is proved, at exactly those hypotheses, as
`Stacks.FundamentalGroup.finiteEtaleColimitEquivalence_zeroScheme_of_depth` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeFiniteEtaleEquivalence`; this
file keeps the depth hypothesis and the named statements of the source's argument below.

The source proves it as a formal consequence of two results: Lemma [Stacks, Tag 0EK1], which is
`Stacks.FundamentalGroup.isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage`,
and Algebraic and Formal Geometry, Proposition [Stacks, Tag 0EL7], which says that under the same
depth hypothesis the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is an equivalence on the
finite locally free objects. Tag 0EL7 is not in this library, and its statement cannot even be
written down here, so it enters through the two halves of its proof.

## The two halves of Tag 0EL7, and how each is handled

Tag 0EL7 proves full faithfulness and essential surjectivity by completely different routes, and
only one of the two can be assembled from what this library has.

* **Full faithfulness is derived, not granted.** The source's argument is that full faithfulness
  of completion follows from `colim_𝒱 Γ(V, L^{⊗ m}) ⟶ lim Γ(Y_n, L^{⊗ m}|_{Y_n})` being an
  isomorphism for all `m`, by Lemma [Stacks, Tag 0EK2], and that this is Lemma
  [Stacks, Tag 0EL2]. That chain runs through [Stacks, Tag 0EK0],
  `Stacks.FundamentalGroup.fullyFaithful_restrictionFunctor_of_neighbourhoodSectionsComplete`,
  whose condition (2) is exactly that isomorphism. So the depth hypothesis does real work here:
  it produces condition (2) through the named
  `Stacks.FundamentalGroup.NeighbourhoodAmplePowerSectionsCompleteFromDepth`, which is Tag 0EL2
  read in the colimit vocabulary `Stacks.Algebraization.IsNeighbourhoodSectionsComplete` of Tag
  0EK2, and Tag 0EK0 then gives full faithfulness of the restriction functor out of
  the colimit.
* **Essential surjectivity is granted.** The source's argument algebraizes a finite locally free
  object of `Coh(X, I)` by Proposition [Stacks, Tag 0EL5], after converting the depth hypothesis
  on `X` into the depth hypothesis on the completed local rings by Local Cohomology, Lemma
  [Stacks, Tag 0EHW]; Tag 0EK1 then turns the tower `π_{n, *}𝒪_{U_n}` of a finite
  étale cover of `Y` into a cover of a neighbourhood using [Stacks, Tag 0BQB], the algebra
  structure, and the relative spectrum. Neither `Coh(X, I)` nor its finite locally free objects
  nor Tag 0EL5 nor Tag 0EHW has a carrier in this library, so the composite of the two steps is
  carried whole as `Stacks.FundamentalGroup.FiniteEtaleAlgebraizationFromDepth`.

## Vacuity: the carried essential image is as strong as half the conclusion

This is checked in both directions and reported rather than hidden.

* **Carry `⟹` conclusion.** `Stacks.FundamentalGroup.FiniteEtaleAlgebraizationFromDepth`, taken
  at the data of the theorem, gives essential surjectivity of the restriction functor by
  `Stacks.FundamentalGroup.essSurj_restrictionFunctor_of_essentialImage`, which is
  unconditional. So one of the two halves of the conclusion follows from that carry alone, with
  no use of ampleness, properness or depth. It is not inter-derivable with the *whole*
  conclusion: full faithfulness does not follow from it, and is obtained here from the depth
  hypothesis instead.
* **Conclusion `⟹` carry.** The converse does **not** hold as stated, and the gap is not
  mathematical but structural. Essential surjectivity of `P.restrictionFunctor` says every
  `A : FÉt_Y` is isomorphic to `P.restrictionFunctor.obj Z` for some object `Z` of
  `colimit P.diagram`; recovering the carry needs in addition that every object of that colimit
  comes from one of the stages `colimit.ι P.diagram W`, which holds for the standard
  construction of a filtered colimit of categories but is not part of `HasColimit P.diagram`,
  and this library records no such surjectivity-on-objects statement. So the carry is strictly
  stronger than the half of the conclusion it supplies, by exactly that plumbing.

The honest summary: along this route the essential-surjectivity half of [Stacks, Tag 0ELD] is
**not proved**; it is the carried hypothesis, up to the colimit plumbing just described. The
full-faithfulness half follows from the depth hypothesis, modulo the two general statements that
Tag 0EK0 already carries. Both halves are proved outright by
`Stacks.FundamentalGroup.finiteEtaleColimitEquivalence_zeroScheme_of_depth`.

## Main definitions

* `Stacks.FundamentalGroup.DepthAddDimGtTwoOutsideSupport` — the hypothesis
  `depth(𝒪_{X, x}) + dim({x}‾) > 2` of [Stacks, Tag 0ELD], in the `EInt` arithmetic of the
  library's [Stacks, Tag 0EL1] in which
  `Stacks.FundamentalGroup.DepthAddDimGtOneOutsideSupport` of [Stacks, Tag 0ELC] is already
  spelled, so that the two differ only in the integer bound.
* `Stacks.FundamentalGroup.NeighbourhoodAmplePowerSectionsCompleteFromDepth` —
  [Stacks, Tag 0EL2] in the colimit-over-neighbourhoods shape that condition (2) of
  [Stacks, Tag 0EK0] consumes.
* `Stacks.FundamentalGroup.FiniteEtaleAlgebraizationFromDepth` — the essential-surjectivity half
  of [Stacks, Tag 0EL7] composed with the construction in the proof of [Stacks, Tag 0EK1], as a
  statement about general objects.

## Main results

* `Stacks.FundamentalGroup.depthAddDimGtOneOutsideSupport_of_gtTwo` — the depth hypothesis of
  [Stacks, Tag 0ELD] implies that of [Stacks, Tag 0ELC].

## What would discharge each carry, by name

* `NeighbourhoodAmplePowerSectionsCompleteFromDepth` is discharged by [Stacks, Tag 0EL2] once
  `Stacks.Algebraization.isIso_zeroSchemeComparison_of_depthAddDim_gt` ([Stacks, Tag 0EL1])
  is bridged to `Stacks.Algebraization.IsNeighbourhoodSectionsComplete`; the four obstructions to
  that bridge are listed in the module documentation of
  `StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeRestriction`, and the
  open-subscheme form of Tag 0EL2 has no carrier at all. Note that this is a *different* carry
  from Tag 0ELC's `Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth`, which is the
  same source lemma in the single-scheme vocabulary
  `Stacks.Algebraization.IsInfinitesimalSectionsComplete`; neither implies the other in this
  library, because the colimit clauses quantify over shrinking neighbourhoods.
* `AmplePowersImpliesFiniteLocallyFree` and `FullyFaithfulRestrictionOfSectionsComplete` are the
  carries of [Stacks, Tag 0EK0] and are passed through unchanged; they are the
  implications `(2) ⇒ (3)` of [Stacks, Tag 0EK2] and `(3) ⇒ (4)` of Tag 0EK2 followed by
  [Stacks, Tag 0ELA]. The library's `@[stacks 0ELA]`
  `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_sectionsExtendNearSubscheme` does
  **not** discharge the second: its conclusion is
  `Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful`, the fullness-and-faithfulness pair
  written out without the colimit category, and no lemma in this library turns that into
  `Nonempty P.restrictionFunctor.FullyFaithful` for a presentation `P`. Such a bridge would
  discharge it, together with the shrinking form of [Stacks, Tag 0EL8] which that theorem
  assumes.
* `FiniteEtaleAlgebraizationFromDepth` is discharged by [Stacks, Tag 0EL7] together with the
  construction in the proof of [Stacks, Tag 0EK1]; the inputs with no carrier here are
  [Stacks, Tag 0EL5], [Stacks, Tag 0EHW], the finite locally free objects of `Coh(X, I)`, and the
  relative spectrum of an algebraized algebra. [Stacks, Tag 0BQB] is formalized, as
  `AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_isThickening`, and
  [Stacks, Tag 0A43] is formalized in its étale form in
  `StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase`.

## References

* [Stacks Project, Tag 0ELD](https://stacks.math.columbia.edu/tag/0ELD)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EK0](https://stacks.math.columbia.edu/tag/0EK0)
* [Stacks Project, Tag 0EL7](https://stacks.math.columbia.edu/tag/0EL7)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-! ### The depth and dimension hypothesis of Tag 0ELD -/

/-- **The hypothesis of [Stacks, Tag 0ELD]:** at every point `x` of `X` outside the closed
subscheme cut out by `Y` one has `depth(𝒪_{X, x}) + dim({x}‾) > 2`.

This is `Stacks.FundamentalGroup.DepthAddDimGtOneOutsideSupport`, the hypothesis of
[Stacks, Tag 0ELC], with the integer bound `1` replaced by `2`: the depth is the depth of the
local ring over itself along its maximal ideal, the dimension is
`Stacks.Algebraization.dimClosureAt`, and the sum is formed in `EInt` through
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt`, exactly as the
hypothesis `hdepth` of [Stacks, Tag 0EL1] forms it. -/
public def DepthAddDimGtTwoOutsideSupport (X : Scheme.{u}) (Y : X.IdealSheafData) : Prop :=
  ∀ x : X, x ∉ (Y.support : Set X) →
    Stacks.Algebraization.enatToEInt
        (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) +
      Stacks.Algebraization.krullDimToEInt (Stacks.Algebraization.dimClosureAt X x) >
        ((2 : ℤ) : EInt)

/-- The bound `1` is smaller than the bound `2` in the extended integers. -/
public theorem one_lt_two_eInt : ((1 : ℤ) : EInt) < ((2 : ℤ) : EInt) := by
  simp

/-- The hypothesis of [Stacks, Tag 0ELD] implies the hypothesis of [Stacks, Tag 0ELC]: a sum
exceeding `2` exceeds `1`. This is what lets the full faithfulness part of Tag 0ELD be read off
Tag 0EL2, whose own bound is `1`. -/
public theorem depthAddDimGtOneOutsideSupport_of_gtTwo {X : Scheme.{u}} {Y : X.IdealSheafData}
    (h : DepthAddDimGtTwoOutsideSupport X Y) : DepthAddDimGtOneOutsideSupport X Y :=
  fun x hx => lt_trans one_lt_two_eInt (h x hx)

/-! ### The two general statements granted to Tag 0ELD -/

/-- **[Stacks, Tag 0EL2], in the colimit-over-neighbourhoods shape that condition (2) of
[Stacks, Tag 0EK0] consumes**, as a statement about general objects.

Tag 0EL2 says that for `X` proper over a field `k`, `L` an ample invertible `𝒪_X`-module, `s` a
global section of `L` with zero scheme `Y = Z(s)`, and `𝓕` a coherent `𝒪_X`-module whose depth
satisfies `depth(𝓕_x) + dim({x}‾) > 1` outside `Y`, the map `Γ(V, 𝓕) → lim Γ(Y_n, 𝓕|_{Y_n})` is
an isomorphism for every open `V ⊆ X` containing `Y`. Applied to `𝓕 = L^{⊗ m}` — whose depth at a
point is that of `𝒪_{X, x}`, the stalks of an invertible module being free of rank one — and read
over the directed family of those `V`, it gives exactly
`Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteAmplePowers`: the surjectivity clause is
the case `V = X`, and the clause identifying two sections over `V` and `W` is the injectivity of
the map at `V ⊓ W`.

This is the statement the proof of [Stacks, Tag 0EL7] quotes for its full faithfulness half. It
is a different carry from `Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth` of
[Stacks, Tag 0ELC], which is the same source lemma in the single-scheme vocabulary
`Stacks.Algebraization.IsInfinitesimalSectionsComplete`. -/
public def NeighbourhoodAmplePowerSectionsCompleteFromDepth : Prop :=
  ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L],
    AlgebraicGeometry.Scheme.Modules.IsAmple X L →
    ∀ s : Γ(L, ⊤), DepthAddDimGtOneOutsideSupport X (zeroScheme X L s) →
      NeighbourhoodSectionsCompleteAmplePowers (zeroScheme X L s)

/-- **The essential-surjectivity half of [Stacks, Tag 0EL7], composed with the construction in
the proof of [Stacks, Tag 0EK1]**, as a statement about general objects: under the depth
hypothesis of [Stacks, Tag 0ELD], every finite étale cover of the zero scheme `Y = Z(s)` is
isomorphic to the restriction of a finite étale cover of some open neighbourhood of `Y`.

In the source this is two steps. Tag 0EL7 shows that a finite locally free object of
`Coh(X, I)` is the completion of a finite locally free module on a neighbourhood: the depth
hypothesis on `X` is converted to the depth hypothesis on the completed local rings by Local
Cohomology, Lemma [Stacks, Tag 0EHW] together with dimension theory, and Proposition
[Stacks, Tag 0EL5] algebraizes. Tag 0EK1 then produces the cover: lift a finite étale cover of
`Y` to the infinitesimal neighbourhoods `Y_n` by [Stacks, Tag 0BQB], push forward to get the
finite locally free object `(π_{n, *}𝒪_{U_n})` of `Coh(X, I)`, algebraize it, transport the
multiplication by fullness and then faithfulness of completion after shrinking, and take the
relative spectrum, which is étale near `Y` by More on Morphisms, Lemma [Stacks, Tag 0A43].

Neither `Coh(X, I)`, nor its finite locally free objects, nor Tag 0EL5, nor Tag 0EHW, nor the
relative spectrum of an algebraized algebra has a carrier in this library, so the composite is
carried whole. **This carry supplies the essential-surjectivity half of the conclusion of
[Stacks, Tag 0ELD] directly**, through the unconditional
`Stacks.FundamentalGroup.essSurj_restrictionFunctor_of_essentialImage`; see the module
documentation for the two-directional check. -/
public def FiniteEtaleAlgebraizationFromDepth : Prop :=
  ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L],
    AlgebraicGeometry.Scheme.Modules.IsAmple X L →
    ∀ s : Γ(L, ⊤), DepthAddDimGtTwoOutsideSupport X (zeroScheme X L s) →
    ∀ A : FiniteEtaleOver (zeroScheme X L s).subscheme,
      ∃ (W : Neighborhood X (zeroScheme X L s))
        (U : FiniteEtaleOver (Neighborhood.open X (zeroScheme X L s) W).toScheme),
        Nonempty ((finiteEtaleBaseChange
          (Neighborhood.toSchemeHom X (zeroScheme X L s) W)).obj U ≅ A)

end Stacks.FundamentalGroup

end

end
