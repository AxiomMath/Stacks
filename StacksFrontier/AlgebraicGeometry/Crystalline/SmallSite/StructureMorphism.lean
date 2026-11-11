module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.NilpotentUnits
public import StacksFrontier.RingTheory.DividedPowers.Nilpotent

/-!
# The structure morphism of the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  When `p` is locally nilpotent on the
closed fibre `S₀ = V(I)`, the closed fibre is itself a global crystalline situation over
`(S, I, γ)` — `Crystalline.GlobalCrystallineSituation.closedFiberSituation`, [Stacks, Tag 07IE] —
so the small crystalline site `Cris(S₀/S)` is available, and the structure morphism `f : X ⟶ S₀`
of `X` over `S` induces the morphism of small crystalline topoi
`f_cris : (X/S)_cris ⟶ (S₀/S)_cris` of [Stacks, Tag 07IK].  That is the top arrow of the diagram
of [Stacks, Tag 07IM].

This file supplies the arrows of that diagram that the library does not already have, and its
lower route.  The lower route runs `u_{X/S}` of [Stacks, Tag 07IL] into the small Zariski topos of
`X`, then the small Zariski morphisms along `X ⟶ S₀` and `S₀ ⟶ S`; those two compose to the one
along `X ⟶ S`, so the lower route is the structure morphism
`τ_{X/S} : (X/S)_cris ⟶ Sh(S_Zar)`, which is therefore defined whether or not `p` is locally
nilpotent on `S₀`.

## Change of divided power base: the compatibility of [Stacks, Tag 07MH]

[Stacks, Tag 07MH] asserts that the morphisms of the section "satisfy numerous compatibilities",
and gives as its example a commutative square whose horizontal arrows are `f_cris` of
[Stacks, Tag 07IK] and the Zariski morphism along `(S, I, γ) ⟶ (S', I', γ')`, and whose vertical
arrows are the structure morphisms of [Stacks, Tag 07IM].  (The displayed diagram of the remark
writes the *big* Zariski topoi `Sh((Sch/S)_Zar)` for the two targets, inherited verbatim from the
big crystalline remark [Stacks, Tag 07MG]; the structure morphism of the small crystalline site is
`τ_{X/S} : (X/S)_cris ⟶ Sh(S_Zar)`, so the small Zariski topoi are what the vertical arrows of
this section's diagram can land in, and that is the reading taken here; the printed big corners
are a typo, recorded in `errata.md`.)

The remark's square itself, with `f_cris = π_Y ∘ f_CRIS ∘ i_X` on top, is proved downstream, as a
square of ringed topoi, by
`Crystalline.GlobalCrystallineSituation.SmallSite.structureSquareTwoIso` of
`SmallSite/BaseChangeSquareRinged07MS.lean`, on top of the comparison square of
[Stacks, Tag 07IK] (`SmallSite/CrisZariskiSquareIso.lean`).  This file has three ingredients and
variants of it.  The first is the *Zariski half*: the square of small Zariski topoi obtained from
`X ⟶ Y`, `X ⟶ S`, `Y ⟶ S'` and `S ⟶ S'` commutes, because the two composites `X ⟶ S ⟶ S'` and
`X ⟶ Y ⟶ S'` are the same morphism of schemes
(`Crystalline.GlobalCrystallineSituation.comp_sourceToBase`); whiskering that with `u_{X/S}`
identifies the lower route of the remark's square.  The second is a different square, with the
big Zariski topoi `Sh((Sch/S)_Zar)` and `Sh((Sch/S')_Zar)` at the bottom, the structure morphism of
the big crystalline site read on the small crystalline topos along the inclusion `i_X` of
[Stacks, Tag 07IJ] on the left, the *big* crystalline topos `(Y/S')_CRIS` at the top right and
`f_CRIS ∘ i_X : (X/S)_cris ⟶ (Y/S')_CRIS` at the top; that square is
`changeBaseSmallStructureSquareOfComparison`, and it holds for every `g : X ⟶ Y`, being the
square of [Stacks, Tag 07MG] whiskered with `i_X`.

## The upper square of [Stacks, Tag 07IM], and the obstruction (★)

The *upper square* of the remark — `u_{S₀/S} ∘ f_cris ≅ f_small ∘ u_{X/S}`, for `f : X ⟶ S₀` the
structure morphism — is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/UpperSquare.lean` as
`Crystalline.GlobalCrystallineSituation.closedFiberCrisUpperSquare`, at the remark's own
hypotheses: local nilpotence of `p` on `S₀` and nothing more.  It is an instance of the general
comparison square of [Stacks, Tag 07IK] for an *arbitrary* morphism of global crystalline
situations,
`Crystalline.GlobalCrystallineSituation.SmallSite.crisZariskiSquareCoeff` of
`SmallSite/CrisZariskiSquareIso.lean`, read at the coefficients `Type (u + 1)` with the closed
fibre situation as the target.

The general square is *not* proved by comparing the two right Kan extensions index by index, and
the reason is recorded here as (★).  Change of divided power base does not restrict to the small
crystalline sites, so `f_cris` is the detour
`π_Y ∘ f_CRIS ∘ i_X` of [Stacks, Tag 07IK] rather than the morphism of topoi of a cocontinuous
functor `Cris(X/S) ⥤ Cris(Y/S')`; the pushforward of the square's left-and-bottom route is a
single right Kan extension, while that of its top-and-right route carries the extra factor
`i_Y^{-1}` followed by `i_{Y, *}`, which is the comonad of the inclusion and not the identity
(only `π ∘ i` is the identity, [Stacks, Tag 07IJ]).  Identifying the two amounts to
(★) `i_{Y, !}(u^{-1} h_V) ⟶ U^{-1} h_{V/Y}` is an isomorphism,
which the source asserts with no argument beyond a pointer to [Stacks, Tag 07IK].

The cofinality route to (★) is **false** as stated.  Take `p` a prime, `S = Spec ℤ_{(p)}` with
divided power ideal `(p)`, `X = ⨆_{n ≥ 1} Spec 𝔽_p` and `T = ⨆_{n ≥ 1} Spec ℤ/p^n`: the comma
category `StructuredArrow (κ A) ι` is then *empty*, so `CategoryTheory.Functor.Final`,
`CategoryTheory.Functor.Initial` for the opposite functor and
`CategoryTheory.RepresentablyFlat` all fail simultaneously, the obstruction being exactly
non-quasi-compactness.  (It is not a counterexample to (★) itself: in it `i_! * ≠ *`, which left
exactness of `i_!` already excludes, and left exactness holds in general —
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.preservesFiniteLimits_lowerShriek`,
proved where [Stacks, Tag 07HP] supplies only the affine case and [Stacks, Tag 07IJ] omits the
general one — which is what makes `f_cris`,
`Crystalline.GlobalCrystallineSituation.crisMorphism`, exist with no hypothesis beyond its data.)

What is true, and what `SmallSite/CrisZariskiSquare{Covering, Limit, Iso}.lean` carries out, is the
covering-local form of (★): a *fixed* object `A'` of `Cris(X/S)` over an open `V` need admit no
morphism to an object of `Cris(Y/S')` over `V`, but the refinements of `A'` which do admit one form
a covering sieve (`...SmallSite.dominatedSieve_mem`, by the divided power pushout of
[Stacks, Tag 07RT]), and any two such dominations are refined by a third
(`...SmallSite.exists_cone_domination`).  Both composites being limits of a *sheaf*, the sheaf
condition — separatedness and amalgamation at that covering sieve, which Mathlib has at a general
object as `CategoryTheory.Presheaf.IsSheaf.hom_ext` and
`CategoryTheory.Presheaf.IsSheaf.amalgamate` — turns those two facts into the inverse of the
canonical `2`-cell.  No Beck–Chevalley transfer is involved.

The square of [Stacks, Tag 07MH] meets the same comparison, for an arbitrary `g : X ⟶ Y` over
`S ⟶ S'`, and is proved through `SmallSite.crisZariskiSquareCoeff` in
`SmallSite/BaseChangeSquare07MS.lean` (as topoi) and `SmallSite/BaseChangeSquareRinged07MS.lean`
(as ringed topoi).

## The closed fibre as a terminal object, and what it is still for

Situation [Stacks, Tag 07MF] assumes `p` locally nilpotent on `X` and, in [Stacks, Tag 07IM], on
the closed fibre `S₀`; if `p` is locally nilpotent on `S` itself then by [Stacks, Tag 07GR]
(`DividedPowers.locallyNilpotent_iff_isNilpotent_natCast`) the divided power ideal `I` is locally
nilpotent, so `S₀ ↪ S` is itself a thickening
(`Crystalline.DividedPowerScheme.isThickening_closedFiberι_of_isNilpotent_natCast`) and hence a
divided power thickening of `S₀` over `(S, I, γ)`, and `(S₀, S, γ)` is then a terminal object of
`Cris(S₀/S)`
(`Crystalline.GlobalCrystallineSituation.isTerminal_closedFiberCrystallineThickening`).

That condition is *strictly stronger* than the standing hypotheses, and the declarations at the
end of this file pin that down:
`Crystalline.DividedPowerScheme.isThickening_closedFiberι_iff` shows that `S₀ ↪ S` being a
thickening is **equivalent** to local nilpotence of `I`, so by [Stacks, Tag 07GR] it is equivalent
to nilpotence of `p` on the sections of `S`.  Situation [Stacks, Tag 07MF] puts local nilpotence
of `p` on `X` (the field
`Crystalline.GlobalCrystallineSituation.prime_locallyNilpotent`) and [Stacks, Tag 07IM] adds it on
`S₀ = V(I)`; the structure `Crystalline.GlobalCrystallineSituation` has no further field, and in
particular none on `I` or on `p` over `S`.  The basic example of the theory separates them: over
`S = Spec ℤ_(p)` with divided power ideal `(p)`, `p` is nilpotent on `S₀ = Spec 𝔽_p` and `(p)` is
not locally nilpotent in `ℤ_(p)`, so `S₀ ↪ S` is not a thickening.

The terminal object is therefore *not* used for the upper square of [Stacks, Tag 07IM], which the
covering-local route proves without it; it is recorded for its own sake, as the structure
`Cris(S₀/S)` acquires when `p` is nilpotent on the base.  Its reach is in any case the site
`Cris(S₀/S)` and no further: the indexing category in (★) belongs to the *target* of `f`, and
`Cris(Y/S')` has no terminal object for general `Y` over `S'₀` — one would be a universal divided
power thickening of `Y` over `(S', I', γ')`, which is what divided power envelopes of embeddings
into smooth schemes replace, cofinally and not terminally.

Finally, the source is in doubt at this point, not merely hard: [Stacks, Tag 07IM] carries a
May 2025 comment citing Berthelot, *Cohomologie cristalline des schémas de caractéristique p > 0*
III, Remarque 3.2.5, to the effect that a map appearing in Situation [Stacks, Tag 07MF] may not be
a morphism of ringed topoi at all.

The big crystalline analogues of both squares do not meet the obstruction and are proved, as
`Crystalline.GlobalCrystallineSituation.comparisonSquare`, [Stacks, Tag 07IE], and
`Crystalline.GlobalCrystallineSituation.changeBaseStructureSquare`, [Stacks, Tag 07MG].

## Main definitions

* `StacksZariskiSite.opensMapMorphismOfTopoiComp` — the morphisms of small Zariski topoi compose,
  and `StacksZariskiSite.opensMapMorphismOfTopoiCongr` — equal continuous maps induce the same one.
* `Crystalline.GlobalCrystallineSituation.closedFiberCrisMorphism` — the top arrow
  `f_cris : (X/S)_cris ⟶ (S₀/S)_cris` of the diagram of [Stacks, Tag 07IM].
* `Crystalline.GlobalCrystallineSituation.closedFiberThickening` and
  `Crystalline.GlobalCrystallineSituation.closedFiberCrystallineThickening` — the triple
  `(S₀, S, γ)` as an object of `CRIS(S₀/S)` and of `Cris(S₀/S)`, available once the closed fibre
  inclusion `S₀ ↪ S` is a thickening.

## Main results

* `Crystalline.GlobalCrystallineSituation.closedFiberCrisMorphism_eq` — the top arrow is the
  detour `π_{S₀} ∘ f_CRIS ∘ i_X` of [Stacks, Tag 07IK], with `f_CRIS` the arrow
  `closedFiberMorphism` of [Stacks, Tag 07IE].
* `Crystalline.GlobalCrystallineSituation.smallZariskiStructureTriangle` — the trailing arrow of
  the diagram: the small Zariski morphisms along `X ⟶ S₀` and `S₀ ⟶ S` compose to the one along
  `X ⟶ S`.
* `Crystalline.GlobalCrystallineSituation.structureToposMorphism_isoLowerRoute` — the structure
  morphism `τ_{X/S}` is the lower route of the diagram.
* `Crystalline.GlobalCrystallineSituation.smallZariskiChangeBaseSquare` — the Zariski half of the
  square of [Stacks, Tag 07MH]: the small Zariski square along `X ⟶ S ⟶ S'` and `X ⟶ Y ⟶ S'`.
* `Crystalline.GlobalCrystallineSituation.changeBaseSmallStructureLowerRoute` — the lower route of
  the square of [Stacks, Tag 07MH] is `u_{X/S}` followed by the small Zariski route
  `X ⟶ Y ⟶ S'`.
* `Crystalline.GlobalCrystallineSituation.changeBaseSmallStructureSquareOfComparison` — the square
  of [Stacks, Tag 07MG] restricted along `i_X`: big Zariski corners at the bottom, the small
  crystalline topos of `X/S` on the left and the *big* crystalline topos of `Y/S'` on the right,
  with `f_CRIS ∘ i_X` on top.  It is not the square of [Stacks, Tag 07MH], which is
  `Crystalline.GlobalCrystallineSituation.SmallSite.structureSquareTwoIso`.
* `Crystalline.DividedPowerScheme.isThickening_closedFiberι` and
  `Crystalline.DividedPowerScheme.isThickening_closedFiberι_of_isNilpotent_natCast` — local
  nilpotence of the divided power ideal, and in particular nilpotence of `p` on sections by
  [Stacks, Tag 07GR], makes the closed fibre inclusion `S₀ ↪ S` a thickening.
* `Crystalline.DividedPowerScheme.isNilpotent_of_isThickening_closedFiberι` and
  `Crystalline.DividedPowerScheme.isThickening_closedFiberι_iff` — the converse, and so the
  identification of the condition under which the closed fibre is a terminal object: `S₀ ↪ S` is a
  thickening **exactly** when `I` is locally nilpotent, which by [Stacks, Tag 07GR] is nilpotence
  of `p` on `S` and not on `S₀`, and so is strictly more than the standing hypotheses give.
* `Crystalline.GlobalCrystallineSituation.isTerminal_closedFiberThickening` and
  `Crystalline.GlobalCrystallineSituation.isTerminal_closedFiberCrystallineThickening` —
  `(S₀, S, γ)` is then a terminal object of `CRIS(S₀/S)` and of `Cris(S₀/S)`.  The upper square of
  [Stacks, Tag 07IM] does not need it — see the section above — and neither does the square of
  [Stacks, Tag 07MH], whose indexing category belongs to a target with no terminal object in
  general.

## Implementation notes

A commutative diagram of morphisms of topoi is recorded, as in
`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/StructureMorphism.lean`, as an isomorphism of
the composite pushforward functors — an invertible 2-morphism in the sense of
[Stacks, Tag 04IA], `TwoMorphismOfTopoi` — and not as an equality; the companion isomorphism of
inverse images is its mate under the two adjunctions.  The two triangles below are invertible
2-morphisms whose underlying comparison of site functors is `TopologicalSpace.Opens.mapComp`, so
they in fact hold by `Iso.refl`: the pushforward of a morphism of small Zariski topoi is
precomposition with `Opens.map`, which is strictly functorial.  They are nevertheless built from
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` rather than from `Iso.refl`, so that the
proof records which comparison of site functors is responsible.

`closedFiberCrisMorphism` has the one hypothesis the source itself puts on the arrow it names.
`hlocnil` is the standing assumption of [Stacks, Tag 07IM] — "if we assume that `p` is locally
nilpotent on `S₀`" — which is *not* part of Situation [Stacks, Tag 07MF] (that assumes `p` locally
nilpotent on `X`, the field
`Crystalline.GlobalCrystallineSituation.prime_locallyNilpotent`) nor of Definition
[Stacks, Tag 07I6]; it is the datum that makes `S₀` a global crystalline situation over
`(S, I, γ)`, i.e. the `prime_locallyNilpotent` field of `closedFiberSituation S hlocnil`, so the
target topos does not exist without it.  Left exactness of `i_!` for `S₀/S`, which
`Crystalline.GlobalCrystallineSituation.crisMorphism`, [Stacks, Tag 07IK], needs for the
retraction `π_{S₀}` of [Stacks, Tag 07IJ] to be a morphism of topoi, is not a hypothesis: it is
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.preservesFiniteLimits_lowerShriek`.

## References

* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 07IE](https://stacks.math.columbia.edu/tag/07IE)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 07MH](https://stacks.math.columbia.edu/tag/07MH)
* [Stacks Project, Tag 07MG](https://stacks.math.columbia.edu/tag/07MG)
* [Stacks Project, Tag 07GR](https://stacks.math.columbia.edu/tag/07GR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Thickenings

universe u

namespace StacksZariskiSite

/-- **The morphisms of small Zariski topoi compose.**  The pushforward of
`opensMapMorphismOfTopoi` is precomposition with `Opens.map`, and `Opens.map` turns a composite
of continuous maps into the composite of the two precompositions, in the opposite order. -/
def opensMapMorphismOfTopoiComp {X Y Z : TopCat.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :
    ((opensMapMorphismOfTopoi b).comp (opensMapMorphismOfTopoi a)).pushforward ≅
      (opensMapMorphismOfTopoi (a ≫ b)).pushforward :=
  Functor.sheafPushforwardContinuousComp' (Opens.mapComp a b).symm (Type (u + 1))
    (Opens.grothendieckTopology Z) (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X)

/-- **Equal continuous maps induce the same morphism of small Zariski topoi.**  Recorded as an
isomorphism of the pushforwards, so that it can be spliced into a composite of 2-morphisms. -/
def opensMapMorphismOfTopoiCongr {X Y : TopCat.{u}} {a b : X ⟶ Y} (hab : a = b) :
    (opensMapMorphismOfTopoi a).pushforward ≅ (opensMapMorphismOfTopoi b).pushforward := by
  subst hab
  exact Iso.refl _

end StacksZariskiSite

namespace Crystalline.DividedPowerScheme

variable (X : DividedPowerScheme.{u})

/-- **Over an affine open, the kernel ideal of the closed fibre inclusion is the divided power
ideal.**  Over an affine open a section dies on the closed fibre exactly when it lies in the
divided power ideal, `Crystalline.DividedPowerScheme.ClosedFiberPresentation.app_eq_zero_iff`.
This is the datum `Crystalline.SchemeThickening.ideal_eq_ker` for the closed fibre inclusion. -/
theorem ker_ideal_closedFiberι_eq_ideal_obj (V : X.scheme.affineOpens) :
    (closedFiberι X).ker.ideal V = X.ideal.obj (Opposite.op (V : X.scheme.Opens)) := by
  rw [Scheme.Hom.ker_apply]
  refine SetLike.ext fun s ↦ ?_
  rw [RingHom.mem_ker]
  exact (closedFiberPresentation X).app_eq_zero_iff V s

/-- **Over an affine open, the divided power ideal is the kernel ideal of the closed fibre
inclusion**, in the orientation the field `Crystalline.SchemeThickening.ideal_eq_ker` asks for. -/
theorem ideal_obj_eq_ker_ideal_closedFiberι (V : X.scheme.affineOpens) :
    X.ideal.obj (Opposite.op (V : X.scheme.Opens)) = (closedFiberι X).ker.ideal V :=
  (ker_ideal_closedFiberι_eq_ideal_obj X V).symm

/-- **If the divided power ideal is locally nilpotent then the closed fibre inclusion is a
thickening.**  The kernel ideal sheaf of the inclusion is the divided power ideal, so local
nilpotence of the latter puts that kernel inside the nilradical, whose support is the whole space;
the support of the kernel is the closure of the range of the inclusion, and the inclusion is a
closed embedding, so its range is everything.

The hypothesis `hnil` is the scheme-level form of the left hand side of [Stacks, Tag 07GR], and
the conclusion is what makes `(S₀, S, γ)` an object of `Cris(S₀/S)`. -/
theorem isThickening_closedFiberι
    (hnil : ∀ (V : X.scheme.affineOpens) (s : Γ(X.scheme, (V : X.scheme.Opens))),
      s ∈ X.ideal.obj (Opposite.op (V : X.scheme.Opens)) → IsNilpotent s) :
    IsThickening (closedFiberι X) := by
  have hle : (closedFiberι X).ker ≤ X.scheme.nilradical := by
    rw [← Scheme.IdealSheafData.radical_bot]
    intro V s hs
    rw [Scheme.IdealSheafData.radical_ideal]
    rw [← ideal_obj_eq_ker_ideal_closedFiberι X V] at hs
    obtain ⟨n, hn⟩ := hnil V s hs
    exact Ideal.mem_radical_iff.mpr ⟨n, by simp [hn]⟩
  have hmono := Scheme.IdealSheafData.support_antitone hle
  rw [X.scheme.support_nilradical] at hmono
  refine ⟨inferInstance, ?_⟩
  rw [← Set.range_eq_univ, ← (closedFiberι X).isClosedEmbedding.isClosed_range.closure_eq,
    ← Scheme.Hom.support_ker, top_le_iff.mp hmono]
  exact TopologicalSpace.Closeds.coe_top

/-- **If the closed fibre inclusion is a thickening then the divided power ideal is locally
nilpotent.**  The converse of `Crystalline.DividedPowerScheme.isThickening_closedFiberι`: a
thickening is a closed immersion whose underlying map is onto, the ideal sheaf of such a morphism
lies in the nilradical (`Stacks.LiftInvertible.ker_le_nilradical_of_surjective`), and the ideal
sheaf of the closed fibre inclusion is the divided power ideal by
`Crystalline.DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι`. -/
theorem isNilpotent_of_isThickening_closedFiberι (hthick : IsThickening (closedFiberι X))
    (V : X.scheme.affineOpens) (s : Γ(X.scheme, (V : X.scheme.Opens)))
    (hs : s ∈ X.ideal.obj (Opposite.op (V : X.scheme.Opens))) :
    IsNilpotent s := by
  have := hthick.1
  have hle := Stacks.LiftInvertible.ker_le_nilradical_of_surjective (closedFiberι X) hthick.2
  rw [ideal_obj_eq_ker_ideal_closedFiberι] at hs
  have hnil := Scheme.IdealSheafData.le_def.mp hle V hs
  rw [Scheme.nilradical, Scheme.IdealSheafData.radical_ideal] at hnil
  exact mem_nilradical.mp hnil

/-- **The closed fibre inclusion `S₀ ↪ S` is a thickening exactly when the divided power ideal is
locally nilpotent.**  So the hypothesis that the closed fibre inclusion is a thickening is neither
more nor less than local nilpotence of `I`, which by [Stacks, Tag 07GR] is nilpotence of `p` on
the sections of `S` — a condition on the *base*.  Situation [Stacks, Tag 07MF] imposes local
nilpotence of `p` on `X` only, and [Stacks, Tag 07IM] adds it on the closed fibre `S₀ = V(I)`;
neither gives it on `S`.  Over `S = Spec ℤ_(p)` with divided power ideal `(p)` — the basic example
of the theory — `p` is nilpotent on `S₀ = Spec 𝔽_p` and `(p)` is not locally nilpotent, so the two
hypotheses are genuinely different. -/
theorem isThickening_closedFiberι_iff :
    IsThickening (closedFiberι X) ↔
      ∀ (V : X.scheme.affineOpens) (s : Γ(X.scheme, (V : X.scheme.Opens))),
        s ∈ X.ideal.obj (Opposite.op (V : X.scheme.Opens)) → IsNilpotent s :=
  ⟨isNilpotent_of_isThickening_closedFiberι X, isThickening_closedFiberι X⟩

/-- **Nilpotence of `p` on sections makes the divided power ideal locally nilpotent.**  This is
[Stacks, Tag 07GR], `DividedPowers.locallyNilpotent_iff_isNilpotent_natCast`, applied over an
affine open to the divided power structure that a divided power scheme carries on the ideal of
sections there; nilpotence of `p` in the ring of sections gives nilpotence of `p` in its quotient
by that ideal, which is the standing hypothesis of the equivalence. -/
theorem isNilpotent_of_mem_ideal {p : ℕ} (hprime : p.Prime)
    (hpX : ∀ V : X.scheme.affineOpens, IsNilpotent (p : Γ(X.scheme, (V : X.scheme.Opens))))
    (V : X.scheme.affineOpens) (s : Γ(X.scheme, (V : X.scheme.Opens)))
    (hs : s ∈ X.ideal.obj (Opposite.op (V : X.scheme.Opens))) :
    IsNilpotent s := by
  refine (DividedPowers.locallyNilpotent_iff_isNilpotent_natCast hprime
    (X.dividedPowers.dividedPowers (Opposite.op (V : X.scheme.Opens))) ?_).mpr (hpX V) s hs
  exact (hpX V).map
    (Ideal.Quotient.mk (sectionIdeal X.scheme.sheaf X.ideal (Opposite.op (V : X.scheme.Opens))))

/-- **If `p` is nilpotent on the sections over every affine open of `S` then the closed fibre
inclusion `S₀ ↪ S` is a thickening**, hence a divided power thickening of `S₀` over `(S, I, γ)`.
This is the composite of [Stacks, Tag 07GR] with
`Crystalline.DividedPowerScheme.isThickening_closedFiberι`. -/
theorem isThickening_closedFiberι_of_isNilpotent_natCast {p : ℕ} (hprime : p.Prime)
    (hpX : ∀ V : X.scheme.affineOpens, IsNilpotent (p : Γ(X.scheme, (V : X.scheme.Opens)))) :
    IsThickening (closedFiberι X) :=
  isThickening_closedFiberι X fun V s hs ↦ isNilpotent_of_mem_ideal X hprime hpX V s hs

end Crystalline.DividedPowerScheme

namespace Crystalline.GlobalCrystallineSituation

open CrystallineThickening StacksZariskiSite

variable (S : GlobalCrystallineSituation.{u})

/-- **Stacks Project, Tag 07IM.**  The top arrow
`f_cris : (X/S)_cris ⟶ (S₀/S)_cris` of the diagram, for `f : X ⟶ S₀` the structure morphism of `X`
over `S`.  Local nilpotence of `p` on the closed fibre `S₀ = V(I)` is the standing assumption the
remark makes before it draws the diagram, and it is what makes `S₀` a global crystalline situation
over `(S, I, γ)`, [Stacks, Tag 07IE], hence what the small crystalline site `Cris(S₀/S)` and its
topos are built from; the arrow is then the one of [Stacks, Tag 07IK] for change of divided power
base along the identity of `(S, I, γ)`, whose left exactness of `i_!` for `S₀/S` makes the
retraction `π_{S₀}` of [Stacks, Tag 07IJ] a morphism of topoi. -/
@[stacks 07IM "the top arrow f_cris : (X/S)_cris ⟶ (S₀/S)_cris of the diagram, together with the
  site Cris(S₀/S) it lands in, for p locally nilpotent on S₀ = V(I), which is the remark's own
  standing condition on this arrow"]
def closedFiberCrisMorphism
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x)) :
    MorphismOfTopoi (smallTopos S) (smallTopos (closedFiberSituation S hlocnil)) :=
  crisMorphism S (closedFiberSituation S hlocnil) (𝟙 S.S) S.toClosedFiber
    (closedFiberSituation_comm S hlocnil)

/-- **The top arrow of the diagram is the detour of [Stacks, Tag 07IK].**  It is
`π_{S₀} ∘ f_CRIS ∘ i_X`, with `i_X` the inclusion morphism of topoi of [Stacks, Tag 07IJ],
`f_CRIS` the arrow `closedFiberMorphism` of the big crystalline diagram of [Stacks, Tag 07IE], and
`π_{S₀}` the retraction of [Stacks, Tag 07IJ]. -/
theorem closedFiberCrisMorphism_eq
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x)) :
    closedFiberCrisMorphism S hlocnil =
      (retractionMorphism (closedFiberSituation S hlocnil)).comp
        ((closedFiberMorphism S hlocnil).comp (smallToBigMorphism S)) :=
  rfl

/-- **Stacks Project, Tag 07IM.**  The trailing arrow of the diagram: the small Zariski morphism
`f_small : Sh(X_Zar) ⟶ Sh(S₀, Zar)` along the structure morphism `f : X ⟶ S₀`, followed by the
small Zariski morphism `Sh(S₀, Zar) ⟶ Sh(S_Zar)` along the closed immersion `S₀ ⟶ S`, is the small
Zariski morphism along `X ⟶ S`. -/
@[stacks 07IM "the trailing arrow of the diagram: the small Zariski morphisms along X ⟶ S₀ and
  S₀ ⟶ S compose to the one along X ⟶ S, as an invertible 2-morphism of topoi"]
def smallZariskiStructureTriangle :
    ((opensMapMorphismOfTopoi (DividedPowerScheme.closedFiberι S.S).base).comp
        (opensMapMorphismOfTopoi S.toClosedFiber.base)).pushforward ≅
      (opensMapMorphismOfTopoi (sourceToBase S).base).pushforward :=
  opensMapMorphismOfTopoiComp S.toClosedFiber.base (DividedPowerScheme.closedFiberι S.S).base

/-- **Stacks Project, Tag 07IM.**  The structure morphism
`τ_{X/S} : (X/S)_cris ⟶ Sh(S_Zar)` is the lower route of the diagram: the comparison `u_{X/S}` of
[Stacks, Tag 07IL], then the small Zariski morphism along `X ⟶ S₀`, then the small Zariski
morphism along `S₀ ⟶ S`.  This is the route the remark takes as the definition of `τ_{X/S}`, and
it does not assume `p` locally nilpotent on `S₀`. -/
@[stacks 07IM "the structure morphism τ_{X/S} is the lower route of the diagram, u_{X/S} followed
  by f_small and then by the trailing arrow, as an invertible 2-morphism of topoi,
  with no hypothesis on p.  The diagram's upper square u_{S₀/S} ∘ f_cris ≅ f_small ∘ u_{X/S} is a separate
  clause of the remark and is registered separately, on
  Crystalline.GlobalCrystallineSituation.closedFiberCrisUpperSquare of SmallSite/UpperSquare.lean"]
def structureToposMorphism_isoLowerRoute :
    ((opensMapMorphismOfTopoi (DividedPowerScheme.closedFiberι S.S).base).comp
        ((opensMapMorphismOfTopoi S.toClosedFiber.base).comp
          (zariskiToposMorphism S))).pushforward ≅
      (structureToposMorphism S).pushforward :=
  Functor.isoWhiskerLeft (zariskiToposMorphism S).pushforward (smallZariskiStructureTriangle S)

/-- **The two routes from `X` to the divided power base `S'` agree on topological spaces.**  The
composites `X ⟶ S ⟶ S'` and `X ⟶ Y ⟶ S'` are the same morphism of schemes, by
`Crystalline.GlobalCrystallineSituation.comp_sourceToBase`, hence have the same continuous map. -/
theorem comp_sourceToBase_base (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    g.base ≫ (sourceToBase S').base = (sourceToBase S).base ≫ f.hom.base := by
  rw [← Scheme.Hom.comp_base, comp_sourceToBase (h := h), Scheme.Hom.comp_base]

/-- **The Zariski half of the square of [Stacks, Tag 07MH].**  The small Zariski morphism along
`X ⟶ S` followed by the one along `S ⟶ S'` agrees with the one along `X ⟶ Y` followed by the one
along `Y ⟶ S'`, both being the small Zariski morphism along the single morphism of schemes
`X ⟶ S'`.  No crystalline topos appears; the square of the remark itself is
`Crystalline.GlobalCrystallineSituation.SmallSite.structureSquareTwoIso`. -/
def smallZariskiChangeBaseSquare (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    ((opensMapMorphismOfTopoi f.hom.base).comp
        (opensMapMorphismOfTopoi (sourceToBase S).base)).pushforward ≅
      ((opensMapMorphismOfTopoi (sourceToBase S').base).comp
        (opensMapMorphismOfTopoi g.base)).pushforward :=
  opensMapMorphismOfTopoiComp (sourceToBase S).base f.hom.base ≪≫
    opensMapMorphismOfTopoiCongr (comp_sourceToBase_base S S' f g h).symm ≪≫
    (opensMapMorphismOfTopoiComp g.base (sourceToBase S').base).symm

/-- **The lower route of the square of [Stacks, Tag 07MH].**  The structure morphism `τ_{X/S}`
followed by the small Zariski morphism along `S ⟶ S'` is the comparison `u_{X/S}` of
[Stacks, Tag 07IL] followed by the small Zariski morphisms along `X ⟶ Y` and `Y ⟶ S'`.  It is to
the square of [Stacks, Tag 07MH] what
`Crystalline.GlobalCrystallineSituation.structureToposMorphism_isoLowerRoute` is to the diagram of
[Stacks, Tag 07IM]: the part of the square that does not meet the obstruction (★).  The square of
the remark itself is `Crystalline.GlobalCrystallineSituation.SmallSite.structureSquareTwoIso`. -/
def changeBaseSmallStructureLowerRoute (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    ((opensMapMorphismOfTopoi f.hom.base).comp (structureToposMorphism S)).pushforward ≅
      ((opensMapMorphismOfTopoi (sourceToBase S').base).comp
        ((opensMapMorphismOfTopoi g.base).comp (zariskiToposMorphism S))).pushforward :=
  Functor.isoWhiskerLeft (zariskiToposMorphism S).pushforward
    (smallZariskiChangeBaseSquare S S' f g h)

/-- **The square of [Stacks, Tag 07MG] restricted to the small crystalline topos of `X/S`.**  The
two targets are the *big* Zariski topoi `Sh((Sch/S)_Zar)` and `Sh((Sch/S')_Zar)`, the vertical
arrows are the structure morphisms of the big crystalline sites of [Stacks, Tag 07IE], the left one
read on the small crystalline topos along the inclusion `i_X` of [Stacks, Tag 07IJ], the bottom
arrow is the big Zariski morphism along `(S, I, γ) ⟶ (S', I', γ')` and the top arrow is the
composite `f_CRIS ∘ i_X : (X/S)_cris ⟶ (Y/S')_CRIS` of the inclusion with change of divided power
base.  It holds for every `f` and `g`: it is the square of [Stacks, Tag 07MG] whiskered with the
direct image of `i_X`.

It is not the square of [Stacks, Tag 07MH]: its top right corner is the big crystalline topos
`(Y/S')_CRIS`, not `(Y/S')_cris`, and its top arrow is `f_CRIS ∘ i_X`, not
`f_cris = π_Y ∘ f_CRIS ∘ i_X` of [Stacks, Tag 07IK].  The square of the remark, with the small
Zariski topoi at the bottom in which the structure morphisms `τ` of [Stacks, Tag 07IM] land, is
`Crystalline.GlobalCrystallineSituation.SmallSite.structureSquareTwoIso`. -/
def changeBaseSmallStructureSquareOfComparison (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    ((zariskiOverMorphism f.hom).comp
        ((structureMorphism S).comp (smallToBigMorphism S))).pushforward ≅
      ((structureMorphism S').comp
        ((changeBaseMorphism S S' f g h).comp (smallToBigMorphism S))).pushforward :=
  Functor.isoWhiskerLeft (smallToBigMorphism S).pushforward
    (changeBaseStructureSquare S S' f g h)

/-! ### The closed fibre as a terminal object of its own crystalline site

The structure `Cris(S₀/S)` acquires when `p` is nilpotent on the base, made explicit.  When the
closed fibre inclusion `S₀ ↪ S` is itself a thickening — equivalently, by
`Crystalline.DividedPowerScheme.isThickening_closedFiberι_iff`, when the divided power ideal `I`
is locally nilpotent, which by [Stacks, Tag 07GR] is nilpotence of `p` on `S` — the triple
`(S₀, S, γ)` is an object of `Cris(S₀/S)`, and it is a *terminal* object:
a morphism into it is forced, its two components being the structure maps `U ⟶ S₀` and `T ⟶ S` of
the source object.

That condition is strictly stronger than the standing hypotheses, as the equivalence just cited
and the example `S = Spec ℤ_(p)` with divided power ideal `(p)` show, so it is worth recording
what the terminal object is and is not for.  It is **not** what the upper square of
[Stacks, Tag 07IM] rests on: that square holds at the remark's own hypotheses, by the
covering-local route of `SmallSite/CrisZariskiSquare{Covering, Limit, Iso}.lean`, as
`Crystalline.GlobalCrystallineSituation.closedFiberCrisUpperSquare`.  Nor does it
bear on the square of [Stacks, Tag 07MH], whose data is a *general* `f : X ⟶ Y` over `S ⟶ S'`: the
obstruction (★) of the module docstring is a statement about `Cris(Y/S')`, and `Cris(Y/S')` has no
terminal object for general `Y` over `S'₀` — a terminal object there would be a universal divided
power thickening of `Y` over `(S', I', γ')`, which is what divided power envelopes of embeddings
into smooth schemes replace, cofinally and not terminally.
-/

/-- **The closed fibre thickened by the divided power base: the object `(S₀, S, γ)` of
`CRIS(S₀/S)`.**  Its thickening is the closed fibre inclusion `S₀ ↪ S`, which is a thickening of
schemes by the hypothesis `hthick` and whose defining ideal is the divided power ideal by
`Crystalline.DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι`; its divided power map to the
base and its map to `S₀` are both identities.

The hypothesis `hthick` is discharged by
`Crystalline.DividedPowerScheme.isThickening_closedFiberι_of_isNilpotent_natCast`, hence by
[Stacks, Tag 07GR]; the hypothesis `hlocnil` is the one of
`Crystalline.GlobalCrystallineSituation.closedFiberSituation`, [Stacks, Tag 07IE], which produces
the situation on the closed fibre and hence the category this object lives in. -/
def closedFiberThickening
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    Thickening (closedFiberSituation S hlocnil) where
  thickening :=
    { source := DividedPowerScheme.closedFiber S.S
      target := S.S
      immersion := DividedPowerScheme.closedFiberι S.S
      isThickening := hthick
      ideal_eq_ker := DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι S.S }
  toBase := 𝟙 S.S
  toX := 𝟙 _
  over_base := by simp [sourceToBase]

/-- The thickened scheme of `closedFiberThickening` is the closed fibre `S₀`. -/
@[simp]
theorem closedFiberThickening_thickening_source
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    (closedFiberThickening S hlocnil hthick).thickening.source =
      DividedPowerScheme.closedFiber S.S :=
  rfl

/-- The ambient scheme of `closedFiberThickening` is the base `S`. -/
@[simp]
theorem closedFiberThickening_thickening_target
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    (closedFiberThickening S hlocnil hthick).thickening.target = S.S :=
  rfl

/-- The thickening of `closedFiberThickening` is the closed fibre inclusion `S₀ ↪ S`. -/
@[simp]
theorem closedFiberThickening_thickening_immersion
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    (closedFiberThickening S hlocnil hthick).thickening.immersion =
      DividedPowerScheme.closedFiberι S.S :=
  rfl

/-- The divided power map of `closedFiberThickening` to the base is the identity of `S`. -/
@[simp]
theorem closedFiberThickening_toBase
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    (closedFiberThickening S hlocnil hthick).toBase = 𝟙 S.S :=
  rfl

/-- The map of `closedFiberThickening` to `S₀` is the identity of `S₀`. -/
@[simp]
theorem closedFiberThickening_toX
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    (closedFiberThickening S hlocnil hthick).toX = 𝟙 (DividedPowerScheme.closedFiber S.S) :=
  rfl

/-- **The morphism of `CRIS(S₀/S)` from an arbitrary object to `(S₀, S, γ)`.**  Its map on
thickened schemes is the structure map `U ⟶ S₀` of the source object and its divided power map on
ambient schemes is the structure map `T ⟶ S`; the square of thickenings it has to make commute is
exactly the compatibility `Crystalline.GlobalCrystallineSituation.Thickening.over_base` carried by
that object. -/
def toClosedFiberThickening
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S))
    (A : Thickening (closedFiberSituation S hlocnil)) :
    A ⟶ closedFiberThickening S hlocnil hthick where
  sourceHom := A.toX
  targetHom := A.toBase
  immersion_naturality := by simpa [sourceToBase] using A.over_base
  base_naturality := Category.comp_id _
  toX_naturality := Category.comp_id _

/-- The map on thickened schemes of `toClosedFiberThickening A` is the structure map `U ⟶ S₀`
of `A`. -/
@[simp]
theorem toClosedFiberThickening_sourceHom
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S))
    (A : Thickening (closedFiberSituation S hlocnil)) :
    (toClosedFiberThickening S hlocnil hthick A).sourceHom = A.toX :=
  rfl

/-- The map on ambient schemes of `toClosedFiberThickening A` is the structure map `T ⟶ S` of
`A`. -/
@[simp]
theorem toClosedFiberThickening_targetHom
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S))
    (A : Thickening (closedFiberSituation S hlocnil)) :
    (toClosedFiberThickening S hlocnil hthick A).targetHom = A.toBase :=
  rfl

/-- **`(S₀, S, γ)` is a terminal object of `CRIS(S₀/S)`.**  A morphism into it has no freedom: the
compatibility of its divided power map with the structure maps to the base forces that map to be
the structure map `T ⟶ S`, and the compatibility of its map on thickened schemes with the maps to
`S₀` forces that one to be the structure map `U ⟶ S₀`. -/
def isTerminal_closedFiberThickening
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    IsTerminal (closedFiberThickening S hlocnil hthick) :=
  IsTerminal.ofUniqueHom (toClosedFiberThickening S hlocnil hthick) fun _ f ↦
    Thickening.Hom.ext ((Category.comp_id f.sourceHom).symm.trans f.toX_naturality)
      ((Category.comp_id f.targetHom).symm.trans f.base_naturality)

/-- **`(S₀, S, γ)` lies in the small crystalline site.**  Its map to `S₀` is the identity, which is
an open immersion. -/
theorem isCrystalline_closedFiberThickening
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    Thickening.IsCrystalline (closedFiberThickening S hlocnil hthick) := by
  change IsOpenImmersion (𝟙 (DividedPowerScheme.closedFiber S.S))
  infer_instance

/-- **`(S₀, S, γ)` as an object of the small crystalline site `Cris(S₀/S)`.** -/
def closedFiberCrystallineThickening
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    CrystallineThickening (closedFiberSituation S hlocnil) :=
  ⟨closedFiberThickening S hlocnil hthick, isCrystalline_closedFiberThickening S hlocnil hthick⟩

/-- **`(S₀, S, γ)` is a terminal object of `Cris(S₀/S)`.**  It is terminal in the big crystalline
category and lies in the small one, which is a full subcategory. -/
def isTerminal_closedFiberCrystallineThickening
    (hlocnil : ∀ x : DividedPowerScheme.closedFiber S.S,
      IsNilpotent (S.p : (DividedPowerScheme.closedFiber S.S).presheaf.stalk x))
    (hthick : IsThickening (DividedPowerScheme.closedFiberι S.S)) :
    IsTerminal (closedFiberCrystallineThickening S hlocnil hthick) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ ObjectProperty.homMk (toClosedFiberThickening S hlocnil hthick A.obj))
    fun _ _ ↦ ObjectProperty.hom_ext _
      ((isTerminal_closedFiberThickening S hlocnil hthick).hom_ext _ _)

end Crystalline.GlobalCrystallineSituation

end
