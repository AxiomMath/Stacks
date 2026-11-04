module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankStratum
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LocallyFreeChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# The locus on an algebraic space where the bottom cohomology of a derived pullback is free

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `E` be an
object of the derived category of `𝒪_X`-modules on the small étale site of `X`, let `a` be an
integer and let `r` be a natural number. A morphism `f : Y ⟶ X` of algebraic spaces is
*universally of bottom rank `r`* when, for every further morphism `g : Y' ⟶ Y`, the
`𝒪_{Y'}`-module `H^a(L(g ∘ f)^* E)` is finite locally free of rank `r`
(`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank`, the notion of Stacks 0D20). A
morphism `j : Z ⟶ X` which is an immersion of algebraic spaces is a
*bottom rank `r` stratum* for `E` in degree `a` when `H^a(Lj^* E)` is finite locally free of rank
`r` and a morphism `f : Y ⟶ X` factors through `j` exactly when it is universally of bottom rank
`r`. These are the two descriptions by which [stacks 0D21] characterises its locally closed
subspace.

Three things are proved about this notion, and all three are unconditional. Being universally of
bottom rank `r` is stable under precomposition, and at the identity it gives back finite local
freeness of rank `r` of `H^a(Lf^* E)`. A bottom rank `r` stratum is itself universally of bottom
rank `r`, because it factors through itself through the identity. And the two descriptions
determine the stratum: any two bottom rank `r` strata for the same data are related by a unique
isomorphism over `X`, because an immersion of algebraic spaces is a monomorphism of presheaves.

The existence of a stratum is not unconditional, and the input it needs is carried as a named
hypothesis, in the manner of
`AlgebraicGeometry.Space.isEtaleLocallyConstructible_setOf_eq` and of the derived
pullback-stalk comparison of
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricStalkCohomologyMap.lean`:
`AlgebraicGeometry.Space.BottomRankLocus.BottomRankBaseChange`, the derived-pullback
computation: that rank `r` local freeness of `H^a(Lf^* E)` is inherited by further pullbacks.
Under it the universal condition of description (2) collapses to the plain one, and a subspace
representing the plain condition is a bottom rank `r` stratum.

## Main definitions

* `AlgebraicGeometry.Space.BottomRankLocus.pullbackHomology`: the `𝒪_Y`-module
  `H^a(Lf^* E)`.
* `AlgebraicGeometry.Space.BottomRankLocus.IsUniversallyFreeBottom`: the condition on
  `f : Y ⟶ X` that `H^a(L(g ∘ f)^* E)` be finite locally free of rank `r` for every
  `g : Y' ⟶ Y`.
* `AlgebraicGeometry.Space.BottomRankLocus.BottomRankBaseChange`: the derived-pullback
  computation, as the statement that rank `r` local freeness of `H^a(Lf^* E)` passes to
  `H^a(L(g ∘ f)^* E)`.
* `AlgebraicGeometry.Space.BottomRankLocus.IsBottomRankStratum`: the condition on a morphism
  `j : Z ⟶ X` of being an immersion satisfying the two descriptions above.

## Main results

* `AlgebraicGeometry.Space.BottomRankLocus.IsUniversallyFreeBottom.comp` and
  `AlgebraicGeometry.Space.BottomRankLocus.IsUniversallyFreeBottom.self`: the condition is
  stable under precomposition, and implies finite local freeness of rank `r` of `H^a(Lf^* E)`.
* `AlgebraicGeometry.Space.BottomRankLocus.IsBottomRankStratum.isUniversallyFreeBottom`: a
  bottom rank `r` stratum is itself universally of bottom rank `r`.
* `AlgebraicGeometry.Space.BottomRankLocus.IsBottomRankStratum.existsUnique_iso`: two bottom
  rank `r` strata for the same data are related by a unique isomorphism over `X`.
* `AlgebraicGeometry.Space.BottomRankLocus.isUniversallyFreeBottom_iff`: under the
  derived-pullback computation the universal condition is the plain one.
* `AlgebraicGeometry.Space.BottomRankLocus.exists_isBottomRankStratum`: descriptions (1) and
  (2) and finite presentation, from the derived-pullback computation and the étale-localization
  input; superseded by the unconditional
  `AlgebraicGeometry.Space.BottomRankLocus.exists_isBottomRankStratum_isFinitePresentation`.
* `AlgebraicGeometry.Space.BottomRankLocus.factorsThrough_iff_isFiniteLocallyFreeOfRank`:
  part (4), (a) if and only if (b), conditional on the derived-pullback computation.
* `AlgebraicGeometry.Space.BottomRankLocus.isBottomRankStratum_id`: the identity of `X` is a
  bottom rank `r` stratum as soon as `H^a(L(𝟙_X)^* E)` is finite locally free of rank `r`, which
  is what keeps the conditional existence statement from being vacuous.

## Implementation notes

The rank is a natural number, where the source says `r ≥ 0`.

The universal condition quantifies over all morphisms `g : Y' ⟶ Y` out of the source rather than
asking finite local freeness of `H^a(Lf^* E)` alone. That is what the source asks, and on a
general `E` the two are not the same: the bottom cohomology of a derived pullback is not the
pullback of the bottom cohomology. Making them the same is exactly the content of
`BottomRankBaseChange`.

Finite local freeness of rank `r` is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank` at `(r : ℤ)`, as for Stacks 0D20;
it is étale local
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfIntRank_homology_iff_forall_chart`), which is what
lets the universal condition be tested on represented sources
(`isUniversallyFreeBottom_of_forall_representable`).

The derived category model is `CategoryTheory.HasDerivedCategory.standard`, installed as a local
instance, as it is in the file defining the derived pullback; a statement proved at one model of
`HasDerivedCategory` says nothing about another.

**Why `E` carries no hypothesis.** The source takes `E` perfect of Tor amplitude in `[a, b]`.
Nothing below uses either, and the statements are correspondingly stated for an arbitrary object
of `D(𝒪_X)`. That is not a strengthening of the tag: perfectness and the Tor amplitude are what
power the construction of `Z` in the scheme case, and the construction is precisely what is
carried here as the hypothesis `hstratum`. An existence statement with fewer hypotheses on `E`
and an extra hypothesis supplying the object whose existence is asserted is weaker, not stronger,
and the section below says so.

### The conditional statements below are not registered

The unconditional statement is
`AlgebraicGeometry.Space.BottomRankLocus.exists_isBottomRankStratum_isFinitePresentation` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/BottomRankStratumExistence.lean`; the notes below
describe the earlier conditional versions, which carry no `@[stacks]` attribute.

The tag asserts, for `E` perfect of Tor amplitude in `[a, b]`, the existence of a locally closed
subspace `j : Z ⟶ X` with descriptions (1) and (2), together with its finite presentation, the
base-change formula (3), and, when `β_a ≤ r` everywhere, the closedness of `j` and the
equivalence of (4)(a), (4)(b) and — for `r = 1` — (4)(c). Its proof is "follows from the case of
schemes by étale localization", citing [stacks 0BDL].

The two conditional statements are the following.

* `exists_isBottomRankStratum` proves the existence of a `j` with descriptions (1) and (2) and
  its finite presentation **from** `hbc`, the derived-pullback computation, **and** `hstratum`,
  an immersion of finite presentation through which a morphism factors exactly when the plain
  rank condition holds at it. `hstratum` is what [stacks 0BDL] plus descent along an étale chart
  would supply, and it is not supplied here; what the theorem adds to it is the passage from the
  plain condition to the universal condition of description (2), which is `hbc` and nothing else.
* `factorsThrough_iff_isFiniteLocallyFreeOfRank` is the equivalence of (4)(a) and (4)(b) for a
  bottom rank `r` stratum, again under `hbc`. As in the scheme case, no bound on the derived
  fibre Betti numbers enters: `hbc` is what the bound is used for.

Four things are not covered. Part (3), the identification `H^a(Lf^* E) = g^* H^a(Lj^* E)`, is an
isomorphism of `𝒪_Y`-modules and not merely the transport of a rank, and nothing in this
development produces it: every route to computing `Lf^*` — `derivedPullbackSingleFunctorObjIso`,
`derivedPullbackObjIsoOfFlat`, the composition isomorphism of [stacks 0D6D] — presents the
morphism of ringed topoi by a functor of the underlying sites, and
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` ([stacks 03G8]) is a bare
`AlgebraicGeometry.RingedToposHom` with no such presentation. The closedness of `j` under a Betti
bound, and part (4)(c), are not treated: the former needs the Betti function of [stacks 0D1Y],
which in this development is itself data
(`AlgebraicGeometry.Space.IsEtaleLocallyDerivedFibreBetti`), and the latter needs the internal
endomorphism sheaf of `H^a(Lf^* E)`. And the étale localization itself is absent at both ends:
the scheme case [stacks 0BDL] is proved in
`StacksFrontier/AlgebraicGeometry/Perfect/BottomRankStratum.lean` only for an `E` which is a finite
type quasi-coherent module placed in degree `a`, and no comparison identifies the derived
pullback along an étale chart `V ⟶ X` from a scheme with the derived pullback of sheaves of
modules on `V` itself.

`IsBottomRankStratum.existsUnique_iso` is the uniqueness carried by the word "characterized"; as
in the scheme case it is a consequence of description (2), not a part of the tag, and is
untagged. `isBottomRankStratum_id` is the degenerate case `Z = X`; it is a genuine instance of
the tag's conclusion, with no appeal to `hstratum`, and it is recorded so that the conditional
existence statement is visibly not vacuous. It is untagged because it omits the finite
presentation of `j`, which for the identity would be quasi-compactness and quasi-separatedness of
`X` over itself and is not proved here.

## References

* [The Stacks Project, Lemma 75.26.6 (0D21)](https://stacks.math.columbia.edu/tag/0D21)
* [The Stacks Project, Lemma 36.31.4 (0BDL)](https://stacks.math.columbia.edu/tag/0BDL)
* [The Stacks Project, Section 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [The Stacks Project, Section 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [The Stacks Project, Definition 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.BottomRankLocus

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The bottom cohomology of a derived pullback -/

/-- **The `𝒪_Y`-module `H^a(Lf^* E)`.** The degree-`a` cohomology sheaf of the derived pullback
of `E` along `f : Y ⟶ X`. -/
def pullbackHomology {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) :=
  (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) a).obj
    ((smallEtaleDerivedModulePullback B S hS f).obj E)

/-! ### Morphisms universally of bottom rank `r` -/

/-- **A morphism universally of bottom rank `r`.** The morphism `f : Y ⟶ X` is universally of
bottom rank `r` for `E` in degree `a` when, for every morphism `g : Y' ⟶ Y`, the
`𝒪_{Y'}`-module `H^a(L(g ∘ f)^* E)` is finite locally free of rank `r`.

This is the right-hand side of description (2) of [stacks 0D21]. -/
def IsUniversallyFreeBottom
    {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (r : ℕ) {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) : Prop :=
  ∀ (Y' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y),
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      (pullbackHomology E a (g ≫ f)) (r : ℤ)

/-- **The derived-pullback computation.** Rank `r` local freeness of `H^a(Lf^* E)` passes to
`H^a(L(g ∘ f)^* E)` for every further `g : Y' ⟶ Y`.

This is the part of the base-change formula (3) of [stacks 0D21] that the characterisation uses.
It is not available in this development: computing `L(g ∘ f)^*` from `Lf^*` needs the
composition isomorphism of [stacks 0D6D], which presents a morphism of ringed topoi by a functor
of the underlying sites, and `AlgebraicGeometry.Space.smallEtaleRingedToposHom` carries no such
presentation. -/
def BottomRankBaseChange
    {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (r : ℕ) : Prop :=
  ∀ {Y Y' : AlgebraicSpaces B S hS} (f : Y ⟶ X) (g : Y' ⟶ Y),
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      (pullbackHomology E a f) (r : ℤ) →
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      (pullbackHomology E a (g ≫ f)) (r : ℤ)

variable {X : AlgebraicSpaces B S hS}
  {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  {a : ℤ} {r : ℕ}

/-- **Being universally of bottom rank `r` is stable under precomposition.** The condition for
`g ∘ f` quantifies over the morphisms `k` and asks about `(k ∘ g) ∘ f`, so it is the condition
for `f` read at the composites `k ∘ g`. -/
theorem IsUniversallyFreeBottom.comp {Y Y' : AlgebraicSpaces B S hS} {f : Y ⟶ X}
    (h : IsUniversallyFreeBottom E a r f) (g : Y' ⟶ Y) :
    IsUniversallyFreeBottom E a r (g ≫ f) := by
  intro Y'' k
  simpa only [Category.assoc] using h Y'' (k ≫ g)

/-- **A morphism universally of bottom rank `r` has `H^a(Lf^* E)` finite locally free of rank
`r`.** This is the condition at the identity. -/
theorem IsUniversallyFreeBottom.self {Y : AlgebraicSpaces B S hS} {f : Y ⟶ X}
    (h : IsUniversallyFreeBottom E a r f) :
    SheafOfModules.IsFiniteLocallyFreeOfIntRank
      (pullbackHomology E a f) (r : ℤ) := by
  simpa only [Category.id_comp] using h Y (𝟙 Y)

/-- **The universal condition may be tested on represented sources.** A morphism `f : Y ⟶ X` is
universally of bottom rank `r` as soon as `H^a(L(t ∘ f)^* E)` is finite locally free of rank `r`
for every morphism `t` to `Y` from the algebraic space represented by an object of the site: for
an arbitrary `g : Y' ⟶ Y` this is the condition at the étale charts of `Y'`, and finite local
freeness is étale local. -/
theorem isUniversallyFreeBottom_of_forall_representable {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (h : ∀ (T : BigFppfOver B S hS)
      (t : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y),
      SheafOfModules.IsFiniteLocallyFreeOfIntRank (pullbackHomology E a (t ≫ f)) (r : ℤ)) :
    IsUniversallyFreeBottom E a r f := by
  intro Y' g
  refine (isFiniteLocallyFreeOfIntRank_homology_iff_forall_chart B S hS (g ≫ f) E a r).2
    fun y => ?_
  obtain ⟨V, hV⟩ := exists_smallEtale_mem_range B S hS Y'.2 y
  have hV' := h V.1.left (chartToSpace B S hS Y' V ≫ g)
  have e : (chartToSpace B S hS Y' V ≫ g) ≫ f = chartToSpace B S hS Y' V ≫ g ≫ f :=
    Category.assoc _ _ _
  exact ⟨V, hV, isFiniteLocallyFreeOfIntRank_of_iso B S hS
    (eqToIso (congrArg (fun k => pullbackHomology E a k) e)) hV'⟩

/-- **Under the derived-pullback computation the universal condition is the plain one.** The
quantification over further morphisms in description (2) of [stacks 0D21] costs nothing as soon
as rank `r` local freeness of the bottom cohomology is inherited by further pullbacks. -/
theorem isUniversallyFreeBottom_iff (hbc : BottomRankBaseChange E a r)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    IsUniversallyFreeBottom E a r f ↔
      SheafOfModules.IsFiniteLocallyFreeOfIntRank
        (pullbackHomology E a f) (r : ℤ) :=
  ⟨fun h => h.self, fun h _ g => hbc f g h⟩

/-! ### Bottom rank strata and their uniqueness -/

/-- **A bottom rank `r` stratum.** The morphism `j : Z ⟶ X` is an immersion of algebraic spaces,
`H^a(Lj^* E)` is finite locally free of rank `r`, and a morphism `f : Y ⟶ X` factors through `j`
exactly when it is universally of bottom rank `r`.

These are the two descriptions by which [stacks 0D21] characterises its locally closed subspace;
the tag's assertion that such a `j` exists for `E` perfect of Tor amplitude in `[a, b]` is proved
below only from the hypotheses of `exists_isBottomRankStratum`. -/
structure IsBottomRankStratum
    {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (r : ℕ) {Z : AlgebraicSpaces B S hS} (j : Z ⟶ X) : Prop where
  /-- `j` is an immersion, so `Z` is a locally closed subspace of `X`. -/
  isImmersion : IsImmersion B S hS j.hom
  /-- Description (1): `H^a(Lj^* E)` is finite locally free of rank `r`. -/
  freeRank : SheafOfModules.IsFiniteLocallyFreeOfIntRank
    (pullbackHomology E a j) (r : ℤ)
  /-- Description (2): a morphism factors through `j` exactly when it is universally of bottom
  rank `r`. -/
  factorsThrough_iff : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
    (∃ g : Y ⟶ Z, g ≫ j = f) ↔ IsUniversallyFreeBottom E a r f

/-- **A bottom rank `r` stratum is itself universally of bottom rank `r`.** It factors through
itself through the identity, so description (2) applies to it. -/
theorem IsBottomRankStratum.isUniversallyFreeBottom {Z : AlgebraicSpaces B S hS} {j : Z ⟶ X}
    (h : IsBottomRankStratum E a r j) : IsUniversallyFreeBottom E a r j :=
  (h.factorsThrough_iff Z j).1 ⟨𝟙 Z, Category.id_comp j⟩

/-- **Description (2) determines the stratum.** Two bottom rank `r` strata for the same `E`, `a`
and `r` are related by a unique isomorphism over `X`.

Each stratum is universally of bottom rank `r`, so each factors through the other; the two
factorisations compose to the identity because an immersion is a monomorphism, and that same
monomorphism property makes the morphism over `X`, hence the isomorphism, unique. -/
theorem IsBottomRankStratum.existsUnique_iso {Z₁ Z₂ : AlgebraicSpaces B S hS} {j₁ : Z₁ ⟶ X}
    {j₂ : Z₂ ⟶ X} (h₁ : IsBottomRankStratum E a r j₁)
    (h₂ : IsBottomRankStratum E a r j₂) :
    ∃! e : Z₁ ≅ Z₂, e.hom ≫ j₂ = j₁ := by
  have m₁ : Mono j₁ := BottomRankStratum.mono_of_isImmersion h₁.isImmersion
  have m₂ : Mono j₂ := BottomRankStratum.mono_of_isImmersion h₂.isImmersion
  obtain ⟨g₁, hg₁⟩ := (h₂.factorsThrough_iff Z₁ j₁).2 h₁.isUniversallyFreeBottom
  obtain ⟨g₂, hg₂⟩ := (h₁.factorsThrough_iff Z₂ j₂).2 h₂.isUniversallyFreeBottom
  have h12 : g₁ ≫ g₂ = 𝟙 Z₁ := by
    refine (cancel_mono j₁).1 ?_
    rw [Category.assoc, hg₂, hg₁, Category.id_comp]
  have h21 : g₂ ≫ g₁ = 𝟙 Z₂ := by
    refine (cancel_mono j₂).1 ?_
    rw [Category.assoc, hg₁, hg₂, Category.id_comp]
  exact ⟨⟨g₁, g₂, h12, h21⟩, hg₁, fun e he => Iso.ext ((cancel_mono j₂).1 (he.trans hg₁.symm))⟩

/-! ### The conditional existence statement -/

/-- **A subspace representing the plain rank condition is a bottom rank `r` stratum.** Under the
derived-pullback computation the plain condition and the universal condition of description (2)
agree, and description (1) is the plain condition read at `j` itself. -/
theorem isBottomRankStratum_of_factorsThrough_iff (hbc : BottomRankBaseChange E a r)
    {Z : AlgebraicSpaces B S hS} {j : Z ⟶ X} (hj : IsImmersion B S hS j.hom)
    (hfactor : ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
      (∃ g : Y ⟶ Z, g ≫ j = f) ↔
        SheafOfModules.IsFiniteLocallyFreeOfIntRank
          (pullbackHomology E a f) (r : ℤ)) :
    IsBottomRankStratum E a r j where
  isImmersion := hj
  freeRank := (hfactor Z j).1 ⟨𝟙 Z, Category.id_comp j⟩
  factorsThrough_iff Y f := (hfactor Y f).trans (isUniversallyFreeBottom_iff hbc f).symm

/-- **Stacks 0D21, descriptions (1) and (2) and the finite presentation of `j`**, conditional on
the derived-pullback computation `hbc` and on the étale-localization input `hstratum`.

`hstratum` asks for an immersion of finite presentation through which a morphism `f : Y ⟶ X`
factors exactly when `H^a(Lf^* E)` is finite locally free of rank `r` — the plain rank condition,
which is condition (4)(b) of the source. That is what the scheme case [stacks 0BDL] together with
descent along an étale chart would supply, and neither half of that is available here. What this
theorem contributes is the passage from the plain condition to the universal condition of
description (2), and that passage is `hbc`. -/
theorem exists_isBottomRankStratum (hbc : BottomRankBaseChange E a r)
    (hstratum : ∃ (Z : AlgebraicSpaces B S hS) (j : Z ⟶ X),
      IsImmersion B S hS j.hom ∧ IsFinitePresentation B S hS j.hom ∧
        ∀ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
          (∃ g : Y ⟶ Z, g ≫ j = f) ↔
            SheafOfModules.IsFiniteLocallyFreeOfIntRank
              (pullbackHomology E a f) (r : ℤ)) :
    ∃ (Z : AlgebraicSpaces B S hS) (j : Z ⟶ X),
      IsBottomRankStratum E a r j ∧ IsFinitePresentation B S hS j.hom := by
  obtain ⟨Z, j, hj, hfp, hfactor⟩ := hstratum
  exact ⟨Z, j, isBottomRankStratum_of_factorsThrough_iff hbc hj hfactor, hfp⟩

/-- **Stacks 0D21, part (4), (a) if and only if (b)**, conditional on the derived-pullback
computation `hbc`: a morphism factors through a bottom rank `r` stratum exactly when
`H^a(Lf^* E)` is finite locally free of rank `r`.

No bound on the derived-fibre Betti numbers enters, exactly as in the scheme case: the bound is
what the source uses to make the quantification over further morphisms in description (2) cost
nothing, and here that is `hbc`. -/
theorem factorsThrough_iff_isFiniteLocallyFreeOfRank (hbc : BottomRankBaseChange E a r)
    {Z : AlgebraicSpaces B S hS} {j : Z ⟶ X} (h : IsBottomRankStratum E a r j)
    (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z, g ≫ j = f) ↔
      SheafOfModules.IsFiniteLocallyFreeOfIntRank
        (pullbackHomology E a f) (r : ℤ) :=
  (h.factorsThrough_iff Y f).trans (isUniversallyFreeBottom_iff hbc f)

/-! ### The subfunctor of points universally of bottom rank `r` -/

/-- The morphism of algebraic spaces from a represented space given by a section. -/
abbrev sectionMap (T : BigFppfOver B S hS) (x : X.1.obj (Opposite.op T)) :
    (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ X :=
  ObjectProperty.homMk (yonedaEquiv.symm x)

/-- The morphism given by the restriction of a section `x` along `i : T' ⟶ T` is the composite of
the represented morphism `h_{T'} ⟶ h_T` with the morphism given by `x`. -/
theorem sectionMap_map {T T' : BigFppfOver B S hS} (i : T' ⟶ T) (x : X.1.obj (Opposite.op T)) :
    sectionMap T' (X.1.map i.op x) = representedSpaceMap B S hS i ≫ sectionMap T x :=
  InducedCategory.hom_ext (yonedaEquiv.injective (by
    show yonedaEquiv (yonedaEquiv.symm (X.1.map i.op x)) =
      yonedaEquiv (yoneda.map i ≫ yonedaEquiv.symm x)
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
      yonedaEquiv_symm_app_apply]
    simp))

/-- The morphism given by the image of a section `y` of `Y` under `f : Y ⟶ X` is the composite of
the morphism given by `y` with `f`. -/
theorem sectionMap_app {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) {T : BigFppfOver B S hS}
    (y : Y.1.obj (Opposite.op T)) :
    sectionMap T (f.hom.app _ y) = sectionMap T y ≫ f :=
  InducedCategory.hom_ext (yonedaEquiv.injective (by
    show yonedaEquiv (yonedaEquiv.symm (f.hom.app _ y)) =
      yonedaEquiv (yonedaEquiv.symm y ≫ f.hom)
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]))

variable (E a r) in
/-- **The candidate stratum.** The subfunctor of `X` of the points `x : h_T ⟶ X` which are
universally of bottom rank `r` for `E` in degree `a`. -/
def bottomRankSubfunctor : Subfunctor X.1 where
  obj U := {x | IsUniversallyFreeBottom E a r (sectionMap U.unop x)}
  map {U V} i x hx := by
    change IsUniversallyFreeBottom E a r (sectionMap V.unop (X.1.map i.unop.op x))
    rw [sectionMap_map]
    exact hx.comp _

/-- **A morphism factors through the candidate stratum exactly when it is universally of bottom
rank `r`.** This is description (2) of [stacks 0D21] for the subfunctor
`bottomRankSubfunctor`, whatever `E` is. -/
theorem exists_lift_bottomRankSubfunctor_iff {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    (∃ g : Y.1 ⟶ (bottomRankSubfunctor E a r).toFunctor,
        g ≫ (bottomRankSubfunctor E a r).ι = f.hom) ↔
      IsUniversallyFreeBottom E a r f := by
  constructor
  · rintro ⟨g, hg⟩
    refine isUniversallyFreeBottom_of_forall_representable f fun T t => ?_
    have hx : IsUniversallyFreeBottom E a r
        (sectionMap T (g.app _ (yonedaEquiv t.hom)).1) := (g.app _ (yonedaEquiv t.hom)).2
    have heq : (g.app _ (yonedaEquiv t.hom)).1 = f.hom.app _ (yonedaEquiv t.hom) := by
      rw [← hg]
      rfl
    have ht : sectionMap T (yonedaEquiv t.hom) = t :=
      InducedCategory.hom_ext (Equiv.symm_apply_apply _ _)
    rw [heq, sectionMap_app, ht] at hx
    exact hx.self
  · intro h
    refine ⟨Subfunctor.lift f.hom ?_, Subfunctor.lift_ι _ _⟩
    rintro U _ ⟨y, rfl⟩
    show IsUniversallyFreeBottom E a r (sectionMap U.unop (f.hom.app U y))
    rw [sectionMap_app]
    exact h.comp _

/-! ### The degenerate stratum -/

/-- **The identity of `X` is a bottom rank `r` stratum as soon as `H^a(L(𝟙_X)^* E)` is finite
locally free of rank `r`.** Every morphism to `X` factors through the identity, and under the
derived-pullback computation every morphism is then universally of bottom rank `r`.

This is the degenerate case `Z = X` of [stacks 0D21], and it is the reason the hypotheses of
`exists_isBottomRankStratum` are not vacuous. The hypothesis is phrased at `𝟙 X` rather than at
`E` itself because this development has no identity isomorphism for the derived pullback of an
algebraic space: `H^a(L(𝟙_X)^* E)` is not known here to be `H^a(E)`. -/
theorem isBottomRankStratum_id (hbc : BottomRankBaseChange E a r)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfIntRank
      (pullbackHomology E a (𝟙 X)) (r : ℤ)) :
    IsBottomRankStratum E a r (𝟙 X) where
  isImmersion := BottomRankStratum.isImmersion_id _
  freeRank := hE
  factorsThrough_iff Y f := by
    refine ⟨fun _ Y' g => ?_, fun _ => ⟨f, Category.comp_id f⟩⟩
    simpa only [Category.comp_id] using hbc (𝟙 X) (g ≫ f) hE

end AlgebraicGeometry.Space.BottomRankLocus

end
