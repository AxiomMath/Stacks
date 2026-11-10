module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings

/-!
# Filtrations by closed subspaces whose strata have blowups with the resolution property

Stacks 0GV6 asserts that a quasi-compact, quasi-separated algebraic space `X` over a scheme
`S` carries a chain of closed subspaces `X ⊇ Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t = ∅` with each `Z_i → X` of
finite presentation, with `Z₀ ⊆ X` a thickening, and with, for every `i < t`, a
`(Z_i ∖ Z_{i+1})`-admissible blowing up `Z'_i → Z_i` such that `Z'_i` has the resolution
property.

This file introduces the predicate that chain is, and proves the statements about it that need
no input beyond what is already proved: the chain exists over a closed subspace with no points
and over an algebraic space with no points, a chain over a closed subspace extends to a chain
over a bigger one once the blowup datum for the bigger one is supplied, and the chain over `⊤`
is the source's filtration in the source's own words. **Nothing here claims Stacks 0GV6**, and
nothing here carries `@[stacks 0GV6]`; see the implementation notes for exactly which step of
the source's proof is still missing and why.

## Main definitions

* `AlgebraicGeometry.Space.IsResolutionBlowupStratified`: the chain of Stacks 0GV6 for a
  subfunctor `W` of an algebraic space `X`, with the thickening condition on its first member
  read off the point sets, as in `AlgebraicGeometry.Space.IsCoverStratified` for Stacks 0GUP.

## Main results

* `AlgebraicGeometry.Space.isThickening_of_subspacePointSet_eq_univ`: the bridge from the
  point-set form of the first condition to `AlgebraicGeometry.Space.IsThickening`, Stacks 05ZK
  part (1), which is the word the source uses.
* `AlgebraicGeometry.Space.isResolutionBlowupStratified_emptyClosedSubspace` and
  `AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isEmpty_points`: the empty closed
  subspace is stratified, and so is an algebraic space with no points, by the chain of length
  `0`.  This is the base case of the source's induction on the dimension of `|X|`.
* `AlgebraicGeometry.Space.IsResolutionBlowupStratified.prepend`: the induction step of the
  source's Step 2, as a statement about the chain alone.
* `AlgebraicGeometry.Space.exists_thickening_filtration_of_isResolutionBlowupStratified_top`:
  the chain over `⊤`, unpacked into the source's own words — a thickening `Z₀ ⊆ X`, an empty
  last member, and the admissible blowups.

## Implementation notes

**The chain lives in `X`, not in its members.** As in
`AlgebraicGeometry.Space.IsCoverStratified` (Stacks 0GUP) in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FiniteEtaleCoverStratificationSteps.lean`, every
member of the chain is a subfunctor of the *ambient* `X`, and the predicate is relative to a
subfunctor `W` of `X` that the chain's first member must be a thickening of.  Taking `W = ⊤`
gives the absolute statement of Stacks 0GV6; keeping `W` general is what makes the chain over
`Z₁ ⊆ X` reusable as the tail of a chain over `X` without transporting subfunctors across the
closed immersion `Z₁ ⟶ X`, which is exactly how the source's induction proceeds.

**The thickening condition in point-set form.** "`Z₀ ⊆ W` is a thickening" is recorded as
`Z₀ ≤ W` together with equality of the two point sets, again as in `IsCoverStratified`.  For
`W = ⊤` this is equivalent to `AlgebraicGeometry.Space.IsThickening` on the nose: a closed
immersion is injective on points, so having all of them is surjectivity of
`AlgebraicGeometry.Space.pointsMap`, which is what `IsThickening` asks.  That equivalence is
`AlgebraicGeometry.Space.isThickening_of_subspacePointSet_eq_univ` below, and it is why the
point-set form is not a weakening.

**The open subspace `Z_i ∖ Z_{i+1}`.** The blowup of `Z_i` is required to be admissible for an
open subspace `U ⊆ Z_i` whose points, *measured in `X`*, are exactly
`|Z_i| ∖ |Z_{i+1}|`.  Since `|Z_i| ⟶ |X|` is injective this pins `U` down to the open
complement of `Z_{i+1}` in `Z_i`, and it is the shape the library's own step lemma
`AlgebraicGeometry.Space.isFiniteEtaleCoverStep_of_isEtaleCoverOver` uses for the same set.
The source writes the index as `Z_i ∖ Z_{i-1}`, which cannot be meant: `Z_{-1}` is not defined
and the chain is decreasing, so the difference intended is `Z_i ∖ Z_{i+1}`.

**The module universe is fixed at `{u, u}`.**  `AlgebraicGeometry.Space.HasResolutionProperty`
leaves the universe of the module sections free; it is instantiated at `{u, u}` here, which is
the instantiation at which every resolution-property result of this tree is stated
(Stacks 0GUT, 0GUU, 0GUV in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyRelativeAmpleMain.lean`,
`…/ResolutionPropertyQuasiAffineMain.lean` and `…/ResolutionPropertyFiniteLocallyFreeTrace.lean`)
and the only one at which `AlgebraicGeometry.Space.modulePushforward` and
`AlgebraicGeometry.Space.modulePullback` exist.

**What is missing, and where.** `AlgebraicGeometry.Space.IsResolutionBlowupStratified.prepend`
carries the whole level-`0` datum as hypotheses: the closed subspace `D` that will be `Z₀`, the
closed subspace `W₁` that will be `Z₁`, the open `U ⊆ D` with `|U| = |D| ∖ |W₁|`, and a
`U`-admissible blowup of `D` whose source has the resolution property.  Those are *inputs* to
the source's proof and not part of its conclusion at the level being proved: the source
produces them from Stacks 0GV5 (Lemma 76.57.1), which gives, for a quasi-compact,
quasi-separated algebraic space with finitely many irreducible components, a quasi-compact
dense open `U` and a `U`-admissible blowup with the resolution property, and then takes `W₁` to
be the reduced closed subspace supported on the complement of `|U|`.  That last object the
library does have: `AlgebraicGeometry.Space.openComplementReducedSubspace` of
`StacksFrontier/AlgebraicGeometry/Spaces/ElementaryDistinguishedSquare.lean`, with its point set
computed by `AlgebraicGeometry.Space.range_pointsMap_ι_openComplementReducedSubspace`, is
exactly `W₁`.  **Stacks 0GV5 is not proved in this library**, so the blowup datum cannot be
produced here and the recursion that `prepend` and
`isResolutionBlowupStratified_top_of_isEmpty_points` would drive cannot be run.
The source's Step 1, the reduction of the general quasi-compact, quasi-separated case to the
case of finite presentation over `Spec ℤ` by absolute Noetherian approximation (Stacks 07SU)
together with ascent of the resolution property along affine morphisms (Stacks 0GUU), is
likewise not assembled here.

## References

* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The thickening condition -/

/-- **A closed subspace carrying every point of `X` is a thickening of `X`**, Stacks 05ZK part
(1).  A closed immersion is injective on points, so carrying every point is exactly
surjectivity of the induced map on points, which is what `IsThickening` asks for. -/
theorem isThickening_of_subspacePointSet_eq_univ (X : AlgebraicSpaces B S hS)
    {G : Subfunctor X.1} (hG : IsClosedSubspace B S hS G)
    (h : subspacePointSet B S hS X.1 G = Set.univ) :
    IsThickening B S hS X G :=
  ⟨hG, Set.range_eq_univ.mp h⟩

/-- The top subfunctor of an algebraic space carries every point. -/
private theorem subspacePointSet_top_eq_univ (X : AlgebraicSpaces B S hS) :
    subspacePointSet B S hS X.1 (⊤ : Subfunctor X.1) = Set.univ :=
  Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor X.1).ι)

/-! ### The chain of Stacks 0GV6 -/

/-- **The chain of Stacks 0GV6 over a subfunctor `W` of an algebraic space `X`**: a decreasing
chain `Z₀ ⊇ Z₁ ⊇ ⋯` of closed subspaces of `X`, each of finite presentation over `X`, with `Z₀`
a thickening of `W` — contained in `W` and carrying all of its points — with `Z_t` carrying no
points, and with, for every `i < t`, an open subspace `U ⊆ Z_i` whose points are `|Z_i| ∖
|Z_{i+1}|` and a `U`-admissible blowing up of `Z_i` whose source has the resolution property.

At `W = ⊤` this is the conclusion of Stacks 0GV6; see the module documentation for why the
thickening condition is stated on point sets and for the index `Z_i ∖ Z_{i+1}`. -/
def IsResolutionBlowupStratified (X : AlgebraicSpaces B S hS) (W : Subfunctor X.1) : Prop :=
  ∃ (t : ℕ) (Z : ℕ → Subfunctor X.1) (hZ : ∀ i, IsClosedSubspace B S hS (Z i)),
    (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
    (∀ i, Z (i + 1) ≤ Z i) ∧
    Z 0 ≤ W ∧
    subspacePointSet B S hS X.1 (Z 0) = subspacePointSet B S hS X.1 W ∧
    subspacePointSet B S hS X.1 (Z t) = ∅ ∧
    ∀ i < t, ∃ (U : OpenSubspaces B S hS (Z i).toFunctor) (Y : AlgebraicSpaces B S hS)
        (f : Y ⟶ (⟨(Z i).toFunctor, (hZ i).1⟩ : AlgebraicSpaces B S hS)),
      Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ (Z i).ι)) =
          subspacePointSet B S hS X.1 (Z i) \ subspacePointSet B S hS X.1 (Z (i + 1)) ∧
        IsAdmissibleBlowup B S hS U f ∧
        HasResolutionProperty.{u, u} B S hS Y.1 Y.2

/-- **The base case of the induction of Stacks 0GV6.**  The empty closed subspace of an
algebraic space is stratified by the chain of length `0` constant at it: it is closed, its
inclusion is of finite presentation because it has no points, and the condition on the strata
is vacuous. -/
theorem isResolutionBlowupStratified_emptyClosedSubspace (X : AlgebraicSpaces B S hS) :
    IsResolutionBlowupStratified B S hS X (emptyClosedSubspace X).1 :=
  ⟨0, fun _ => (emptyClosedSubspace X).1,
    fun _ => (emptyClosedSubspace X).2,
    fun _ => isFinitePresentation_ι_emptyClosedSubspace X,
    fun _ => le_rfl, le_rfl, rfl,
    subspacePointSet_emptyClosedSubspace X,
    fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- **The base case of the induction of Stacks 0GV6 on the dimension of `|X|`.**  An algebraic
space with no points is stratified by the chain of length `0` constant at its empty closed
subspace: that chain's first member carries every point of `X`, because `X` has none. -/
theorem isResolutionBlowupStratified_top_of_isEmpty_points (X : AlgebraicSpaces B S hS)
    (hX : IsEmpty (points B S hS X.1)) :
    IsResolutionBlowupStratified B S hS X ⊤ := by
  refine ⟨0, fun _ => (emptyClosedSubspace X).1, fun _ => (emptyClosedSubspace X).2,
    fun _ => isFinitePresentation_ι_emptyClosedSubspace X, fun _ => le_rfl, le_top, ?_,
    subspacePointSet_emptyClosedSubspace X, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  rw [subspacePointSet_emptyClosedSubspace, subspacePointSet_top_eq_univ]
  exact (Set.univ_eq_empty_iff.mpr hX).symm

variable {B S hS}

/-- **The induction step of Step 2 of the proof of Stacks 0GV6.**  Let `W` be a subfunctor of
an algebraic space `X`, let `D ⊆ W` be a closed subspace of `X`, of finite presentation over
`X`, carrying every point of `W`, and let `W₁ ⊆ D` be a closed subspace of `X`.  Suppose given
an open subspace `U ⊆ D` whose points are `|D| ∖ |W₁|` and a `U`-admissible blowing up
`f : Y ⟶ D` with `Y` having the resolution property.  Then a chain over `W₁` extends to a chain
over `W`, by prepending `D`.

**Every hypothesis beyond `h₁` is the level-`0` datum of the source's induction, which the
source obtains from Stacks 0GV5 and the reduced induced structure on the complement, and which
this library cannot yet produce**; see the module documentation.  The conclusion is not
weakened: `D` becomes `Z₀` and the chain over `W₁` becomes `Z₁ ⊇ Z₂ ⊇ ⋯`, and the chain's own
conditions — closedness, finite presentation over `X`, decrease, the thickening of `W`, the
empty last member, and an admissible blowup with the resolution property over each stratum —
are all discharged. -/
theorem IsResolutionBlowupStratified.prepend {X : AlgebraicSpaces B S hS}
    {W D W₁ : Subfunctor X.1} (hD : IsClosedSubspace B S hS D)
    (hDfp : IsFinitePresentation B S hS D.ι) (hDW : D ≤ W)
    (hDpts : subspacePointSet B S hS X.1 D = subspacePointSet B S hS X.1 W)
    (hW₁D : W₁ ≤ D) (U : OpenSubspaces B S hS D.toFunctor)
    (hUpts : Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ D.ι)) =
      subspacePointSet B S hS X.1 D \ subspacePointSet B S hS X.1 W₁)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ (⟨D.toFunctor, hD.1⟩ : AlgebraicSpaces B S hS))
    (hf : IsAdmissibleBlowup B S hS U f)
    (hres : HasResolutionProperty.{u, u} B S hS Y.1 Y.2)
    (h₁ : IsResolutionBlowupStratified B S hS X W₁) :
    IsResolutionBlowupStratified B S hS X W := by
  obtain ⟨t, Z, hZcl, hZfp, hZmono, hZ₀W₁, hZ₀pts, hZt, hstep⟩ := h₁
  refine ⟨t + 1, fun i => Nat.casesOn i D Z, fun i => Nat.casesOn i hD hZcl,
    fun i => Nat.casesOn i hDfp hZfp, fun i => ?_, hDW, hDpts.symm ▸ rfl, hZt, fun i hi => ?_⟩
  · cases i with
    | zero => exact hZ₀W₁.trans hW₁D
    | succ j => exact hZmono j
  · cases i with
    | zero =>
      refine ⟨U, Y, f, ?_, hf, hres⟩
      change Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ D.ι)) =
        subspacePointSet B S hS X.1 D \ subspacePointSet B S hS X.1 (Z 0)
      rw [hUpts, hZ₀pts]
    | succ j => exact hstep j (Nat.lt_of_succ_lt_succ hi)

/-! ### The chain over the whole space, in the source's words -/

/-- **The chain of Stacks 0GV6 over `⊤`, unpacked into the words of the source.**  A chain over
the top subfunctor of `X` gives closed subspaces `Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t` of `X`, each of finite
presentation over `X`, with `Z₀ ⊆ X` a thickening in the sense of Stacks 05ZK part (1), with
`Z_t` the empty algebraic space, and with a `(Z_i ∖ Z_{i+1})`-admissible blowing up of `Z_i`
whose source has the resolution property for each `i < t`.

This is the translation of `AlgebraicGeometry.Space.IsResolutionBlowupStratified` at `⊤` into
`AlgebraicGeometry.Space.IsThickening` and emptiness of the space of points, and is what makes
the point-set form of the predicate's first and last conditions faithful to the source.  It
asserts nothing about when the hypothesis holds. -/
theorem exists_thickening_filtration_of_isResolutionBlowupStratified_top
    {X : AlgebraicSpaces B S hS} (h : IsResolutionBlowupStratified B S hS X ⊤) :
    ∃ (t : ℕ) (Z : ℕ → Subfunctor X.1) (hZ : ∀ i, IsClosedSubspace B S hS (Z i)),
      (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
      (∀ i, Z (i + 1) ≤ Z i) ∧
      IsThickening B S hS X (Z 0) ∧
      IsEmpty (points B S hS (Z t).toFunctor) ∧
      ∀ i < t, ∃ (U : OpenSubspaces B S hS (Z i).toFunctor) (Y : AlgebraicSpaces B S hS)
          (f : Y ⟶ (⟨(Z i).toFunctor, (hZ i).1⟩ : AlgebraicSpaces B S hS)),
        Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ (Z i).ι)) =
            subspacePointSet B S hS X.1 (Z i) \ subspacePointSet B S hS X.1 (Z (i + 1)) ∧
          IsAdmissibleBlowup B S hS U f ∧
          HasResolutionProperty.{u, u} B S hS Y.1 Y.2 := by
  obtain ⟨t, Z, hZcl, hZfp, hZmono, -, hZ₀pts, hZt, hstep⟩ := h
  refine ⟨t, Z, hZcl, hZfp, hZmono,
    isThickening_of_subspacePointSet_eq_univ B S hS X (hZcl 0) ?_, ?_, hstep⟩
  · rw [hZ₀pts, subspacePointSet_top_eq_univ]
  · exact Set.range_eq_empty_iff.mp hZt

end AlgebraicGeometry.Space

end
