module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreEnlargedByDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupComposite
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupDivisorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPreimageSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupReesProjContains
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupSecondCentreChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties

/-!
# The composite centre of two blowups of an algebraic space

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `Z ⊆ X` be a closed subspace of
finite presentation, let `b : X' ⟶ X` be the blowup of `X` in `Z`, let `Z' ⊆ X'` be a closed
subspace of finite presentation and let `c : X'' ⟶ X'` be the blowup of `X'` in `Z'`.
Stacks 0860 asserts that there is a closed subspace `Y ⊆ X` of finite presentation with

1. `|Y| = |Z| ∪ |b|(|Z'|)`, and
2. `c ≫ b : X'' ⟶ X` the blowup of `X` in `Y`.

Stacks 086C is the corollary: if `b` is a `U`-admissible blowup for a quasi-compact open
subspace `U ⊆ X` and `c` is a `b⁻¹(U)`-admissible blowup, then `c ≫ b` is a `U`-admissible
blowup.

## Which substrate this is about

Both tags are about the **`AlgebraicSpaces B S hS` substrate**: `X`, `X'` and `X''` are sheaves
on the big fppf site, and "is the blowup of `X` in `Z`" is the universal property of Stacks
085U, `AlgebraicGeometry.Space.IsBlowupAlong`, as it is throughout
`StacksFrontier/AlgebraicGeometry/Spaces/AdmissibleBlowup.lean`.  Neither tag is about the
`AlgebraicGeometry.RelativeProjSituation` substrate, whose base is a `Scheme`: the blowup `X'`
of an algebraic space is not an object of that substrate at all, it is glued from the relative
`Proj` of the Rees algebra on an étale chart.  The relative `Proj` substrate enters only through
the input that this file does **not** discharge, Stacks 085N; see *What is missing* below.

## What is proved here

The source's proof factors through a **second centre** on the base: Stacks 085N produces a
degree `d` and a finite type submodule `ℱ ⊆ 𝒜_d = 𝓘_Z^d`, read as an ideal sheaf `𝒥 ⊆ 𝒪_X`, for
which `b^{-1}𝒥·𝒪_{X'} = 𝓘_E^d · 𝓘_{Z'}` with `E = b^{-1}(Z)` the exceptional divisor; the
composite centre is then `Y = V(𝓘_Z 𝒥)`.  Everything the source does with that datum is proved
here, unconditionally:

* `AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong_of_preimage_eq` is the
  **engine**: given a closed subspace `W = V(𝒥) ⊆ X` of finite presentation, a degree `d`, the
  identity `b^{-1}(W) = Z' + dE` and the containment `|W| ⊆ |Z| ∪ |b|(|Z'|)`, it produces the
  closed subspace `Y = Z + W` of Stacks 083U and proves all three of 0860's conclusions about
  it — finite presentation, the point-set identity
  `AlgebraicGeometry.Space.IsCompositeCentre`, and that `c ≫ b` is the blowup of `X` in `Y`.

This is the exact mirror of the scheme-level Stacks 080B, whose engine
`Stacks.Blowup.supportSet_mul_eq_union_image` and
`Stacks.Blowup.nonempty_blowUpCompositionIso` in
`StacksFrontier/AlgebraicGeometry/Blowup/CompositeCentre.lean` consume the same datum
`J.comap (blowUpToBase I) = exceptionalIdeal I ^ d * Z'`, and whose existence half
`Stacks.Blowup.exists_secondCentre` is the scheme case of the input named below.

The reduction of the *composite* blowup to the blowup in `Z' + dE` uses three facts:
Stacks 085X for the second blowup (`…isPullbackDefined_of_isBlowupAlong`, so that the
exceptional divisor of `b` pulls back along `c`), Stacks 0867 part (1) to enlarge the centre of
`c` by that divisor (`…isBlowupAlong_sumClosedSubspaces`), and Stacks 085Y to compose
(`…isBlowupAlong_comp_of_isBlowupAlong'`), which applies because `Z' + dE` is, by the carried
identity, the inverse image along `b` of a closed subspace of `X`.

## Main results

* `AlgebraicGeometry.Space.isPullbackDefined_sumClosedSubspaces_iff`: pullback-definedness along
  a morphism holds for a sum of two closed subspaces exactly when it holds for each summand.
  This is Stacks 083W in one direction and Stacks 0840 in the other, and it is exactly the
  `h083V` hypothesis of `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces`, so that
  hypothesis is discharged here rather than carried.
* `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspacesList_const`: a blowup of `𝔅` in `Z₀`
  is also the blowup of `𝔅` in `Z₀` plus any number of copies of a fixed effective Cartier
  divisor which it pulls back.  This is `dE` of the source's computation.
* `AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong_of_preimage_eq`: the engine
  described above.
* `AlgebraicGeometry.Space.exists_secondCentre_exceptionalDivisor`: **the engine's carried
  clauses are satisfiable, unconditionally and together** — for `Z'` the exceptional divisor
  `E = b^{-1}(Z)` they hold with `W = Z` and `d = 0`, for an arbitrary `X`, `Z` and `b`.  So the
  engine is not vacuous; and since those clauses mention no blowup they are not a restatement of
  its conclusion either.
* `AlgebraicGeometry.Space.HasSecondCentre`: the existence of that datum for every finitely
  presented `Z' ⊆ X'`, which is Stacks 085N at the Rees algebra of the first centre.
* `AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong`: Stacks 0860 from the
  source's own hypotheses together with that one input, for an arbitrary algebraic space.
* `AlgebraicGeometry.Space.hasSecondCentre`: **that input holds on a quasi-compact and
  quasi-separated algebraic space**.
* `AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong_of_isQuasiCompactSpace`:
  **Stacks 0860**, at the source's hypotheses, with nothing assumed.
* `AlgebraicGeometry.Space.isAdmissibleBlowup_comp`: **the whole of Stacks 086C** from the
  source's own hypotheses together with the same one assumed input — a `U`-admissible blowup
  followed by a `b^{-1}(U)`-admissible blowup is `U`-admissible.  Beyond Stacks 0860 this needs
  only that the composite centre misses `U`, which is a point-set computation.

## How the second centre is obtained

The source obtains the pair `(d, W)` from Stacks 085N, through the relative `Proj` of the Rees
algebra of `𝓘_Z` and the support clause of 085N.  This development has no relative `Proj` of a
graded algebra on an algebraic space, and it reaches the same pair without one, following the
source's own local computation:

* over a surjective étale affine chart of `X`, the blowup is the blowup of the chart (Stacks
  085S and 085R), so the scheme case of the second centre, Stacks 080B
  (`Stacks.Blowup.exists_secondCentre`), gives `d` and a finite type ideal `J` on the chart with
  `b^{-1}J·𝒪 = 𝓘_E^d·𝓘_{Z'}`; then `J` lies in the ideal of the scheme-theoretic image `C_d` of
  `Z' + dE ⟶ X`, and any closed subspace whose chart ideal contains `J` has inverse image inside
  `Z' + dE` (`AlgebraicGeometry.Space.exists_chart_le_chartKer_exceptionalSumImage`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/BlowupSecondCentreChart.lean`);
* on a quasi-compact quasi-separated algebraic space a closed subspace is approximated from
  above by finitely presented ones compatibly with a quasi-compact étale chart
  (`AlgebraicGeometry.Space.exists_isFinitePresentation_le_chartKer`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceApproximation.lean`, proved by the
  induction principle Stacks 08GP rather than by the Noetherian approximation behind Stacks
  0829), which turns `C_d` into a finitely presented `W` with `b^{-1}(W) = Z' + dE`;
* the support clause `|W| ⊆ |Z| ∪ |b|(|Z'|)` is then automatic, by Stacks 085T part (1)
  (`AlgebraicGeometry.Space.subspacePointSet_subset_union_image_of_preimage_eq`).

Quasi-compactness and quasi-separatedness of `X` enter exactly here, as in the source, where
they are what 085N and 0855 need.

Stacks **084B** is *not* needed by anything in this file, and is not carried as a hypothesis
anywhere in it.  The engine never forms a relative `Proj`, and it carries no 085Q construction
data for `X'`: the étale presentation is obtained from
`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace`, and the three `B.Contains` smallness
conditions along a finitely presented centre are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupReesProjContains.lean`
(`AlgebraicGeometry.Space.contains_reesProj_of_isFinitePresentation`).  They reach Stacks 085U
through `AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`, whose
blowup `AlgebraicGeometry.Space.blowUpAlong'` takes no 084B-shaped argument: the two cartesian
fields of `AlgebraicGeometry.Space.RelativeProjGlueingData` which stand in for 084B in general
are supplied by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_centreIdeal`, that is, proved
outright for the Rees algebra.

Nothing in this file mentions or consumes `AlgebraicGeometry.Space.RelativeProjPoints`, which
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjPointsAlgebraicSpace.lean` records as
uninhabited in this library; so no statement here is exposed to the absence of a witness for
it.

## References

* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
* [Stacks Project, Tag 086C](https://stacks.math.columbia.edu/tag/086C)
* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 085Y](https://stacks.math.columbia.edu/tag/085Y)
* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 0867](https://stacks.math.columbia.edu/tag/0867)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083W](https://stacks.math.columbia.edu/tag/083W)
* [Stacks Project, Tag 0840](https://stacks.math.columbia.edu/tag/0840)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Pullback-definedness along a sum, in both directions -/

/-- **Stacks 083W and Stacks 0840 together.**  The inverse image of a sum of two closed
subspaces along `f` is an effective Cartier divisor exactly when the inverse images of the two
summands are.

The forward implication splits the sum, Stacks 083W; the converse recombines it, Stacks 0840.
This is verbatim the `h083V` hypothesis of
`AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces`, so every use of that result below
discharges it rather than carrying it. -/
theorem isPullbackDefined_sumClosedSubspaces_iff {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    IsPullbackDefined B S hS f (sumClosedSubspaces B S hS X D₁ D₂) ↔
      IsPullbackDefined B S hS f D₁ ∧ IsPullbackDefined B S hS f D₂ :=
  ⟨fun h => ⟨isPullbackDefined_left_of_sumClosedSubspaces f D₁ D₂ h,
      isPullbackDefined_right_of_sumClosedSubspaces f D₁ D₂ h⟩,
    fun h => isPullbackDefined_sumClosedSubspaces B S hS f D₁ D₂ h.1 h.2⟩

/-! ### Adding a multiple of a divisor to the centre -/

/-- **The centre of a blowup may be enlarged by any number of copies of an effective Cartier
divisor the blowup pulls back.**  If `c : B'' ⟶ 𝔅` is the blowup of `𝔅` in `Z₀` and `D` is an
effective Cartier divisor on `𝔅` whose inverse image along `c` is again one, then `c` is also
the blowup of `𝔅` in `Z₀ + D + ⋯ + D`, with one summand `D` for each entry of the list.

This is Stacks 0867 part (1), `AlgebraicGeometry.Space.isBlowupAlong_sumClosedSubspaces`,
iterated; its `h083V` hypothesis is discharged by
`AlgebraicGeometry.Space.isPullbackDefined_sumClosedSubspaces_iff`.  For a list of `d` entries
this is the source's `Z' + dE`. -/
theorem isBlowupAlong_sumClosedSubspacesList_const {𝔅 B'' : AlgebraicSpaces B S hS}
    (D Z₀ : ClosedSubspaces B S hS 𝔅.1) (hD : IsEffectiveCartierDivisor B S hS 𝔅 D)
    {c : B'' ⟶ 𝔅} (hc : IsBlowupAlong B S hS Z₀ c)
    (hcD : IsPullbackDefined B S hS c D) :
    ∀ l : List Unit,
      IsBlowupAlong B S hS (sumClosedSubspacesList 𝔅 (fun _ : Unit => D) Z₀ l) c
  | [] => hc
  | _ :: l => by
    have ih : IsBlowupAlong B S hS (sumClosedSubspacesList 𝔅 (fun _ : Unit => D) Z₀ l) c :=
      isBlowupAlong_sumClosedSubspacesList_const D Z₀ hD hc hcD l
    show IsBlowupAlong B S hS
      (sumClosedSubspaces B S hS 𝔅 D (sumClosedSubspacesList 𝔅 (fun _ : Unit => D) Z₀ l)) c
    rw [sumClosedSubspaces_comm]
    exact isBlowupAlong_sumClosedSubspaces B S hS _ D hD ih hcD
      fun g => isPullbackDefined_sumClosedSubspaces_iff g _ D

/-- **The points of the seed of a sum along a list are points of the sum.**  Each step of the
sum only adds points, `AlgebraicGeometry.Space.subspacePointSet_sumClosedSubspaces`. -/
theorem subspacePointSet_subset_sumClosedSubspacesList {X : AlgebraicSpaces B S hS}
    (D Z₀ : ClosedSubspaces B S hS X.1) :
    ∀ l : List Unit, subspacePointSet B S hS X.1 Z₀.1 ⊆
      subspacePointSet B S hS X.1 (sumClosedSubspacesList X (fun _ : Unit => D) Z₀ l).1
  | [] => subset_rfl
  | _ :: l => by
    show subspacePointSet B S hS X.1 Z₀.1 ⊆ subspacePointSet B S hS X.1
      (sumClosedSubspaces B S hS X D (sumClosedSubspacesList X (fun _ : Unit => D) Z₀ l)).1
    rw [subspacePointSet_sumClosedSubspaces]
    exact (subspacePointSet_subset_sumClosedSubspacesList D Z₀ l).trans Set.subset_union_right

/-! ### The engine of Stacks 0860 -/

variable {X X' X'' : AlgebraicSpaces B S hS}

/-- **The engine of Stacks 0860: the composite centre, from the second centre on the base.**

Let `b : X' ⟶ X` be the blowup of the algebraic space `X` in a closed subspace `Z` of finite
presentation and let `c : X'' ⟶ X'` be the blowup of `X'` in a closed subspace `Z'` of finite
presentation.  Suppose given, as Stacks 085N provides, a closed subspace `W ⊆ X` of finite
presentation and a degree `d` such that

* `b^{-1}(W) = Z' + dE`, where `E = b^{-1}(Z)` is the exceptional divisor of `b` and `dE` is the
  sum of `d` copies of it — the source's `b^{-1}𝒥·𝒪_{X'} = 𝓘_E^d·𝓘_{Z'}`; and
* `|W| ⊆ |Z| ∪ |b|(|Z'|)` — the support clause of Stacks 085N.

Then the sum `Y = Z + W` of Stacks 083U satisfies all of Stacks 0860: its inclusion is of
finite presentation, its points are `|Z| ∪ |b|(|Z'|)`, and `c ≫ b` is the blowup of `X` in `Y`.

The point-set identity is the conclusion in the form
`AlgebraicGeometry.Space.IsCompositeCentre`, which is the hypothesis `hY` of the two Stacks 0868
theorems of `StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformProperties.lean`; the
containment `|b|(|Z'|) ⊆ |W|` which that identity also needs is read off the carried identity
`b^{-1}(W) = Z' + dE`, since `Z'` is a summand on the right and the points of an inverse image
are the inverse image of the points.

The construction data of Stacks 085Q for `X'` is not carried: an étale presentation of `X'`
exists (`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace`), and the three relative `Proj`s
which the construction forms over it lie in the site along the two finitely presented centres
the proof uses, `Z'` and `b^{-1}(W)`
(`AlgebraicGeometry.Space.contains_reesProj_of_isFinitePresentation`).  Beyond the source's
hypotheses and the datum `(W, d)` of Stacks 085N, only the `HasSheafify` universe choice is
taken.

What is **not** proved is the existence of `W` and `d`: that is Stacks 085N, and it is why this
declaration is deliberately left unregistered for Stacks 0860.  See the module documentation. -/
theorem exists_isCompositeCentre_isBlowupAlong_of_preimage_eq
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (hZfp : IsFinitePresentation B S hS Z.1.ι)
    {Z' : ClosedSubspaces B S hS X'.1} {c : X'' ⟶ X'} (hc : IsBlowupAlong B S hS Z' c)
    (hZ'fp : IsFinitePresentation B S hS Z'.1.ι)
    (W : ClosedSubspaces B S hS X.1) (d : ℕ)
    (hWfp : IsFinitePresentation B S hS W.1.ι)
    (hWpre : preimageClosedSubspace b W =
      sumClosedSubspacesList X' (fun _ : Unit => preimageClosedSubspace b Z) Z'
        (List.replicate d ()))
    (hWsupp : subspacePointSet B S hS X.1 W.1 ⊆
      subspacePointSet B S hS X.1 Z.1 ∪
        pointsMap B S hS X'.1 b.hom '' subspacePointSet B S hS X'.1 Z'.1) :
    ∃ Y : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Y.1.ι ∧
      IsCompositeCentre B S hS b Z Z' Y ∧ IsBlowupAlong B S hS Y (c ≫ b) := by
  -- The construction of Stacks 085Q for `X'` runs over an étale presentation of `X'`, and its
  -- three relative `Proj`s lie in the site along the two finitely presented centres used below.
  let P := presentationOfIsAlgebraicSpace B S hS X'.obj X'.property
  have hkZ' := contains_reesProj_of_isFinitePresentation Z' hZ'fp P
  have hkW := contains_reesProj_of_isFinitePresentation (preimageClosedSubspace b W)
    (isFinitePresentation_ι_preimage b W hWfp) P
  -- The exceptional divisor `E = b⁻¹(Z)` is an effective Cartier divisor on `X'`, and `c`,
  -- being a blowup, pulls it back to one on `X''` (Stacks 085X).
  have hE : IsEffectiveCartierDivisor B S hS X' (preimageClosedSubspace b Z) :=
    hb.isPullbackDefined
  have hcE : IsPullbackDefined B S hS c (preimageClosedSubspace b Z) :=
    isPullbackDefined_of_isBlowupAlong Z' P hkZ'.1 hkZ'.2.1 hkZ'.2.2 hc
      (preimageClosedSubspace b Z) hE
  -- So `c` is also the blowup of `X'` in `Z' + dE`, which by hypothesis is `b⁻¹(W)`.
  have hpre : IsBlowupAlong B S hS (preimageClosedSubspace b W) c := by
    rw [hWpre]
    exact isBlowupAlong_sumClosedSubspacesList_const _ Z' hE hc hcE _
  refine ⟨sumClosedSubspaces B S hS X Z W,
    isFinitePresentation_ι_sumClosedSubspaces X Z W hZfp hWfp, ?_,
    isBlowupAlong_comp_of_isBlowupAlong' hb hpre P hkW.1 hkW.2.1 hkW.2.2⟩
  -- The point set of `Z + W` is `|Z| ∪ |W|`; it remains to identify `|Z| ∪ |W|` with
  -- `|Z| ∪ |b|(|Z'|)`.
  have himg : pointsMap B S hS X'.1 b.hom '' subspacePointSet B S hS X'.1 Z'.1 ⊆
      subspacePointSet B S hS X.1 W.1 := by
    rw [Set.image_subset_iff, ← subspacePointSet_preimage]
    calc subspacePointSet B S hS X'.1 Z'.1
        ⊆ subspacePointSet B S hS X'.1
            (sumClosedSubspacesList X' (fun _ : Unit => preimageClosedSubspace b Z) Z'
              (List.replicate d ())).1 :=
          subspacePointSet_subset_sumClosedSubspacesList _ Z' _
      _ = subspacePointSet B S hS X'.1 (W.1.preimage b.hom) :=
          congrArg (subspacePointSet B S hS X'.1) (congrArg Subtype.val hWpre).symm
  show subspacePointSet B S hS X.1 (sumClosedSubspaces B S hS X Z W).1 = _
  rw [subspacePointSet_sumClosedSubspaces]
  exact subset_antisymm
    (Set.union_subset Set.subset_union_left hWsupp)
    (Set.union_subset Set.subset_union_left (himg.trans Set.subset_union_right))

/-- **The empty sum is its seed.**  For `d = 0` the sum of Stacks 083U along the list is the
seed closed subspace, so the identity
`b^{-1}(W) = Z' + dE` of
`AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong_of_preimage_eq` holds at
`d = 0`, `Z' = b^{-1}(W)` for any `W`. -/
theorem preimage_eq_sumClosedSubspacesList_zero (b : X' ⟶ X)
    (D : ClosedSubspaces B S hS X'.1) (V : ClosedSubspaces B S hS X.1) :
    preimageClosedSubspace b V =
      sumClosedSubspacesList X' (fun _ : Unit => D) (preimageClosedSubspace b V)
        (List.replicate 0 ()) :=
  rfl

/-- **Both of the engine's carried clauses are satisfiable, together, unconditionally.**  Take
for `Z'` the exceptional divisor `E = b^{-1}(Z)` of `b` itself.  Then the pair `(W, d) = (Z, 0)`
satisfies all three clauses of
`AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong_of_preimage_eq`: `W = Z` has a
finitely presented inclusion whenever `Z` does, the identity `b^{-1}(Z) = E + 0·E` holds by
definition because the empty sum is its seed, and the containment `|Z| ⊆ |Z| ∪ |b|(|E|)` is the
left inclusion of a union.

This is the witness that rules out the two failure modes for that theorem that no check of the
axioms used detects.  The
carried clauses are not **unsatisfiable** — they hold here for an arbitrary algebraic space `X`,
an arbitrary finitely presented centre `Z` and an arbitrary morphism `b`, so the engine is not
vacuous.  And they are not **equivalent to the conclusion**: they are an equality of closed
subspaces and a containment of point sets, and mention no blowup at all, while the conclusion
asserts that a composite *is* a blowup.  Every blowup fact in the engine's proof comes from the
source's own hypotheses `hb` and `hc` through Stacks 085X, 0867 and 085Y. -/
theorem exists_secondCentre_exceptionalDivisor (b : X' ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (hZfp : IsFinitePresentation B S hS Z.1.ι) :
    ∃ (W : ClosedSubspaces B S hS X.1) (d : ℕ), IsFinitePresentation B S hS W.1.ι ∧
      preimageClosedSubspace b W =
        sumClosedSubspacesList X' (fun _ : Unit => preimageClosedSubspace b Z)
          (preimageClosedSubspace b Z) (List.replicate d ()) ∧
        subspacePointSet B S hS X.1 W.1 ⊆
          subspacePointSet B S hS X.1 Z.1 ∪
            pointsMap B S hS X'.1 b.hom '' subspacePointSet B S hS X'.1
              (preimageClosedSubspace b Z).1 :=
  ⟨Z, 0, hZfp, rfl, Set.subset_union_left⟩

/-! ### Stacks 0860, with the second centre named -/

/-- **The second centre of Stacks 085N, as Stacks 0860 consumes it.**  For `b : X' ⟶ X` the
blowup of `X` in `Z`, this says that every closed subspace `Z' ⊆ X'` of finite presentation
arises from a closed subspace `W ⊆ X` of finite presentation and a degree `d` with
`b^{-1}(W) = Z' + dE`, for `E = b^{-1}(Z)` the exceptional divisor, and with
`|W| ⊆ |Z| ∪ |b|(|Z'|)`.

This is the content of Stacks 085N read at the Rees algebra `𝒜 = ⨁_{n ≥ 0} 𝓘_Z^n`, after the
local computation of Stacks 085R has turned its clause `Z' = Proj_X(𝒜/ℱ𝒜)` into the stated
identity of closed subspaces: `W = V(𝒥)` for `𝒥` the ideal sheaf of the submodule `ℱ ⊆ 𝒜_d`,
and `|W| ⊆ |Z| ∪ |b|(|Z'|)` is 085N's support clause.

It is the exact analogue of the scheme-level `Stacks.Blowup.SecondCentreFactorization` of
`StacksFrontier/AlgebraicGeometry/Blowup/AdmissibleComposition.lean`, which the scheme development
discharges with `Stacks.Blowup.exists_secondCentre`.  On a quasi-compact and quasi-separated
algebraic space it holds, `AlgebraicGeometry.Space.hasSecondCentre`. -/
abbrev HasSecondCentre (Z : ClosedSubspaces B S hS X.1) (b : X' ⟶ X) : Prop :=
  ∀ Z' : ClosedSubspaces B S hS X'.1, IsFinitePresentation B S hS Z'.1.ι →
    ∃ (W : ClosedSubspaces B S hS X.1) (d : ℕ), IsFinitePresentation B S hS W.1.ι ∧
      preimageClosedSubspace b W =
        sumClosedSubspacesList X' (fun _ : Unit => preimageClosedSubspace b Z) Z'
          (List.replicate d ()) ∧
        subspacePointSet B S hS X.1 W.1 ⊆
          subspacePointSet B S hS X.1 Z.1 ∪
            pointsMap B S hS X'.1 b.hom '' subspacePointSet B S hS X'.1 Z'.1

/-- **Stacks 0860, granted the second centre of Stacks 085N.**  Let `S` be a scheme, let `X` be
an algebraic space over `S`, let `Z ⊆ X` be a closed subspace of finite presentation, let
`b : X' ⟶ X` be the blowup of `X` in `Z`, let `Z' ⊆ X'` be a closed subspace of finite
presentation and let `c : X'' ⟶ X'` be the blowup of `X'` in `Z'`.  Then there is a closed
subspace `Y ⊆ X` of finite presentation with `|Y| = |Z| ∪ |b|(|Z'|)` and with `c ≫ b` the
blowup of `X` in `Y`.

This is the whole of Stacks 0860 — the two clauses of its conclusion are
`AlgebraicGeometry.Space.IsCompositeCentre` and `AlgebraicGeometry.Space.IsBlowupAlong` of the
composite — stated from the source's own hypotheses together with the **single** assumed input
`h085N`, `AlgebraicGeometry.Space.HasSecondCentre`, which is Stacks 085N at the Rees algebra of
the first centre.  It is
`AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong_of_preimage_eq` with the pair
`(W, d)` obtained from that input rather than supplied.  The construction data of Stacks 085Q
for `X'` is not taken; see the engine.

The tag is registered on
`AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong_of_isQuasiCompactSpace`, which
is this statement at the source's hypotheses with the input proved
(`AlgebraicGeometry.Space.hasSecondCentre`). -/
theorem exists_isCompositeCentre_isBlowupAlong
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (hZfp : IsFinitePresentation B S hS Z.1.ι)
    {Z' : ClosedSubspaces B S hS X'.1} {c : X'' ⟶ X'} (hc : IsBlowupAlong B S hS Z' c)
    (hZ'fp : IsFinitePresentation B S hS Z'.1.ι)
    (h085N : HasSecondCentre Z b) :
    ∃ Y : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Y.1.ι ∧
      IsCompositeCentre B S hS b Z Z' Y ∧ IsBlowupAlong B S hS Y (c ≫ b) := by
  obtain ⟨W, d, hWfp, hWpre, hWsupp⟩ := h085N Z' hZ'fp
  exact exists_isCompositeCentre_isBlowupAlong_of_preimage_eq hb hZfp hc hZ'fp W d hWfp hWpre
    hWsupp

/-! ### Stacks 0860 -/

/-- **The second centre exists on a quasi-compact quasi-separated algebraic space.**  Let `X` be
quasi-compact and quasi-separated, `Z ⊆ X` a closed subspace of finite presentation and
`b : X' ⟶ X` the blowup of `X` in `Z`.  Then every closed subspace `Z' ⊆ X'` of finite
presentation arises from a closed subspace `W ⊆ X` of finite presentation and a degree `d` with
`b^{-1}(W) = Z' + dE`, `E = b^{-1}(Z)`, and `|W| ⊆ |Z| ∪ |b|(|Z'|)`.

On a surjective étale affine chart of `X` the scheme case of the second centre gives a finite
type ideal `J₀` inside the chart ideal of the scheme-theoretic image `C_d` of `Z' + dE`, such that
every closed subspace whose chart ideal contains `J₀` has inverse image inside `Z' + dE`
(`AlgebraicGeometry.Space.exists_chart_le_chartKer_exceptionalSumImage`).  The approximation of
`C_d` from above by a finitely presented `W` compatibly with that chart
(`AlgebraicGeometry.Space.exists_isFinitePresentation_le_chartKer`) gives `b^{-1}(W) ⊆ Z' + dE`,
and `W ⊇ C_d` gives the converse since `Z' + dE` maps into its image.  The support clause is
`AlgebraicGeometry.Space.subspacePointSet_subset_union_image_of_preimage_eq`. -/
theorem hasSecondCentre [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {Z : ClosedSubspaces B S hS X.1} (hZfp : IsFinitePresentation B S hS Z.1.ι)
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b) : HasSecondCentre Z b := by
  intro Z' hZ'fp
  obtain ⟨d, V, p, J₀, hV, hp, hJ₀, hJ₀C, hT⟩ :=
    exists_chart_le_chartKer_exceptionalSumImage hXqc hZfp hb hZ'fp
  have := hV
  obtain ⟨W, hWfp, hCW, hJW⟩ := exists_isFinitePresentation_le_chartKer B S hS hZ X hXqc hXqs
    (exceptionalSumImage b Z Z' d) p hp J₀ hJ₀ hJ₀C
  have hWpre : preimageClosedSubspace b W = exceptionalSum b Z Z' d :=
    Subtype.ext (le_antisymm (hT W hJW)
      ((exceptionalSum_le_preimage_exceptionalSumImage b Z Z' d).trans
        fun _ _ hx => hCW _ hx))
  exact ⟨W, d, hWfp, hWpre, subspacePointSet_subset_union_image_of_preimage_eq hb Z' W d hWpre⟩

/-- **Stacks 0860.**  Let `S` be a scheme and let `X` be a quasi-compact and quasi-separated
algebraic space over `S`.  Let `Z ⊆ X` be a closed subspace of finite presentation and let
`b : X' ⟶ X` be the blowing up of `X` in `Z`.  Let `Z' ⊆ X'` be a closed subspace of finite
presentation and let `c : X'' ⟶ X'` be the blowing up of `X'` in `Z'`.  Then there exists a
closed subspace `Y ⊆ X` of finite presentation such that `|Y| = |Z| ∪ |b|(|Z'|)` and
`c ≫ b : X'' ⟶ X` is isomorphic to the blowing up of `X` in `Y`.

The blowups are named by their universal property, Stacks 085U
(`AlgebraicGeometry.Space.IsBlowupAlong`), so "isomorphic to the blowing up of `X` in `Y`" is
`IsBlowupAlong B S hS Y (c ≫ b)`, and `|Y| = |Z| ∪ |b|(|Z'|)` is
`AlgebraicGeometry.Space.IsCompositeCentre`.  Quasi-separatedness of `X` is absolute
quasi-separatedness, which needs the terminal scheme in the site (`hZ`).

This is `AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong` with its second centre
supplied by `AlgebraicGeometry.Space.hasSecondCentre`; see the module documentation for how that
replaces the source's appeal to Stacks 085N. -/
@[stacks 0860]
theorem exists_isCompositeCentre_isBlowupAlong_of_isQuasiCompactSpace
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (hZfp : IsFinitePresentation B S hS Z.1.ι)
    {Z' : ClosedSubspaces B S hS X'.1} {c : X'' ⟶ X'} (hc : IsBlowupAlong B S hS Z' c)
    (hZ'fp : IsFinitePresentation B S hS Z'.1.ι) :
    ∃ Y : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Y.1.ι ∧
      IsCompositeCentre B S hS b Z Z' Y ∧ IsBlowupAlong B S hS Y (c ≫ b) :=
  exists_isCompositeCentre_isBlowupAlong hb hZfp hc hZ'fp
    (hasSecondCentre hZ hXqc hXqs hZfp hb)

/-! ### Stacks 086C -/

/-- **Stacks 086C, granted the second centre of Stacks 085N.**  Let `S` be a scheme, let `X` be
an algebraic space over `S`, let `U ⊆ X` be an open subspace, let `b : X' ⟶ X` be a
`U`-admissible blowup and let `c : X'' ⟶ X'` be a `b^{-1}(U)`-admissible blowup.  Then the
composition `c ≫ b : X'' ⟶ X` is a `U`-admissible blowup.

The source writes the second blowup as `U`-admissible, which is a statement about `X'` and so
reads `b^{-1}(U)`-admissible; that is how the scheme-level Tag 080L
(`Stacks.Blowup.IsAdmissibleBlowup.comp`) and clause (b) of Tag 086E
(`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_factoring_isAdmissibleBlowup`) read it too.

The centre is the composite centre `Y` of Stacks 0860,
`AlgebraicGeometry.Space.exists_isCompositeCentre_isBlowupAlong`.  It is finitely presented and
`c ≫ b` is the blowup of `X` in it by that result, and it is disjoint from `U`: its points are
`|Z| ∪ |b|(|Z'|)`, the first centre `Z` is disjoint from `U` because `b` is `U`-admissible, and
`|b|(|Z'|)` is disjoint from `U` because `Z'` is disjoint from `|b|^{-1}(|U|)`, which is the
point set of `b^{-1}(U)`.

Quasi-compactness and quasi-separatedness of `X` and quasi-compactness of `U` are not taken:
the source uses them only to reach Stacks 085N, which is the assumed input `h085N` here.  Their
omission widens the class of algebraic spaces the statement is about.

**This declaration is deliberately left unregistered for Stacks 086C**, for the same reason as
at Stacks 0860: `h085N` is Stacks 085N at the Rees algebra of the first centre, quantified over
the centres the proof unpacks from the admissibility of `b`, and nothing in this tree discharges
it.  See the module documentation. -/
theorem isAdmissibleBlowup_comp [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (U : OpenSubspaces B S hS X.1) {b : X' ⟶ X} {c : X'' ⟶ X'}
    (hb : IsAdmissibleBlowup B S hS U b)
    (hc : IsAdmissibleBlowup B S hS
      ⟨U.1.preimage b.hom, isOpenSubspace_preimage B S hS b.hom U.1 X.2 X'.2 U.2⟩ c)
    (h085N : ∀ Z : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Z.1.ι →
      IsBlowupAlong B S hS Z b → HasSecondCentre Z b) :
    IsAdmissibleBlowup B S hS U (c ≫ b) := by
  obtain ⟨Z, hZfp, hZdisj, hbZ⟩ := hb
  obtain ⟨Z', hZ'fp, hZ'disj, hcZ'⟩ := hc
  obtain ⟨Y, hYfp, hYcomp, hYb⟩ :=
    exists_isCompositeCentre_isBlowupAlong hbZ hZfp hcZ' hZ'fp (h085N Z hZfp hbZ)
  have hY : subspacePointSet B S hS X.1 Y.1 =
      subspacePointSet B S hS X.1 Z.1 ∪
        pointsMap B S hS X'.1 b.hom '' subspacePointSet B S hS X'.1 Z'.1 := hYcomp
  refine isAdmissibleBlowup_of_isBlowupAlong hYfp ?_ hYb
  rw [hY]
  refine Set.disjoint_union_right.2 ⟨hZdisj, Set.disjoint_left.2 fun v hv hmem => ?_⟩
  obtain ⟨w, hwZ', hbw⟩ := hmem
  have hwpre : w ∈ subspacePointSet B S hS X'.1 (U.1.preimage b.hom) := by
    rwa [subspacePointSet_preimage, Set.mem_preimage, hbw]
  exact Set.disjoint_left.1 hZ'disj hwpre hwZ'

end AlgebraicGeometry.Space

end
