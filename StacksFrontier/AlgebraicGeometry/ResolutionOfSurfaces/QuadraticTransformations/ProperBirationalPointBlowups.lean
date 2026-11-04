module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence

/-!
# A proper birational morphism of regular surfaces as a sequence of blowups at closed points

Let `f : X ⟶ Y` be a proper birational morphism between integral Noetherian schemes regular of
dimension two. The assertion of [Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) is
that `f` is a sequence of blowups in closed points, that is, that `f` is — up to an isomorphism
of its source — the composite of a chain `Yₙ → Yₙ₋₁ → … → Y₀ = Y` in which each step is the
blowup of its target at a closed point. That notion is already in the library: the chain is
`Stacks.ResolutionOfSurfaces.PointBlowupChain` and its isomorphism-invariant form is
`Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups`, with no restriction on the centres, i.e.
with `T = Set.univ`, which is the spelling the library's Tag 0BIB also uses.

The source's argument is an induction. Its base case is that an isomorphism is the empty chain,
and its step is: if `f` is not an isomorphism and `y` is a closed point of `Y` outside the
maximal open over which `f` is an isomorphism, then `f` factors through the blowup `Y' ⟶ Y` at
`y`, by a morphism `X ⟶ Y'` which is again proper and birational, and the number of curves in
the fibres of that morphism is strictly smaller than for `f`.

## Main definitions

* `Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface` — the hypothesis Tag 0C5R imposes on
  both of its schemes: integral, Noetherian, regular and of dimension two. Regularity is
  `AlgebraicGeometry.IsRegular` and the dimension is `topologicalKrullDim`, which is the pair
  the library's Tag 0BIB uses for "regular Noetherian scheme of dimension two".

## Main results

* `Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.of_isIso` — an isomorphism is the empty
  sequence of blowups at closed points.
* `Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups.compChain` — a morphism which factors as a
  sequence of blowups at closed points over the source of a point blowup chain composes with
  that chain to a sequence of blowups at closed points.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_blowUpToBase` — the blowup at one closed
  point is a sequence of blowups at closed points.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_comp_blowUpToBase` — the induction step
  of Tag 0C5R, in the only direction that is unconditional: a morphism which factors through the
  blowup at a closed point by a morphism that is itself a sequence of blowups at closed points
  is a sequence of blowups at closed points.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupStep` — the statement of Tag
  0C5R, proved from the source's induction step and the globalization of Tag 0AGR, both carried
  as named hypotheses.

## What is and is not proved

Proved unconditionally: the base case (`FactorsAsPointBlowups.of_isIso`), the two composition
lemmas (`FactorsAsPointBlowups.compChain`, `factorsAsPointBlowups_blowUpToBase`), the
unconditional direction of the induction step
(`factorsAsPointBlowups_of_comp_blowUpToBase`), and the well-founded induction itself
(`factorsAsPointBlowups_of_pointBlowupStep`), which turns the source's one-blowup step into the
full chain.

Not proved, and carried as explicit hypotheses of `factorsAsPointBlowups_of_pointBlowupStep`:

* `blowUpSurface`, the globalization of [Stacks, Tag 0AGR]: the blowup of an integral Noetherian
  scheme regular of dimension two at a closed point is again such a scheme. The library has Tag
  0AGR only for the blowup of `Spec A` at the closed point of a two-dimensional regular local
  ring `A`, as `AlgebraicGeometry.irreducibleSpace_blowUp_maximalIdeal` and
  `AlgebraicGeometry.isRegular_blowUp_maximalIdeal`; passing from there to a closed point of an
  arbitrary such scheme is not done here.
* `step`, the body of the source's proof of Tag 0C5R together with its omitted bookkeeping: for
  a proper birational morphism `g` of such schemes which is not an isomorphism, a closed point
  of the target through whose blowup `g` factors, by a morphism which is again proper and
  birational and which has strictly smaller `μ`, where `μ` is an arbitrary natural-number
  measure also carried as a hypothesis. In the source, `μ` is the number of curves in the fibres
  and the measure's decrease is the step for which the text says "Some details omitted".

Consequently **no `@[stacks 0C5R]` attribute is placed in this file.** The hypothesis `step` is
inter-derivable with the conclusion — from the conclusion one reads off a nonempty chain, whose
first blowup is a blowup of the target at a closed point and whose length is a measure that
drops — so a declaration concluding Tag 0C5R from `step` would be assuming its own content, and
the tag would be unsound on it. What is missing for a tagged Tag 0C5R is a proof of `step`: by
[Stacks, Tag 0C5H] one dominates `g` by a chain of blowups, and then either the exceptional
curve of one blowup collapses, and [Stacks, Tag 0C5J] contracts it, or it maps isomorphically to
the exceptional curve of `Y'`, the conormal comparison on `P¹` is an isomorphism, and `g` is
unramified and hence quasi-finite along it, so that [Stacks, Tag 0BFP] puts `y` in the
isomorphism locus against the choice of `y`.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The hypothesis on the two schemes -/

/-- The hypothesis [Stacks, Tag 0C5R] imposes on each of its two schemes: an integral Noetherian
scheme which is regular and of dimension two. -/
public structure IsIntegralRegularSurface (X : Scheme.{u}) : Prop where
  /-- The scheme is integral. -/
  isIntegral : AlgebraicGeometry.IsIntegral X
  /-- The scheme is Noetherian. -/
  isNoetherian : AlgebraicGeometry.IsNoetherian X
  /-- Every point has an affine neighbourhood with regular ring of sections. -/
  isRegular : AlgebraicGeometry.IsRegular X
  /-- The scheme has dimension two. -/
  topologicalKrullDim_eq : topologicalKrullDim X = 2

/-! ### The base case and the composition lemmas -/

/-- An isomorphism is the empty sequence of blowups at closed points. -/
public theorem FactorsAsPointBlowups.of_isIso {X Y : Scheme.{u}} (T : Set Y) (f : X ⟶ Y)
    [IsIso f] : FactorsAsPointBlowups Y T X f :=
  ⟨Y, 𝟙 Y, PointBlowupChain.refl, asIso f, by simp⟩

/-- A morphism which factors as a sequence of blowups at closed points of the source of a point
blowup chain composes with that chain to a sequence of blowups at closed points, provided the
centres of the inner sequence lie over those allowed for the outer one. -/
public theorem FactorsAsPointBlowups.compChain {Y W Z : Scheme.{u}} {T : Set Y} {S : Set W}
    {r : W ⟶ Y} {q : Z ⟶ W} (hq : FactorsAsPointBlowups W S Z q)
    (hr : PointBlowupChain Y T W r) (hST : ∀ w ∈ S, r.base w ∈ T) :
    FactorsAsPointBlowups Y T Z (q ≫ r) := by
  obtain ⟨W', p, hchain, e, he⟩ := hq
  exact ⟨W', p ≫ r, hr.comp hchain hST, e, by rw [← Category.assoc, he]⟩

/-- The blowup at a single closed point is a sequence of blowups at closed points. -/
public theorem factorsAsPointBlowups_blowUpToBase {Y : Scheme.{u}} (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    FactorsAsPointBlowups Y Set.univ
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) :=
  (FactorsAsPointBlowups.refl _).step _ hy trivial

/-- The point blowup chain consisting of the blowup at one closed point. -/
public theorem pointBlowupChain_blowUpToBase {Y : Scheme.{u}} (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    PointBlowupChain Y Set.univ
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) := by
  simpa using (PointBlowupChain.refl (X := Y) (T := (Set.univ : Set Y))).step y hy trivial

/-- The induction step of [Stacks, Tag 0C5R], in the direction that holds unconditionally: a
morphism which factors through the blowup at a closed point by a morphism that is itself a
sequence of blowups at closed points is a sequence of blowups at closed points. -/
public theorem factorsAsPointBlowups_of_comp_blowUpToBase {X Y : Scheme.{u}} {f : X ⟶ Y}
    (y : Y) (hy : IsClosed ({y} : Set Y))
    {g : X ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))}
    (hg : g ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f)
    (hgfac : FactorsAsPointBlowups
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) Set.univ X g) :
    FactorsAsPointBlowups Y Set.univ X f :=
  (hgfac.compChain (pointBlowupChain_blowUpToBase y hy) fun _ _ => trivial).congr hg

/-! ### The induction of Tag 0C5R -/

/-- **Stacks Project, Tag 0C5R**, the induction, from the source's step. Let `f : X ⟶ Y` be a
proper birational morphism between integral Noetherian schemes regular of dimension two. Then
`f` is a sequence of blowups in closed points.

Two inputs are carried as hypotheses rather than proved, and because the first of them is
inter-derivable with the conclusion this declaration deliberately carries **no** Tag 0C5R
attribute:

* `step`, the body of the source's proof together with the bookkeeping it omits: for a proper
  birational morphism `g` of such schemes which is not an isomorphism, a closed point of the
  target through whose blowup `g` factors by a morphism which is again proper and birational and
  whose measure `μ` is strictly smaller. In the source `μ` is the number of curves in the fibres.
* `blowUpSurface`, the globalization of [Stacks, Tag 0AGR]: the blowup of such a scheme at a
  closed point is again such a scheme. -/
public theorem factorsAsPointBlowups_of_pointBlowupStep
    (μ : ∀ (A B : Scheme.{u}), (B ⟶ A) → ℕ)
    (blowUpSurface : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)),
      IsIntegralRegularSurface A →
        IsIntegralRegularSurface
          (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))))
    (step : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
        ∃ (a : A) (ha : IsClosed ({a} : Set A))
          (g' : B ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))),
          g' ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)) = g ∧
            IsProper g' ∧ IsBirational g' ∧
              μ (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) B g' <
                μ A B g)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsIntegralRegularSurface Y)
    (hX : IsIntegralRegularSurface X) (hproper : IsProper f) (hbirational : IsBirational f) :
    FactorsAsPointBlowups Y Set.univ X f := by
  classical
  suffices H : ∀ (m : ℕ) (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → μ A B g = m →
      FactorsAsPointBlowups A Set.univ B g by
    exact H (μ Y X f) Y X f hY hX hproper hbirational rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    intro A B g hA hB hp hb hm
    by_cases hiso : IsIso g
    · exact @FactorsAsPointBlowups.of_isIso B A Set.univ g hiso
    · obtain ⟨a, ha, g', hfactor, hp', hb', hlt⟩ := step A B g hA hB hp hb hiso
      exact factorsAsPointBlowups_of_comp_blowUpToBase a ha hfactor
        (ih (μ _ B g') (hm ▸ hlt) _ B g' (blowUpSurface A a ha hA) hB hp' hb' rfl)

/-- On an integral scheme of dimension two the ideal sheaf of a reduced closed point is nonzero:
were it zero its support would be everything, forcing the scheme to be a single point. -/
public theorem vanishingIdeal_singleton_ne_bot {W : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] (hdim : topologicalKrullDim W = 2) (w : W)
    (hw : IsClosed ({w} : Set W)) :
    Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) ≠ ⊥ := by
  intro hbot
  have htop : (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).support = ⊤ :=
    Scheme.IdealSheafData.support_eq_top_iff.mpr hbot
  have hcoe : ({w} : Set W) = Set.univ := by
    have hsupp := Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
    rw [htop] at hsupp
    simpa using hsupp.symm
  have hsingle : Subsingleton W :=
    ⟨fun a b => (hcoe ▸ Set.mem_univ a : a ∈ ({w} : Set W)).trans
      (hcoe ▸ Set.mem_univ b : b ∈ ({w} : Set W)).symm⟩
  have hne : Nonempty W := ⟨w⟩
  rw [topologicalKrullDim_eq_zero_of_subsingleton] at hdim
  exact absurd hdim (by norm_num)

end Stacks.ResolutionOfSurfaces

end
