module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ProperBirationalPointBlowups
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg

/-!
# A proper birational morphism of regular surfaces is a sequence of blowups at closed points

Let `f : X ⟶ Y` be a proper birational morphism between integral Noetherian schemes regular of
dimension two. [Stacks, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R) (Resolution of
Surfaces, Lemma 54.17.1) asserts that `f` is a sequence of blowups in closed points, that is,
that `f` is, up to an isomorphism of its source, the composite of a chain
`Yₙ → Yₙ₋₁ → … → Y₀ = Y` each of whose steps is the blowup of its target at a closed point. In
this library that conclusion is
`Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups Y Set.univ X f`.

The source argues by induction on the number of curves in the fibres. If `f` is not an
isomorphism, the maximal open `V ⊆ Y` over which it is an isomorphism omits a closed point `y`;
one blows `y` up to get `b : Y' ⟶ Y`, dominates the resulting rational map by a chain of blowups
of `X`, and reduces to a single blowup `π : X' ⟶ X` sitting in a commuting square over `b`. The
exceptional curve `E ⊆ X'` then either collapses in `Y'`, in which case `f` factors through `b`,
or maps isomorphically onto the exceptional curve of `Y'`, which is impossible.

That last dichotomy and the contradiction it leads to are already in this library, in
`ExceptionalCurveLocus.lean`. What this file adds is the induction that consumes them: the
geometric input is the commuting *square* over the blowup, not the factorization through it, and
from the square the factorization is produced rather than assumed. This is the difference from
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupStep`, whose `step` hypothesis
is the factorization itself and is therefore inter-derivable with the conclusion, so that no tag
could be placed on it.

## Main definitions

* `Stacks.ResolutionOfSurfaces.pointBlowUp` and
  `Stacks.ResolutionOfSurfaces.pointBlowUpToBase` — the blowup of a scheme at a reduced closed
  point and its structure morphism.
* `Stacks.ResolutionOfSurfaces.HasExceptionalSquareOver` — the geometric data the source's steps
  2 and 3 supply at a closed point `a` of the target: a dominating scheme `B'`, a contraction
  `π : B' ⟶ B` of an exceptional curve of the first kind, a proper birational morphism
  `g' : B' ⟶ pointBlowUp ha` making the square over the blowup commute, an exceptional curve of
  the first kind in `pointBlowUp ha` containing the fibre over `a`, and the dichotomy of step 3.
* `Stacks.ResolutionOfSurfaces.HasExceptionalSquareAt` — the same, with the field of definition
  of the two curves existentially quantified.

## Main results

* `Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_pointBlowUp` — the blowup of an integral
  Noetherian scheme regular of dimension two at a closed point is integral and Noetherian, so
  that regularity and the dimension are all that [Stacks, Tag 0AGR] still has to supply at a
  closed point of such a scheme.
* `Stacks.ResolutionOfSurfaces.isProper_of_comp_pointBlowUpToBase` and
  `Stacks.ResolutionOfSurfaces.isBirational_of_comp_pointBlowUpToBase` — a morphism factoring a
  proper birational morphism through the blowup at a closed point is itself proper and
  birational.
* `Stacks.ResolutionOfSurfaces.exists_comp_eq_pointBlowUpToBase_of_hasExceptionalSquareOver` —
  one step of the source's induction: from the square at a closed point outside the maximal
  isomorphism open, the morphism factors through the blowup at that point.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_proper_birational` — **Tag 0C5R**: a
  proper birational morphism between integral Noetherian schemes regular of dimension two is a
  sequence of blowups at closed points.

## What is and is not proved

Proved here: the step, from the square (the choice of the closed point is
`Stacks.ResolutionOfSurfaces.exists_isClosed_singleton_notMem_isomorphism_open` and the
factorization is `Stacks.ResolutionOfSurfaces.exists_comp_eq_of_exceptionalCurveDichotomy`), the
well-founded induction that turns the step into the full chain, integrality and Noetherianity of
the blowup at the chosen point, and properness and birationality of the factorization through
it.

Three inputs remain as named arguments of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_proper_birational`, together with the
measure drop:

* `hsec`, `Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow`, the second arrow of
  [Stacks, Tag 067L] with the two clauses of that tag absent from this library. It is
  quantified over every triangle of immersions of schemes and is the standing hypothesis of
  every file in this directory. What is present is the first arrow,
  `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap`, and, for the conormal sequence
  of a single immersion ([Stacks, Tag 01UZ]), the right-hand epimorphism and the vanishing of
  the composite; exactness in the middle of Tag 01UZ is available only for a smooth source, as
  `Stacks.ConormalSequenceRight.conormalShortComplex_shortExact`, and the exceptional curve is
  not smooth over the base.
* `blowUpSurface`, what is left after
  `Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_pointBlowUp` of the hypothesis that the
  blowup of an integral Noetherian scheme regular of dimension two at a closed point is again
  such a scheme: its regularity, which is the globalization of the second conclusion of
  [Stacks, Tag 0AGR], and that it again has dimension two, which that tag leaves implicit. The
  library has the tag only for the blowup of `Spec A` at the closed point of a two-dimensional
  regular local ring, as
  `AlgebraicGeometry.irreducibleSpace_blowUp_maximalIdeal` and
  `AlgebraicGeometry.isRegular_blowUp_maximalIdeal`; its chart criterion
  `isRegular_blowUp_of_charts` asks for one affine open covering the base, so passing to a
  closed point of an arbitrary such scheme needs the blowup to be compared with the blowup of a
  restriction, which is not in the library.
* `square`, the source's step 2 together with the dichotomy of its step 3: the chain of blowups
  dominating the rational map to the blowup of the chosen point, reduced to a single blowup. This
  comes from [Stacks, Tag 0C5H] — which this library has in `DominateRationalMap.lean`, itself
  with three named arguments — together with an induction on the length of that chain, the
  globalization of [Stacks, Tag 0AGR] and [Stacks, Tag 0C5K] identifying the exceptional curves
  as copies of `𝐏¹`, and the fact that a morphism between two copies of `𝐏¹` is constant or an
  isomorphism.

`descent` is now only the bookkeeping for which the source says "some details omitted": that a
factorization of the morphism through the blowup at the chosen point has strictly smaller
measure `μ`, where `μ` is an arbitrary natural-number measure also supplied as an argument. In
the source `μ` is the number of curves in the fibres. That the factorization is again proper and
birational, which `descent` used to assert as well, is proved here: properness is cancellation
of a proper morphism against the separated `pointBlowUpToBase`
(`AlgebraicGeometry.IsProper.of_comp`) and birationality is
`AlgebraicGeometry.isBirational_of_comp_blowUpToBase`.

Unlike the `step` hypothesis of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupStep`, none of these is
inter-derivable with the conclusion. From the conclusion one reads off a nonempty chain and hence
a factorization through a blowup, which is what `step` asserts; but `square` asserts the existence
of a scheme dominating the source on which an exceptional curve of the first kind — a copy of
`𝐏¹` over a field — is contracted to a point, and the conclusion provides no such curve.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The blowup at a closed point -/

/-- The blowup of a scheme at a reduced closed point. -/
public abbrev pointBlowUp {A : Scheme.{u}} {a : A} (ha : IsClosed ({a} : Set A)) : Scheme.{u} :=
  blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))

/-- The structure morphism of the blowup of a scheme at a reduced closed point. -/
public abbrev pointBlowUpToBase {A : Scheme.{u}} {a : A} (ha : IsClosed ({a} : Set A)) :
    pointBlowUp ha ⟶ A :=
  blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))

/-! ### What the blowup at a closed point of a surface inherits -/

/-- **The blowup at a closed point of an integral Noetherian scheme regular of dimension two is
integral and Noetherian.** Integrality is integrality of the blowup of an integral scheme in a
nonzero ideal, the ideal of a closed point being nonzero in dimension two; Noetherianity is
properness of the blowup over a Noetherian base. Regularity and the dimension of the blowup,
which are the content of [Stacks, Tag 0AGR], are the two remaining arguments. -/
public theorem isIntegralRegularSurface_pointBlowUp {A : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) {a : A} (ha : IsClosed ({a} : Set A))
    (hreg : IsRegular (pointBlowUp ha))
    (hdim : topologicalKrullDim (pointBlowUp ha) = 2) :
    IsIntegralRegularSurface (pointBlowUp ha) := by
  have hint := hA.isIntegral
  have hnoe := hA.isNoetherian
  have hLN : IsLocallyNoetherian A := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  have hLN' : IsLocallyNoetherian (pointBlowUp ha) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointBlowUpToBase ha)
  have hcpt : CompactSpace (pointBlowUp ha) :=
    QuasiCompact.compactSpace_of_compactSpace (pointBlowUpToBase ha)
  exact ⟨isIntegral_blowUp _ (vanishingIdeal_singleton_ne_bot hA.topologicalKrullDim_eq a ha),
    ⟨⟩, hreg, hdim⟩

/-- **A factorization through the blowup at a closed point of a locally Noetherian scheme is
proper when the morphism it factors is.** The blowup is separated, so properness cancels. -/
public theorem isProper_of_comp_pointBlowUpToBase {A B : Scheme.{u}} [IsLocallyNoetherian A]
    {a : A} (ha : IsClosed ({a} : Set A)) {g : B ⟶ A} (hg : IsProper g)
    (ψ : B ⟶ pointBlowUp ha) (hψ : ψ ≫ pointBlowUpToBase ha = g) : IsProper ψ := by
  have hcomp : IsProper (ψ ≫ pointBlowUpToBase ha) := hψ ▸ hg
  exact IsProper.of_comp ψ (pointBlowUpToBase ha)

/-- **A factorization through the blowup at a closed point of an integral scheme of dimension two
is birational when the morphism it factors is.** The ideal of the point is nonzero, so the blowup
is birational and birationality descends along it. -/
public theorem isBirational_of_comp_pointBlowUpToBase {A B : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral A] [AlgebraicGeometry.IsIntegral B]
    (hdim : topologicalKrullDim A = 2) {a : A} (ha : IsClosed ({a} : Set A)) {g : B ⟶ A}
    (hg : IsBirational g) (ψ : B ⟶ pointBlowUp ha)
    (hψ : ψ ≫ pointBlowUpToBase ha = g) : IsBirational ψ :=
  isBirational_of_comp_blowUpToBase _ (vanishingIdeal_singleton_ne_bot hdim a ha) ψ (hψ ▸ hg)

/-! ### The square the source's steps 2 and 3 produce -/

/-- **The geometric input of steps 2 and 3 of [Stacks, Tag 0C5R] at a closed point `a`, over a
field `k`.** The data is: a reduced scheme `B'` dominating `B` by a morphism `π` which is
surjective and which contracts an exceptional curve of the first kind `D ⊆ B'`, presented as
`𝐏¹_k`, to a single point; a proper birational morphism `g' : B' ⟶ pointBlowUp ha` making the
square over the blowup commute; an exceptional curve of the first kind `D' ⊆ pointBlowUp ha`,
also presented as `𝐏¹_k`, whose points include the whole fibre of the blowup over `a`; and the
dichotomy of the source's step 3, namely that `g'` either carries `D` to a single point of
`pointBlowUp ha` or maps it to `D'` by a morphism compatible with the two presentations whose
conormal comparison map is nonzero.

In the source this is produced by [Stacks, Tag 0C5H], which dominates the rational map from `B`
to the blowup by a chain of blowups at closed points, followed by the reduction of that chain to
its last step. -/
public def HasExceptionalSquareOver (k : Type u) [Field k] {A B : Scheme.{u}} (g : B ⟶ A)
    (a : A) (ha : IsClosed ({a} : Set A)) : Prop :=
  ∃ (B' : Scheme.{u}) (_ : IsReduced B') (π : B' ⟶ B) (g' : B' ⟶ pointBlowUp ha)
      (_ : IsProper g'),
    IsBirational g' ∧ g' ≫ pointBlowUpToBase ha = π ≫ g ∧ Function.Surjective π.base ∧
      ∃ (D : B'.IdealSheafData) (D' : (pointBlowUp ha).IdealSheafData)
          (e : projectiveLineProj k ≅ D.subscheme)
          (e' : projectiveLineProj k ≅ D'.subscheme),
        IsContractionOfExceptionalCurve D π ∧
          D.IsExceptionalCurveOfFirstKind k e ∧ D'.IsExceptionalCurveOfFirstKind k e' ∧
            ((pointBlowUpToBase ha) ⁻¹' {a} : Set (pointBlowUp ha)) ⊆
                Set.range D'.subschemeι.base ∧
              (∃ x : B, ∀ t : D.subscheme, π (D.subschemeι t) = x) ∧
                ((∃ w : pointBlowUp ha, ∀ z : D.subscheme, g' (D.subschemeι z) = w) ∨
                  ∃ (γ : D.subscheme ⟶ D'.subscheme) (_ : e.hom ≫ γ = e'.hom)
                    (j : D.subscheme ⟶ pointBlowUp ha) (_ : IsImmersion j)
                    (hj : γ ≫ D'.subschemeι = j) (h : D.subschemeι ≫ g' = j),
                    Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι γ g'
                      (Stacks.Immersion.toShHom_square (h.trans hj.symm)) ≠ 0)

/-- **The geometric input of steps 2 and 3 of [Stacks, Tag 0C5R] at a closed point `a`.** This is
`Stacks.ResolutionOfSurfaces.HasExceptionalSquareOver` with the field of definition of the two
exceptional curves existentially quantified; in the source it is the residue field at `a`. -/
public def HasExceptionalSquareAt {A B : Scheme.{u}} (g : B ⟶ A) (a : A)
    (ha : IsClosed ({a} : Set A)) : Prop :=
  ∃ (k : Type u) (fk : Field k), @HasExceptionalSquareOver k fk A B g a ha

/-! ### One step of the induction -/

/-- **One step of [Stacks, Tag 0C5R]: the factorization through the blowup at the chosen point.**
Let `g : B ⟶ A` be a proper birational morphism onto a regular Noetherian scheme with reduced
source, let `U` be the maximal open over which `g` is an isomorphism and let `a ∉ U` be a closed
point. If the square of
`Stacks.ResolutionOfSurfaces.HasExceptionalSquareOver` is available at `a`, then `g` factors
through the blowup of `A` at `a`.

By `Stacks.ResolutionOfSurfaces.exists_comp_eq_of_exceptionalCurveDichotomy` the second
alternative of the dichotomy is impossible — it would put `a` in `U` against its choice — so the
exceptional curve of `B'` collapses and [Stacks, Tag 0C5J] contracts it. -/
public theorem exists_comp_eq_pointBlowUpToBase_of_hasExceptionalSquareOver (k : Type u)
    [Field k] (hsec : ConormalSequenceSecondArrow.{u}) {A B : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian A] [IsReduced B] (g : B ⟶ A) [IsProper g]
    (hg : IsBirational g) (hA : IsRegular A) (U : A.Opens)
    (hU : IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U) (a : A)
    (ha : IsClosed ({a} : Set A)) (haU : a ∉ U)
    [AlgebraicGeometry.IsNoetherian (pointBlowUp ha)] (hA' : IsRegular (pointBlowUp ha))
    (hdata : HasExceptionalSquareOver k g a ha) :
    ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g := by
  obtain ⟨B', hred, π, g', hprop, hg', hsq, hπ, D, D', e, e', hcontr, hE, hE', hbfib,
    ⟨x, hx⟩, hdich⟩ := hdata
  have : IsReduced B' := hred
  have : IsProper g' := hprop
  obtain ⟨ψ, -, hψ⟩ := exists_comp_eq_of_exceptionalCurveDichotomy k hsec g hg hA U hU haU
    (pointBlowUpToBase ha) g' hg' hA' hsq hπ hcontr hE hE' hbfib x hx hdich
  exact ⟨ψ, hψ⟩

/-! ### The induction -/

/-- **Stacks Project, Tag 0C5R.** Let `f : X ⟶ Y` be a proper birational morphism between
integral Noetherian schemes regular of dimension two. Then `f` is a sequence of blowups in closed
points, that is, `f` is up to an isomorphism of its source the composite of a chain of blowups at
closed points.

Three inputs are arguments rather than theorems: `hsec`, the second arrow of
[Stacks, Tag 067L]; `blowUpSurface`, the regularity ([Stacks, Tag 0AGR] globally) and the
dimension of the blowup at a closed point; and `square`, the reduction of [Stacks, Tag 0C5H]
to a single blowup together with the dichotomy of the source's step 3. The fourth argument
`descent` is the strict drop of the measure `μ`, the bookkeeping the source omits. None of them
is inter-derivable with the conclusion; see the module documentation. -/
@[stacks 0C5R "the conclusion in full; the inputs hsec, blowUpSurface and square remain named \
arguments and descent is reduced to the drop of the measure, as the module documentation \
records"]
public theorem factorsAsPointBlowups_of_proper_birational
    (hsec : ConormalSequenceSecondArrow.{u}) (μ : ∀ (A B : Scheme.{u}), (B ⟶ A) → ℕ)
    (blowUpSurface : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)),
      IsIntegralRegularSurface A →
        IsRegular (pointBlowUp ha) ∧ topologicalKrullDim (pointBlowUp ha) = 2)
    (square : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          HasExceptionalSquareAt g a ha)
    (descent : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          ∀ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g →
            μ (pointBlowUp ha) B ψ < μ A B g)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsIntegralRegularSurface Y)
    (hX : IsIntegralRegularSurface X) (hproper : IsProper f) (hbirational : IsBirational f) :
    FactorsAsPointBlowups Y Set.univ X f := by
  classical
  suffices H : ∀ (m : ℕ) (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → μ A B g = m →
      FactorsAsPointBlowups A Set.univ B g from
    H (μ Y X f) Y X f hY hX hproper hbirational rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    intro A B g hA hB hp hb hm
    by_cases hiso : IsIso g
    · exact @FactorsAsPointBlowups.of_isIso B A Set.univ g hiso
    · have : AlgebraicGeometry.IsNoetherian A := hA.isNoetherian
      have : AlgebraicGeometry.IsIntegral A := hA.isIntegral
      have : AlgebraicGeometry.IsIntegral B := hB.isIntegral
      have : IsProper g := hp
      obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open g
      obtain ⟨a, ha, haU⟩ := exists_isClosed_singleton_notMem_isomorphism_open g U hU hiso
      obtain ⟨k, fk, hdata⟩ := square A B g hA hB hp hb hiso a ha U hU haU
      have hLN : IsLocallyNoetherian A := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
      obtain ⟨hregblow, hdimblow⟩ := blowUpSurface A a ha hA
      have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
        isIntegralRegularSurface_pointBlowUp hA ha hregblow hdimblow
      have : AlgebraicGeometry.IsNoetherian (pointBlowUp ha) := hA'.isNoetherian
      obtain ⟨ψ, hψ⟩ := exists_comp_eq_pointBlowUpToBase_of_hasExceptionalSquareOver k hsec g
        hb hA.isRegular U hU a ha haU hA'.isRegular hdata
      have hlt := descent A B g hA hB hp hb hiso a ha U hU haU ψ hψ
      exact factorsAsPointBlowups_of_comp_blowUpToBase a ha hψ
        (ih (μ _ B ψ) (hm ▸ hlt) _ B ψ hA' hB (isProper_of_comp_pointBlowUpToBase ha hp ψ hψ)
          (isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hb ψ hψ) rfl)

end Stacks.ResolutionOfSurfaces

end
