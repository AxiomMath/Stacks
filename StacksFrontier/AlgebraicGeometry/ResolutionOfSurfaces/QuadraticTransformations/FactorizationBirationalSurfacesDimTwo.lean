module

public import StacksFrontier.AlgebraicGeometry.Properties.RegularStalkDvr
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ConormalSequenceSecondArrow
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMapsDimTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalSurfaces
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FibreCurveMeasure
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusDVR
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0C5R with its conormal and blowup inputs discharged

`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_proper_birational` of
`ResolutionOfSurfaces/QuadraticTransformations/FactorizationBirationalSurfaces.lean` is
[Stacks, Tag 0C5R] over four arguments: `hsec`, the second arrow of [Stacks, Tag 067L];
`blowUpSurface`, the regularity and dimension of the blowup at a closed point;
`square`, the reduction of [Stacks, Tag 0C5H] to a single blowup together with the dichotomy of
the source's step 3; and `descent`, the strict drop of an abstract measure. The first two are
discharged here, and so — in the last theorem below — are the measure and its drop.

## Main definitions

* `Stacks.ResolutionOfSurfaces.ExceptionalCurveMapsOntoOver` — the second alternative of the
  source's step 3, over a field `k`: an exceptional curve of the first kind in `pointBlowUp ha`
  containing the fibre over `a`, presented as `𝐏¹_k` compatibly with the curve upstairs, and the
  nonvanishing of the conormal comparison map.
* `Stacks.ResolutionOfSurfaces.ExceptionalCurveDichotomy` — the dichotomy of step 3: either the
  curve upstairs collapses, or the previous alternative holds over some field.
* `Stacks.ResolutionOfSurfaces.HasExceptionalSquareDichotomyAt` — the geometric data the source's
  steps 2 and 3 supply at a closed point `a` of the target, with the dichotomy in that form. It
  is the counterpart of `Stacks.ResolutionOfSurfaces.HasExceptionalSquareAt` of
  `FactorizationBirationalSurfaces.lean`, which presents both curves over one common field
  outside the dichotomy.

## Main results

* `Stacks.ResolutionOfSurfaces.ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open` — a closed
  point outside the maximal isomorphism open of a proper birational morphism onto an integral
  Noetherian scheme regular of dimension two has a two-dimensional local ring.
* `Stacks.ResolutionOfSurfaces.preimage_singleton_subset_range_exceptionalIdeal` — the fibre of
  the blowup at a closed point lies in its exceptional curve.
* `Stacks.ResolutionOfSurfaces.exists_comp_eq_pointBlowUpToBase_of_hasExceptionalSquareDichotomyAt`
  — one step of the source's induction, from the square in the dichotomy form.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_step_of_descent` — the shape of the
  induction, with no geometry in it.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_square_of_descent` — **Tag 0C5R** over
  `square` and `descent` alone.
* `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupFactorization` and
  `Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_hasExceptionalSquareDichotomyAt` — the
  same with the measure and its descent supplied, so that the step, respectively the input
  square, is the only hypothesis left.

## What is and is not proved

The two clauses of [Stacks, Tag 067L] that the files of this directory carry as
`Stacks.ResolutionOfSurfaces.ConormalSequenceSecondArrow` are discharged in
`ConormalSequenceSecondArrow.lean` of this directory, as
`Stacks.ResolutionOfSurfaces.conormalSequenceSecondArrow`. That the blowup at a closed point of
an integral Noetherian scheme regular of dimension two is again such a scheme — the
globalization of [Stacks, Tag 0AGR] — is
`Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal` of
`FactorizationBirationalMapsDimTwo.lean`.

What remains missing, and is the only mathematical input of the source this library does not
carry, is the nonvanishing of the conormal comparison map of step 3's second alternative, which
no declaration in the library proves; it sits inside
`Stacks.ResolutionOfSurfaces.ExceptionalCurveMapsOntoOver` and hence inside `square`.

**The field data of the two curves sits inside the non-collapsing alternative.**
`Stacks.ResolutionOfSurfaces.HasExceptionalSquareOver` of `FactorizationBirationalSurfaces.lean`
presents both curves over one and the same field `k` outside the dichotomy. That is what the
source's step 3 produces in its second alternative, where the two curves are isomorphic, but it
is unsatisfiable in general: `D'` contains the fibre over `a` and is irreducible and reduced, so
it *is* the exceptional curve of the blowup at `a`, i.e. `𝐏¹_{κ(a)}`, and `Γ(𝐏¹_k) = k` then
forces `k ≅ κ(a)`, while `AlgebraicGeometry.IsContractionOfExceptionalCurve` makes `π` the
blowup at a closed point `x` and forces `k ≅ κ(x)`. The source produces that coincidence only in
the non-collapsing alternative, where `γ` is birational; in the collapsing alternative `κ(x)` is
unrelated to `κ(a)` and nothing needs it, since
`Stacks.ResolutionOfSurfaces.exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve`
consumes only the contraction and the square. So the field, the second curve, its presentation
and the fibre clause are all attached to the non-collapsing alternative alone, in
`Stacks.ResolutionOfSurfaces.ExceptionalCurveMapsOntoOver`, and the collapsing alternative
mentions none of them.

`descent` and `μ` are the bookkeeping for which the source says "some details omitted": that a
factorization of the morphism through the blowup at the chosen point has strictly smaller
measure `μ`, where `μ` is an arbitrary natural-number measure also supplied as an argument.
`FibreCurveMeasure.lean` of this directory defines the source's own measure —
`Stacks.ResolutionOfSurfaces.fibreCurveCount`, the number of curves in the fibres — and proves
its strict drop, which is why the last two theorems need neither.

The declarations of `FactorizationBirationalSurfaces.lean` keep their arguments: they are the
forms the rest of the development was compiled against, and what is here is an addition to them,
not a replacement.

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0C5K](https://stacks.math.columbia.edu/tag/0C5K)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The codimension of the chosen point -/

/-- **The chosen point of [Stacks, Tag 0C5R] has codimension two.** A closed point outside the
maximal open over which a proper birational morphism onto an integral Noetherian scheme regular
of dimension two is an isomorphism has a two-dimensional local ring: on such a scheme a closed
point has a local ring of dimension one or two, and in the first case that local ring is a
discrete valuation ring, so [Stacks, Tag 0BFP] puts the point inside the maximal open. -/
public theorem ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open {A B : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) [IsReduced B] (g : B ⟶ A) [IsProper g]
    (hg : IsBirational g) (U : A.Opens) (hU : IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U)
    {a : A} (ha : IsClosed ({a} : Set A)) (haU : a ∉ U) :
    ringKrullDim (A.presheaf.stalk a) = 2 := by
  have := hA.isIntegral
  have := hA.isNoetherian
  rcases ringKrullDim_stalk_eq_one_or_two hA a ha with hone | htwo
  · refine absurd ?_ haU
    have hco : Order.coheight a = 1 := by
      exact_mod_cast (ringKrullDim_stalk_eq_coheight a).symm.trans hone
    have : IsDiscreteValuationRing (A.presheaf.stalk a) :=
      isDiscreteValuationRing_stalk_of_isRegular hA.isRegular hco
    exact mem_maximal_isomorphism_open_of_isDiscreteValuationRing g hg U hU a
  · exact htwo

/-- **The fibre of the blowup at a closed point lies in its exceptional curve.** The exceptional
ideal is the inverse image of the centre, so its support is the inverse image of the support of
the centre, which is the point itself. -/
public theorem preimage_singleton_subset_range_exceptionalIdeal {A : Scheme.{u}} {a : A}
    (ha : IsClosed ({a} : Set A)) :
    ((pointBlowUpToBase ha) ⁻¹' {a} : Set (pointBlowUp ha)) ⊆
      Set.range (exceptionalIdeal
        (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))).subschemeι.base := by
  intro z hz
  have hsupp : z ∈ ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{a}, ha⟩ : Closeds A))).support : Set (pointBlowUp ha)) := by
    change z ∈ (((Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)).comap
      (pointBlowUpToBase ha)).support : Set (pointBlowUp ha))
    simp only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hz
  rw [← Scheme.IdealSheafData.range_subschemeι] at hsupp
  simpa using hsupp

/-! ### The square the source's steps 2 and 3 produce -/

/-- **The second alternative of step 3 of [Stacks, Tag 0C5R], over a field `k`.** The curve `D`
of the dominating scheme `B'` is not collapsed by `g'`; instead there is an exceptional curve of
the first kind `D' ⊆ pointBlowUp ha` whose points include the whole fibre of the blowup over `a`,
the two curves are presented as `𝐏¹_k` over *one and the same* field `k` by isomorphisms `e` and
`e'`, and `g'` carries `D` to `D'` by a morphism `γ` compatible with the two presentations whose
conormal comparison map is nonzero.

The field lives here, inside this alternative, and nowhere else: it is this alternative that
forces the two curves to be defined over a common field, the source obtaining it from the
birationality of `γ`. -/
public def ExceptionalCurveMapsOntoOver (k : Type u) [Field k] (A B' : Scheme.{u}) (a : A)
    (ha : IsClosed ({a} : Set A)) (D : B'.IdealSheafData) (g' : B' ⟶ pointBlowUp ha) : Prop :=
  ∃ (D' : (pointBlowUp ha).IdealSheafData) (e : projectiveLineProj k ≅ D.subscheme)
      (e' : projectiveLineProj k ≅ D'.subscheme),
    D.IsExceptionalCurveOfFirstKind k e ∧ D'.IsExceptionalCurveOfFirstKind k e' ∧
      ((pointBlowUpToBase ha) ⁻¹' {a} : Set (pointBlowUp ha)) ⊆ Set.range D'.subschemeι.base ∧
        ∃ (γ : D.subscheme ⟶ D'.subscheme) (_ : e.hom ≫ γ = e'.hom)
          (j : D.subscheme ⟶ pointBlowUp ha) (_ : IsImmersion j)
          (hj : γ ≫ D'.subschemeι = j) (h : D.subschemeι ≫ g' = j),
          Stacks.Immersion.immersionConormalSheafMap D.subschemeι D'.subschemeι γ g'
            (Stacks.Immersion.toShHom_square (h.trans hj.symm)) ≠ 0

/-- **The dichotomy of step 3 of [Stacks, Tag 0C5R].** Either `g'` carries the curve `D` to a
single point of the blowup, or the second alternative
`Stacks.ResolutionOfSurfaces.ExceptionalCurveMapsOntoOver` holds over some field.

Note where the quantifier sits: the collapsing alternative mentions no field and no second
curve, because nothing in the collapsing branch needs them —
`Stacks.ResolutionOfSurfaces.exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve`
consumes only the contraction and the commuting square. -/
public def ExceptionalCurveDichotomy (A B' : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A))
    (D : B'.IdealSheafData) (g' : B' ⟶ pointBlowUp ha) : Prop :=
  (∃ w : pointBlowUp ha, ∀ z : D.subscheme, g' (D.subschemeι z) = w) ∨
    ∃ (k : Type u) (fk : Field k), @ExceptionalCurveMapsOntoOver k fk A B' a ha D g'

/-- **The geometric input of steps 2 and 3 of [Stacks, Tag 0C5R] at a closed point `a`.** The
data is: a reduced scheme `B'` dominating `B` by a surjective morphism `π` which contracts an
exceptional curve `D ⊆ B'` to a single point; a proper birational morphism
`g' : B' ⟶ pointBlowUp ha` making the square over the blowup commute; and the dichotomy of the
source's step 3, `Stacks.ResolutionOfSurfaces.ExceptionalCurveDichotomy`.

In the source this is produced by [Stacks, Tag 0C5H], which dominates the rational map from `B`
to the blowup by a chain of blowups at closed points, followed by the reduction of that chain to
its last step. -/
public def HasExceptionalSquareDichotomyAt {A B : Scheme.{u}} (g : B ⟶ A) (a : A)
    (ha : IsClosed ({a} : Set A)) : Prop :=
  ∃ (B' : Scheme.{u}) (_ : IsReduced B') (π : B' ⟶ B) (g' : B' ⟶ pointBlowUp ha)
      (_ : IsProper g'),
    IsBirational g' ∧ g' ≫ pointBlowUpToBase ha = π ≫ g ∧ Function.Surjective π.base ∧
      ∃ D : B'.IdealSheafData,
        IsContractionOfExceptionalCurve D π ∧
          (∃ x : B, ∀ t : D.subscheme, π (D.subschemeι t) = x) ∧
            ExceptionalCurveDichotomy A B' a ha D g'

/-! ### One step of the induction -/

/-- **One step of [Stacks, Tag 0C5R]: the factorization through the blowup at the chosen point.**
Let `g : B ⟶ A` be a proper birational morphism onto a regular Noetherian scheme with reduced
source, let `U` be the maximal open over which `g` is an isomorphism and let `a ∉ U` be a closed
point. If the square of `Stacks.ResolutionOfSurfaces.HasExceptionalSquareDichotomyAt` is
available at `a`, then `g` factors through the blowup of `A` at `a`.

In the collapsing alternative of the dichotomy the factorization is
`Stacks.ResolutionOfSurfaces.exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve`, which
is [Stacks, Tag 0C5J] and reads nothing but the contraction and the commuting square. In the
other alternative
`Stacks.ResolutionOfSurfaces.false_of_exceptionalCurvePair_of_notMem_isomorphismLocus` derives a
contradiction: it would put `a` in `U` against its choice. -/
public theorem exists_comp_eq_pointBlowUpToBase_of_hasExceptionalSquareDichotomyAt
    {A B : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian A] [IsReduced B] (g : B ⟶ A) [IsProper g]
    (hg : IsBirational g) (hA : IsRegular A) (U : A.Opens)
    (hU : IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U) (a : A)
    (ha : IsClosed ({a} : Set A)) (haU : a ∉ U)
    [AlgebraicGeometry.IsNoetherian (pointBlowUp ha)] (hA' : IsRegular (pointBlowUp ha))
    (hdata : HasExceptionalSquareDichotomyAt g a ha) :
    ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g := by
  obtain ⟨B', hred, π, g', hprop, hg', hsq, hπ, D, hcontr, ⟨x, hx⟩, hdich⟩ := hdata
  have : IsReduced B' := hred
  have : IsProper g' := hprop
  rcases hdich with hconst | ⟨k, fk, D', e, e', hE, hE', hbfib, hmaps⟩
  · obtain ⟨ψ, -, hψ⟩ := exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve hcontr g
      (pointBlowUpToBase ha) g' hsq hconst
    exact ⟨ψ, hψ⟩
  · let _ : Field k := fk
    obtain ⟨ψ, -, hψ⟩ := exists_comp_eq_of_exceptionalCurveDichotomy k conormalSequenceSecondArrow
      g hg hA U hU haU (pointBlowUpToBase ha) g' hg' hA' hsq hπ hcontr hE hE' hbfib x hx
      (Or.inr hmaps)
    exact ⟨ψ, hψ⟩

/-- **One step of [Stacks, Tag 0C5R] between integral Noetherian schemes regular of dimension
two**: given the square at every closed point outside the maximal isomorphism open, the morphism
factors through the blowup at that point. -/
private theorem exists_comp_eq_pointBlowUpToBase_of_square
    (square : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          HasExceptionalSquareDichotomyAt g a ha)
    (A B : Scheme.{u}) (g : B ⟶ A) (hA : IsIntegralRegularSurface A)
    (hB : IsIntegralRegularSurface B) (hp : IsProper g) (hb : IsBirational g) (hiso : ¬ IsIso g)
    (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens)
    (hU : IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U) (haU : a ∉ U) :
    ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g := by
  have : AlgebraicGeometry.IsNoetherian A := hA.isNoetherian
  have : AlgebraicGeometry.IsIntegral B := hB.isIntegral
  have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA
  have : AlgebraicGeometry.IsNoetherian (pointBlowUp ha) := hA'.isNoetherian
  exact exists_comp_eq_pointBlowUpToBase_of_hasExceptionalSquareDichotomyAt g hb hA.isRegular U hU
    a ha haU hA'.isRegular (square A B g hA hB hp hb hiso a ha U hU haU)

/-! ### The induction -/

/-- **The induction of [Stacks, Tag 0C5R] on the number of curves in the fibres**, granted its
step in the bare form the induction reads: at a closed point outside the maximal isomorphism open
the morphism factors through the blowup at that point.

This is the shape of the induction, with no geometry in it: `step` is consumed only to produce the
factorization `ψ`, and `descent` only to see the measure drop. The geometric input of the source's
steps 2 and 3 enters through the `step` arguments of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_square_of_descent` and
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupFactorization`. -/
public theorem factorsAsPointBlowups_of_step_of_descent
    (μ : ∀ (A B : Scheme.{u}), (B ⟶ A) → ℕ)
    (step : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g)
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
      FactorsAsPointBlowups A Set.univ B g by
    exact H (μ Y X f) Y X f hY hX hproper hbirational rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
    intro A B g hA hB hp hb hm
    by_cases hiso : IsIso g
    · exact @FactorsAsPointBlowups.of_isIso B A Set.univ g hiso
    · have : AlgebraicGeometry.IsNoetherian A := hA.isNoetherian
      have : AlgebraicGeometry.IsIntegral A := hA.isIntegral
      have : AlgebraicGeometry.IsIntegral B := hB.isIntegral
      obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open g
      obtain ⟨a, ha, haU⟩ := exists_isClosed_singleton_notMem_isomorphism_open g U hU hiso
      have hLN : IsLocallyNoetherian A := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
      have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
        isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA
      have : AlgebraicGeometry.IsNoetherian (pointBlowUp ha) := hA'.isNoetherian
      obtain ⟨ψ, hψ⟩ := step A B g hA hB hp hb hiso a ha U hU haU
      have hlt := descent A B g hA hB hp hb hiso a ha U hU haU ψ hψ
      exact factorsAsPointBlowups_of_comp_blowUpToBase a ha hψ
        (ih (μ _ B ψ) (hm ▸ hlt) _ B ψ hA' hB (isProper_of_comp_pointBlowUpToBase ha hp ψ hψ)
          (isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hb ψ hψ) rfl)

/-- **Stacks Project, Tag 0C5R**, with the `hsec` and `blowUpSurface` inputs of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_proper_birational` discharged. Let
`f : X ⟶ Y` be a proper birational morphism between integral Noetherian schemes regular of
dimension two. Then `f` is a sequence of blowups in closed points, that is, `f` is up to an
isomorphism of its source the composite of a chain of blowups at closed points.

One input is an argument rather than a theorem: `square`, the reduction of [Stacks, Tag 0C5H] to
a single blowup together with the dichotomy of the source's step 3, in the shape
`Stacks.ResolutionOfSurfaces.HasExceptionalSquareDichotomyAt`. The remaining argument `descent`
is the strict drop of the measure `μ`, the bookkeeping the source omits. Neither is
inter-derivable with the conclusion; see the module documentation. -/
public theorem factorsAsPointBlowups_of_square_of_descent
    (μ : ∀ (A B : Scheme.{u}), (B ⟶ A) → ℕ)
    (square : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          HasExceptionalSquareDichotomyAt g a ha)
    (descent : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          ∀ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g →
            μ (pointBlowUp ha) B ψ < μ A B g)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsIntegralRegularSurface Y)
    (hX : IsIntegralRegularSurface X) (hproper : IsProper f) (hbirational : IsBirational f) :
    FactorsAsPointBlowups Y Set.univ X f := by
  exact factorsAsPointBlowups_of_step_of_descent μ
    (exists_comp_eq_pointBlowUpToBase_of_square square) descent f hY hX hproper hbirational

/-! ### The measure and its descent, supplied -/

/-- **[Stacks, Tag 0C5R] with the measure and its descent supplied.** A proper birational
morphism between integral Noetherian schemes regular of dimension two is a sequence of blowups at
closed points, granted only the source's one-blowup step: at a closed point outside the maximal
isomorphism open the morphism factors through the blowup at that point.

The measure is `Stacks.ResolutionOfSurfaces.fibreCurveCount`, the number of curves in the fibres
— the source's own measure — and its strict drop is
`Stacks.ResolutionOfSurfaces.fibreCurveCount_lt_of_comp_eq_blowUpToBase_vanishingIdeal`, whose
hypotheses the loop of
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_step_of_descent` provides: the
two-dimensionality of the local ring at the chosen point is
`Stacks.ResolutionOfSurfaces.ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open`, and properness
and birationality of the factorization are
`Stacks.ResolutionOfSurfaces.isProper_of_comp_pointBlowUpToBase` and
`Stacks.ResolutionOfSurfaces.isBirational_of_comp_pointBlowUpToBase`. So `descent` is no longer an
assumption of the theorem.

The bare step itself, rather than the square, is the hypothesis here because that is what
`ExceptionalSquareChain.lean` proves from the dichotomy of the source's step 3 alone, 0C5H and the
chain induction being discharged there. -/
public theorem factorsAsPointBlowups_of_pointBlowupFactorization
    (step : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsIntegralRegularSurface Y)
    (hX : IsIntegralRegularSurface X) (hproper : IsProper f) (hbirational : IsBirational f) :
    FactorsAsPointBlowups Y Set.univ X f := by
  refine factorsAsPointBlowups_of_step_of_descent fibreCurveCount step ?_ f hY hX hproper
    hbirational
  intro A B g hA hB hp hb _ a ha U hU haU ψ hψ
  have := hA.isIntegral
  have := hB.isIntegral
  have := hA.isNoetherian
  exact fibreCurveCount_lt_of_comp_eq_blowUpToBase_vanishingIdeal g hA hB hp hb ha
    (ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open hA g hb U hU ha haU)
    (isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA) ψ
    (isProper_of_comp_pointBlowUpToBase ha hp ψ hψ)
    (isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hb ψ hψ) hψ

/-- **[Stacks, Tag 0C5R] with the measure, its descent and the chain of step 2 supplied**, so that
the input square of the source's steps 2 and 3 is the only assumption left. -/
public theorem factorsAsPointBlowups_of_hasExceptionalSquareDichotomyAt
    (square : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g → ¬ IsIso g →
      ∀ (a : A) (ha : IsClosed ({a} : Set A)) (U : A.Opens),
        IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U →
          HasExceptionalSquareDichotomyAt g a ha)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsIntegralRegularSurface Y)
    (hX : IsIntegralRegularSurface X) (hproper : IsProper f) (hbirational : IsBirational f) :
    FactorsAsPointBlowups Y Set.univ X f := by
  exact factorsAsPointBlowups_of_pointBlowupFactorization
    (exists_comp_eq_pointBlowUpToBase_of_square square) f hY hX hproper hbirational

end Stacks.ResolutionOfSurfaces

end
