module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionSquare
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Transition isomorphisms along chart squares

A *chart square* (`AlgebraicGeometry.Scheme.Hom.ChartSquare`) from `f : X ⟶ S` to
`f' : X' ⟶ S'` is a commutative square `g' ≫ f = f' ≫ g` whose gap map
`X' ⟶ X ×_S S'` is étale. Every chart square is the pasting of the cartesian square of
`X ×_S S' ⟶ S'` over `g` and of the square of the étale gap map over the identity of `S'`
(`AlgebraicGeometry.Scheme.Hom.ChartSquare.gap_comp_fst`).

Cartesian squares have transition isomorphisms
(`AlgebraicGeometry.Scheme.Hom.hasRelDualizingTransition_of_isPullback`) and transition
isomorphisms paste (`AlgebraicGeometry.Scheme.Hom.HasRelDualizingTransition.comp`); so a chart
square has a transition isomorphism as soon as its étale gap square does
(`AlgebraicGeometry.Scheme.Hom.ChartSquare.hasRelDualizingTransition_of_gap`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S X' S' : Scheme.{u}}

/-- **A chart square** from `f : X ⟶ S` to `f' : X' ⟶ S'`: morphisms `g' : X' ⟶ X` and
`g : S' ⟶ S` with `g' ≫ f = f' ≫ g` such that the induced `X' ⟶ X ×_S S'` is étale. These are
the squares between étale charts of an algebraic space over `S` and of its base changes. -/
structure ChartSquare (f : X ⟶ S) (f' : X' ⟶ S') where
  /-- The map of total spaces. -/
  g' : X' ⟶ X
  /-- The map of bases. -/
  g : S' ⟶ S
  /-- The square commutes. -/
  comm : g' ≫ f = f' ≫ g
  /-- The gap map `X' ⟶ X ×_S S'` is étale. -/
  etale_gap : Etale (pullback.lift g' f' comm)

namespace ChartSquare

variable {f : X ⟶ S} {f' : X' ⟶ S'} (sq : ChartSquare f f')

/-- The étale gap map `X' ⟶ X ×_S S'`. -/
abbrev gap : X' ⟶ pullback f sq.g := pullback.lift sq.g' f' sq.comm

/-- The gap map of a chart square is étale. -/
instance : Etale sq.gap := sq.etale_gap

/-- The gap map followed by the first projection is `g'`. -/
theorem gap_comp_fst : sq.gap ≫ pullback.fst f sq.g = sq.g' := pullback.lift_fst _ _ _

/-- The gap map followed by the second projection is `f'`. -/
theorem gap_comp_snd : sq.gap ≫ pullback.snd f sq.g = f' := pullback.lift_snd _ _ _

/-- The gap map over the identity of `S'`. -/
theorem gap_comm : sq.gap ≫ pullback.snd f sq.g = f' ≫ 𝟙 S' := by
  rw [gap_comp_snd, Category.comp_id]

variable [Flat f] [LocallyOfFinitePresentation f] [Flat f'] [LocallyOfFinitePresentation f']

/-- **A chart square has a transition isomorphism as soon as its étale gap square does**: it
is the pasting of the gap square over `𝟙_{S'}` and of the cartesian square of
`X ×_S S' ⟶ S'`. -/
theorem hasRelDualizingTransition_of_gap
    (h : HasRelDualizingTransition sq.gap (𝟙 S') sq.gap_comm) :
    HasRelDualizingTransition sq.g' sq.g sq.comm := by
  have hc := (hasRelDualizingTransition_of_isPullback
    (IsPullback.of_hasPullback f sq.g)).comp h
  exact hc.congr sq.gap_comp_fst (Category.id_comp _) sq.comm

/-- **The transition isomorphism of a chart square** `L(g')^*ω^•_{X/S} ≅ ω^•_{X'/S'}`, given a
transition for its étale gap square. -/
def relDualizingTransition (h : HasRelDualizingTransition sq.gap (𝟙 S') sq.gap_comm) :
    DiagonalOpen.baseChangeComplex sq.g' (relDualizingComplex f) ≅ relDualizingComplex f' :=
  Scheme.Hom.relDualizingTransition sq.g' sq.g sq.comm (sq.hasRelDualizingTransition_of_gap h)

/-- The transition isomorphism of a chart square is characterised by the transition relation. -/
theorem relDualizingTransition_eq (h : HasRelDualizingTransition sq.gap (𝟙 S') sq.gap_comm)
    {α : DiagonalOpen.baseChangeComplex sq.g' (relDualizingComplex f) ≅ relDualizingComplex f'}
    (hα : IsRelDualizingTransition sq.g' sq.g sq.comm α) : sq.relDualizingTransition h = α :=
  Scheme.Hom.relDualizingTransition_eq _ hα

end ChartSquare

end AlgebraicGeometry.Scheme.Hom

end
