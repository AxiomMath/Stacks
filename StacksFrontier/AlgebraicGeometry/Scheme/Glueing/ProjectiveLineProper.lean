module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineFiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSeparated
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineUniversallyClosed

/-!
# Properness of the projective line

The structure morphism `ℙ¹_k ⟶ Spec k` of the two-chart gluing of Tag 01JE is separated and
universally closed; this file supplies the remaining ingredient, that it is locally of finite
type, and assembles the three into properness. On either affine chart the structure morphism is
`Spec k[X] ⟶ Spec k`, induced by `Polynomial.C = algebraMap k k[X]`, which is of finite type;
since being locally of finite type is Zariski-local on the source, the glued morphism inherits
the property from the two charts.

Over the integers the base `Spec (ULift ℤ)` is a terminal scheme, so `ℙ¹_ℤ ⟶ ⊤_ Scheme` is
proper as well, and properness is stable under base change, so the relative projective line
`ℙ¹_S = S ×_{⊤} ℙ¹_ℤ` is proper over every base `S`, and `X ×_S ℙ¹_S` is proper over `X`.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_projectiveLineAffineStructureMorphism`: the affine
  chart `Spec k[X] ⟶ Spec k` is locally of finite type.
* `AlgebraicGeometry.projectiveLine_locallyOfFiniteType`: the structure morphism of `ℙ¹_k` is
  locally of finite type.
* `AlgebraicGeometry.projectiveLine_isProper`: the structure morphism of `ℙ¹_k` is proper, for an
  arbitrary commutative ring `k`.
* `AlgebraicGeometry.isProper_terminalFrom_projectiveLine`: `ℙ¹_ℤ` is proper over the terminal
  scheme.
* `AlgebraicGeometry.isProper_pullback_fst_terminalFrom_projectiveLine`: the relative projective
  line is proper over its base.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]




/-- The terminal morphism of `Spec (ULift ℤ)` is an isomorphism, since that scheme is itself
terminal. -/
theorem isIso_terminalFrom_specULiftZ : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) := by
  have h := (terminalIsTerminal.uniqueUpToIso
    (AlgebraicGeometry.specULiftZIsTerminal.{u})).isIso_inv
  convert h using 1
  exact Subsingleton.elim _ _

/-- The projective line over the integers is proper over the terminal scheme. -/
theorem isProper_terminalFrom_projectiveLine :
    IsProper (terminal.from (projectiveLine (ULift.{u} ℤ))) := by
  rw [← terminal.comp_from (projectiveLine (ULift.{u} ℤ) ↘ Spec (.of (ULift.{u} ℤ)))]
  have := projectiveLine_isProper (ULift.{u} ℤ)
  have := isIso_terminalFrom_specULiftZ.{u}
  have : MorphismProperty.ContainsIdentities (@IsProper) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have : IsProper (terminal.from (Spec (.of (ULift.{u} ℤ)))) :=
    MorphismProperty.of_isIso @IsProper _
  infer_instance

/-- The relative projective line is proper over its base: the first projection of
`pullback (terminal.from S) (terminal.from (projectiveLine (ULift ℤ)))` is proper. For the
relative projective line of Tag 02S5 this is, by definition, its structure morphism. -/
instance isProper_pullback_fst_terminalFrom_projectiveLine (S : Scheme.{u}) :
    IsProper (pullback.fst (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ)))) :=
  have := isProper_terminalFrom_projectiveLine.{u}
  inferInstance

end AlgebraicGeometry

end

end
