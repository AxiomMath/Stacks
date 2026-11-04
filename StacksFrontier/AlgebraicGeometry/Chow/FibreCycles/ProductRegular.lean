module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.SectionRange
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProper
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSmooth
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularSmooth

/-!
# The family of projective lines over a nonsingular variety is regular

Tag 0B07 is a statement about a nonsingular variety `X` over an algebraically closed field and a
closed subvariety of `X × ℙ¹`. The Section 43.14 intersection product it uses is formed on a
regular ambient scheme, so the clause needs the ambient `X × ℙ¹` to be regular. That is not an
extra assumption: `ℙ¹` is smooth over its base, so `X ×_S ℙ¹_S ⟶ X` is smooth, hence
`X ×_S ℙ¹_S` is smooth over the ground field, hence regular.

## Main results

* `Stacks.Chow.smooth_relativeProjectiveLine_over`: the relative projective line is smooth over
  its base, for an arbitrary base scheme.
* `Stacks.Chow.smooth_projectiveLineProduct_fst`: the family `X ×_S ℙ¹_S` is smooth over `X`.
* `Stacks.Chow.isRegular_projectiveLineProduct`: **`X ×_S ℙ¹_S` is regular when `X` is a regular
  scheme locally of finite type over a perfect field.** This is the hypothesis `hY` of the Tag
  0B07 statements, derived from nonsingularity of `X`.
* `Stacks.Chow.isRegular_projectiveLineProduct_of_eq`: the same with the base presented by an
  equality `S = Spec Kf`, which is the shape a Chow situation offers.

## Implementation notes

The relative projective line is the base change of `ℙ¹_ℤ` along the terminal morphism, so
smoothness over the base is smoothness of `terminal.from ℙ¹_ℤ` together with stability of
smoothness under base change; the terminal morphism is handled exactly as in
`AlgebraicGeometry.isProper_terminalFrom_projectiveLine`, through
`AlgebraicGeometry.isIso_terminalFrom_specULiftZ`: an isomorphism is an open immersion and
therefore smooth.

Regularity of the product is then not obtained from regularity of the two factors — which would
need `ℙ¹` to be identified as a regular scheme — but directly: over a perfect field a regular
scheme locally of finite type is smooth (`smooth_of_isRegular_over_perfectField`), the first
projection of the product is the base change of the structure morphism of `ℙ¹_S`, and a composite
of smooth morphisms is smooth, so Tag 056S applies to the structure morphism of the product.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- The projective line over the integers is smooth over the terminal scheme. -/
theorem smooth_terminalFrom_projectiveLine :
    Smooth (terminal.from (projectiveLine (ULift.{u} ℤ))) := by
  rw [← terminal.comp_from (projectiveLine (ULift.{u} ℤ) ↘ Spec (.of (ULift.{u} ℤ)))]
  have := projectiveLine_smooth (ULift.{u} ℤ)
  have := isIso_terminalFrom_specULiftZ.{u}
  infer_instance

/-- **The relative projective line is smooth over its base.** It is the base change of `ℙ¹_ℤ`
along the terminal morphism of the base. -/
instance smooth_relativeProjectiveLine_over (S : Scheme.{u}) :
    Smooth (relativeProjectiveLine S ↘ S) := by
  rw [relativeProjectiveLine_over_hom]
  have := smooth_terminalFrom_projectiveLine.{u}
  infer_instance

/-- **The family `X ×_S ℙ¹_S` is smooth over `X`.** The first projection is the base change of
the structure morphism of `ℙ¹_S`. -/
instance smooth_projectiveLineProduct_fst {X S : Scheme.{u}} (f : X ⟶ S) :
    Smooth (pullback.fst f (relativeProjectiveLine S ↘ S)) :=
  inferInstance

/-- **The family of projective lines over a nonsingular variety is regular.** If `X` is a regular
scheme locally of finite type over a perfect field, then `X ×_S ℙ¹_S` is regular.

This is the hypothesis `hY` of the Tag 0B07 statements of
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalence`, derived
from nonsingularity of `X`: the source's hypothesis on `X` already forces it. -/
theorem isRegular_projectiveLineProduct {Kf : Type u} [Field Kf] [PerfectField Kf]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of Kf)) [LocallyOfFiniteType p] (hX : IsRegular X) :
    IsRegular (projectiveLineProduct p) :=
  have : Smooth p := smooth_of_isRegular_over_perfectField p hX
  isRegular_of_smooth_over_field
    (pullback.fst p (relativeProjectiveLine (Spec (.of Kf)) ↘ Spec (.of Kf)) ≫ p)

/-- **The family of projective lines over a nonsingular variety is regular**, for a base scheme
presented as the spectrum of a perfect field by an equality rather than by its type. This is the
form the Tag 0B07 statements consume, their base being the `C.S` of a Chow situation together
with `hS : C.S = Spec Kf`. -/
theorem isRegular_projectiveLineProduct_of_eq {Kf : Type u} [Field Kf] [PerfectField Kf]
    {X S : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p]
    (hS : S = Spec (.of Kf)) (hX : IsRegular X) :
    IsRegular (projectiveLineProduct p) := by
  subst hS
  exact isRegular_projectiveLineProduct p hX

end Stacks.Chow

end
