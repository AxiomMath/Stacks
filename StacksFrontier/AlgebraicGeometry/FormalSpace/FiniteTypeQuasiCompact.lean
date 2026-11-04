module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism

/-!
# Finite type morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AM4, part (2)** says that a
morphism `f : X ⟶ Y` of formal algebraic spaces over `S` is *of finite type* when it is
locally of finite type — part (1) of the same definition, representability by algebraic spaces
together with the Bootstrap condition of Stacks 03XZ for being locally of finite type — and
quasi-compact in the sense of Definition 0AJC.

**Stacks 0AJJ** says that being of finite type is equivalent to representability by algebraic
spaces together with being of finite type in the Bootstrap sense of Stacks 03XZ, that is, to
`AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType`. The source's proof runs through Lemma
0AM2, the agreement of Definition 0AJC with the Bootstrap notion of quasi-compactness for a
morphism representable by algebraic spaces; both are proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismComparison`, which is where the
equivalence of the conditions of Stacks 0AJ9 they rest on is available.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsFiniteType`: **Stacks 0AM4**, part (2), which is condition
  (1) of **Stacks 0AJJ**.

## Main results

* `AlgebraicGeometry.FormalSpace.IsFiniteType.of_isPullback`: **Stacks 0AQ5**, the global
  half.

## Implementation notes

Neither of the two conditions uses the witnesses that the source and the target are formal
algebraic spaces — the Bootstrap condition of Stacks 03XZ does not, and neither does
Definition 0AJC as `AlgebraicGeometry.FormalSpace.IsQuasiCompact` spells it out — so both are
stated, here and in `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType`, for an arbitrary
morphism of fppf sheaves on the big fppf site of `S`.

The definition is placed in this file rather than beside Definition 0AM4, part (1), in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType`, because it needs Definition 0AJC,
which lives in `StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism`; that file
imports the reduction and closed immersion theories, which part (1) does not need.

Stacks 0AJJ itself is not proved here but in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismComparison`,
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`: it is proved exactly as
the source proves it, through Stacks 0AM2, and Stacks 0AM2 rests on the equivalence of the
conditions of Stacks 0AJ9, which is further down the import order than this file.

Base change, the global half of Stacks 0AQ5, needs no hypothesis: it is the conjunction
of `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isPullback` with
`AlgebraicGeometry.FormalSpace.IsQuasiCompact.of_isPullback`. Composition, the global half of
Stacks 0AQ4, does not follow this way: a fibre product of `f ≫ g` with an affine scheme over
the target of `g` is a fibre product of `f` with a fibre product of `g`, which is a
quasi-compact formal algebraic space and not a scheme, so proving Definition 0AJC for the
composite directly needs more of Stacks 0AJB than this library has. It is proved for
condition (2) of Stacks 0AJJ instead, as
`AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType.comp`, from which Stacks 0AJJ carries it
to Definition 0AM4, part (2), unconditionally.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AJJ](https://stacks.math.columbia.edu/tag/0AJJ)
* [Stacks Project, Tag 0AM2](https://stacks.math.columbia.edu/tag/0AM2)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AM4, part (2)**, which is **Stacks 0AJJ, condition (1)**. A morphism of formal
algebraic spaces over `S` is *of finite type* when it is locally of finite type, in the sense
of Definition 0AM4, part (1), and quasi-compact, in the sense of Definition 0AJC. The
condition makes sense, and is stated, for an arbitrary morphism of fppf sheaves on the big
fppf site of `S`. -/
@[stacks 0AM4 "part (2): finite type", stacks 0AJJ "condition (1): of finite type",
  ega "I 10.13.3" "representable morphisms"]
abbrev IsFiniteType' {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  IsLocallyOfFiniteType B S hS f ∧ IsQuasiCompact B S hS f

/-- **Stacks 0AQ5, the global half.** A base change of a morphism of formal algebraic spaces
over `S` which is of finite type is of finite type: both halves of the condition are stable
under base change. -/
@[stacks 0AQ5 "finite type"]
theorem IsFiniteType.of_isPullback' {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsFiniteType' B S hS f) :
    IsFiniteType' B S hS p :=
  ⟨IsLocallyOfFiniteType.of_isPullback B S hS sq hf.1,
    IsQuasiCompact.of_isPullback B S hS sq hf.2⟩

end AlgebraicGeometry.FormalSpace

end
