module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpaceDifferentialsVanishing

/-!
# Unramifiedness and the vanishing of `Ω_{X/Y}`: Stacks 04GA

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`.
Stacks 04GA asserts the equivalence of

1. `f` is unramified,
2. `f` is locally of finite type and `Ω_{X/Y} = 0`,
3. `f` is locally of finite type and `f` is formally unramified.

The equivalence of (1) and (3) is
`AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified` in
`StacksFrontier/AlgebraicGeometry/Spaces/FormallyUnramifiedEtaleDescent.lean`.  The passage between
(2) and (3) is Stacks 04G9, the equivalence of formal unramifiedness with `Ω_{X/Y} = 0`, which is
`AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials'`: its forward
direction is `AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified`, and its
backward direction rests on the chart comparison
`AlgebraicGeometry.Space.sheafOfDifferentialsChartComparisonMp` of
`StacksFrontier/AlgebraicGeometry/Spaces/SchemeSpaceDifferentialsVanishing.lean`.

## Main results

* `AlgebraicGeometry.Space.isUnramified_tfae_sheafOfDifferentials`: **Stacks 04GA**, the three
  conditions are equivalent.
* `AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_isZero_sheafOfDifferentials`:
  the equivalence of conditions (1) and (2).
* `Space.isLocallyOfFiniteType_and_isZero_sheafOfDifferentials_of_formallyUnramified`
  and `Space.isLocallyOfFiniteType_and_isZero_sheafOfDifferentials_of_isUnramified`:
  the implications (3) ⟹ (2) and (1) ⟹ (2), which need only the forward direction of 04G9.

## References

* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
* [Stacks Project, Tag 04G9](https://stacks.math.columbia.edu/tag/04G9), the equivalence of
  formal unramifiedness with the vanishing of `Ω_{X/Y}`.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  small Zariski and small étale differentials of a morphism of schemes.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- **Condition (3) of Stacks 04GA implies condition (2).**  A morphism `f : X ⟶ Y` of algebraic
spaces over `S` which is locally of finite type and formally unramified is locally of finite
type and has a vanishing sheaf of differentials `Ω_{X/Y}`.

The second conjunct is the forward direction of Stacks 04G9,
`AlgebraicGeometry.Space.isZero_sheafOfDifferentials_of_formallyUnramified`, which carries no
assumed input; the first is carried through unchanged. -/
theorem isLocallyOfFiniteType_and_isZero_sheafOfDifferentials_of_formallyUnramified (f : X ⟶ Y)
    (h : IsLocallyOfFiniteType B S hS f.hom ∧ FormallyUnramified f.hom) :
    IsLocallyOfFiniteType B S hS f.hom ∧ IsZero (sheafOfDifferentials B S hS f) :=
  ⟨h.1, isZero_sheafOfDifferentials_of_formallyUnramified B S hS f h.2⟩

/-- **Condition (1) of Stacks 04GA implies condition (2).**  An unramified morphism `f : X ⟶ Y` of
algebraic spaces over `S` is locally of finite type and has a vanishing sheaf of differentials
`Ω_{X/Y}`.

Unramifiedness splits into local finite type and formal unramifiedness by the equivalence
of conditions (1) and (3),
`AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified`, and
`Space.isLocallyOfFiniteType_and_isZero_sheafOfDifferentials_of_formallyUnramified`
turns that into condition (2). -/
theorem isLocallyOfFiniteType_and_isZero_sheafOfDifferentials_of_isUnramified (f : X ⟶ Y)
    (h : IsUnramified B S hS f.hom) :
    IsLocallyOfFiniteType B S hS f.hom ∧ IsZero (sheafOfDifferentials B S hS f) :=
  isLocallyOfFiniteType_and_isZero_sheafOfDifferentials_of_formallyUnramified B S hS f
    ((isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified B S hS X.2 Y.2 f.hom).mp h)

/-- **The equivalence of conditions (1) and (2) of Stacks 04GA.**  A morphism `f : X ⟶ Y` of
algebraic spaces over `S` is unramified exactly when it is locally of finite type and
`Ω_{X/Y} = 0`: unramifiedness is local finite type plus formal unramifiedness by
`AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified`, and
formal unramifiedness is `Ω_{X/Y} = 0` by Stacks 04G9,
`AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials'`. -/
theorem isUnramified_iff_isLocallyOfFiniteType_and_isZero_sheafOfDifferentials (f : X ⟶ Y) :
    IsUnramified B S hS f.hom ↔
      (IsLocallyOfFiniteType B S hS f.hom ∧ IsZero (sheafOfDifferentials B S hS f)) := by
  rw [isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified B S hS X.2 Y.2 f.hom]
  exact and_congr_right fun _ => formallyUnramified_iff_isZero_sheafOfDifferentials' B S hS f

/-- **Stacks 04GA.**  For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the
following are equivalent:

1. `f` is unramified,
2. `f` is locally of finite type and `Ω_{X/Y} = 0`,
3. `f` is locally of finite type and formally unramified.

(1) ⟺ (3) is
`AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified`, and
(1) ⟺ (2) is
`AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_isZero_sheafOfDifferentials`.
-/
@[stacks 04GA]
theorem isUnramified_tfae_sheafOfDifferentials (f : X ⟶ Y) :
    List.TFAE [IsUnramified B S hS f.hom,
      IsLocallyOfFiniteType B S hS f.hom ∧ IsZero (sheafOfDifferentials B S hS f),
      IsLocallyOfFiniteType B S hS f.hom ∧ FormallyUnramified f.hom] := by
  tfae_have 1 ↔ 2 :=
    isUnramified_iff_isLocallyOfFiniteType_and_isZero_sheafOfDifferentials B S hS f
  tfae_have 1 ↔ 3 :=
    isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramified B S hS X.2 Y.2 f.hom
  tfae_finish

end AlgebraicGeometry.Space

end
