module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactMonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints

/-!
# The six conditions of Stacks 03JV on a point of an algebraic space

Stacks 03JV lists six conditions on a point `x` of an algebraic space `X` over a scheme `S`
and asserts that they are equivalent. Condition (4), the one which Stacks 03I8 turns into the
definition of a decent algebraic space, is
`AlgebraicGeometry.Space.HasQuasiCompactMonomorphicFieldRepresentative`. This file states the
other five, together with the three implications between them that the source calls immediate or
clear.

## Main definitions

* `AlgebraicGeometry.Space.HasFiniteFibresOnEveryAffineEtaleChart` is condition (1):
  for every affine `U` and every étale `U ⟶ X`, the fibres over `x` of `|U| → |X|` and of
  `|R| → |X|`, where `R = U ×_X U`, are both finite.
* `AlgebraicGeometry.Space.HasFiniteFibresOnSomeEtaleCover` is condition (2): the same
  finiteness for the members of one étale covering family.
* `AlgebraicGeometry.Space.HasMonomorphicFieldRepresentativeWithFiniteCharts` is
  condition (3): a monomorphic field-valued representative whose base change to every affine
  étale chart is a finite scheme over the field.
* `AlgebraicGeometry.Space.HasQuasiCompactFieldRepresentative` is condition (5) and
  `AlgebraicGeometry.Space.EveryFieldRepresentativeIsQuasiCompact` is condition (6).
* `AlgebraicGeometry.Space.chartFibre` and `AlgebraicGeometry.Space.relationFibre`: the fibres
  of `|U| → |X|` and of `|R| → |X|` above `x`, in terms of which conditions (1) and (2) are
  stated.

## Main results

* `HasQuasiCompactMonomorphicFieldRepresentative.hasQuasiCompactFieldRepresentative`:
  condition (4) implies condition (5), which the source calls immediate.
* `EveryFieldRepresentativeIsQuasiCompact.hasQuasiCompactFieldRepresentative`: condition (6)
  implies condition (5), which the source calls clear; the content is that a point of `|X|`
  is by construction the class of *some* field-valued point.
* `HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteRelationFiber`: condition (1) bounds the
  relation fibres of Stacks 03JU above any pair of points of an affine étale chart over `x`.

## Implementation notes

The six conditions are separate `def`s, as condition (4) already is. The equivalence of the six
conditions, which is what Tag 03JV asserts, is not proved here; the three theorems are exactly the
three implications the source itself calls immediate or clear.

`|R| → |X|` is the composite of either projection of the presheaf pullback `h_U ×_X h_U` with
the chart, the two composites being equal by `CategoryTheory.Limits.pullback.condition`; the
first projection is used. No separate model of the relation is needed, since the points of a
presheaf pullback are already the points of the relation.

Condition (2) renders the source's "`∐ U_i → X` is surjective" as
`AlgebraicGeometry.Space.IsSurjective` — Stacks 03ME, surjectivity on the point sets of
Tag 03BU — applied to the `CategoryTheory.Limits.Sigma.desc` of the family. This departs from
the source in two ways. First, the coproduct is taken
in the presheaf category and not in schemes; the two agree for this purpose, because a
section of a presheaf coproduct over an object of the site lies in exactly one summand, so
the maps `|U_i| → |∐ h_{U_i}|` are jointly surjective and surjectivity of the descended map
is equivalent to joint surjectivity of the family on points, which is in turn what
surjectivity of the scheme-level `∐ U_i → X` says. Second, the index type is required to
live in the working universe, which the presheaf coproduct needs; this makes the existential
of condition (2) formally *stronger* than the source's, and is harmless here only because
the covering families Tag 03FX produces for an algebraic space are indexed by a type of that
universe. The source's `U_i` are schemes and are not required to be affine, so no affineness
hypothesis appears in condition (2).

In condition (3) "the fibre product `Spec(k) ×_X U` is a finite scheme over `k`" is
`AlgebraicGeometry.Space.IsFinite` of Tag 03ZP applied to the first projection of the
presheaf pullback. Both sides of that projection are representable — `U` is a scheme and the
base change of an étale chart along `Spec(k) ⟶ X` is one — so Tag 03ZP's affine-local
condition on it is finiteness of the corresponding morphism of schemes.

## References

* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The two fibres above a point -/

/-- The fibre of `|U| → |F|` above a point `x` of `|F|`, for a chart `φ : h_U ⟶ F`. -/
abbrev chartFibre {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ F) (x : points B S hS F) :
    Set (points B S hS (yoneda.obj U)) :=
  {a | pointsMap B S hS (yoneda.obj U) φ a = x}

/-- The fibre of `|R| → |F|` above a point `x` of `|F|`, where `R = h_U ×_F h_U` is the
relation attached to a chart `φ : h_U ⟶ F` and `|R| → |F|` is the composite of the first
projection with `φ`. -/
abbrev relationFibre {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ F) (x : points B S hS F) :
    Set (points B S hS (pullback φ φ)) :=
  {r | pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) r = x}

/-! ### Conditions (1) and (2): finite fibres on charts -/

/-- **Stacks 03JV, condition (1).** For every affine scheme `U` and every étale morphism
`φ : h_U ⟶ F`, setting `R = h_U ×_F h_U`, the fibres of `|U| → |F|` and of `|R| → |F|`
above `x` are both finite. -/
@[stacks 03JV "part (1)"]
def HasFiniteFibresOnEveryAffineEtaleChart (x : points B S hS F) : Prop :=
  ∀ U : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ φ : yoneda.obj U ⟶ F, IsEtale B S hS φ →
      (chartFibre B S hS F φ x).Finite ∧ (relationFibre B S hS F φ x).Finite

/-- **Stacks 03JV, condition (2).** There is a family of étale morphisms `φ i : h_{U i} ⟶ F`
whose coproduct is surjective on points and for which, setting `R i = h_{U i} ×_F h_{U i}`,
the fibres of `|U i| → |F|` and of `|R i| → |F|` above `x` are all finite. -/
@[stacks 03JV "part (2)"]
def HasFiniteFibresOnSomeEtaleCover (x : points B S hS F) : Prop :=
  ∃ (I : Type u) (U : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (U i) ⟶ F),
    (∀ i, IsEtale B S hS (φ i)) ∧
    IsSurjective B S hS (Sigma.desc φ) ∧
    ∀ i, (chartFibre B S hS F (φ i) x).Finite ∧ (relationFibre B S hS F (φ i) x).Finite

/-! ### Condition (3): a monomorphic representative with finite charts -/

/-- **Stacks 03JV, condition (3).** Some field-valued representative of `x` presents it by a
monomorphism `Spec(k) ⟶ F` whose base change along every étale chart of `F` with affine
source is a finite scheme over `k`. -/
@[stacks 03JV "part (3)"]
def HasMonomorphicFieldRepresentativeWithFiniteCharts (x : points B S hS F) : Prop :=
  ∃ p : FieldValuedPoint B S hS F,
    p.class B S hS F = x ∧
    Mono (fieldMorphism B S hS F p) ∧
    ∀ U : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ φ : yoneda.obj U ⟶ F, IsEtale B S hS φ →
        IsFinite B S hS (pullback.fst (fieldMorphism B S hS F p) φ)

/-! ### Conditions (5) and (6): quasi-compact field-valued representatives -/

/-- **Stacks 03JV, condition (5).** Some field-valued point in the class of `x` presents it
by a quasi-compact morphism, the monomorphism condition of condition (4) being dropped. -/
@[stacks 03JV "part (5)"]
def HasQuasiCompactFieldRepresentative (x : points B S hS F) : Prop :=
  ∃ p : FieldValuedPoint B S hS F,
    p.class B S hS F = x ∧ IsQuasiCompact B S hS (fieldMorphism B S hS F p)

/-- **Stacks 03JV, condition (6).** *Every* field-valued point in the class of `x` presents
it by a quasi-compact morphism. -/
@[stacks 03JV "part (6)"]
def EveryFieldRepresentativeIsQuasiCompact (x : points B S hS F) : Prop :=
  ∀ p : FieldValuedPoint B S hS F,
    p.class B S hS F = x → IsQuasiCompact B S hS (fieldMorphism B S hS F p)

/-! ### The implications the source calls immediate -/

/-- **Stacks 03JV, condition (4) implies condition (5).** Forgetting that the presenting
morphism is a monomorphism leaves a quasi-compact field-valued representative. -/
@[stacks 03JV "part (4) implies part (5)"]
theorem HasQuasiCompactMonomorphicFieldRepresentative.hasQuasiCompactFieldRepresentative
    {x : points B S hS F}
    (h : HasQuasiCompactMonomorphicFieldRepresentative B S hS F x) :
    HasQuasiCompactFieldRepresentative B S hS F x := by
  obtain ⟨p, hpx, -, hqc⟩ := h
  exact ⟨p, hpx, hqc⟩

/-- **Stacks 03JV, condition (6) implies condition (5).** A point of `|F|` is by construction
the class of some field-valued point, so a universally quasi-compact class has a
quasi-compact representative. -/
@[stacks 03JV "part (6) implies part (5)"]
theorem EveryFieldRepresentativeIsQuasiCompact.hasQuasiCompactFieldRepresentative
    {x : points B S hS F}
    (h : EveryFieldRepresentativeIsQuasiCompact B S hS F x) :
    HasQuasiCompactFieldRepresentative B S hS F x := by
  obtain ⟨p, hp⟩ := Quot.exists_rep x
  exact ⟨p, hp, h p hp⟩

/-- Condition (1) of Stacks 03JV bounds the relation fibres of Stacks 03JU: on an affine
étale chart, the set of points of `R` with prescribed projections above `x` is contained in
the fibre of `|R| → |F|` above `x`, which condition (1) declares finite. -/
theorem HasFiniteFibresOnEveryAffineEtaleChart.hasFiniteRelationFiber {x : points B S hS F}
    (h : HasFiniteFibresOnEveryAffineEtaleChart B S hS F x) (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (φ : yoneda.obj U ⟶ F)
    (hφ : IsEtale B S hS φ) (a b : points B S hS (yoneda.obj U))
    (ha : pointsMap B S hS (yoneda.obj U) φ a = x) :
    HasFiniteRelationFiber B S hS F U φ a b := by
  refine (h U hU φ hφ).2.subset ?_
  rintro r ⟨hra, -⟩
  change pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) r = x
  rw [pointsMap_comp, Function.comp_apply, hra, ha]

end AlgebraicGeometry.Space

end
