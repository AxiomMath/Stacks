module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodalOverFieldCriterion
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodalUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent

/-!
# Nodal curves over a field (Stacks 0DSY, part (2))

Part (2) of Stacks 0DSY characterizes, for a scheme `X` proper over a field `k` with
`dim(X) ≤ 1`, when the classifying morphism `Spec(k) → Curves` factors through the open
substack `Curves^{nodal}`: exactly when the singularities of `X` are at-worst-nodal and `X` is
equidimensional of dimension one. That is proved here.

## Main definitions

* `AlgebraicGeometry.curveFamilyOfProperOverFieldEqSpec`: the family of curves of Stacks 0D4Z
  attached to a proper scheme of dimension at most one over a field — the object of `Curves`
  over `Spec(k)` whose classifying morphism part (2) is about.

## Main results

* `AlgebraicGeometry.isNodalCurveFamily_curveFamilyOfProperOverField_iff`: that family is
  at-worst-nodal of relative dimension one exactly when the morphism of schemes is.
* `AlgebraicGeometry.lifts_nodalCurves_curveFamilyOfProperOverField_iff` and
  `AlgebraicGeometry.lifts_nodalCurvesInclusion_curveFamilyOfProperOverField_iff`: **Stacks
  0DSY, part (2)**, the second stated through the inclusion 1-morphism
  `AlgebraicGeometry.nodalCurvesInclusion` of the open substack, so that it is about the same
  object as the other registrations of the tag.

## Implementation notes

The family of curves is `AlgebraicGeometry.curveFamilyOfSchemeMorphism` with all of its
hypotheses discharged from properness of the morphism of schemes and the hypothesis that its
target be the spectrum of a field, so that nothing beyond the source's "X proper over `k` with
`dim(X) ≤ 1`" is assumed. Flatness is automatic over a field and finite presentation follows
from the finite typeness contained in properness, both after replacing the target by the
spectrum of the field; quasi-compactness, separatedness and quasi-separatedness of the induced
morphism of algebraic spaces — Stacks 04XW and 03KY, which
`AlgebraicGeometry.curveFamilyOfSchemeMorphism` carries as hypotheses for lack of a declaration
— are available for a *representable* morphism, which this one is, as
`AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_quasiCompact`,
`AlgebraicGeometry.Space.isSeparated_yoneda_map_iff` and
`AlgebraicGeometry.Space.isQuasiSeparated_yoneda_map_iff`.

Factoring the classifying morphism through `Curves^{nodal}` is lifting the object of `Curves`
it corresponds to through the inclusion of the strictly full subcategory, which is how part (1)
of the source is stated in `AlgebraicGeometry.lifts_nodalCurves_iff`. That form of part (1) is
unconditional — it does not use the `Bootstrap04S6Spaces` hypothesis that the open substack of
`AlgebraicGeometry.nodalCurvesOpenSubstackUnconditional` needs — so part (2) is stated against it
and is unconditional too.

The two sides are then joined in two steps. The nodal condition on the family is the
every-étale-chart condition of Stacks 03MJ at a morphism of the site, which for a property
étale local on the source and target is the scheme-level condition itself (Stacks 0DSG, here
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` at the étale-locality witness
of Stacks 0C5B, 0C5D, 0CD8 and 0C5E). Over a field that scheme-level condition is the
conjunction the source states, by
`Stacks.Curves.isAtWorstNodalOfRelativeDimensionOne_iff_hasAtWorstNodalSingularities`, which
rests on Tag 0C4E over an arbitrary base field.

## References

* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0DSE](https://stacks.math.columbia.edu/tag/0DSE)
* [Stacks Project, Tag 0DSG](https://stacks.math.columbia.edu/tag/0DSG)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### Properness over a field -/

/-- A morphism of schemes locally of finite type whose target is the spectrum of a field is flat
and locally of finite presentation: a module over a field is free, and a finite type algebra over
a field is of finite presentation. -/
theorem flat_and_locallyOfFinitePresentation_of_target_eq_spec {X Y : Scheme.{u}}
    (q : X ⟶ Y) (k : Type u) [Field k] (hY : Y = Spec (.of k)) [LocallyOfFiniteType q] :
    Flat q ∧ LocallyOfFinitePresentation q := by
  subst hY
  exact ⟨inferInstance, inferInstance⟩

/-- **The family of curves of a proper scheme of dimension at most one over a field.** For a
morphism of the big fppf site of the integers whose target scheme is the spectrum of a field,
which is proper on underlying schemes and whose source scheme has dimension at most one, the
induced morphism of algebraic spaces is a family of curves in the sense of Stacks 0D4Z.

This is the object of `Curves` over `Spec(k)` whose classifying morphism part (2) of Stacks
0DSY is about. It is `AlgebraicGeometry.curveFamilyOfSchemeMorphism` with every one of its
hypotheses discharged: flatness and finite presentation because the target is the spectrum of a
field, and quasi-compactness, separatedness and quasi-separatedness of the induced morphism of
algebraic spaces because that morphism is representable. -/
def curveFamilyOfProperOverFieldEqSpec {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
    (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    CurveFamily B hZ :=
  haveI := hproper
  haveI : LocallyOfFiniteType ((BigFppfOver.toScheme B integerBase hZ).map g) :=
    inferInstance
  curveFamilyOfSchemeMorphism B hZ g
    (flat_and_locallyOfFinitePresentation_of_target_eq_spec _ k hW).1 hproper
    (flat_and_locallyOfFinitePresentation_of_target_eq_spec _ k hW).2
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance)
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance)
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).mpr inferInstance)
    hdim

/-! ### Stacks 0DSY, part (2) -/

/-- **The nodal condition on the family of curves of a morphism of schemes.** The family of
curves attached to a proper morphism of the site onto the spectrum of a field is at-worst-nodal
of relative dimension one exactly when that morphism of schemes is.

The condition on the family is the every-étale-chart condition of Stacks 03MJ at a morphism of
the site, and being at-worst-nodal of relative dimension one is étale local on the source and
target, so the condition is the scheme-level one itself. -/
theorem isNodalCurveFamily_curveFamilyOfProperOverField_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    isNodalCurveFamily B hZ (curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) ↔
      IsAtWorstNodalOfRelativeDimensionOne ((BigFppfOver.toScheme B integerBase hZ).map g) :=
  Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget g

/-- **At-worst-nodal of relative dimension one over a field, with the field named by an equality
of schemes.** The criterion
`Stacks.Curves.isAtWorstNodalOfRelativeDimensionOne_iff_hasAtWorstNodalSingularities` read for a
morphism whose target is only identified with the spectrum of the field by an equality, which is
how the base of a family of curves over a field presents itself. -/
private theorem isAtWorstNodalOfRelativeDimensionOne_iff_of_target_eq_spec {X Y : Scheme.{u}}
    (q : X ⟶ Y) (k : Type u) [Field k] (hY : Y = Spec (.of k)) [LocallyOfFiniteType q] :
    letI : X.Over (Spec (.of k)) := ⟨q ≫ eqToHom hY⟩
    (IsAtWorstNodalOfRelativeDimensionOne q ↔
      (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ Equidimensional X ∧
        ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞))) := by
  subst hY
  let : X.Over (Spec (.of k)) := ⟨q ≫ eqToHom rfl⟩
  have hq : (X ↘ Spec (.of k)) = q := by
    change q ≫ eqToHom rfl = q
    simp
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := hq ▸ ‹LocallyOfFiniteType q›
  have h :=
    Stacks.Curves.isAtWorstNodalOfRelativeDimensionOne_iff_hasAtWorstNodalSingularities k X
  rwa [hq] at h

/-- **Stacks 0DSY, part (2).** Let `k` be a field and let `X ⟶ Spec(k)` be a morphism of the big
fppf site of the integers which is proper and whose source has dimension at most one. The
classifying morphism `Spec(k) → Curves` of the attached family of curves factors through
`Curves^{nodal}` — that is, that family lifts through the inclusion of the strictly full
subcategory of families which are at-worst-nodal of relative dimension one — if and only if the
singularities of `X` are at worst nodal and `X` is equidimensional of dimension one.

The hypotheses are those of the source: `X` is proper over the field and of dimension at most
one. Nothing else is assumed; in particular this does not use the hypothesis
`AlgebraicGeometry.Stack.Bootstrap04S6Spaces` on which
`AlgebraicGeometry.nodalCurvesOpenSubstackUnconditional` — the open substack itself, part of the
same tag — is conditional, because factoring through the substack is tested by lifting the
classifying object through the inclusion, and that inclusion is constructed unconditionally.

"Equidimensional of dimension one" is read as the source's definition reads it: `X` is
equidimensional and every irreducible component of `X` has dimension one. -/
@[stacks 0DSY "part (2): for a scheme X proper over a field k with dim(X) ≤ 1, the classifying \
morphism Spec(k) → Curves factors through Curves^{nodal} if and only if the singularities of X \
are at-worst-nodal and X is equidimensional of dimension 1. Factoring through the substack is \
lifting the classifying object through the inclusion of the strictly full subcategory of \
at-worst-nodal families, as in AlgebraicGeometry.lifts_nodalCurves_iff; no part of Tag 04S6 \
is assumed, and this declaration carries no hypothesis beyond the source's"]
theorem lifts_nodalCurves_curveFamilyOfProperOverField_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
      ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
    ((∃ Y : (isNodalCurveFamily B hZ).FullSubcategory,
        Y.obj = curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) ↔
      (Stacks.Curves.HasAtWorstNodalSingularities k
          ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        ∀ Z ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
          topologicalKrullDim Z = (1 : WithBot ℕ∞))) := by
  have := hproper
  exact (lifts_nodalCurves_iff B hZ _).trans
    ((isNodalCurveFamily_curveFamilyOfProperOverField_iff B hZ g k hW hproper hdim).trans
      (isAtWorstNodalOfRelativeDimensionOne_iff_of_target_eq_spec _ k hW))

/-- **Stacks 0DSY, part (2).** Let `k` be a field and let `X ⟶ Spec(k)` be a morphism of the big
fppf site of the integers which is proper and whose source has dimension at most one. The
classifying morphism `Spec(k) → Curves` of the attached family of curves factors through the
open substack `Curves^{nodal}` if and only if the singularities of `X` are at worst nodal and
`X` is equidimensional of dimension one.

This is `AlgebraicGeometry.lifts_nodalCurves_curveFamilyOfProperOverField_iff` with factoring
through `Curves^{nodal}` read as being in the image on objects of the 1-morphism
`AlgebraicGeometry.nodalCurvesInclusion`, so that the statement is about the same object as the
other registrations of the tag: the strictly full subcategory
`AlgebraicGeometry.nodalCurvesFiberedCategory` of the fibred category of families of curves,
whose inclusion is proved representable by algebraic spaces and an open immersion in
`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_nodalCurvesInclusion` and
`AlgebraicGeometry.isOpenImmersion_nodalCurvesInclusion`.

The hypotheses are those of the source: `X` is proper over the field and of dimension at most
one. Nothing else is assumed; in particular there is no algebraic stack `𝒳`, no equivalence
identifying it with the category of families of curves, and no part of Stacks 04S6.

"Equidimensional of dimension one" is read as the source's definition reads it: `X` is
equidimensional and every irreducible component of `X` has dimension one. -/
@[stacks 0DSY "part (2), stated through the inclusion 1-morphism \
AlgebraicGeometry.nodalCurvesInclusion of the open substack: for a scheme X proper over a field \
k with dim(X) ≤ 1, the classifying morphism Spec(k) → Curves factors through Curves^nodal if \
and only if the singularities of X are at-worst-nodal and X is equidimensional of dimension 1. \
Unconditional: no presentation of Curves as an algebraic stack (Tag 0D5A) and no part of \
Tag 04S6 is assumed, and this declaration carries no hypothesis beyond the source's"]
theorem lifts_nodalCurvesInclusion_curveFamilyOfProperOverField_iff
    {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
      ⟨(BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW⟩
    ((∃ Y : (nodalCurvesFiberedCategory B hZ).based.obj,
        (CatFiberedInGroupoids.homFunctor (nodalCurvesInclusion B hZ)).obj Y =
          curveFamilyOfProperOverFieldEqSpec B hZ g k hW hproper hdim) ↔
      (Stacks.Curves.HasAtWorstNodalSingularities k
          ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        Equidimensional ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
        ∀ Z ∈ irreducibleComponents ((BigFppfOver.toScheme B integerBase hZ).obj T),
          topologicalKrullDim Z = (1 : WithBot ℕ∞))) := by
  have := hproper
  exact (lifts_nodalCurvesInclusion_iff B hZ _).trans
    ((isNodalCurveFamily_curveFamilyOfProperOverField_iff B hZ g k hW hproper hdim).trans
      (isAtWorstNodalOfRelativeDimensionOne_iff_of_target_eq_spec _ k hW))

end AlgebraicGeometry

end
