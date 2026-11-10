module

public import StacksFrontier.AlgebraicGeometry.Picard.PicardSchemeCurveOf
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.PicardCurveRepresentable
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
public import StacksFrontier.AlgebraicGeometry.Curves.BaseChangeTwistLowCohomology

/-!
# The Picard scheme of a smooth projective curve over a separably closed field

[Stacks, Tag 0BA0], registered on a covering set of its clauses: for a smooth projective curve `X`
of genus `g` over a separably closed field `k`,

1. `Pic_{X/k}` is a disjoint union of `g`-dimensional smooth proper varieties `Pic^d_{X/k}`;
2. the `k`-points of `Pic^d_{X/k}` correspond to invertible `𝒪_X`-modules of degree `d`;
3. `Pic^0_{X/k}` is an open and closed subgroup scheme;
4. for `d ≥ 0` there is a canonical morphism `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}`;
5. `γ_d` is surjective for `d ≥ g` and smooth for `d ≥ 2g - 1`;
6. `γ_g` is birational.

The Picard scheme exists by [Stacks, Tag 0B9Z]
(`Stacks.PicardFunctor.isRepresentable_picardFunctor_of_isSepClosed`); its degree components are
taken at a rational point of `X` ([Stacks, Tag 056U]). The two inputs of
`StacksFrontier/AlgebraicGeometry/Picard/PicardSchemeCurveOf.lean` are discharged here: the
conclusion of [Stacks, Tag 0B9Y]
(`AlgebraicGeometry.exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed`)
and the vanishing of [Stacks, Tag 0B90] (in the namespace `AlgebraicGeometry`,
`isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree`).

## Main results

* `Stacks.AbelMap.picardScheme_clause_one`, `Stacks.AbelMap.picardScheme_clause_two`,
  `Stacks.AbelMap.picardScheme_clause_three`, `Stacks.AbelMap.picardScheme_clauses_four_five_six`:
  [Stacks, Tag 0BA0], clauses (1)-(6).
* `Stacks.AbelMap.exists_hilbertSchemeOfRank_of_isSepClosed`: the Hilbert scheme `Hilb^d_{X/k}`
  exists in the site ([Stacks, Tag 0B9I]).
* `Stacks.AbelMap.isAbelianVariety_picardDegreeZero_of_isSepClosed`,
  `Stacks.AbelMap.exists_nsmul_eq_of_mem_picardDegreeZero_of_isAlgClosed`: `Pic⁰_{X/k}` is an
  abelian variety and `Pic⁰(X)` is divisible by integers invertible in `k`.
* `Stacks.AbelMap.picardDegreeZero_inputs_of_isSepClosed`: the facts about `Pic⁰_{X/k}` that
  [Stacks, Tags 03RQ and 03RR] take, at an arbitrary rational point.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.PicardFunctor Stacks.PicardCurve

universe u

namespace Stacks.AbelMap

variable {k : Type u} [Field k] [IsSepClosed k] (B : BigFppfSite.{u}) {X : Scheme.{u}}
  (hX : B.Contains X) (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)]
  (hproj : IsProjective (B.inclusion.map f))

include hproj in
/-- The conclusion of [Stacks, Tag 0B9Y] for the curve, at the instances of
`Stacks.AbelMap.TwistToNormalized'`:
`Stacks.PicardFunctor.twistToNormalized_of_isSepClosed_of_isProjectiveVariety`. -/
theorem twistToNormalized'_of_isSepClosed : TwistToNormalized' B hX hk f hproj :=
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  twistToNormalized_of_isSepClosed_of_isProjectiveVariety B hX hk f

/-- The vanishing of [Stacks, Tag 0B90] on proper curves over algebraically closed fields, in the
form `Stacks.AbelMap.LargeDegreeVanishing` takes. -/
theorem largeDegreeVanishing : LargeDegreeVanishing.{u} :=
  fun K _ _ _ fZ _ _ M hM hdeg =>
    isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree K fZ M hM hdeg

include hproj in
/-- **Stacks Project, Tag 0BA0, clause (1).** -/
@[stacks 0BA0 "(1)"]
theorem picardScheme_clause_one :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
    Nonempty (IsColimit (Cofan.mk (picardScheme B hX hk f)
        fun d => (picardDegreeLocus B hX hk f (curveSection B hX hk f)
          (curveSection_comp B hX hk f) d).ι)) ∧
      ∀ d : ℤ, SmoothOfRelativeDimension (genus (B.inclusion.map f))
          (picardDegreeComponentHom B hX hk f (curveSection B hX hk f)
            (curveSection_comp B hX hk f) d) ∧
        IsProper (picardDegreeComponentHom B hX hk f (curveSection B hX hk f)
            (curveSection_comp B hX hk f) d) ∧
        IsVariety k (picardDegreeComponentHom B hX hk f (curveSection B hX hk f)
            (curveSection_comp B hX hk f) d) ∧
        topologicalKrullDim (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f
            (curveSection B hX hk f) (curveSection_comp B hX hk f) d).left) =
          (genus (B.inclusion.map f) : WithBot ℕ∞) :=
  picardScheme_clause_one_of B hX hk f hproj (twistToNormalized'_of_isSepClosed B hX hk f hproj)

include hproj in
/-- **Stacks Project, Tag 0BA0, clause (2).** -/
@[stacks 0BA0 "(2)"]
theorem picardScheme_clause_two (d : ℤ) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
    Nonempty ((baseOver B hk ⟶ picardSchemeDegreeComponent B hX hk f (curveSection B hX hk f)
        (curveSection_comp B hX hk f) d) ≃
      {x : Stacks.Picard.ofScheme X //
        @invertibleCurveDegree k _ X (B.inclusion.map f) _
          (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le (rep x)
          (Stacks.Picard.picardRepresentative X.toRingedSpace x).property = d}) :=
  picardScheme_clause_two_of B hX hk f hproj (twistToNormalized'_of_isSepClosed B hX hk f hproj) d

include hproj in
/-- **Stacks Project, Tag 0BA0, clause (3).** -/
@[stacks 0BA0 "(3)"]
theorem picardScheme_clause_three :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
    ∃ H : AlgebraicGeometry.OpenSubgroupScheme (picardGrp B hX hk f),
      IsClosedImmersion H.ι.hom.hom.left ∧
        Set.range H.ι.hom.hom.left.base = (picardDegreeLocus B hX hk f (curveSection B hX hk f)
          (curveSection_comp B hX hk f) 0 : Set (picardScheme B hX hk f)) :=
  picardScheme_clause_three_of B hX hk f hproj (twistToNormalized'_of_isSepClosed B hX hk f hproj)

include hproj in
/-- **The degree-`d` Hilbert scheme of the curve exists in the site**: by [Stacks, Tag 0B9I],
part (1) (`Stacks.Hilbert.Curve.hilbertScheme_geometry`), the degree-`d` Hilbert functor of
points of `X` is represented by a proper scheme over `k`, which lies in the site
(`Stacks.PicardFunctor.contains_of_isProper`). -/
theorem exists_hilbertSchemeOfRank_of_isSepClosed (d : ℕ) :
    ∃ H : BigFppfOver B (Spec (.of k)) hk,
      Nonempty (Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
        (Over.mk (B.inclusion.map H.hom)) d) := by
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have : IsProper (B.inclusion.map f) := hproj.isProper
  have hg := Stacks.Hilbert.Curve.hilbertScheme_geometry (B.inclusion.map f) d
  obtain ⟨⟨H₀, hH₀⟩⟩ := hg.1
  have := (hg.2 H₀ hH₀).2.1
  have hc : B.Contains H₀.left := Stacks.PicardFunctor.contains_of_isProper B hk H₀.hom
  exact ⟨Over.mk (ObjectProperty.homMk (X := B.obj hc) (Y := B.obj hk) H₀.hom), ⟨hH₀⟩⟩

include hproj in
/-- **Stacks Project, Tag 0BA0, clauses (4), (5) and (6).** For every `d ≥ 0` the degree-`d`
Hilbert scheme `Hilb^d_{X/k}` exists in the site ([Stacks, Tag 0B9I]), and for every scheme `H`
representing it there is a unique morphism `γ_d : H ⟶ Pic^d_{X/k}` classifying the invertible
module `𝒪(D_univ)` of the universal divisor (clause (4)); it is surjective for `d ≥ g` and smooth
for `d ≥ 2g - 1` (clause (5)), and birational for `d = g` (clause (6)). -/
@[stacks 0BA0 "(4), (5) and (6)"]
theorem picardScheme_clauses_four_five_six (d : ℕ) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
    (∃ H : BigFppfOver B (Spec (.of k)) hk,
      Nonempty (Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
        (Over.mk (B.inclusion.map H.hom)) d)) ∧
    ∀ (H : BigFppfOver B (Spec (.of k)) hk)
      (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
        (Over.mk (B.inclusion.map H.hom)) d),
    ∃! γ : H ⟶ picardSchemeDegreeComponent B hX hk f (curveSection B hX hk f)
        (curveSection_comp B hX hk f) d,
      (∀ {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H),
        picardHomEquiv B hX hk f (t ≫ γ ≫ picardSchemeDegreeComponentι B hX hk f
            (curveSection B hX hk f) (curveSection_comp B hX hk f) d) =
          (toPicardFunctor B hX hk f).app (op T) (hH.family (testMap B hk t)).picardClass) ∧
      (genus (B.inclusion.map f) ≤ d → Surjective (B.inclusion.map γ.left)) ∧
      (2 * (genus (B.inclusion.map f) : ℤ) - 1 ≤ d →
        AlgebraicGeometry.Smooth (B.inclusion.map γ.left)) ∧
      (d = genus (B.inclusion.map f) → IsBirational (B.inclusion.map γ.left)) :=
  ⟨exists_hilbertSchemeOfRank_of_isSepClosed B hX hk f hproj d, fun H hH =>
    picardScheme_clauses_four_five_six_of B hX hk f hproj
      (twistToNormalized'_of_isSepClosed B hX hk f hproj) largeDegreeVanishing d H hH⟩

include hproj in
/-- **`Pic⁰_{X/k}` is an abelian variety**: by clause (1) its degree-zero component is a smooth
proper variety, and an open and closed subgroup scheme by clause (3). -/
theorem isAbelianVariety_picardDegreeZero_of_isSepClosed :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
    IsAbelianVariety k (picardDegreeZeroSubgroup B hX hk f (curveSection B hX hk f)
      (curveSection_comp B hX hk f)).carrier.X :=
  isAbelianVariety_picardDegreeZero_of B hX hk f hproj
    (twistToNormalized'_of_isSepClosed B hX hk f hproj)

include hproj in
/-- **`Pic⁰(X)` is `n`-divisible** for `n` invertible in an algebraically closed field `k`, for a
smooth projective curve `X` over `k`: the hypothesis `hdvd` of the consumers of
[Stacks, Tags 03RQ and 03RR], from clause (1) of [Stacks, Tag 0BA0]. -/
theorem exists_nsmul_eq_of_mem_picardDegreeZero_of_isAlgClosed [IsAlgClosed k] (n : ℕ)
    (hn : IsUnit (n : k)) (x : schemePicard X)
    (hx : haveI : IsProper (B.inclusion.map f) := hproj.isProper
      x ∈ picardDegreeZero k (B.inclusion.map f)
        (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le) :
    ∃ y, n • y = x :=
  exists_nsmul_eq_of_mem_picardDegreeZero_of B hX hk f hproj
    (twistToNormalized'_of_isSepClosed B hX hk f hproj) n hn x hx

end Stacks.AbelMap

/-! ### The degree-zero inputs of [Stacks, Tags 03RQ and 03RR] at an arbitrary rational point -/

namespace Stacks.AbelMap

variable {k : Type u} [Field k] [IsSepClosed k] (B : BigFppfSite.{u}) {X : Scheme.{u}}
  (hX : B.Contains X) (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

/-- **The facts about `Pic⁰_{X/k}` that [Stacks, Tags 03RQ and 03RR] consume**, at every rational
point `σ` of a smooth projective curve `X` over a separably closed field: the Picard functor is
representable ([Stacks, Tag 0B9Z]) and, by clause (1) of [Stacks, Tag 0BA0], the degree-zero
component is proper, smooth and integral over `k`, with `Pic⁰_{X/k}` of dimension the genus. -/
theorem picardDegreeZero_inputs_of_isSepClosed :
    ∃ _ : (picardFunctor B hX hk f).IsRepresentable,
      IsProper (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom) ∧
      AlgebraicGeometry.Smooth
        (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom) ∧
      IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left) ∧
      Stacks.Groupoids.abelianVarietyDimension
        (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X = genus (B.inclusion.map f) := by
  have hrep := isRepresentable_picardFunctor_of_isSepClosed B hX hk f
  obtain ⟨hsm, hpr, hvar, hdim⟩ := picardDegreeComponent_smooth_proper_variety B hX hk f σ hσ
    (twistToNormalized_of_isSepClosed_of_isProjectiveVariety B hX hk f) 0
  refine ⟨hrep, hpr, @SmoothOfRelativeDimension.smooth (genus (B.inclusion.map f)) _ _ _ hsm,
    hvar.toIsIntegral, ?_⟩
  change ((topologicalKrullDim (B.inclusion.obj
    (picardSchemeDegreeComponent B hX hk f σ hσ 0).left)).unbotD 0).toNat = _
  rw [hdim]
  rfl

end Stacks.AbelMap

end
