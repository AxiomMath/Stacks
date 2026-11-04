module

public import StacksFrontier.AlgebraicGeometry.Picard.PicardComponents
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroSubgroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeZeroAbelianVariety
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# The clauses of [Stacks, Tag 0BA0] over a separably closed field, from their two inputs

For a smooth projective curve `X` over a separably closed field `k`, the clauses (1), (4), (5) and
(6) of [Stacks, Tag 0BA0], stated for the Picard scheme of `X` and its degree components at a
chosen rational point, from the conclusion of [Stacks, Tag 0B9Y] and the vanishing of
[Stacks, Tag 0B90] over algebraically closed fields.

## Main results

* `Stacks.AbelMap.picardScheme_clause_one_of`, `…_clause_four_of`, `…_clause_five_of`,
  `…_clause_six_of`.
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

omit hproj in
/-- The conclusion of [Stacks, Tag 0B9Y] for the curve, at the instances its statement needs. -/
abbrev TwistToNormalized' (hproj : IsProjective (B.inclusion.map f)) : Prop :=
  haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
  haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
  TwistToNormalized B hX hk f

include hproj in
/-- **[Stacks, Tag 0B9Z]** for the curve, from the conclusion of [Stacks, Tag 0B9Y]. -/
theorem isRepresentable_of_twistToNormalized' (htw : TwistToNormalized' B hX hk f hproj) :
    (picardFunctor B hX hk f).IsRepresentable :=
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  isRepresentable_picardFunctor_of_twistToNormalized B hX hk f (curveSection B hX hk f)
    (curveSection_comp B hX hk f) htw

include hproj in
/-- **Clause (1)**: the Picard scheme is the disjoint union of its degree components, each a smooth
proper variety of dimension `g`. -/
theorem picardScheme_clause_one_of (htw : TwistToNormalized' B hX hk f hproj) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
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
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  have := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
  ⟨nonempty_isColimit_picardDegreeLocus B hX hk f _ _,
    fun d => picardDegreeComponent_smooth_proper_variety B hX hk f _ _ htw d⟩

/-- The vanishing of [Stacks, Tag 0B90] on proper curves over algebraically closed fields. -/
abbrev LargeDegreeVanishing : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of K))
    [IsProper fZ] [IsCurve K fZ] (M : Z.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M),
    2 * (genus fZ : ℤ) - 1 ≤ @invertibleCurveDegree K _ Z fZ _
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := fZ)).le M hM →
    IsZero (cohomologyOverField K fZ M 1)

include hproj in
/-- **Clauses (4), (5) and (6)**: for `d ≥ 0` there is exactly one morphism
`γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` sending a family `D` to the class of `𝒪(D)`; it is surjective
for `d ≥ g` and smooth for `d ≥ 2g - 1`, and `γ_g` is birational. -/
theorem picardScheme_clauses_four_five_six_of (htw : TwistToNormalized' B hX hk f hproj)
    (hvan1 : LargeDegreeVanishing.{u}) (d : ℕ) (H : BigFppfOver B (Spec (.of k)) hk)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map H.hom)) d) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
    ∃! γ : H ⟶ picardSchemeDegreeComponent B hX hk f (curveSection B hX hk f)
        (curveSection_comp B hX hk f) d,
      (∀ {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H),
        picardHomEquiv B hX hk f (t ≫ γ ≫ picardSchemeDegreeComponentι B hX hk f
            (curveSection B hX hk f) (curveSection_comp B hX hk f) d) =
          (toPicardFunctor B hX hk f).app (op T) (hH.family (testMap B hk t)).picardClass) ∧
      (genus (B.inclusion.map f) ≤ d → Surjective (B.inclusion.map γ.left)) ∧
      (2 * (genus (B.inclusion.map f) : ℤ) - 1 ≤ d →
        AlgebraicGeometry.Smooth (B.inclusion.map γ.left)) ∧
      (d = genus (B.inclusion.map f) → IsBirational (B.inclusion.map γ.left)) := by
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  have := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
  obtain ⟨γ, hγ, huniq⟩ := existsUnique_abelMap B hX hk f (curveSection B hX hk f)
    (curveSection_comp B hX hk f) d H hH
  have hγe : curveAbelMap B hX hk f _ _ H hH = γ :=
    huniq _ (fun t => picardHomEquiv_comp_curveAbelMap B hX hk f _ _ H hH t)
  subst hγe
  obtain ⟨hs, hsm⟩ := surjective_smooth_curveAbelMap B hX hk f _ _ htw hvan1 d H hH
  refine ⟨_, ⟨hγ, hs, hsm, fun hd => ?_⟩, fun γ' h => huniq γ' h.1⟩
  subst hd
  exact isBirational_curveAbelMap B hX hk f _ _ htw H hH

include hproj in
/-- **Clause (2)**: the `k`-points of `Pic^d_{X/k}` correspond to the isomorphism classes of
invertible `𝒪_X`-modules of degree `d`. -/
theorem picardScheme_clause_two_of (htw : TwistToNormalized' B hX hk f hproj) (d : ℤ) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
    Nonempty ((baseOver B hk ⟶ picardSchemeDegreeComponent B hX hk f (curveSection B hX hk f)
        (curveSection_comp B hX hk f) d) ≃
      {x : Stacks.Picard.ofScheme X //
        @invertibleCurveDegree k _ X (B.inclusion.map f) _
          (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le (rep x)
          (Stacks.Picard.picardRepresentative X.toRingedSpace x).property = d}) :=
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  have := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
  ⟨degreePointsEquiv' B hX hk f _ _ d⟩

include hproj in
/-- **Clause (3)**: `Pic⁰_{X/k}` is an open and closed subgroup scheme of the Picard group scheme:
an open subgroup scheme whose inclusion is a closed immersion with image the degree-zero
component. -/
theorem picardScheme_clause_three_of (htw : TwistToNormalized' B hX hk f hproj) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
    ∃ H : AlgebraicGeometry.OpenSubgroupScheme (picardGrp B hX hk f),
      IsClosedImmersion H.ι.hom.hom.left ∧
        Set.range H.ι.hom.hom.left.base = (picardDegreeLocus B hX hk f (curveSection B hX hk f)
          (curveSection_comp B hX hk f) 0 : Set (picardScheme B hX hk f)) :=
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  have := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
  ⟨picardDegreeZeroSubgroup B hX hk f _ _,
    isClosedImmersion_picardDegreeZeroSubgroup_ι B hX hk f _ _,
    range_picardDegreeZeroSubgroup_ι B hX hk f _ _⟩

include hproj in
/-- **`Pic⁰_{X/k}` is an abelian variety**, from clause (1). -/
theorem isAbelianVariety_picardDegreeZero_of (htw : TwistToNormalized' B hX hk f hproj) :
    haveI := geometricallyIrreducible_of_isSepClosed B hX hk f
    haveI := isProjectiveVariety_of_isProjective B hX hk f hproj
    haveI := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
    IsAbelianVariety k (picardDegreeZeroSubgroup B hX hk f (curveSection B hX hk f)
      (curveSection_comp B hX hk f)).carrier.X := by
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  have := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
  obtain ⟨hsm, hpr, hvar, -⟩ := picardDegreeComponent_smooth_proper_variety B hX hk f
    (curveSection B hX hk f) (curveSection_comp B hX hk f) htw 0
  exact isAbelianVariety_picardDegreeZero B hX hk f _ _ hpr
    (@SmoothOfRelativeDimension.smooth (genus (B.inclusion.map f)) _ _ _ hsm) hvar.toIsIntegral

include hproj in
/-- **`Pic⁰(X)` is `n`-divisible** for `n` invertible in an algebraically closed field, from
clause (1); this is the hypothesis `hdvd` of the consumers of [Stacks, Tags 03RQ and 03RR]. -/
theorem exists_nsmul_eq_of_mem_picardDegreeZero_of [IsAlgClosed k]
    (htw : TwistToNormalized' B hX hk f hproj) (n : ℕ) (hn : IsUnit (n : k))
    (x : schemePicard X)
    (hx : haveI : IsProper (B.inclusion.map f) := hproj.isProper
      x ∈ picardDegreeZero k (B.inclusion.map f)
        (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le) :
    ∃ y, n • y = x := by
  have := geometricallyIrreducible_of_isSepClosed B hX hk f
  have := isProjectiveVariety_of_isProjective B hX hk f hproj
  have := isRepresentable_of_twistToNormalized' B hX hk f hproj htw
  obtain ⟨hsm, hpr, hvar, -⟩ := picardDegreeComponent_smooth_proper_variety B hX hk f
    (curveSection B hX hk f) (curveSection_comp B hX hk f) htw 0
  exact exists_nsmul_eq_of_mem_picardDegreeZero B hX hk f _ _ hpr
    (@SmoothOfRelativeDimension.smooth (genus (B.inclusion.map f)) _ _ _ hsm) hvar.toIsIntegral
    n hn x hx

end Stacks.AbelMap

end
