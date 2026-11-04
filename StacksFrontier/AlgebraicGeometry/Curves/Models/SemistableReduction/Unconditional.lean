module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.Theorem
public import StacksFrontier.AlgebraicGeometry.Curves.PicardTorsionVisible
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionReducedProperCurve

/-!
# The semistable reduction theorem

[Stacks, Tag 0CDN]: let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth
projective curve over `K` with `H⁰(C, 𝒪_C) = K`. Then there is an extension of discrete valuation
rings `R ⊆ R'` inducing a finite separable extension `K'/K` of fraction fields such that `C_{K'}`
has semistable reduction; more precisely

1. in genus `0`, a separable `K'/K` of degree `2` with `C_{K'} ≅ 𝐏¹_{K'}`, the generic fibre of
   the smooth projective `𝐏¹_{R'}` over the integral closure `R'` of `R` in `K'`;
2. in genus `1`, a finite separable `K'/K` with `C_{K'}` semistable over every `R'_𝔪`, the special
   fibre of every minimal model being a smooth genus one curve or a cycle of rational curves;
3. in genus `g ≥ 2`, a finite separable `K'/K` of degree at most `B_g` ([Stacks, Tag 0CEJ]) with
   `C_{K'}` semistable over every `R'_𝔪`.

## Main results

* `Stacks.Models.semistableReduction`: **Tag 0CDN**, the whole statement.
* `Stacks.Models.exists_genusOne_semistableReduction`: part (2), genus one.
* `Stacks.Models.exists_hasSemistableReductionAtMaximalIdeals_of_two_le_genus`: part (3), genus
  at least two.

Part (1), genus zero, is `AlgebraicGeometry.SemistableReduction.genusZero_splitting`.

## Implementation notes

The proofs instantiate `Stacks.Models.semistableReduction_of_statements`,
`Stacks.Models.exists_genusOne_semistableReduction_of_statements` and
`Stacks.Models.exists_hasSemistableReductionAtMaximalIdeals_of_two_le_genus_of_statements` with
the proved results they use: Tag 0CDU (1) and (2)
(`Stacks.Picard.exists_finite_separable_torsionBy_of_genus_eq_one`,
`Stacks.Picard.exists_finite_separable_torsionBy_of_two_le_genus`), Tag 0CE6
(`AlgebraicGeometry.finrank_picardTorsion_le_genus_add_geometricGenus`), Tag 0C20 (in the
namespace `AlgebraicGeometry`,
`finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one` and
`finrank_picardTorsion_eq_iff_forall_isMulticrossSingularity_of_isReduced_dim_one`), Tag 0CA6
(in the namespace `Stacks.Models.RegularProperModelSituation`,
`isMinimal_associatedNumericalType_of_not_hasExceptionalCurveOfFirstKind`) and Tag 0C6U
(`Stacks.Models.nonempty_iso_projectiveLine_of_isRationalPoint`). The torsion subgroup
`AddSubgroup.torsionBy A n` is by definition `(Submodule.torsionBy ℤ A n).toAddSubgroup`, so the
two forms of `Pic(X)[n]` agree.

## References

* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] AddSubgroup.torsionBy.zmodModule

namespace Stacks.Models

/-- **Stacks Project, Tag 0CDN.** Let `R` be a discrete valuation ring with fraction field `K` and
`C` a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K`. Then there is an extension of
discrete valuation rings `R ⊆ R'` inducing a finite separable extension `K'/K` of fraction fields
such that `C_{K'}` has semistable reduction over `R'`. More precisely:

1. if the genus of `C` is zero, there is a separable `K'/K` of degree `2` with `C_{K'} ≅ 𝐏¹_{K'}`,
   and `C_{K'}` is the generic fibre of the smooth projective `𝐏¹_{R'}` over the integral closure
   `R'` of `R` in `K'`;
2. if the genus of `C` is one, there is a finite separable `K'/K` such that `C_{K'}` has
   semistable reduction over `R'_𝔪` for every maximal ideal `𝔪` of the integral closure `R'` of `R`
   in `K'`, and the special fibre of the minimal model of `C_{K'}` over `R'_𝔪` is a smooth genus
   one curve or a cycle of rational curves;
3. if the genus `g` of `C` is at least two, there is a finite separable `K'/K` of degree at most
   `B_g` such that `C_{K'}` has semistable reduction over `R'_𝔪` for every maximal ideal `𝔪` of
   the integral closure `R'` of `R` in `K'`. -/
@[stacks 0CDN]
theorem semistableReduction
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] :
    haveI : IsProper c := hproj.isProper
    (∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
        (_ : Algebra R' K') (_ : IsFractionRing R' K') (_ : Algebra R R')
        (_ : IsScalarTower R R' K'), IsLocalHom (algebraMap R R') ∧
        HasSemistableReduction R'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (hproj.pullback_snd _)) ∧
    (genus c = 0 →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
        (_ : IsScalarTower R K K'),
        FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧ Module.finrank K K' = 2 ∧
        Nonempty (Over.mk (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≅
          Over.mk (projectiveSpaceOver 1 (Spec (.of K')) ↘ Spec (.of K'))) ∧
        IsFractionRing (integralClosure R K') K' ∧
        Smooth (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
          Spec (.of (integralClosure R K'))) ∧
        IsProjective (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
          Spec (.of (integralClosure R K'))) ∧
        Nonempty (Over.mk (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))) ≅
          Over.mk (pullback.snd (C := Scheme.{u})
            (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
              Spec (.of (integralClosure R K')))
            (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K')))))) ∧
    (genus c = 1 →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
        (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
        HasSemistableReductionAtMaximalIdeals R K'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (hproj.pullback_snd _) ∧
        HasGenusOneMinimalFibresAtMaximalIdeals R K'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))) ∧
    (2 ≤ genus c →
      ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
        (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
        Module.finrank K K' ≤
          AlgebraicGeometry.SemistableReduction.semistableReductionDegreeBound (genus c) ∧
        HasSemistableReductionAtMaximalIdeals R K'
          (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
          (hproj.pullback_snd _)) :=
  semistableReduction_of_statements
    (fun _ _ _ f _ _ _ _ _ hn hg =>
      Stacks.Picard.exists_finite_separable_torsionBy_of_genus_eq_one f hg hn.ne_zero)
    (fun _ _ _ f _ _ _ _ _ hn hg =>
      Stacks.Picard.exists_finite_separable_torsionBy_of_two_le_genus f hg hn.ne_zero)
    (fun k _ _ g _ hdim ℓ _ hℓ => finrank_picardTorsion_le_genus_add_geometricGenus k g hdim ℓ hℓ)
    (fun k _ _ X _ _ _ hdim ℓ _ hℓ =>
      finrank_picardTorsion_le_genus_add_geometricGenus_of_isReduced_dim_one k X hdim ℓ hℓ)
    (fun k _ _ X _ _ _ hdim ℓ _ hℓ =>
      finrank_picardTorsion_eq_iff_forall_isMulticrossSingularity_of_isReduced_dim_one k X hdim ℓ
        hℓ)
    R K c hproj

/-- **Stacks Project, Tag 0CDN (2), genus one.** Let `R` be a discrete valuation ring with fraction
field `K` and `C` a smooth projective curve of genus one over `K` with `H⁰(C, 𝒪_C) = K`. Then there
is a finite separable extension `K'/K` such that `C_{K'}` has semistable reduction over `R'_𝔪` for
every maximal ideal `𝔪` of the integral closure `R'` of `R` in `K'`, and the special fibre of the
minimal model of `C_{K'}` over `R'_𝔪` is a smooth genus one curve or a cycle of rational
curves. -/
@[stacks 0CDN "(2), genus one"]
theorem exists_genusOne_semistableReduction
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (hg : genus c = 1) :
    haveI : IsProper c := hproj.isProper
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      HasSemistableReductionAtMaximalIdeals R K'
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (hproj.pullback_snd _) ∧
      HasGenusOneMinimalFibresAtMaximalIdeals R K'
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))) :=
  (semistableReduction R K c hproj).2.2.1 hg

/-- **Stacks Project, Tag 0CDN (3), genus at least two.** Let `R` be a discrete valuation ring with
fraction field `K` and `C` a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K`, of genus
`g ≥ 2`. Then there is a finite separable extension `K'/K` of degree at most `B_g` such that
`C_{K'}` has semistable reduction over `R'_𝔪` for every maximal ideal `𝔪` of the integral closure
`R'` of `R` in `K'`. -/
@[stacks 0CDN "(3), genus at least two"]
theorem exists_hasSemistableReductionAtMaximalIdeals_of_two_le_genus
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c]
    (hproj : IsProjective c) [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    (hg : 2 ≤ genus c) :
    haveI : IsProper c := hproj.isProper
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      Module.finrank K K' ≤ AlgebraicGeometry.SemistableReduction.semistableReductionDegreeBound
        (genus c) ∧
      HasSemistableReductionAtMaximalIdeals R K'
        (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
        (hproj.pullback_snd _) :=
  (semistableReduction R K c hproj).2.2.2 hg

end Stacks.Models

end
