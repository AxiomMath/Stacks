module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.HigherGenusLocal
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.HigherGenusReduction
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelExistence
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalTypeIff

/-!
# Semistable reduction in genus at least two

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth projective curve
of genus `g ≥ 2` over `K` with `H⁰(C, 𝒪_C) = K`. By [Stacks, Section 0CEI] there is a finite
separable extension `K'/K` of degree bounded in terms of `g` such that `C_{K'}` has semistable
reduction over `R'_𝔪` for every maximal ideal `𝔪` of the integral closure `R'` of `R` in `K'`.

## Main results

* `Stacks.Models.exists_hasSemistableReductionAtMaximalIdeals_of_two_le_genus_of_statements` —
  clause (3) of [Stacks, Tag 0CDN], with the statements of [Stacks, Tags 0CDU, 0CE6 and 0C20]
  as premises.

## References

* [Stacks Project, Section 0CEI](https://stacks.math.columbia.edu/tag/0CEI)
* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] AddSubgroup.torsionBy.zmodModule

namespace Stacks.Models

/-- **Semistable reduction in genus at least two** ([Stacks, Section 0CEI]). Let `R` be a discrete
valuation ring with fraction field `K` and `C` a smooth projective curve over `K` of genus
`g ≥ 2` with `H⁰(C, 𝒪_C) = K`. Then there is a finite separable extension `K'/K` of degree at
most `B_g` ([Stacks, Tag 0CEJ]) such that `C_{K'}` has semistable reduction over `R'_𝔪` for every
maximal ideal `𝔪` of the integral closure `R'` of `R` in `K'`, given the statements of
[Stacks, Tags 0CDU (2), 0CE6 and 0C20] as the premises `h0CDU`, `h0CE6`, `h0C20` and
`h0C20eq`. -/
theorem exists_hasSemistableReductionAtMaximalIdeals_of_two_le_genus_of_statements
    (h0CDU : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
      [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (n : ℕ),
      IsUnit (n : k) → 2 ≤ genus f →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
        Algebra.IsSeparable k k' ∧
        Module.finrank k k' ≤ (2 * genus f - 2) * (n ^ (2 * genus f)).factorial ∧
        (∃ x : Spec (.of k') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))),
          x ≫ pullback.snd _ _ = 𝟙 _) ∧
        Nonempty (AddSubgroup.torsionBy (Stacks.Picard.ofScheme
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) (n : ℤ) ≃+
          (Fin (2 * genus f) → ZMod n)))
    (h0CE6 : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
      (_ : topologicalKrullDim (X : Type u) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime] (_ : IsUnit (ℓ : k)),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus g + geometricGenus k g)
    (h0C20 : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [IsReduced X] (_hdim : topologicalKrullDim (X : Type u) = 1)
      (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ≤
          genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)))
    (h0C20eq : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsReduced X]
      (_hdim : topologicalKrullDim (X : Type u) = 1) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : k) ≠ 0),
      FiniteDimensional (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) ∧
        (Module.finrank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
            genus (X ↘ Spec (.of k)) + geometricGenus k (X ↘ Spec (.of k)) ↔
          ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
            Stacks.Curves.IsMulticrossSingularity k X x))
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
        (hproj.pullback_snd _) := by
  refine exists_hasSemistableReductionAtMaximalIdeals_of_local ?_ h0CDU ?_ R K c hproj hg
  · intro A L _ _ _ _ _ _ C c _ _ hproj _
    have : IsProper c := hproj.isProper
    open Stacks.HQuasiProjectiveDimensionOne in
    exact exists_isMinimalModel (R := A) c
      (isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
        c (IsCurve.topologicalKrullDim_eq_one (k := L) (f := c)).le) inferInstance
  · intro S hexc p hp hg ℓ _ hℓ hℓk htors
    classical
    obtain ⟨⟨x, hx, -, hxZ⟩, -, -⟩ :=
      S.exists_isRationalPoint_smoothAt_specialFiber_and_genus_eq p hp
    obtain ⟨Z₀, hZ₀⟩ := S.exists_mem_specialFiberComponent x
    have hgcd : Finset.univ.gcd S.specialFiberMultiplicity = 1 := by
      have hdvd : Finset.univ.gcd S.specialFiberMultiplicity ∣ S.specialFiberMultiplicity Z₀ :=
        Finset.gcd_dvd (Finset.mem_univ Z₀)
      rwa [(hxZ Z₀ hZ₀).2, Nat.dvd_one] at hdvd
    obtain ⟨h₁, h₂⟩ := S.genus_reduction_le_and_lt_of_not_hasExceptionalCurveOfFirstKind hexc hgcd
      (S.isIso_globalSections_reduction_specialFiber x hx)
    let e := (Fintype.equivFin (irreducibleComponents S.specialFiber)).symm
    exact S.isAtWorstNodalOfRelativeDimensionOne_of_picardTorsion_local h0CE6 h0C20 h0C20eq _ e
      (S.isMinimal_associatedNumericalType_of_not_hasExceptionalCurveOfFirstKind hexc _ e) h₁
      (fun heq => by_contra fun hnr => (h₂ hnr).ne heq) p hp hg ℓ hℓ hℓk
      htors

end Stacks.Models

end
