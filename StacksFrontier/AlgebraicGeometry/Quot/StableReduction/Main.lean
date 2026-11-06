module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.Unconditional
public import StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.Existence
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing
public import StacksFrontier.AlgebraicGeometry.Size.AlgebraicExtension

/-!
# The stable reduction theorem

[Stacks, Tag 0E98] ([DM, Corollary 2.7]): let `R` be a discrete valuation ring with fraction field
`K` and let `C` be a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` and genus `g ≥ 2`.
Then

1. there is an extension of discrete valuation rings `R ⊆ R'` inducing a finite separable
   extension `K'/K` of fraction fields and a stable family of curves `Y ⟶ Spec R'` of genus `g`
   with `Y_{K'} ≅ C_{K'}` over `K'`, and
2. there is a finite separable extension `L/K` and a stable family of curves `Y ⟶ Spec A` of genus
   `g`, `A ⊆ L` the integral closure of `R` in `L`, with `Y_L ≅ C_L` over `L`.

## Main results

* `Stacks.Models.stableReduction`: **Tag 0E98**, both parts.

## Implementation notes

A stable family of curves of genus `g` over `Spec R'` given by a morphism of schemes is
`AlgebraicGeometry.IsStableFamilyOfSchemesOfGenus` (Stacks 0E75, 0E78) relative to a big fppf
site `B` containing `Spec R`; the conclusion records that `B` contains `Spec R'`, resp. `Spec A`.

The proof is the source's. Part (1): by the semistable reduction theorem (Stacks 0CDN,
`Stacks.Models.semistableReduction`) `C_{K'}` has semistable reduction over a discrete valuation
ring `R'` dominating `R`; a semistable model of a curve of genus `g ≥ 2` is contracted to a stable
one (Stacks 0E8D, `Stacks.Models.exists_stableModel_of_hasSemistableReduction`), and a family of
schemes whose fibres are stable of genus `g` is a stable family of genus `g`
(`AlgebraicGeometry.isStableFamilyOfSchemesOfGenus_of_forall_isStableFibreOfGenus`). Part (2): for
the extension `L/K` of part (3) of Stacks 0CDN the curve `C_L` has semistable reduction over every
localization `A_𝔪`, which gives stable models over the `A_𝔪`; these glue over the semi-local
Dedekind domain `A` (`Stacks.Models.exists_family_of_forall_isLocalization_atPrime`, the argument
the source gives via Stacks 0E8Z).

## References

* [Stacks Project, Tag 0E98](https://stacks.math.columbia.edu/tag/0E98)
* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
* [Stacks Project, Tag 0E8D](https://stacks.math.columbia.edu/tag/0E8D)
* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 09E8](https://stacks.math.columbia.edu/tag/09E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A big fppf site containing the spectrum of a domain `R` contains the spectrum of every domain
`R'` with an `R`-algebra embedding into an algebraic extension `K'` of the fraction field of
`R`. -/
theorem _root_.AlgebraicGeometry.BigFppfSite.contains_spec_of_algebra_of_isFractionRing
    (B : BigFppfSite.{u}) (K' : Type u) [Field K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [Algebra.IsAlgebraic K K'] (R' : Type u) [CommRing R'] [Algebra R' K']
    [IsFractionRing R' K'] (hR : B.Contains (Spec (.of R))) : B.Contains (Spec (.of R')) := by
  have hκ := B.aleph0_lt_cutoff
  have : Module.IsTorsionFree R K' := .trans_faithfulSMul R K K'
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R K' := .trans R K K'
  refine (schemeSizeBelow_spec_iff hκ R').2 ?_
  calc Cardinal.mk R' ≤ Cardinal.mk K' :=
        Cardinal.mk_le_of_injective (IsFractionRing.injective R' K')
    _ ≤ max (Cardinal.mk R) Cardinal.aleph0 := Cardinal.mk_le_max_of_isAlgebraic R K'
    _ < B.cutoff := max_lt ((schemeSizeBelow_spec_iff hκ R).1 hR) hκ

/-- The integral closure `A` of a discrete valuation ring `R` in a finite separable extension `L`
of its fraction field has finitely many maximal ideals (Stacks 09E8). -/
theorem finite_setOf_isMaximal_integralClosure (R K L : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : {m : Ideal (integralClosure R L) | m.IsMaximal}.Finite := by
  have : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  refine (Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal R)).subset
    fun m (hm : m.IsMaximal) => ⟨hm.isPrime, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m)).symm

/-- The localization of the integral closure `A` of a discrete valuation ring `R` in a finite
separable extension `L` of its fraction field at a maximal ideal `𝔪` is a discrete valuation ring
with fraction field `L` (Stacks 09E8). -/
theorem exists_isDiscreteValuationRing_isLocalization_atPrime (R K L : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (m : Ideal (integralClosure R L)) [m.IsMaximal] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra (integralClosure R L) A') (_ : IsLocalization.AtPrime A' m) (_ : Algebra A' L)
      (_ : IsFractionRing A' L), IsScalarTower (integralClosure R L) A' L := by
  have : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  have : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  have hinjR : Function.Injective (algebraMap R (integralClosure R L)) := by
    intro a b hab
    have := congrArg (algebraMap (integralClosure R L) L) hab
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K L] at this
    exact IsFractionRing.injective R K ((algebraMap K L).injective this)
  have hnf : ¬ IsField (integralClosure R L) := fun hF =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinjR hF)
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField ‹_› hnf
  set A := Localization.AtPrime m
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure R L) hm0
      A
  have hunit : ∀ y : m.primeCompl, IsUnit (algebraMap (integralClosure R L) L y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h0 =>
      y.2 (by
        rw [(IsFractionRing.injective (integralClosure R L) L).eq_iff.mp
          (h0.trans (map_zero _).symm)]
        exact m.zero_mem)
  let : Algebra A L := (IsLocalization.lift (M := m.primeCompl) (S := A) hunit).toAlgebra
  have : IsScalarTower (integralClosure R L) A L := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := m.primeCompl) (S := A) hunit x).symm
  have : IsFractionRing A L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl A L
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- The base change of a stable family along an isomorphism of its generic fibre: the generic
fibre of a model `p : Y ⟶ Spec R'` of `C'` is isomorphic over `K'` to `C'`. -/
theorem nonempty_over_iso_of_isModel {R' K' : Type u} [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    {C' Y : Scheme.{u}} (c' : C' ⟶ Spec (.of K')) (p : Y ⟶ Spec (.of R'))
    (e : C' ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R' K')))) (h : IsModel c' p e) :
    Nonempty (Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R' K')))) ≅
      Over.mk c') :=
  ⟨Over.isoMk e.symm (by simp [← h.2.2.2])⟩

/-- **Stacks Project, Tag 0E98** (stable reduction, [DM, Corollary 2.7]). Let `R` be a discrete
valuation ring with fraction field `K` and let `C` be a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K` and genus `g ≥ 2`. Let `B` be a big fppf site containing `Spec R`. Then

1. there exist an extension of discrete valuation rings `R ⊆ R'` inducing a finite separable
   extension of fraction fields `K'/K` and a stable family of curves `Y ⟶ Spec R'` of genus `g`
   with `Y_{K'} ≅ C_{K'}` over `K'`, and
2. there exist a finite separable extension `L/K` and a stable family of curves `Y ⟶ Spec A` of
   genus `g`, where `A ⊆ L` is the integral closure of `R` in `L`, such that `Y_L ≅ C_L` over
   `L`. -/
@[stacks 0E98]
theorem stableReduction (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hproj : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hg : 2 ≤ genus c) (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) :
    (∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K'), FiniteDimensional K K' ∧ Algebra.IsSeparable K K' ∧
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
        (_ : Algebra R' K') (_ : IsFractionRing R' K') (_ : Algebra R R')
        (_ : IsScalarTower R R' K'), IsLocalHom (algebraMap R R') ∧
        ∃ (hR' : B.Contains (Spec (.of R'))) (Y : Scheme.{u}) (p : Y ⟶ Spec (.of R')),
          IsStableFamilyOfSchemesOfGenus B hZ (genus c) p hR' ∧
          Nonempty (Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R' K')))) ≅
            Over.mk (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K')))))) ∧
    (∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L), FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
      ∃ (hA : B.Contains (Spec (.of (integralClosure R L)))) (Y : Scheme.{u})
        (p : Y ⟶ Spec (.of (integralClosure R L))),
        IsStableFamilyOfSchemesOfGenus B hZ (genus c) p hA ∧
        Nonempty (Over.mk (pullback.snd p
            (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R L) L)))) ≅
          Over.mk (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K L)))))) := by
  have : IsProper c := hproj.isProper
  obtain ⟨h1, -, -, h3⟩ := semistableReduction R K c hproj
  constructor
  · obtain ⟨K', _, _, _, _, hfd, hsep, R', _, _, _, _, _, _, _, hloc, hss⟩ := h1
    have hgen := (isCurve_isProjectiveVariety_genus_pullback c K').2.2
    obtain ⟨Y, p, e, hmod, hprop, hnod, hfib⟩ :=
      exists_stableModel_of_hasSemistableReduction R' K' _ (hproj.pullback_snd _)
        (hgen ▸ hg) hss
    have : Algebra.IsAlgebraic K K' := Algebra.IsAlgebraic.of_finite K K'
    have hR' : B.Contains (Spec (.of R')) :=
      BigFppfSite.contains_spec_of_algebra_of_isFractionRing (K := K) B K' R' hR
    have := hmod.1
    have := hmod.2.1
    have : LocallyOfFinitePresentation p := inferInstance
    exact ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, hfd, hsep, R',
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hloc, hR', Y, p,
      isStableFamilyOfSchemesOfGenus_of_forall_isStableFibreOfGenus B hZ p hR' hnod _
        fun s => hgen ▸ hfib s,
      nonempty_over_iso_of_isModel _ p e hmod⟩
  · obtain ⟨L, _, _, _, _, hfd, hsep, -, hssm⟩ := h3 hg
    have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    have hgen := (isCurve_isProjectiveVariety_genus_pullback c L).2.2
    have : IsFractionRing (integralClosure R L) L :=
      integralClosure.isFractionRing_of_finite_extension K L
    have : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
    have hA : B.Contains (Spec (.of (integralClosure R L))) :=
      BigFppfSite.contains_spec_subalgebra_of_fractionRing B R K L _ hR
    obtain ⟨Y, p, e, he, hprop, hflat, hlfp, hnod, hfib⟩ :=
      exists_family_of_forall_isLocalization_atPrime (integralClosure R L) L
        (finite_setOf_isMaximal_integralClosure R K L) _ (genus c) fun m _ => by
          obtain ⟨A', _, _, _, _, _, _, _, _⟩ :=
            exists_isDiscreteValuationRing_isLocalization_atPrime R K L m
          obtain ⟨Y, p, e, hmod, hprop, hnod, hfib⟩ :=
            exists_stableModel_of_hasSemistableReduction A' L _ (hproj.pullback_snd _)
              (hgen ▸ hg) (hssm m A')
          have := hmod.1
          have := hmod.2.1
          exact ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
            Y, p, e, hmod.2.2.2, hprop, hmod.1, inferInstance, hnod, fun s => hgen ▸ hfib s⟩
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hfd, hsep, hA, Y, p,
      isStableFamilyOfSchemesOfGenus_of_forall_isStableFibreOfGenus B hZ p hA hnod _ hfib,
      ⟨Over.isoMk e.symm (by simp [← he])⟩⟩

end Stacks.Models

end
