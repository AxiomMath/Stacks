module

public import Mathlib.RingTheory.Localization.Integral
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.GorensteinConic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.Characterization
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SmoothGeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveProjectiveSmoothPoint
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniResiduePointDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import StacksFrontier.RingTheory.DiscreteValuationRing.SeparableQuadraticExtension

/-!
# Semistable reduction in genus zero

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a smooth projective
curve over `K` with `H⁰(C, 𝒪_C) = K` and of genus `0`. Section 0CDK of the Stacks project argues:
`C` is a plane conic ([Stacks, Tag 0C6N]), so it has a closed point whose residue field is a
separable extension of `K` of degree at most `2` ([Stacks, Tag 0CCU]); over that extension `K'`
the curve has a rational point, hence `C_{K'} ≅ 𝐏¹_{K'}` ([Stacks, Tag 0C6U]), and `𝐏¹_{R'}`
over the integral closure `R'` of `R` in `K'` is a smooth projective model.

This file proves the steps of that argument which do not use Tags 0C6N and 0C6U, the argument
itself from the statements of those two tags, and then part (1) of [Stacks, Tag 0CDN] outright
from `AlgebraicGeometry.exists_planeCurveData_deg_two_of_isGorenstein`
(Tag 0C6N; a smooth curve is Gorenstein) and
`AlgebraicGeometry.ProjectiveLineCriterion.nonempty_iso_projectiveLine_of_section` (Tag 0C6U).

## Main results

* `AlgebraicGeometry.SemistableReduction.exists_section_pullback_of_comp_eq`: a `K`-morphism
  `Spec L ⟶ C` is a section of the base change `C_L ⟶ Spec L`.
* `AlgebraicGeometry.SemistableReduction.exists_quadratic_point_of_planeConic`: a smooth plane
  conic over `K` has a point over a separable extension of `K` of degree exactly `2`.
* `AlgebraicGeometry.SemistableReduction.projectiveSpace_integralClosure`: for a finite separable
  `K'/K`, the projective line over the integral closure `R'` of `R` in `K'` is smooth and
  projective over `R'`, `K'` is the fraction field of `R'`, and the generic fibre of `𝐏¹_{R'}` is
  `𝐏¹_{K'}` over `K'`.
* `hasGoodReduction_and_hasSemistableReduction_of_iso_projectiveLine`
  and `hasSemistableReductionAtMaximalIdeals_of_iso_projectiveLine`:
  a curve isomorphic to `𝐏¹_{K'}` has good and semistable reduction over every discrete valuation
  ring with fraction field `K'`, in particular over every `R'_𝔪`, with model `𝐏¹`.
* `AlgebraicGeometry.SemistableReduction.genusZero_splitting_of_planeConic_of_projectiveLine`:
  part (1) of [Stacks, Tag 0CDN], from the statements of Tags 0C6N and 0C6U.
* `AlgebraicGeometry.SemistableReduction.genusZero_splitting`: **part (1) of
  [Stacks, Tag 0CDN]**.

## Implementation notes

The source finds an extension of degree *at most* `2` with a rational point, while part (1) of
Tag 0CDN asks for degree *exactly* `2`. When the point is already rational any extension splits
the curve, and the fraction field of a discrete valuation ring always has a separable quadratic
extension (`IsDiscreteValuationRing.exists_finiteDimensional_isSeparable_finrank_eq_two`).

The extension `K'` is returned with an `R`-algebra structure compatible with `K → K'`; the
integral closure `R'` is `integralClosure R K'`, and the generic fibre of `𝐏¹_{R'}` is its base
change along `Spec K' ⟶ Spec R'`.

## References

* [Stacks Project, Tag 0CDK](https://stacks.math.columbia.edu/tag/0CDK)
* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
* [Stacks Project, Tag 0CCU](https://stacks.math.columbia.edu/tag/0CCU)
* [Stacks Project, Tag 0C6N](https://stacks.math.columbia.edu/tag/0C6N)
* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 09E8](https://stacks.math.columbia.edu/tag/09E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj (PlaneCurveData)
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)

universe u

namespace AlgebraicGeometry.SemistableReduction

/-- **A point over `L` gives a section of the base change to `L`.** A morphism `t : Spec L ⟶ X`
over `Spec K` lifts to a section of the projection `X_L ⟶ Spec L`. -/
theorem exists_section_pullback_of_comp_eq {K L : Type u} [Field K] [Field L] [Algebra K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (t : Spec (.of L) ⟶ X)
    (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ s : Spec (.of L) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))),
      s ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L))) = 𝟙 _ :=
  ⟨pullback.lift t (𝟙 _) (by rw [ht, Category.id_comp]), pullback.lift_snd _ _ _⟩

/-- **A smooth plane conic has a point over a separable quadratic extension.** Let `R` be a
discrete valuation ring with fraction field `K`, and let `X` be smooth over `K` and isomorphic
over `K` to a plane curve `Z ⊆ 𝐏²_K` of degree `2`. By [Stacks, Tag 0CCU] (the field `K` is
infinite) `Z` has a closed point whose residue field `κ` is separable over `K` of degree at most
`2`; if `[κ : K] = 2` take `L = κ`, and otherwise `κ = K` and `L` is any separable quadratic
extension of `K`. Then `X` has an `L`-point over `K`. -/
theorem exists_quadratic_point_of_planeConic (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] (P : PlaneCurveData K)
    (hdeg : P.deg = 2) (e : X ≅ P.Z) (he : e.hom ≫ P.toSpec = f) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧ Module.finrank K L = 2 ∧
        ∃ t : Spec (.of L) ⟶ X, t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  have := P.isClosedImmersion
  have := P.nonempty
  have hKinf : Infinite K := by
    have : Infinite R := by
      by_contra h
      have : Finite R := not_infinite_iff_finite.mp h
      exact IsDiscreteValuationRing.not_isField R (Finite.isField_of_domain R)
    exact Infinite.of_injective (algebraMap R K) (IsFractionRing.injective R K)
  have hfe : e.inv ≫ f = P.i ≫ projToSpecCoeff K 2 := by
    rw [← he, Iso.inv_hom_id_assoc]; rfl
  have hsm : Smooth (P.i ≫ projToSpecCoeff K 2) := by
    rw [← hfe]
    infer_instance
  obtain ⟨z₀⟩ := P.nonempty
  obtain ⟨z, -, -, hz⟩ :=
    Stacks.Curves.exists_isClosed_smoothAt_isSeparable_finrank_le_totalDegree (k := K) P.i
      (d := P.deg) P.F P.F_ne_zero (by rw [smul_eq_mul, mul_one]; exact P.isHomogeneous)
      P.span_eq ⟨z₀, InfinitesimalLifting.smoothAt_of_smooth _ z₀⟩
  set M := P.Z.residueField z
  let : Algebra K M :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (P.i ≫ projToSpecCoeff K 2).appTop ≫
      P.Z.Γevaluation z).hom.toAlgebra
  obtain ⟨hMfin, hMsep, hMdeg⟩ := hz
  have hMdeg' : Module.finrank K M ≤ 2 := hMdeg.trans (by rw [← P.deg_eq_totalDegree, hdeg])
  have hMpos : 0 < Module.finrank K M := Module.finrank_pos
  have hpt : P.Z.fromSpecResidueField z ≫ P.i ≫ projToSpecCoeff K 2 =
      Spec.map (CommRingCat.ofHom (algebraMap K M)) :=
    fromSpecResidueField_comp_eq_Spec_map_algebraMap K (P.i ≫ projToSpecCoeff K 2) z
  -- an extension `L` of degree two together with a `K`-embedding of `M`
  obtain ⟨L, _, _, hLfin, hLsep, hLdeg, φ, hφ⟩ :
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
        FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧ Module.finrank K L = 2 ∧
          ∃ φ : M →+* L, φ.comp (algebraMap K M) = algebraMap K L := by
    rcases (by omega : Module.finrank K M = 1 ∨ Module.finrank K M = 2) with h1 | h2
    · obtain ⟨L, _, _, hLfin, hLsep, hLdeg⟩ :=
        IsDiscreteValuationRing.exists_finiteDimensional_isSeparable_finrank_eq_two R K
      have hbij : Function.Bijective (algebraMap K M) :=
        Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1
      let eKM : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) hbij
      refine ⟨L, inferInstance, inferInstance, hLfin, hLsep, hLdeg,
        (algebraMap K L).comp eKM.symm.toRingHom, ?_⟩
      ext a
      show algebraMap K L (eKM.symm (eKM a)) = algebraMap K L a
      rw [RingEquiv.symm_apply_apply]
    · exact ⟨M, inferInstance, inferInstance, hMfin, hMsep, h2, RingHom.id M, by simp⟩
  refine ⟨L, inferInstance, inferInstance, hLfin, hLsep, hLdeg,
    Spec.map (CommRingCat.ofHom φ) ≫ P.Z.fromSpecResidueField z ≫ e.inv, ?_⟩
  rw [Category.assoc, Category.assoc, hfe, hpt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

/-- The inverse of `𝐏¹_S ×_S T ≅ 𝐏¹_T` is compatible with the projections to `T`. -/
private theorem projectiveSpaceOverBaseChangeIso_inv_comp_snd {S T : Scheme.{u}} (g : T ⟶ S) :
    (projectiveSpaceOverBaseChangeIso 1 g).inv ≫ pullback.snd (projectiveSpaceOver 1 S ↘ S) g =
      projectiveSpaceOver 1 T ↘ T := by
  rw [Iso.inv_comp_eq]
  exact (projectiveSpaceOverBaseChangeIso_hom_over 1 g).symm

/-- **The model `𝐏¹_{R'}`.** Let `R` be a discrete valuation ring with fraction field `K`, let
`K'/K` be a finite extension and `R'` the integral closure of `R` in `K'`. Then `K'` is the
fraction field of `R'`, the projective line `𝐏¹_{R'}` is smooth and projective over `R'`, and its
generic fibre is `𝐏¹_{K'}` over `K'`. -/
theorem projectiveSpace_integralClosure (R K K' : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [FiniteDimensional K K'] :
    IsFractionRing (integralClosure R K') K' ∧
      Smooth (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
        Spec (.of (integralClosure R K'))) ∧
      IsProjective (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
        Spec (.of (integralClosure R K'))) ∧
      Nonempty (Over.mk (projectiveSpaceOver 1 (Spec (.of K')) ↘ Spec (.of K')) ≅
        Over.mk (pullback.snd (C := Scheme.{u})
          (projectiveSpaceOver 1 (Spec (.of (integralClosure R K'))) ↘
            Spec (.of (integralClosure R K')))
          (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K'))))) :=
  ⟨integralClosure.isFractionRing_of_finite_extension K K', inferInstance,
    IsProjectiveMorphism.isProjective (isProjectiveMorphism_projectiveSpaceOver 1 _),
    ⟨Over.isoMk (projectiveSpaceOverBaseChangeIso 1 _).symm
      (projectiveSpaceOverBaseChangeIso_inv_comp_snd _)⟩⟩

/-- **A curve which is the projective line has good and semistable reduction over every
discrete valuation ring with the right fraction field.** Let `A` be a discrete valuation ring
with fraction field `K'` and let `C'` be a smooth projective curve over `K'` with
`H⁰(C', 𝒪) = K'` which is isomorphic over `K'` to `𝐏¹_{K'}`. Then `𝐏¹_A` is a proper smooth
model of `C'` over `A`, and it is at-worst-nodal of relative dimension one, being smooth of
relative dimension one ([Stacks, Tag 0CD7]). This is the last paragraph of section 0CDK. -/
theorem hasGoodReduction_and_hasSemistableReduction_of_iso_projectiveLine (A K' : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K'] [Algebra A K']
    [IsFractionRing A K'] {C' : Scheme.{u}} (c' : C' ⟶ Spec (.of K')) [IsCurve K' c']
    [Smooth c'] (hproj : IsProjective c') [IsIso ((Scheme.ΓSpecIso (.of K')).inv ≫ c'.appTop)]
    (e : Over.mk c' ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of K')) ↘ Spec (.of K'))) :
    Stacks.Models.HasGoodReduction A c' hproj ∧
      Stacks.Models.HasSemistableReduction A c' hproj := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap A K'))
  set p := projectiveSpaceOver 1 (Spec (.of A)) ↘ Spec (.of A)
  let e' : C' ≅ pullback p g :=
    (Over.forget _).mapIso e ≪≫ (projectiveSpaceOverBaseChangeIso 1 g).symm
  have he' : e'.hom ≫ pullback.snd p g = c' := by
    simp only [e', Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Iso.symm_hom,
      Category.assoc]
    rw [projectiveSpaceOverBaseChangeIso_inv_comp_snd g]
    exact Over.w e.hom
  have hmodel : Stacks.Models.IsModel (R := A) c' p e' :=
    ⟨inferInstance, inferInstance, inferInstance, he'⟩
  exact ⟨⟨_, p, e', hmodel, inferInstance, inferInstance⟩,
    ⟨_, p, e', hmodel, inferInstance,
      isAtWorstNodalOfRelativeDimensionOne_of_smoothOfRelativeDimension p⟩⟩

/-- **A curve which is the projective line has semistable reduction over every localization of
the integral closure at a maximal ideal.** For any ring `R` with an algebra map to `K'`, a smooth
projective curve over `K'` with `H⁰ = K'` and isomorphic to `𝐏¹_{K'}` has semistable reduction
over `R'_𝔪` for every maximal ideal `𝔪` of the integral closure `R'` of `R` in `K'`. -/
theorem hasSemistableReductionAtMaximalIdeals_of_iso_projectiveLine (R K' : Type u)
    [CommRing R] [Field K'] [Algebra R K'] {C' : Scheme.{u}} (c' : C' ⟶ Spec (.of K'))
    [IsCurve K' c'] [Smooth c'] (hproj : IsProjective c')
    [IsIso ((Scheme.ΓSpecIso (.of K')).inv ≫ c'.appTop)]
    (e : Over.mk c' ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of K')) ↘ Spec (.of K'))) :
    Stacks.Models.HasSemistableReductionAtMaximalIdeals R K' c' hproj :=
  fun _ _ A _ _ _ _ _ _ _ _ =>
    (hasGoodReduction_and_hasSemistableReduction_of_iso_projectiveLine A K' c' hproj e).2

/-- **Part (1) of [Stacks, Tag 0CDN], from the statements of Tags 0C6N and 0C6U.** Let `R` be a
discrete valuation ring with fraction field `K` and `C` a smooth projective curve over `K` with
`H⁰(C, 𝒪_C) = K` and of genus `0`. Assume that every smooth proper genus-zero curve with constant
global functions over a field is a plane conic (`hconic`, the statement of Tag 0C6N for such
curves) and that such a curve with a rational point is the projective line (`hline`, a case of
Tag 0C6U). Then there is a separable extension `K'/K` of degree `2` with `C_{K'} ≅ 𝐏¹_{K'}`, and
`C_{K'}` is the generic fibre of the smooth projective `𝐏¹_{R'}` over the integral closure `R'`
of `R` in `K'`. -/
theorem genusZero_splitting_of_planeConic_of_projectiveLine
    (hconic : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
      [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)],
      genus f = 0 → ∃ P : PlaneCurveData k, P.deg = 2 ∧ ∃ e : X ≅ P.Z, e.hom ≫ P.toSpec = f)
    (hline : ∀ (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f]
      [Smooth f] [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)],
      genus f = 0 → (∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _) →
        Nonempty (Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))))
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hgenus : genus c = 0) :
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
          (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K'))))) := by
  have : IsProper c := hc.isProper
  obtain ⟨P, hdeg, e, he⟩ := hconic K c hgenus
  obtain ⟨K', _, _, hfin, hsep, hdeg2, t, ht⟩ :=
    exists_quadratic_point_of_planeConic R K c P hdeg e he
  let : Algebra R K' := ((algebraMap K K').comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgenus' := genus_baseChange K K' _ _ c (IsPullback.of_hasPullback _ _)
  obtain ⟨hfrac, hsmooth, hproj, ⟨eP⟩⟩ := projectiveSpace_integralClosure R K K'
  have ⟨eC⟩ := hline K' (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (hgenus'.trans hgenus) (exists_section_pullback_of_comp_eq c t ht)
  exact ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, hfin, hsep, hdeg2,
    ⟨eC⟩, hfrac, hsmooth, hproj, ⟨eC ≪≫ eP⟩⟩

/-- **Stacks Project, Tag 0CDN, part (1).** Let `R` be a discrete valuation ring with fraction
field `K` and `C` a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K`. If the genus of `C`
is zero, then there exists a separable extension `K'/K` of degree `2` such that
`C_{K'} ≅ 𝐏¹_{K'}`, and hence `C_{K'}` is isomorphic to the generic fibre of the smooth projective
scheme `𝐏¹_{R'}` over the integral closure `R'` of `R` in `K'` (whose fraction field is `K'`).

The extension `K'` is returned with an `R`-algebra structure compatible with `K ⟶ K'`, the
integral closure is `integralClosure R K'`, and the generic fibre is the base change of
`𝐏¹_{R'} ⟶ Spec R'` along `Spec K' ⟶ Spec R'`; both isomorphisms are over `K'`. -/
@[stacks 0CDN "(1), genus zero"]
theorem genusZero_splitting (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (hgenus : genus c = 0) :
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
          (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K'))))) := by
  refine genusZero_splitting_of_planeConic_of_projectiveLine ?_ ?_ R K c hc hgenus
  · intro k _ X f _ _ _ _ hg
    have := ProjectiveLineCriterion.isGorenstein_of_smooth f
    exact AlgebraicGeometry.exists_planeCurveData_deg_two_of_isGorenstein f hg
  · intro k _ X f _ _ _ _ hg hs
    obtain ⟨s, hs⟩ := hs
    exact ProjectiveLineCriterion.nonempty_iso_projectiveLine_of_section k f hg s hs

end AlgebraicGeometry.SemistableReduction

end
