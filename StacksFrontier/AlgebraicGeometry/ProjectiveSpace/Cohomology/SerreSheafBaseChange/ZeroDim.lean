module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafBaseChange.TwistBaseChange

/-!
# Multiplication and base change on the cohomology of `ℙ⁰`

Equation [Stacks, Tag 01XU] fails for `n = 0` over a nonzero ring; the statements of
[Stacks, Tag 01XV] for `n = 0`, through [Stacks, Tag 01XT].
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [local instance 5000] IsGrothendieckAbelian.enoughInjectives
attribute [local instance 5000]
  instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover

namespace Stacks.ProjectiveSpace.Cohomology

open Stacks.ProjectiveCohomology Stacks.Cohomology.CechSheaf
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)

/-! ### Projective space of dimension zero -/

open Stacks.Homology.HomologyRep in
/-- A degree-zero class of the monomial Čech complex of `ℙ⁰_R` represented by a cochain is sent
by the identification with the chart inverting `T₀` to the value of that cochain. -/
theorem rep_zeroDimHomologyIso (R : Type u) [CommRing R] {d : ℤ}
    {h : (laurentCechComplex R 0 d).homology 0} {v : (laurentCechComplex R 0 d).X 0}
    (H : Rep (laurentCechComplex R 0 d) 0 h v) :
    ConcreteCategory.hom (zeroDimHomologyIso R d).hom h = zeroDimCochainEquiv R d v := by
  obtain ⟨z, rfl, rfl⟩ := H
  have e1 : ConcreteCategory.hom ((laurentCechComplex R 0 d).isoHomologyπ 0 0 (by simp)
      ((laurentCechComplex R 0 d).shape 0 0 (by simp))).inv
      (ConcreteCategory.hom ((laurentCechComplex R 0 d).homologyπ 0) z) = z :=
    Iso.hom_inv_id_apply ((laurentCechComplex R 0 d).isoHomologyπ 0 0 (by simp)
      ((laurentCechComplex R 0 d).shape 0 0 (by simp))) z
  have e2 := ConcreteCategory.congr_hom
    ((laurentCechComplex R 0 d).sc' 0 0 (0 + 1)).moduleCatCyclesIso_hom_i
    (ConcreteCategory.hom ((laurentCechComplex R 0 d).cyclesIsoSc' 0 0 (0 + 1) (by simp)
      (by simp)).hom z)
  have e3 := ConcreteCategory.congr_hom
    ((laurentCechComplex R 0 d).cyclesIsoSc'_hom_iCycles 0 0 (0 + 1) (by simp) (by simp)) z
  have e4 : ConcreteCategory.hom
      ((laurentCechComplex R 0 d).sc' 0 0 (0 + 1)).moduleCatLeftHomologyData.i
      (ConcreteCategory.hom ((laurentCechComplex R 0 d).sc' 0 0 (0 + 1)).moduleCatCyclesIso.hom
      (ConcreteCategory.hom ((laurentCechComplex R 0 d).cyclesIsoSc' 0 0 (0 + 1) (by simp)
        (by simp)).hom z)) =
      ConcreteCategory.hom ((laurentCechComplex R 0 d).iCycles 0) z :=
    ((ConcreteCategory.comp_apply _ _ _).symm.trans e2).trans
      ((ConcreteCategory.comp_apply _ _ _).symm.trans e3)
  have e5 : ConcreteCategory.hom (zeroDimHomologyIso R d).hom
      (ConcreteCategory.hom ((laurentCechComplex R 0 d).homologyπ 0) z) =
      zeroDimCochainEquiv R d (ConcreteCategory.hom
        ((laurentCechComplex R 0 d).sc' 0 0 (0 + 1)).moduleCatLeftHomologyData.i
        (ConcreteCategory.hom ((laurentCechComplex R 0 d).sc' 0 0 (0 + 1)).moduleCatCyclesIso.hom
          (ConcreteCategory.hom ((laurentCechComplex R 0 d).cyclesIsoSc' 0 0 (0 + 1) (by simp)
            (by simp)).hom (ConcreteCategory.hom ((laurentCechComplex R 0 d).isoHomologyπ 0 0
              (by simp) ((laurentCechComplex R 0 d).shape 0 0 (by simp))).inv
              (ConcreteCategory.hom ((laurentCechComplex R 0 d).homologyπ 0) z))))) := rfl
  refine e5.trans ?_
  rw [e1, e4]

open Stacks.Homology.HomologyRep in
/-- **Multiplication by a homogeneous polynomial on `H⁰(ℙ⁰_R, 𝒪(d))`.** Through the
identification of `H⁰(ℙ⁰_R, 𝒪(d))` with the degree-`d` part of `R[T₀, T₀⁻¹]`, the map induced by
multiplication by `f` is multiplication by `f`. -/
theorem twistCohomologyIsoChartUnivZeroDim_mul {m : ℕ} {d e : ℤ}
    (f : MvPolynomial (Fin (0 + 1)) R) (hf : f.IsHomogeneous m) (hde : d + m = e)
    (x : twistCohomology R 0 d 0) :
    ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R e).hom
        (ConcreteCategory.hom ((ModuleCat.restrictScalars.{u} (coeffScalar R 0)).map
          (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R 0))
            ⊤).rightDerived 0).map (twistScalarSheafMap (polyGrading R 0) m d e
              (by omega) ⟨f, (MvPolynomial.mem_homogeneousSubmodule m f).2 hf⟩))) x) =
      chartMul (chartOfHomogeneous R 0 f hf) hde Set.univ
        (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R d).hom x) := by
  rw [homogeneous_eq_polyOfLaurent R 0 f hf]
  have hsq := ConcreteCategory.congr_hom
    (twistCohomologyIsoLaurentHomology_twistScalarSheafMap R 0 (chartOfHomogeneous R 0 f hf) hde
      (by omega) 0) x
  obtain ⟨c, Hc⟩ :=
    exists_rep (ConcreteCategory.hom (twistCohomologyIsoLaurentHomology R 0 d 0).hom x)
  have H' := rep_map (laurentCechComplexMul R 0 (chartOfHomogeneous R 0 f hf) hde) Hc
  have e1 := rep_zeroDimHomologyIso R H'
  have e2 := rep_zeroDimHomologyIso R Hc
  refine ((ConcreteCategory.comp_apply _ _ _).trans
    (congrArg (ConcreteCategory.hom (zeroDimHomologyIso R e).hom)
      (((ConcreteCategory.comp_apply _ _ _).symm.trans hsq).trans
        (ConcreteCategory.comp_apply _ _ _)))).trans (e1.trans ?_)
  refine Eq.trans ?_ (congrArg (chartMul (chartOfHomogeneous R 0 f hf) hde Set.univ)
    ((ConcreteCategory.comp_apply _ _ _).trans e2).symm)
  exact Subtype.ext rfl

open Stacks.Homology.HomologyRep in
/-- **Base change on `H⁰(ℙ⁰_R, 𝒪(d))`.** Through the identifications of `H⁰(ℙ⁰, 𝒪(d))` with the
degree-`d` parts of `R[T₀, T₀⁻¹]` and of `S[T₀, T₀⁻¹]`, the base-change map is the coefficientwise
base change. -/
theorem twistCohomologyIsoChartUnivZeroDim_baseChange (d : ℤ) (x : twistCohomology R 0 d 0) :
    ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim S d).hom
        (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap 0 φ)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S 0) d)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R 0) d)
          (twistBaseChangeFMap φ 0 d) 0) x) =
      baseChangeChart φ 0 d Set.univ
        (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R d).hom x) := by
  obtain ⟨c, HR, HS⟩ := exists_rep_twistBaseChangeCohomology φ 0 d 0 x
  refine ((ConcreteCategory.comp_apply _ _ _).trans (rep_zeroDimHomologyIso S HS)).trans ?_
  refine Eq.trans ?_ (congrArg (baseChangeChart φ 0 d Set.univ)
    ((ConcreteCategory.comp_apply _ _ _).trans (rep_zeroDimHomologyIso R HR)).symm)
  exact Subtype.ext rfl

/-- The degree-`d` part of `R[T₀, T₀⁻¹]` is nonzero over a nonzero ring. -/
theorem nontrivial_twistChart_univ_zeroDim (R : Type u) [CommRing R] [Nontrivial R] (d : ℤ) :
    Nontrivial (twistChart R 0 d (Set.univ : Set (Fin (0 + 1)))) := by
  refine ⟨⟨⟨Finsupp.single (fun _ => d) 1, Finsupp.single_mem_supported R _ ?_⟩, 0, ?_⟩⟩
  · exact mem_laurentMonomials.2 ⟨by simp, fun i hi => absurd (Set.mem_univ i) hi⟩
  · intro h
    have h' := congrArg (fun w : twistChart R 0 d (Set.univ : Set (Fin (0 + 1))) =>
      (w : (Fin (0 + 1) → ℤ) →₀ R) (fun _ => d)) h
    simp at h'

/-- `H⁰(ℙ⁰_R, 𝒪(d))` is nonzero over a nonzero ring, for every `d`. -/
theorem not_subsingleton_twistCohomology_zeroDim (R : Type u) [CommRing R] [Nontrivial R]
    (d : ℤ) : ¬ Subsingleton (twistCohomology R 0 d 0) := by
  intro h
  have := nontrivial_twistChart_univ_zeroDim R d
  have := (twistCohomologyIsoChartUnivZeroDim R d).symm.toLinearEquiv.toEquiv.subsingleton
  exact not_subsingleton _ this

/-- The degree-`d` part of `R[T₀]` is trivial for negative `d`. -/
private theorem subsingleton_twistChart_empty_zeroDim (R : Type u) [CommRing R] {d : ℤ}
    (hd : d < 0) : Subsingleton (twistChart R 0 d (∅ : Set (Fin (0 + 1)))) := by
  rw [twistChart_eq_bot_of_neg 0 hd]
  infer_instance

/-- **The identifications of [Stacks, Equation 01XU] do not exist on `ℙ⁰`.** Over a nonzero ring
`R`, `H⁰(ℙ⁰_R, 𝒪(-1))` is not isomorphic to `(R[T₀])_{-1} = 0`, so the row `q = 0` of the equation
fails at `n = 0`, `d = -1`. -/
theorem not_nonempty_twistCohomology_zeroDim_iso_twistChart_empty (R : Type u) [CommRing R]
    [Nontrivial R] :
    ¬ Nonempty (twistCohomology R 0 (-1) 0 ≅
      ModuleCat.of R (twistChart R 0 (-1) (∅ : Set (Fin (0 + 1))))) := by
  rintro ⟨e⟩
  have := subsingleton_twistChart_empty_zeroDim R (show (-1 : ℤ) < 0 by norm_num)
  exact not_subsingleton_twistCohomology_zeroDim R (-1) e.toLinearEquiv.toEquiv.subsingleton

/-- **The identifications of [Stacks, Equation 01XU] do not exist on `ℙ⁰`.** Over a nonzero ring
`R`, `H⁰(ℙ⁰_R, 𝒪)` is not isomorphic to `Hom_R((R[T₀])_{-1}, R) = 0`, so the row `q = n` of the
equation fails at `n = 0`, `d = 0`. -/
theorem not_nonempty_twistCohomology_zeroDim_iso_dual (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ Nonempty (twistCohomology R 0 0 0 ≅
      ModuleCat.of R
        (twistChart R 0 (-0 - (((0 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (0 + 1))) →ₗ[R] R)) := by
  rintro ⟨e⟩
  have := subsingleton_twistChart_empty_zeroDim R
    (show (-0 - (((0 : ℕ) : ℤ) + 1) : ℤ) < 0 by norm_num)
  exact not_subsingleton_twistCohomology_zeroDim R 0 e.toLinearEquiv.toEquiv.subsingleton

/-- **[Stacks, Tag 01XV] for `n = 0`, multiplication on `H⁰`, corrected.** On `ℙ⁰_R` the two
rows of [Stacks, Equation 01XU] both concern `H⁰` and hold only under the side conditions of
[Stacks, Tag 01XT]. For `d ≥ 0`, through the identification of `H⁰(ℙ⁰_R, 𝒪(d))` with
`(R[T₀])_d`, the map induced by multiplication by `f`, homogeneous of degree `m`, is
multiplication by `f`. -/
@[stacks 01XV "n = 0: multiplication by a homogeneous f on H^0, d ≥ 0, through Tag 01XT"]
theorem zeroDim_degreeZero_mul {m : ℕ} {d e : ℤ} (f : MvPolynomial (Fin (0 + 1)) R)
    (hf : f.IsHomogeneous m) (hde : d + m = e) (hd : 0 ≤ d) (x : twistCohomology R 0 d 0) :
    LinearEquiv.ofEq _ _ (twistChart_univ_eq_empty_zeroDim R (show 0 ≤ e by omega))
        (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R e).hom
          (ConcreteCategory.hom ((ModuleCat.restrictScalars.{u} (coeffScalar R 0)).map
          (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R 0))
            ⊤).rightDerived 0).map (twistScalarSheafMap (polyGrading R 0) m d e
              (by omega) ⟨f, (MvPolynomial.mem_homogeneousSubmodule m f).2 hf⟩))) x)) =
      chartMul (chartOfHomogeneous R 0 f hf) hde ∅
        (LinearEquiv.ofEq _ _ (twistChart_univ_eq_empty_zeroDim R hd)
          (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R d).hom x)) :=
  Subtype.ext ((LinearEquiv.coe_ofEq_apply _ _).trans
    ((congrArg Subtype.val (twistCohomologyIsoChartUnivZeroDim_mul f hf hde x)).trans rfl))

/-- **[Stacks, Tag 01XV] for `n = 0`, multiplication on `Hⁿ`, corrected.** For `d + m < 0`,
through the identification of `H⁰(ℙ⁰_R, 𝒪(d))` with `Hom_R((R[T₀])_{-1-d}, R)` by the residue
pairing, the map induced by multiplication by `f`, homogeneous of degree `m`, is the
contragredient of multiplication by `f`, `(R[T₀])_{-1-(d+m)} ⟶ (R[T₀])_{-1-d}`. -/
@[stacks 01XV "n = 0: multiplication on H^n is the contragredient, d + m < 0, through Tag 01XT"]
theorem zeroDim_degreeTop_mul {m : ℕ} {d e : ℤ} (f : MvPolynomial (Fin (0 + 1)) R)
    (hf : f.IsHomogeneous m) (hde : d + m = e) (he : e < 0) (x : twistCohomology R 0 d 0)
    (h : twistChart R 0 (-e - (((0 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (0 + 1)))) :
    topDualEquiv R 0 e (LinearEquiv.ofEq _ _ (twistChart_univ_eq_negativeTwistPart_zeroDim R he)
        (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R e).hom
          (ConcreteCategory.hom ((ModuleCat.restrictScalars.{u} (coeffScalar R 0)).map
          (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R 0))
            ⊤).rightDerived 0).map (twistScalarSheafMap (polyGrading R 0) m d e
              (by omega) ⟨f, (MvPolynomial.mem_homogeneousSubmodule m f).2 hf⟩))) x))) h =
      topDualEquiv R 0 d (LinearEquiv.ofEq _ _
          (twistChart_univ_eq_negativeTwistPart_zeroDim R (show d < 0 by omega))
          (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R d).hom x))
        (chartMul (chartOfHomogeneous R 0 f hf) (show -e - (((0 : ℕ) : ℤ) + 1) + m =
          -d - (((0 : ℕ) : ℤ) + 1) by omega) ∅ h) := by
  rw [topDualEquiv_apply, topDualEquiv_apply]
  refine (congrArg (fun z => residuePairing R 0 z h)
    (congrArg Subtype.val (twistCohomologyIsoChartUnivZeroDim_mul f hf hde x))).trans ?_
  exact residuePairing_laurentMul _ _ _

/-- **[Stacks, Tag 01XV] for `n = 0`, base change on `H⁰`, corrected.** For `d ≥ 0`, through the
identifications of `H⁰(ℙ⁰, 𝒪(d))` with `(R[T₀])_d` and `(S[T₀])_d`, the base-change map is the
coefficientwise base change. -/
@[stacks 01XV "n = 0: base change along R → S on H^0, d ≥ 0, through Tag 01XT"]
theorem zeroDim_degreeZero_baseChange (d : ℤ) (hd : 0 ≤ d) (x : twistCohomology R 0 d 0) :
    LinearEquiv.ofEq _ _ (twistChart_univ_eq_empty_zeroDim S hd)
        (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim S d).hom
          (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap 0 φ)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S 0) d)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R 0) d)
          (twistBaseChangeFMap φ 0 d) 0) x)) =
      baseChangeChart φ 0 d ∅ (LinearEquiv.ofEq _ _ (twistChart_univ_eq_empty_zeroDim R hd)
        (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R d).hom x)) :=
  Subtype.ext ((LinearEquiv.coe_ofEq_apply _ _).trans
    ((congrArg Subtype.val (twistCohomologyIsoChartUnivZeroDim_baseChange φ d x)).trans rfl))

/-- **[Stacks, Tag 01XV] for `n = 0`, base change on `Hⁿ`, corrected.** For `d < 0`, through the
identifications of `H⁰(ℙ⁰, 𝒪(d))` with `Hom_R((R[T₀])_{-1-d}, R)` and with
`Hom_S((S[T₀])_{-1-d}, S)` by the residue pairing, the functional attached to the base change of a
class takes the value `φ (λ h)` on the base change of `h`. -/
@[stacks 01XV "n = 0: base change along R → S on H^n, d < 0, through Tag 01XT"]
theorem zeroDim_degreeTop_baseChange (d : ℤ) (hd : d < 0) (x : twistCohomology R 0 d 0)
    (h : twistChart R 0 (-d - (((0 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (0 + 1)))) :
    topDualEquiv S 0 d (LinearEquiv.ofEq _ _ (twistChart_univ_eq_negativeTwistPart_zeroDim S hd)
        (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim S d).hom
          (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap 0 φ)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S 0) d)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R 0) d)
          (twistBaseChangeFMap φ 0 d) 0) x)))
        (baseChangeChart φ 0 (-d - (((0 : ℕ) : ℤ) + 1)) ∅ h) =
      φ (topDualEquiv R 0 d (LinearEquiv.ofEq _ _
        (twistChart_univ_eq_negativeTwistPart_zeroDim R hd)
          (ConcreteCategory.hom (twistCohomologyIsoChartUnivZeroDim R d).hom x)) h) := by
  rw [topDualEquiv_apply, topDualEquiv_apply, residuePairing_baseChangeLaurent]
  exact congrArg (fun z => residuePairing S 0 z (baseChangeLaurent φ 0 (h : _ →₀ R)))
    (congrArg Subtype.val (twistCohomologyIsoChartUnivZeroDim_baseChange φ d x))

end Stacks.ProjectiveSpace.Cohomology

end
