module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafBaseChange.FMapCohomology

/-!
# Base change on the cohomology of the twists of `ℙⁿ`, `n ≥ 1`

The base-change map `Hᵖ(ℙⁿ_R, 𝒪(d)) → Hᵖ(ℙⁿ_S, 𝒪(d))` computed on the charts, and its
compatibility with Equation [Stacks, Tag 01XU] on `H⁰` and `Hⁿ` ([Stacks, Tag 01XV]).
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

/-- The morphism `ℙⁿ_S ⟶ ℙⁿ_R` induced by a change of coefficient ring, as a morphism of ringed
spaces. -/
abbrev projModelRingedHom :
    (AlgebraicGeometry.Proj (polyGrading S n)).toLocallyRingedSpace.toSheafedSpace ⟶
      (AlgebraicGeometry.Proj (polyGrading R n)).toLocallyRingedSpace.toSheafedSpace :=
  (projModelMap n φ).toLRSHom.toShHom

/-- **The `f`-map of the base change of `𝒪(d)`**, in adjoint form: the unit of the
pullback--pushforward adjunction followed by the direct image of the identification
`(ℙⁿ_S ⟶ ℙⁿ_R)^* 𝒪(d) ≅ 𝒪(d)`. -/
def twistBaseChangeAdjoint (d : ℤ) :
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d ⟶
      (Scheme.Modules.pushforward (projModelMap n φ)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (projModelMap n φ)).unit.app _ ≫
    (Scheme.Modules.pushforward (projModelMap n φ)).map (projModelTwistTransport n φ d).hom

/-- **The `f`-map of the base change of `𝒪(d)`** in the form `f^* 𝒪(d) ⟶ 𝒪(d)` that the
functoriality of derived global sections of [Stacks, Tag 01F9] takes. -/
def twistBaseChangeFMap (d : ℤ) :
    (RingedSpaceModuleAdjunction.modulePullback (projModelRingedHom φ n)).obj
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d :=
  (RingedSpaceModuleAdjunction.homEquiv (projModelRingedHom φ n) _ _).symm
    (twistBaseChangeAdjoint φ n d)

/-- **The base-change map on the cohomology of `𝒪(d)`**,
`H^q(ℙⁿ_R, 𝒪(d)) ⟶ H^q(ℙⁿ_S, 𝒪(d))`, the target read over `Γ(ℙⁿ_R, 𝒪)`: the map of
[Stacks, Tag 01FA] attached to the pullback along `ℙⁿ_S ⟶ ℙⁿ_R` composed with the identification
of the pullback of `𝒪(d)` with `𝒪(d)`, read on the cohomology groups as right derived functors of
global sections. -/
abbrev twistBaseChangeCohomology (d : ℤ) (q : ℕ) :=
  Stacks.Cohomology.CechIso.fMapCohomology (projModelMap n φ)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (twistBaseChangeFMap φ n d) q

/-- The standard chart `D₊(Tᵢ)` of `ℙⁿ_S` is the inverse image of the standard chart `D₊(Tᵢ)` of
`ℙⁿ_R`. -/
theorem basicOpenXAtUniverse_le_preimage (i : ULift.{u} (Fin (n + 1))) :
    basicOpenXAtUniverse S n i ≤
      (Opens.map (projModelRingedHom φ n).hom.base).obj (basicOpenXAtUniverse R n i) := by
  refine le_of_eq ?_
  change _ = projModelMap n φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (polyGrading R n)
    (MvPolynomial.X i.down)
  rw [projModelMap, AlgebraicGeometry.Proj.map_preimage_basicOpen]
  exact congrArg (AlgebraicGeometry.Proj.basicOpen (polyGrading S n))
    (MvPolynomial.map_X φ i.down).symm

/-- The Čech refinement map of [Stacks, Tag 01FD] attached to the base change of `𝒪(d)`, on the
standard covers. -/
abbrev twistRefinementMap (d : ℤ) :=
  Stacks.Cohomology.CechRefinement.cechComplexRefinementMap (projModelRingedHom φ n)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (twistBaseChangeFMap φ n d)
    (basicOpenXAtUniverse S n) (basicOpenXAtUniverse R n)
    (iSup_basicOpenXAtUniverse_eq_top S n).symm (iSup_basicOpenXAtUniverse_eq_top R n).symm id
    (basicOpenXAtUniverse_le_preimage φ n)

/-- **The base-change map on the cohomology of `𝒪(d)` is the map induced by the Čech refinement
map**, through the identification of [Stacks, Tag 01XD] of the cohomology of `𝒪(d)` with the
homology of the Čech complex of the standard cover, on `ℙⁿ_R` and on `ℙⁿ_S`. -/
theorem twistBaseChangeCohomology_comp_cechHomologyIso (d : ℤ) (q : ℕ) :
    twistBaseChangeCohomology φ n d q ≫
        (Stacks.Cohomology.restrictGlobalScalars (projModelRingedHom φ n)).map
          (cechHomologyIsoRightDerivedTwistingSheaf S n d q).hom =
      (cechHomologyIsoRightDerivedTwistingSheaf R n d q).hom ≫
        HomologicalComplex.homologyMap (twistRefinementMap φ n d) q ≫
        (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso
          (Stacks.Cohomology.globalSectionsRingHom (projModelRingedHom φ n)).hom
          (cechComplex.{u, u, u, u} (⊤ : (AlgebraicGeometry.Proj (polyGrading S n)).Opens)
            (basicOpenXAtUniverse S n) (iSup_basicOpenXAtUniverse_eq_top S n).symm
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)) q).hom :=
  @Stacks.Cohomology.CechIso.fMapCohomology_comp_cechHomologyIsoRightDerived _ _
    (projModelMap n φ) _ _ (basicOpenXAtUniverse S n) (basicOpenXAtUniverse R n)
    (iSup_basicOpenXAtUniverse_eq_top S n).symm (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse S n r s)
    (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse R n r s)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
    (isQuasicoherent_twistingSheaf S n d) (isQuasicoherent_twistingSheaf R n d)
    (twistBaseChangeFMap φ n d) id (basicOpenXAtUniverse_le_preimage φ n) q

open Stacks.Homology.HomologyRep in
/-- A degree-zero class of the monomial Čech complex represented by a cocycle is sent by the
identification of [Stacks, Equation 01XU] to the element whose diagonal cochain it is. -/
theorem rep_homologyZeroIso (R : Type u) [CommRing R] {N : ℕ} {d : ℤ}
    {h : (laurentCechComplex R (N + 1) d).homology 0} {v : (laurentCechComplex R (N + 1) d).X 0}
    (H : Rep (laurentCechComplex R (N + 1) d) 0 h v) :
    ((laurentCechCohomologyZeroEquiv (R := R) (n := N + 1) (d := d) N.succ_pos
        (ConcreteCategory.hom (homologyZeroIso R N d).hom h) :
          LinearMap.ker (laurentCechDiffRestrict R (N + 1) d 0)) :
        laurentCechCochains R (N + 1) d 0) = v := by
  obtain ⟨z, rfl, rfl⟩ := H
  have h1 := ConcreteCategory.congr_hom (homologyZeroIso_inv_homologyZeroι R N d)
    (ConcreteCategory.hom (homologyZeroIso R N d).hom
      (ConcreteCategory.hom ((laurentCechComplex R (N + 1) d).homologyπ 0) z))
  refine h1.symm.trans ?_
  refine ((ConcreteCategory.comp_apply _ _ _).trans
    (congrArg _ (Iso.hom_inv_id_apply _ _))).trans ?_
  change ConcreteCategory.hom ((laurentCechComplex R (N + 1) d).iCycles 0)
      (ConcreteCategory.hom ((laurentCechComplex R (N + 1) d).isoHomologyπ 0 0 (by simp)
        ((laurentCechComplex R (N + 1) d).shape 0 0 (by simp))).inv
        (ConcreteCategory.hom ((laurentCechComplex R (N + 1) d).isoHomologyπ 0 0 (by simp)
          ((laurentCechComplex R (N + 1) d).shape 0 0 (by simp))).hom z)) = _
  rw [Iso.hom_inv_id_apply]

open Stacks.Homology.HomologyRep in
/-- A top-degree class of the monomial Čech complex represented by a cochain is sent by the
identification of [Stacks, Equation 01XU] to the functional of that cochain. -/
theorem rep_homologyTopIso (R : Type u) [CommRing R] {N : ℕ} {d : ℤ}
    {h : (laurentCechComplex R (N + 1) d).homology (N + 1)}
    {v : (laurentCechComplex R (N + 1) d).X (N + 1)}
    (H : Rep (laurentCechComplex R (N + 1) d) (N + 1) h v) :
    ConcreteCategory.hom (homologyTopIso R N d).hom h =
      laurentCechCohomologyTopEquiv R N d (Submodule.Quotient.mk v) := by
  have hπ : ConcreteCategory.hom (homologyTopπ R N d) v = h := by
    obtain ⟨z, rfl, rfl⟩ := H
    have e := ConcreteCategory.congr_hom
      (HomologicalComplex.homology_π_ι (K := laurentCechComplex R (N + 1) d) (i := N + 1)) z
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine (congrArg (ConcreteCategory.hom ((laurentCechComplex R (N + 1) d).isoHomologyι
      (N + 1) (N + 1 + 1) (by simp) (laurentCechComplex_d_eq_zero_of_lt (by omega))).inv)
      (((ConcreteCategory.comp_apply _ _ _).symm.trans e.symm).trans
        (ConcreteCategory.comp_apply _ _ _))).trans ?_
    exact Iso.hom_inv_id_apply ((laurentCechComplex R (N + 1) d).isoHomologyι (N + 1)
        (N + 1 + 1) (by simp) (laurentCechComplex_d_eq_zero_of_lt (by omega))) _
  rw [← hπ, ← ConcreteCategory.comp_apply, homologyTopπ_homologyTopIso]
  rfl

/-! ### Base change on the charts -/

/-- The chart denominator over `S` is the image of the chart denominator over `R`. -/
theorem map_chartDenom (T : Finset (Fin (n + 1))) :
    MvPolynomial.map φ (chartDenom R n T) = chartDenom S n T := by
  simp only [chartDenom, map_prod, MvPolynomial.map_X]

/-- The localization at the image of the chart denominator is the localization at the chart
denominator. -/
def chartAwayTransport (T : Finset (Fin (n + 1))) :
    LocalizedModule.Away (MvPolynomial.map φ (chartDenom R n T)) (MvPolynomial (Fin (n + 1)) S) →ₗ[
      MvPolynomial (Fin (n + 1)) S]
      LocalizedModule.Away (chartDenom S n T) (MvPolynomial (Fin (n + 1)) S) :=
  LocalizedModule.liftOfLE _ _ (le_of_eq (congrArg Submonoid.powers (map_chartDenom φ n T)))

/-- The transport on a fraction. -/
theorem chartAwayTransport_mk (T : Finset (Fin (n + 1))) (m : MvPolynomial (Fin (n + 1)) S)
    (t : Submonoid.powers (MvPolynomial.map φ (chartDenom R n T))) :
    chartAwayTransport φ n T (LocalizedModule.mk m t) =
      LocalizedModule.mk m ⟨t.1, (le_of_eq (congrArg Submonoid.powers (map_chartDenom φ n T)))
        t.2⟩ := by
  simpa only [chartAwayTransport, IsLocalizedModule.mk_eq_mk'] using
    IsLocalizedModule.liftOfLE_mk' _ _
      (le_of_eq (congrArg Submonoid.powers (map_chartDenom φ n T)))
      (LocalizedModule.mkLinearMap _ _) (LocalizedModule.mkLinearMap _ _) m t

/-- **Base change of a Laurent monomial fraction.** -/
theorem chartAwayTransport_awayModuleMap_smul_laurentFrac (T : Finset (Fin (n + 1)))
    (e : Fin (n + 1) → ℤ) (r : R) :
    chartAwayTransport φ n T (Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap
        (polyGrading R n) (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ) (chartDenom R n T)
        (r • laurentFrac R n T e)) = φ r • laurentFrac S n T e := by
  have h1 : r • laurentFrac R n T e = LocalizedModule.mk
      (MvPolynomial.C r * MvPolynomial.monomial (numExp T e (clearDen T e)) (1 : R))
      (chartPow R n T (clearDen T e)) := by
    rw [laurentFrac, ← algebraMap_smul (MvPolynomial (Fin (n + 1)) R) r, LocalizedModule.smul'_mk]
    rfl
  have h2 : φ r • laurentFrac S n T e = LocalizedModule.mk
      (MvPolynomial.C (φ r) * MvPolynomial.monomial (numExp T e (clearDen T e)) (1 : S))
      (chartPow S n T (clearDen T e)) := by
    rw [laurentFrac, ← algebraMap_smul (MvPolynomial (Fin (n + 1)) S) (φ r),
      LocalizedModule.smul'_mk]
    rfl
  have hs : (polyGradedMap (Fin (n + 1)) φ) ((chartPow R n T (clearDen T e) :
      Submonoid.powers (chartDenom R n T)) : MvPolynomial (Fin (n + 1)) R) ∈
      Submonoid.powers ((polyGradedMap (Fin (n + 1)) φ) (chartDenom R n T)) :=
    ⟨clearDen T e, (map_pow (MvPolynomial.map φ) _ _).symm⟩
  refine (congrArg (fun z => chartAwayTransport φ n T
    (Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap (polyGrading R n)
      (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ) (chartDenom R n T) z)) h1).trans ?_
  refine (congrArg (chartAwayTransport φ n T)
    (Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap_mk (polyGrading R n)
      (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ) _ _ _ hs)).trans ?_
  refine (chartAwayTransport_mk φ n T _ _).trans (Eq.trans ?_ h2.symm)
  congr 1
  · change MvPolynomial.map φ (MvPolynomial.C r * MvPolynomial.monomial _ 1) =
      MvPolynomial.C (φ r) * MvPolynomial.monomial _ 1
    rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_monomial, map_one]
  · exact Subtype.ext (by
      change MvPolynomial.map φ (chartDenom R n T ^ clearDen T e) = chartDenom S n T ^ _
      rw [map_pow, map_chartDenom])

/-- **Base change of the monomial identification of the sections over a chart.** -/
theorem chartAwayTransport_twistChartEquivTwistSections (d : ℤ) (T : Finset (Fin (n + 1)))
    (w : twistChart R n d (↑T : Set (Fin (n + 1)))) :
    chartAwayTransport φ n T (Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap
        (polyGrading R n) (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ) (chartDenom R n T)
        (twistChartEquivTwistSections R n d T w : LocalizedModule.Away (chartDenom R n T)
          (MvPolynomial (Fin (n + 1)) R))) =
      (twistChartEquivTwistSections S n d T (baseChangeChart φ n d (↑T : Set (Fin (n + 1))) w) :
        LocalizedModule.Away (chartDenom S n T) (MvPolynomial (Fin (n + 1)) S)) := by
  let L : twistChart R n d (↑T : Set (Fin (n + 1))) →+
      LocalizedModule.Away (chartDenom S n T) (MvPolynomial (Fin (n + 1)) S) :=
    (chartAwayTransport φ n T).toAddMonoidHom.comp
      ((Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap
        (polyGrading R n) (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ)
          (chartDenom R n T)).comp
        ((twistSections R n d T).subtype.toAddMonoidHom.comp
          (twistChartEquivTwistSections R n d T).toAddMonoidHom))
  let L' : twistChart R n d (↑T : Set (Fin (n + 1))) →+
      LocalizedModule.Away (chartDenom S n T) (MvPolynomial (Fin (n + 1)) S) :=
    (twistSections S n d T).subtype.toAddMonoidHom.comp
      ((twistChartEquivTwistSections S n d T).toAddMonoidHom.comp
        (baseChangeChart φ n d (↑T : Set (Fin (n + 1)))).toAddMonoidHom)
  have key : L.comp (Finsupp.supportedEquivFinsupp (M := R) (R := R)
      (laurentMonomials n d (↑T : Set (Fin (n + 1))))).symm.toAddEquiv.toAddMonoidHom =
      L'.comp (Finsupp.supportedEquivFinsupp (M := R) (R := R)
        (laurentMonomials n d (↑T : Set (Fin (n + 1))))).symm.toAddEquiv.toAddMonoidHom := by
    refine Finsupp.addHom_ext fun e r => ?_
    have hbasis : ∀ (A : Type u) [CommRing A] (a : A),
        ((twistChartEquivTwistSections A n d T
          ((Finsupp.supportedEquivFinsupp (M := A) (R := A)
            (laurentMonomials n d (↑T : Set (Fin (n + 1))))).symm (Finsupp.single e a)) :
            LocalizedModule.Away (chartDenom A n T) (MvPolynomial (Fin (n + 1)) A))) =
          a • laurentFrac A n T e := fun A _ a =>
      (congrArg (fun z => ((twistSectionsBasis A n d T).repr.symm z :
          LocalizedModule.Away (chartDenom A n T) (MvPolynomial (Fin (n + 1)) A)))
        ((Finsupp.supportedEquivFinsupp (M := A) (R := A)
          (laurentMonomials n d (↑T : Set (Fin (n + 1))))).apply_symm_apply _)).trans
        (by rw [Module.Basis.repr_symm_single]; simp [twistSectionsBasis])
    have hb : baseChangeChart φ n d (↑T : Set (Fin (n + 1)))
        ((Finsupp.supportedEquivFinsupp (M := R) (R := R)
          (laurentMonomials n d (↑T : Set (Fin (n + 1))))).symm (Finsupp.single e r)) =
        (Finsupp.supportedEquivFinsupp (M := S) (R := S)
          (laurentMonomials n d (↑T : Set (Fin (n + 1))))).symm (Finsupp.single e (φ r)) :=
      Subtype.ext ((congrArg (Finsupp.mapRange φ (map_zero φ))
        (Finsupp.supportedEquivFinsupp_symm_single (R := R) _ e r)).trans
        (Finsupp.mapRange_single.trans
          (Finsupp.supportedEquivFinsupp_symm_single (R := S) _ e (φ r)).symm))
    exact (congrArg (fun z => chartAwayTransport φ n T
        (Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap (polyGrading R n)
          (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ) (chartDenom R n T) z))
      (hbasis R r)).trans
      ((chartAwayTransport_awayModuleMap_smul_laurentFrac φ n T e r).trans
        ((hbasis S (φ r)).symm.trans (congrArg (fun z => ((twistChartEquivTwistSections S n d T z :
          twistSections S n d T) : LocalizedModule.Away (chartDenom S n T)
            (MvPolynomial (Fin (n + 1)) S))) hb.symm)))
  have h := DFunLike.congr_fun key
    (Finsupp.supportedEquivFinsupp (M := R) (R := R)
      (laurentMonomials n d (↑T : Set (Fin (n + 1)))) w)
  have e := (Finsupp.supportedEquivFinsupp (M := R) (R := R)
      (laurentMonomials n d (↑T : Set (Fin (n + 1))))).symm_apply_apply w
  exact (congrArg L e).symm.trans (h.trans (congrArg L' e))

/-- The adjoint of the `f`-map of the base change of `𝒪(d)` is the explicit pointwise comparison
of the twisting sheaves. -/
theorem homEquiv_twistBaseChangeFMap (d : ℤ) :
    RingedSpaceModuleAdjunction.homEquiv (projModelRingedHom φ n) _ _
        (twistBaseChangeFMap φ n d) =
      Stacks.ProjTwistComparison.pushforwardTwistMap (polyGradedMap (Fin (n + 1)) φ)
        (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ) d :=
  (Equiv.apply_symm_apply _ _).trans
    (Stacks.ProjTwistComparison.unit_comp_map_twistMap _ _ d)

/-- Restricting sections of a twisting sheaf along an equality of standard opens is the canonical
map of localizations. -/
theorem standardOpenEquiv_map_eq {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (t : ℤ) {k : ℕ} (hk : 0 < k)
    {f₁ f₂ : A} (h₁ : f₁ ∈ 𝒜 k) (h₂ : f₂ ∈ 𝒜 k) (e : f₁ = f₂)
    (z : (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 t).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f₁))) :
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 t) h₂ hk
        (ConcreteCategory.hom ((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 t).val.map
          (homOfLE (le_of_eq (congrArg (ProjectiveSpectrum.basicOpen 𝒜) e.symm))).op) z)) :
        LocalizedModule.Away f₂ A) =
      LocalizedModule.liftOfLE _ _ (le_of_eq (congrArg Submonoid.powers e))
        ((AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 t) h₁ hk z) :
          LocalizedModule.Away f₁ A) := by
  subst e
  have hid : (homOfLE (le_of_eq (congrArg (ProjectiveSpectrum.basicOpen 𝒜) (rfl : f₁ = f₁)))).op =
      𝟙 (op (ProjectiveSpectrum.basicOpen 𝒜 f₁)) := rfl
  have hz : ConcreteCategory.hom ((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 t).val.map
      (homOfLE (le_of_eq (congrArg (ProjectiveSpectrum.basicOpen 𝒜) (rfl : f₁ = f₁)))).op) z = z :=
    (ConcreteCategory.congr_hom ((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 t).val.map_id
      (op (ProjectiveSpectrum.basicOpen 𝒜 f₁))) z).trans (ConcreteCategory.id_apply z)
  refine (congrArg (fun w =>
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 t) h₂ hk w) :
        LocalizedModule.Away f₁ A)) hz).trans ?_
  induction ((AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 t) h₁ hk z) :
        LocalizedModule.Away f₁ A) using LocalizedModule.induction_on with
  | h m s =>
    simpa only [IsLocalizedModule.mk_eq_mk'] using
      (IsLocalizedModule.liftOfLE_mk' _ _ (le_of_eq (congrArg Submonoid.powers (rfl : f₁ = f₁)))
        (LocalizedModule.mkLinearMap _ _) (LocalizedModule.mkLinearMap _ _) m s).symm

/-- The image of the chart denominator over `R` cuts out the chart over `S`. -/
theorem basicOpen_chartDenom_le_map (T : Finset (Fin (n + 1))) :
    ProjectiveSpectrum.basicOpen (polyGrading S n) (chartDenom S n T) ≤
      ProjectiveSpectrum.basicOpen (polyGrading S n)
        ((polyGradedMap (Fin (n + 1)) φ) (chartDenom R n T)) :=
  le_of_eq (congrArg (ProjectiveSpectrum.basicOpen (polyGrading S n)) (map_chartDenom φ n T).symm)

/-- **The base change of `𝒪(d)` on the sections over a chart is the coefficientwise base change of
the monomial coordinates.** -/
theorem chartSectionsAddEquivTwistChart_pushforwardTwistMap (d : ℤ) (T : Finset (Fin (n + 1)))
    (hT : T.Nonempty) (x : chartSheafSections R n d T) :
    chartSectionsAddEquivTwistChart S n d T hT
        (ConcreteCategory.hom ((ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d).val.map
          (homOfLE (basicOpen_chartDenom_le_map φ n T)).op)
          (ConcreteCategory.hom ((Stacks.ProjTwistComparison.pushforwardTwistMap
            (polyGradedMap (Fin (n + 1)) φ) (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ)
              d).val.app (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (chartDenom R n T))))
            x)) =
      baseChangeChart φ n d (↑T : Set (Fin (n + 1)))
        (chartSectionsAddEquivTwistChart R n d T hT x) := by
  have hw : chartSectionsAddEquiv R n d T hT x =
      twistChartEquivTwistSections R n d T (chartSectionsAddEquivTwistChart R n d T hT x) :=
    ((twistChartEquivTwistSections R n d T).apply_symm_apply _).symm
  have h1 := standardOpenEquiv_map_eq (polyGrading S n) d (Finset.card_pos.2 hT)
    ((polyGradedMap (Fin (n + 1)) φ).map_mem (chartDenom_mem_homogeneousSubmodule n T))
    (chartDenom_mem_homogeneousSubmodule n T) (map_chartDenom φ n T)
    (ConcreteCategory.hom ((Stacks.ProjTwistComparison.pushforwardTwistMap
      (polyGradedMap (Fin (n + 1)) φ) (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ)
        d).val.app (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (chartDenom R n T)))) x)
  have h2 := congrArg Subtype.val
    (Stacks.AlgebraicGeometry.TwistChartLocality.standardOpenEquiv_pushforwardTwistMap
      (polyGrading R n) (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ)
      (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ) (Finset.card_pos.2 hT)
      (chartDenom_mem_homogeneousSubmodule n T) d x)
  have h3 := chartAwayTransport_twistChartEquivTwistSections φ n d T
    (chartSectionsAddEquivTwistChart R n d T hT x)
  have key : chartSectionsAddEquiv S n d T hT
      (ConcreteCategory.hom ((ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d).val.map
          (homOfLE (basicOpen_chartDenom_le_map φ n T)).op)
          (ConcreteCategory.hom ((Stacks.ProjTwistComparison.pushforwardTwistMap
            (polyGradedMap (Fin (n + 1)) φ) (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ)
              d).val.app (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (chartDenom R n T))))
            x)) =
      twistChartEquivTwistSections S n d T (baseChangeChart φ n d (↑T : Set (Fin (n + 1)))
        (chartSectionsAddEquivTwistChart R n d T hT x)) :=
    Subtype.ext (h1.trans ((congrArg (chartAwayTransport φ n T) h2).trans
      ((congrArg (fun z => chartAwayTransport φ n T
        (Stacks.AlgebraicGeometry.TwistChartLocality.awayModuleMap (polyGrading R n)
          (polyGrading S n) (polyGradedMap (Fin (n + 1)) φ) (chartDenom R n T) z))
        (congrArg Subtype.val hw)).trans h3)))
  exact (congrArg (twistChartEquivTwistSections S n d T).symm key).trans
    ((twistChartEquivTwistSections S n d T).symm_apply_apply _)

open Stacks.Cohomology.Basis (res res_app res_res) in
/-- **The base change of `𝒪(d)` on a Čech term of the standard cover is the coefficientwise base
change of the monomial coordinates.** -/
theorem coe_ordInterChartAddEquiv_pushforwardTwistMap (d : ℤ) (p : ℕ)
    (k : CechCochains.OrdIndex (I := ULift.{u} (Fin (n + 1))) p)
    (u : twistInterSections R n d k.1) :
    ((ordInterChartAddEquiv S n d p k
        (res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d))
          (Stacks.Cohomology.CechRefinement.cechInter_le_map_cechInter (projModelRingedHom φ n)
            (basicOpenXAtUniverse S n) (basicOpenXAtUniverse R n) id
            (basicOpenXAtUniverse_le_preimage φ n) k.1)
          (ConcreteCategory.hom ((Stacks.ProjTwistComparison.pushforwardTwistMap
            (polyGradedMap (Fin (n + 1)) φ) (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ)
              d).val.app (op (CechCochains.inter
                (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
                (basicOpenXAtUniverse R n) k.1))) u)) :
          twistChart S n d (Set.range (chartIndices k.1))) : (Fin (n + 1) → ℤ) →₀ S) =
      baseChangeLaurent φ n ((ordInterChartAddEquiv R n d p k u :
        twistChart R n d (Set.range (chartIndices k.1))) : (Fin (n + 1) → ℤ) →₀ R) := by
  have inj := (strictMono_chartIndices k.2).injective
  have aR := (inter_eq_basicOpen_chartDenom R n p k.1 inj).ge
  have hnat := res_app (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))
    ((PresheafOfModules.toPresheaf _).map (Stacks.ProjTwistComparison.pushforwardTwistMap
      (polyGradedMap (Fin (n + 1)) φ) (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ) d).val)
    aR u
  have aS := (inter_eq_basicOpen_chartDenom S n p k.1 inj).ge
  have maR : ProjectiveSpectrum.basicOpen (polyGrading S n)
      ((polyGradedMap (Fin (n + 1)) φ) (chartDenom R n (Finset.image (chartIndices k.1)
        Finset.univ))) ≤ (Opens.map (projModelRingedHom φ n).hom.base).obj
          (CechCochains.inter (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
            (basicOpenXAtUniverse R n) k.1) :=
    (Opens.map (projModelRingedHom φ n).hom.base).monotone aR
  have eq1 := (res_res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d))
      aS (Stacks.Cohomology.CechRefinement.cechInter_le_map_cechInter (projModelRingedHom φ n)
        (basicOpenXAtUniverse S n) (basicOpenXAtUniverse R n) id
        (basicOpenXAtUniverse_le_preimage φ n) k.1)
      (ConcreteCategory.hom ((Stacks.ProjTwistComparison.pushforwardTwistMap
        (polyGradedMap (Fin (n + 1)) φ) (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ)
          d).val.app (op (CechCochains.inter
            (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
            (basicOpenXAtUniverse R n) k.1))) u)).trans
    ((res_res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d))
      (basicOpen_chartDenom_le_map φ n (Finset.image (chartIndices k.1) Finset.univ)) maR
      (ConcreteCategory.hom ((Stacks.ProjTwistComparison.pushforwardTwistMap
        (polyGradedMap (Fin (n + 1)) φ) (irrelevant_le_map_polyGradedMap (Fin (n + 1)) φ)
          d).val.app (op (CechCochains.inter
            (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
            (basicOpenXAtUniverse R n) k.1))) u)).symm.trans
      (congrArg (res (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d))
        (basicOpen_chartDenom_le_map φ n (Finset.image (chartIndices k.1) Finset.univ))) hnat))
  have e1 := congrArg (fun z => ((chartSectionsAddEquivTwistChart S n d
      (Finset.image (chartIndices k.1) Finset.univ) (image_univ_nonempty (chartIndices k.1)) z :
        twistChart S n d (↑(Finset.image (chartIndices k.1) Finset.univ) : Set (Fin (n + 1)))) :
        (Fin (n + 1) → ℤ) →₀ S)) eq1
  exact e1.trans (congrArg (fun z : twistChart S n d
      (↑(Finset.image (chartIndices k.1) Finset.univ) : Set (Fin (n + 1))) =>
        (z : (Fin (n + 1) → ℤ) →₀ S))
    (chartSectionsAddEquivTwistChart_pushforwardTwistMap φ n d _
      (image_univ_nonempty (chartIndices k.1)) _))

/-- The ordered Čech cochain map of [Stacks, Tag 01FD] for the base change of `𝒪(d)`. -/
abbrev twistRefineOrd (d : ℤ) {p : ℕ}
    (v : CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n)
      (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p) :=
  Stacks.Cohomology.CechRefinement.refineOrd (projModelRingedHom φ n)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (twistBaseChangeFMap φ n d)
    (basicOpenXAtUniverse S n) (basicOpenXAtUniverse R n) (basicOpenXAtUniverse_le_preimage φ n) v

/-- **In the monomial model, the ordered Čech cochain map of the base change of `𝒪(d)` is the
coefficientwise base change of the monomial Čech cochains.** -/
theorem twistOrdCochainEquiv_twistRefineOrd (d : ℤ) (p : ℕ)
    (v : CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n)
      (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p) :
    twistOrdCochainEquiv S n d p (twistRefineOrd φ n d v) =
      baseChangeCechCochain φ n d p (twistOrdCochainEquiv R n d p v) := by
  refine (ordChartEquiv S n d p).injective (funext fun t => Subtype.ext ?_)
  have h₁ := congrArg (fun z : twistChart S n d (Set.range t.1) => (z : (Fin (n + 1) → ℤ) →₀ S))
    (congrFun (ordChartEquiv_twistOrdCochainEquiv S n d p (twistRefineOrd φ n d v)) t)
  have h₂ := congrArg (fun z : twistChart R n d (Set.range t.1) => (z : (Fin (n + 1) → ℤ) →₀ R))
    (congrFun (ordChartEquiv_twistOrdCochainEquiv R n d p v) t)
  have h₃ := Stacks.Cohomology.CechRefinement.refineOrd_apply (projModelRingedHom φ n)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) (twistBaseChangeFMap φ n d)
    (basicOpenXAtUniverse S n) (basicOpenXAtUniverse R n) (basicOpenXAtUniverse_le_preimage φ n)
    v (ordIndexUp n p t)
  rw [homEquiv_twistBaseChangeFMap] at h₃
  refine h₁.trans ((congrArg (fun z => ((ordInterChartAddEquiv S n d p (ordIndexUp n p t) z :
    twistChart S n d (Set.range (chartIndices (ordIndexUp n p t).1))) :
      (Fin (n + 1) → ℤ) →₀ S)) h₃).trans ?_)
  refine (coe_ordInterChartAddEquiv_pushforwardTwistMap φ n d p (ordIndexUp n p t) _).trans ?_
  exact congrArg (baseChangeLaurent φ n) h₂.symm

/-- The identification of the cohomology of `𝒪(d)` with the monomial Čech homology, on
elements. -/
theorem twistCohomologyIsoLaurentHomology_hom_apply {T : Type u} [CommRing T] (m : ℕ) (d : ℤ)
    (q : ℕ) (x : ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading T m))
      ⊤).rightDerived q).obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading T m) d)) :
    ConcreteCategory.hom (twistCohomologyIsoLaurentHomology T m d q).hom x =
      ConcreteCategory.hom (HomologicalComplex.homologyMap
        (twistOrderedComplexIsoLaurent T m d).hom q)
        (ConcreteCategory.hom (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso
          (coeffScalar T m) (twistOrderedComplex T m d) q).inv
          (ConcreteCategory.hom (orderedCechHomologyModuleIso
            (⊤ : (AlgebraicGeometry.Proj (polyGrading T m)).Opens) (basicOpenXAtUniverse T m)
            (iSup_basicOpenXAtUniverse_eq_top T m).symm
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading T m) d) q).inv
            (ConcreteCategory.hom (cechHomologyIsoRightDerivedTwistingSheaf T m d q).hom x))) :=
  rfl

open Stacks.Homology.HomologyRep in
/-- A class of the cohomology of `𝒪(d)` whose ordered Čech class is represented by `v` is sent
by the identification with the monomial Čech homology to the class of the monomial cochain of
`v`. -/
theorem rep_twistCohomologyIsoLaurentHomology {T : Type u} [CommRing T] (m : ℕ) (d : ℤ) (q : ℕ)
    (x : ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading T m))
      ⊤).rightDerived q).obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading T m) d))
    (v : (twistOrderedComplex T m d).X q)
    (H : Rep (twistOrderedComplex T m d) q
      (ConcreteCategory.hom (orderedCechHomologyModuleIso
        (⊤ : (AlgebraicGeometry.Proj (polyGrading T m)).Opens) (basicOpenXAtUniverse T m)
        (iSup_basicOpenXAtUniverse_eq_top T m).symm
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading T m) d) q).inv
        (ConcreteCategory.hom (cechHomologyIsoRightDerivedTwistingSheaf T m d q).hom x)) v) :
    Rep (laurentCechComplex T m d) q
      (ConcreteCategory.hom (twistCohomologyIsoLaurentHomology T m d q).hom x)
      (twistOrdCochainEquiv T m d q v) :=
  (twistCohomologyIsoLaurentHomology_hom_apply m d q x).symm ▸
    rep_map (twistOrderedComplexIsoLaurent T m d).hom
      (rep_restrictScalarsHomologyIso_inv (coeffScalar T m) H)

/-- The identification of the cohomology of `𝒪(d)` with the ordered Čech homology, on elements. -/
theorem sheafCohomologyIsoOrderedHomology_hom_apply {T : Type u} [CommRing T] (m : ℕ) (d : ℤ)
    (q : ℕ) (x : ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading T m))
      ⊤).rightDerived q).obj (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading T m) d)) :
    ConcreteCategory.hom (sheafCohomologyIsoOrderedHomology T m d q).hom x =
      ConcreteCategory.hom (orderedCechHomologyModuleIso
        (⊤ : (AlgebraicGeometry.Proj (polyGrading T m)).Opens) (basicOpenXAtUniverse T m)
        (iSup_basicOpenXAtUniverse_eq_top T m).symm
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading T m) d) q).inv
        (ConcreteCategory.hom (cechHomologyIsoRightDerivedTwistingSheaf T m d q).hom x) :=
  ConcreteCategory.comp_apply _ _ _


open Stacks.Homology.HomologyRep in
/-- **The base change of a cohomology class of `𝒪(d)`, in the monomial model.** A class over `R`
and its base change over `S` are sent by the identifications with the monomial Čech homology
to classes represented by a monomial cochain and by its coefficientwise base change. -/
theorem exists_rep_twistBaseChangeCohomology (d : ℤ) (q : ℕ) (x : twistCohomology R n d q) :
    ∃ c : laurentCechCochains R n d q,
      Rep (laurentCechComplex R n d) q
        (ConcreteCategory.hom (twistCohomologyIsoLaurentHomology R n d q).hom x) c ∧
      Rep (laurentCechComplex S n d) q
        (ConcreteCategory.hom (twistCohomologyIsoLaurentHomology S n d q).hom
          (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap n φ)
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
            (twistBaseChangeFMap φ n d) q) x))
        (baseChangeCechCochain φ n d q c) := by
  obtain ⟨v, H⟩ := exists_rep (ConcreteCategory.hom (orderedCechHomologyModuleIso
    (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens) (basicOpenXAtUniverse R n)
    (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) q).inv
      (ConcreteCategory.hom (cechHomologyIsoRightDerivedTwistingSheaf R n d q).hom x))
  have HS : Rep (twistOrderedComplex S n d) q
      (ConcreteCategory.hom (orderedCechHomologyModuleIso
        (⊤ : (AlgebraicGeometry.Proj (polyGrading S n)).Opens) (basicOpenXAtUniverse S n)
        (iSup_basicOpenXAtUniverse_eq_top S n).symm
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d) q).inv
        (ConcreteCategory.hom (cechHomologyIsoRightDerivedTwistingSheaf S n d q).hom
          (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap n φ)
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
            (twistBaseChangeFMap φ n d) q) x)))
      (twistRefineOrd φ n d v) :=
    @Stacks.Cohomology.CechIso.rep_fMapCohomology _ _ (projModelMap n φ)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
      (isQuasicoherent_twistingSheaf S n d) (isQuasicoherent_twistingSheaf R n d)
      (twistBaseChangeFMap φ n d) _ _ (basicOpenXAtUniverse S n) (basicOpenXAtUniverse R n)
      (iSup_basicOpenXAtUniverse_eq_top S n).symm (iSup_basicOpenXAtUniverse_eq_top R n).symm
      (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse S n r s)
      (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse R n r s)
      (basicOpenXAtUniverse_le_preimage φ n) q x v H
  refine ⟨twistOrdCochainEquiv R n d q v, rep_twistCohomologyIsoLaurentHomology n d q x v H, ?_⟩
  rw [← twistOrdCochainEquiv_twistRefineOrd]
  exact rep_twistCohomologyIsoLaurentHomology (T := S) n d q
    (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap n φ)
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S n) d)
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
            (twistBaseChangeFMap φ n d) q) x) (twistRefineOrd φ n d v) HS

/-- **[Stacks, Tag 01XV], base change on `H⁰`.** For a ring map `φ : R → S`, the base-change map
`H⁰(ℙⁿ_R, 𝒪(d)) ⟶ H⁰(ℙⁿ_S, 𝒪(d))` — the map on cohomology attached to the pullback along
`ℙⁿ_S ⟶ ℙⁿ_R` and the identification of the pullback of `𝒪(d)` with `𝒪(d)` — is, through the
identifications of [Stacks, Equation 01XU] of `H⁰(ℙⁿ_R, 𝒪(d))` with `(R[T₀, …, Tₙ])_d` and of
`H⁰(ℙⁿ_S, 𝒪(d))` with `(S[T₀, …, Tₙ])_d`, the coefficientwise base change
`(R[T₀, …, Tₙ])_d ⟶ (S[T₀, …, Tₙ])_d`. Here `n = N + 1` and `d` is any integer. -/
@[stacks 01XV "base change along R → S on H^0, through Equation 01XU"]
theorem serreTwistCohomology_degreeZero_baseChange (N : ℕ) (d : ℤ)
    (x : twistCohomology R (N + 1) d 0) :
    ConcreteCategory.hom (serreTwistCohomology S N d).degreeZero.hom
        (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap (N + 1) φ)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S (N + 1)) d)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R (N + 1)) d)
          (twistBaseChangeFMap φ (N + 1) d) 0) x) =
      baseChangeChart φ (N + 1) d ∅
        (ConcreteCategory.hom (serreTwistCohomology R N d).degreeZero.hom x) := by
  obtain ⟨c, HR, HS⟩ := exists_rep_twistBaseChangeCohomology φ (N + 1) d 0 x
  have eR := rep_homologyZeroIso R HR
  have eS := rep_homologyZeroIso S HS
  refine (laurentCechCohomologyZeroEquiv (R := S) (n := N + 1) (d := d) N.succ_pos).injective
    (Subtype.ext (Subtype.ext ?_))
  refine (congrArg (fun z : laurentCechCochains S (N + 1) d 0 => (z : LaurentCochain S (N + 1)))
    eS).trans ?_
  refine Eq.trans ?_ (coe_coe_laurentCechCohomologyZeroEquiv N.succ_pos _).symm
  refine Eq.trans ?_ (baseChangeCochain_laurentDiagonalCochain φ _)
  refine congrArg (baseChangeCochain φ (N + 1)) ?_
  exact (congrArg (fun z : laurentCechCochains R (N + 1) d 0 => (z : LaurentCochain R (N + 1)))
    eR).symm.trans (coe_coe_laurentCechCohomologyZeroEquiv N.succ_pos _)

/-- **[Stacks, Tag 01XV], base change on `Hⁿ`.** For a ring map `φ : R → S`, the base-change map
`Hⁿ(ℙⁿ_R, 𝒪(d)) ⟶ Hⁿ(ℙⁿ_S, 𝒪(d))` is, through the identifications of
[Stacks, Equation 01XU] of `Hⁿ` with `Hom((R[T₀, …, Tₙ])_{-n-1-d}, R)` and with
`Hom((S[T₀, …, Tₙ])_{-n-1-d}, S)`, the base change of functionals: the functional attached to the
base change of a class takes the value `φ (λ h)` on the base change of `h`, where `λ` is the
functional attached to the class. Since the base changes of the monomials span
`(S[T₀, …, Tₙ])_{-n-1-d}`, this determines it. Here `n = N + 1` and `d` is any integer. -/
@[stacks 01XV "base change along R → S on H^n, through Equation 01XU"]
theorem serreTwistCohomology_degreeTop_baseChange (N : ℕ) (d : ℤ)
    (x : twistCohomology R (N + 1) d (N + 1))
    (h : twistChart R (N + 1) (-d - (((N + 1 : ℕ) : ℤ) + 1)) (∅ : Set (Fin (N + 1 + 1)))) :
    ConcreteCategory.hom (serreTwistCohomology S N d).degreeTop.hom
        (ConcreteCategory.hom (Stacks.Cohomology.CechIso.fMapCohomology (projModelMap (N + 1) φ)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading S (N + 1)) d)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R (N + 1)) d)
          (twistBaseChangeFMap φ (N + 1) d) (N + 1)) x)
        (baseChangeChart φ (N + 1) (-d - (((N + 1 : ℕ) : ℤ) + 1)) ∅ h) =
      φ (ConcreteCategory.hom (serreTwistCohomology R N d).degreeTop.hom x h) := by
  obtain ⟨c, HR, HS⟩ := exists_rep_twistBaseChangeCohomology φ (N + 1) d (N + 1) x
  have eR := rep_homologyTopIso R HR
  have eS := rep_homologyTopIso S HS
  refine (congrArg (fun F => F (baseChangeChart φ (N + 1) (-d - (((N + 1 : ℕ) : ℤ) + 1)) ∅ h))
    eS).trans ?_
  refine (laurentCechCohomologyTopEquiv_baseChangeCechCochain φ d c h).trans ?_
  exact congrArg φ (congrArg (fun F => F h) eR).symm
end Stacks.ProjectiveSpace.Cohomology

end
