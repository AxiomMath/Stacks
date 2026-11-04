module

public import StacksFrontier.Homology.Perfect.FibreCriterion
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport

/-!
# Splitting off `R` in degree zero, locally

Let `K` be a pseudo-coherent object of `D(R)` concentrated in degrees `≥ 0` with `H⁰(K) ≅ R`, and
let `𝔭` be a prime of `R` at which `H⁰(K) ⊗ κ(𝔭) ⟶ H⁰(K ⊗^L κ(𝔭))` is surjective.  Then after
inverting some `f ∉ 𝔭`,

`K_f ≅ R_f[0] ⊕ P`

with `P` a bounded complex of finite projective `R_f`-modules in degrees `≥ 1`.  This is Stacks
0A1U at `i = 0`, with the lower truncation identified: it is `H⁰(K_f)[0] = R_f[0]` because
`K_f` has no cohomology in negative degrees.  It is the algebraic step of the proof of part (b)
of Stacks 0E6B.

## Main results

* `StacksDraft.Perfect.exists_localization_iso_single_biprod`.
* `StacksDraft.Perfect.exists_derivedExtension_iso_single_biprod`: the same, read after derived
  extension of scalars to an arbitrary localization `R'` of `R` away from `f`.
* `StacksDraft.Perfect.cohomologyBaseChangeSurjective_zero_of_epi_homology_map`: the degree-zero
  base change map is surjective as soon as some `R[0] ⟶ K` hits `H⁰(K ⊗^L κ(𝔭))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

universe u

/-- A module isomorphic to `R` localizes to `R_f`. -/
def localizedModuleIsoOfIsoSelf {R : Type u} [CommRing R] (f : R) {M : ModuleCat.{u} R}
    (e : M ≅ ModuleCat.of R R) :
    ModuleCat.of (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) ≅
      ModuleCat.of (Localization.Away f) (Localization.Away f) :=
  letI : IsLocalizedModule (Submonoid.powers f)
      ((Algebra.linearMap R (Localization.Away f)) ∘ₗ e.toLinearEquiv.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ _
  ((IsLocalizedModule.iso (Submonoid.powers f)
    ((Algebra.linearMap R (Localization.Away f)) ∘ₗ
      e.toLinearEquiv.toLinearMap)).extendScalarsOfIsLocalization (Submonoid.powers f)
        (Localization.Away f)).toModuleIso

/-- **Stacks 0A1U at `i = 0`, with `τ_{≤ 0}` identified.**  Let `K` be a pseudo-coherent object
of `D(R)` with `H^j(K) = 0` for `j < 0` and `H⁰(K) ≅ R`, and let `𝔭` be a prime at which
`H⁰(K) ⊗ κ(𝔭) ⟶ H⁰(K ⊗^L κ(𝔭))` is surjective.  Then there is `f ∉ 𝔭` with
`K_f ≅ R_f[0] ⊕ P` in `D(R_f)`, for `P` a bounded complex of finite projective `R_f`-modules
concentrated in degrees `≥ 1`. -/
theorem exists_localization_iso_single_biprod {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (hGE : K.IsGE 0)
    (e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj K ≅ ModuleCat.of R R)
    (hbase : CohomologyBaseChangeSurjective.{u, u} p K 0) :
    ∃ f : R, f ∉ p ∧ ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ) (b : ℤ),
      P.IsStrictlyGE 1 ∧ P.IsStrictlyLE b ∧
      (∀ j : ℤ, Module.Finite (Localization.Away f) (P.X j)) ∧
      (∀ j : ℤ, Module.Projective (Localization.Away f) (P.X j)) ∧
      Nonempty ((PseudoCoherence.localizationAwayFunctorAux.{u, u} f).obj K ≅
        (DerivedCategory.singleFunctor _ 0).obj
            (ModuleCat.of (Localization.Away f) (Localization.Away f)) ⊞
          DerivedCategory.Q.obj P) := by
  obtain ⟨f, hf, h⟩ := exists_localization_perfect_truncGE_and_iso_biprod.{u, u} p K hK 0 hbase
  obtain ⟨-, ⟨P, b, hP1, hPb, hfin, hproj, ⟨eu⟩, -⟩, ⟨e', -⟩⟩ := h
  set Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, u} f).obj K
  have hKf : Kf.IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    intro n hn
    exact PseudoCoherence.localizationAway_homology_isZero.{u, u} f K n
      (K.isZero_of_isGE 0 n hn)
  set lower := (DerivedCategory.TStructure.t.truncLE 0).obj Kf
  have : lower.IsGE 0 := inferInstanceAs (DerivedCategory.TStructure.t.IsGE
    ((DerivedCategory.TStructure.t.truncLE 0).obj Kf) 0)
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE lower 0
  have hι := Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app 0 0 le_rfl Kf
  let eYR : Y ≅ ModuleCat.of (Localization.Away f) (Localization.Away f) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso eY.symm ≪≫
      asIso ((DerivedCategory.homologyFunctor _ 0).map
        ((DerivedCategory.TStructure.t.truncLEι 0).app Kf)) ≪≫
      PseudoCoherence.localizationAwayHomologyIso.{u, u} f K 0 ≪≫
      localizedModuleIsoOfIsoSelf f e
  exact ⟨f, hf, P, b, by simpa using hP1, hPb, hfin, hproj, ⟨e' ≪≫ biprod.mapIso
    (eY ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eYR) eu⟩⟩

/-- Extension of scalars along a localization away from `f` preserves finite limits. -/
private theorem preservesFiniteLimits_extendScalars_away {R : Type u} [CommRing R] (f : R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away f S] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers f)))

/-- **Stacks 0A1U at `i = 0`, at an arbitrary localization.**  Under the hypotheses of
`StacksDraft.Perfect.exists_localization_iso_single_biprod` there is `f ∉ 𝔭` such that for every
localization `R'` of `R` away from `f`, `K ⊗^L_R R' ≅ R'[0] ⊕ P` with `P` a bounded complex of
finite projective `R'`-modules in degrees `≥ 1`. -/
theorem exists_derivedExtension_iso_single_biprod {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (hGE : K.IsGE 0)
    (e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj K ≅ ModuleCat.of R R)
    (hbase : CohomologyBaseChangeSurjective.{u, u} p K 0) :
    ∃ f : R, f ∉ p ∧ ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [IsLocalization.Away f R'],
      ∃ (P : CochainComplex (ModuleCat.{u} R') ℤ) (b : ℤ),
        P.IsStrictlyGE 1 ∧ P.IsStrictlyLE b ∧
        (∀ j : ℤ, Module.Finite R' (P.X j)) ∧ (∀ j : ℤ, Module.Projective R' (P.X j)) ∧
        Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap R R')).functor.obj K ≅
          (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R' R') ⊞
            DerivedCategory.Q.obj P) := by
  obtain ⟨f, hf, P, b, hP1, hPb, hfin, hproj, ⟨eK⟩⟩ :=
    exists_localization_iso_single_biprod p K hK hGE e hbase
  refine ⟨f, hf, fun R' _ _ _ => ?_⟩
  let a := IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) R'
  let ψ : Localization.Away f →+* R' := a.toRingEquiv
  have hψ : ψ.comp (algebraMap R (Localization.Away f)) = algebraMap R R' :=
    RingHom.ext fun x => a.commutes x
  let G := ModuleCat.extendScalars.{u, u, u} ψ
  have : PreservesFiniteLimits G :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.Flat.of_bijective a.toRingEquiv.bijective)
  have := preservesFiniteLimits_extendScalars_away f (Localization.Away f)
  have := preservesFiniteLimits_extendScalars_away f R'
  let _ : Algebra (Localization.Away f) R' := ψ.toAlgebra
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, b, inferInstance, inferInstance,
    fun j => ?_, fun j => ?_, ⟨?_⟩⟩
  · show Module.Finite R' (TensorProduct (Localization.Away f) R' (P.X j))
    infer_instance
  · show Module.Projective R' (TensorProduct (Localization.Away f) R' (P.X j))
    infer_instance
  have : (G.mapDerivedCategory).Additive := inferInstance
  have := preservesBinaryBiproducts_of_preservesBiproducts G.mapDerivedCategory
  exact (Dualizing.totalDerivedExtensionScalarsIsoExtendScalars (algebraMap R R')).app K ≪≫
    ((Dualizing.extendScalarsCompMapDerivedCategoryIso _ ψ _ hψ).app K).symm ≪≫
    G.mapDerivedCategory.mapIso
      ((Dualizing.extendScalarsIsoLocalizationAwayFunctorAux f).app K ≪≫ eK) ≪≫
    G.mapDerivedCategory.mapBiprod _ _ ≪≫
    biprod.mapIso ((G.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (ModuleCat.ExtendScalars.objSelfIso ψ))
      (G.mapDerivedCategoryFactors.app P)

/-- If `φ : L ⟶ P` is a chain map out of a complex concentrated in degrees `≤ 0` whose image
under an additive functor `F` is surjective on `H⁰`, then every degree-zero cycle of `F(P)` is
cohomologous to the image under `F` of a cycle of `P`. -/
private theorem exists_cyclesMk_map_iCycles_of_epi_homologyMap {R S : Type u} [Ring R] [Ring S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.PreservesZeroMorphisms]
    {L P : CochainComplex (ModuleCat.{u} R) ℤ} [L.IsStrictlyLE 0] (φ : L ⟶ P)
    (h : Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0))
    (x : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).cycles 0) :
    ∃ y : F.obj (P.cycles 0),
      ∃ hy : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).d 0 (0 + 1)
        (F.map (P.iCycles 0) y) = 0,
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homologyπ 0
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).cyclesMk
            (F.map (P.iCycles 0) y) (0 + 1) (by simp) hy) =
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homologyπ 0 x := by
  let Lκ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let Pκ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let φκ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective _).1 h (Pκ.homologyπ 0 x)
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (Lκ.homologyπ 0)).1 inferInstance w
  have hL1 : L.d 0 (0 + 1) = 0 := (L.isZero_of_isStrictlyLE 0 (0 + 1) (by omega)).eq_of_tgt _ _
  have hφd : φ.f 0 ≫ P.d 0 (0 + 1) = 0 := by
    rw [φ.comm, hL1, zero_comp]
  let ψ := P.liftCycles (φ.f 0) (0 + 1) (by simp) hφd
  have hmor : Lκ.iCycles 0 ≫ F.map ψ ≫ F.map (P.iCycles 0) =
      HomologicalComplex.cyclesMap φκ 0 ≫ Pκ.iCycles 0 := by
    rw [← F.map_comp, P.liftCycles_i, HomologicalComplex.cyclesMap_i]
    rfl
  have hyeq : F.map (P.iCycles 0) (F.map ψ (Lκ.iCycles 0 c)) =
      Pκ.iCycles 0 (HomologicalComplex.cyclesMap φκ 0 c) := by
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hmor c
  have hd : Pκ.d 0 (0 + 1) (F.map (P.iCycles 0) (F.map ψ (Lκ.iCycles 0 c))) = 0 := by
    rw [hyeq, ← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  refine ⟨F.map ψ (Lκ.iCycles 0 c), hd, ?_⟩
  have hmk : Pκ.cyclesMk (F.map (P.iCycles 0) (F.map ψ (Lκ.iCycles 0 c))) (0 + 1) (by simp) hd =
      HomologicalComplex.cyclesMap φκ 0 c := by
    apply (ModuleCat.mono_iff_injective (Pκ.iCycles 0)).1 inferInstance
    rw [← hyeq]
    exact Pκ.i_cyclesMk _ _ _ _
  rw [hmk, ← hw, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    HomologicalComplex.homologyπ_naturality]

/-- **The degree-zero base change map is surjective when `R` already hits the fibre.**  Let `K` be
a pseudo-coherent object of `D(R)` and `η : R[0] ⟶ K` a morphism such that the induced map
`κ(𝔭) = H⁰(κ(𝔭)[0]) ⟶ H⁰(K ⊗^L_R κ(𝔭))` is surjective.  Then
`H⁰(K) ⊗_R κ(𝔭) ⟶ H⁰(K ⊗^L_R κ(𝔭))` is surjective. -/
theorem cohomologyBaseChangeSurjective_zero_of_epi_homology_map {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (η : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶ K)
    (hη : Epi ((DerivedCategory.homologyFunctor _ 0).map
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R p.ResidueField)).functor.map η))) :
    CohomologyBaseChangeSurjective.{u, u} p K 0 := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  refine ⟨P, hP, ⟨e⟩, ?_⟩
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R p.ResidueField)
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R p.ResidueField)
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  have hLff := StacksDraft.PseudoCoherence.isBoundedFiniteFree_single (ModuleCat.of R R) 0
  have : L.IsKProjective := StacksDraft.PseudoCoherence.isKProjective_of_boundedFiniteFree hLff
  obtain ⟨φ, hφ⟩ := StacksDraft.PseudoCoherence.exists_chainMap_of_isKProjective L P (η ≫ e.inv)
  have : ∀ i, Projective (L.X i) := fun i =>
    have := (hLff.finiteFree i).2
    ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  have : IsIso (D.comparison.app L) := D.comparison_isIso_of_projective L 0
  let φκ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  have hnat : D.functor.map (DerivedCategory.Q.map φ) ≫ D.comparison.app P =
      D.comparison.app L ≫ DerivedCategory.Q.map φκ := D.comparison.naturality φ
  have hsq : (DerivedCategory.homologyFunctor _ 0).map (D.functor.map η) =
      (DerivedCategory.homologyFunctor _ 0).map (D.functor.map (DerivedCategory.Q.map φ)) ≫
        (DerivedCategory.homologyFunctor _ 0).map (D.functor.map e.hom) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hφ, Category.assoc, e.inv_hom_id,
      Category.comp_id]
  obtain ⟨b, hb⟩ := hP.upperBound
  have : ∀ i, Projective (P.X i) := fun i =>
    have := (hP.finiteFree i).2
    ModuleCat.projective_of_free (Module.Free.chooseBasis R _)
  have : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  have h1 : Epi ((DerivedCategory.homologyFunctor _ 0).map
      (D.functor.map (DerivedCategory.Q.map φ))) := by
    rwa [← epi_comp_iff_of_isIso _ ((DerivedCategory.homologyFunctor _ 0).map
      (D.functor.map e.hom)), ← hsq]
  have h2 : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) 0).map
      (DerivedCategory.Q.map φκ)) := by
    have : Epi ((DerivedCategory.homologyFunctor _ 0).map
        (D.functor.map (DerivedCategory.Q.map φ) ≫ D.comparison.app P)) := by
      rw [Functor.map_comp]
      infer_instance
    exact @epi_of_epi_fac _ _ _ _ _ ((DerivedCategory.homologyFunctor _ 0).map
      (D.comparison.app L)) _ _ this
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) 0).map_comp
        (D.comparison.app L) (DerivedCategory.Q.map φκ)).symm.trans
          (congrArg (DerivedCategory.homologyFunctor _ 0).map hnat.symm))
  have h3 : Epi (HomologicalComplex.homologyMap φκ 0) := by
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) 0).map
        (DerivedCategory.Q.map φκ) ≫ (DerivedCategory.homologyFunctorFactors _ 0).hom.app _) :=
      @epi_comp _ _ _ _ _ _ h2 _ inferInstance
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ this
      (DerivedCategory.homologyFunctorFactors_hom_naturality φκ 0).symm
  exact exists_cyclesMk_map_iCycles_of_epi_homologyMap F φ h3

/-- Over a field `R`, a nonzero morphism `R[0] ⟶ N` to an object with `H⁰(N) ≅ R` is surjective
on `H⁰`. -/
theorem epi_homologyFunctor_map_of_ne_zero {R : Type u} [CommRing R] (hR : IsField R)
    {N : DerivedCategory (ModuleCat.{u} R)}
    (eN : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj N ≅ ModuleCat.of R R)
    (f : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶ N)
    (hf : f ≠ 0) : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f) := by
  have : Projective (ModuleCat.of R R) :=
    ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)
  let ι := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app
    (ModuleCat.of R R)
  let m : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    ι.inv ≫ (DerivedCategory.homologyFunctor _ 0).map f ≫ eN.hom
  have hm : m ≠ 0 := by
    intro h
    apply hf
    apply (DerivedCategory.bijective_homologyFromSingle_of_projective (ModuleCat.of R R) N 0).1
    rw [map_zero, DerivedCategory.homologyFromSingle_apply]
    exact (cancel_mono eN.hom).1 (by rwa [zero_comp, Category.assoc])
  have h1 : m.hom 1 ≠ 0 := by
    intro h
    apply hm
    ext1
    refine LinearMap.ext fun x => ?_
    rw [show x = x • (1 : R) by simp, map_smul, h, smul_zero]
    rfl
  obtain ⟨c, hc⟩ := hR.mul_inv_cancel h1
  have hsurj : Function.Surjective m.hom := fun y => ⟨y * c, by
    rw [show y * c = (y * c) • (1 : R) by simp, map_smul, smul_eq_mul, mul_assoc, mul_comm c, hc,
      mul_one]⟩
  have : Epi m := (ModuleCat.epi_iff_surjective m).2 hsurj
  have hfm : (DerivedCategory.homologyFunctor _ 0).map f = ι.hom ≫ m ≫ eN.inv := by
    simp only [m, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [hfm]
  infer_instance

/-- Surjectivity on `Hⁿ` of a derived base change `- ⊗^L_A A'` is kept by a further base change
along a ring isomorphism `A' ≅ L`. -/
theorem epi_homologyFunctor_map_totalDerivedExtensionScalars_comp_ringEquiv
    {A A' L : Type u} [CommRing A] [CommRing A'] [CommRing L] (φ : A →+* A') (e : A' ≃+* L)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ K') (n : ℤ)
    (h : Epi ((DerivedCategory.homologyFunctor _ n).map
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor.map
        f))) :
    Epi ((DerivedCategory.homologyFunctor _ n).map
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ((e : A' →+* L).comp φ)).functor.map f)) := by
  let ψ : A' →+* L := e
  let G := ModuleCat.extendScalars.{u, u, u} ψ
  have : PreservesFiniteLimits G :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _ (RingHom.Flat.of_bijective e.bijective)
  let Dφ :=
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor
  have h1 : Epi ((DerivedCategory.homologyFunctor _ n).map (G.mapDerivedCategory.map (Dφ.map f))) :=
    (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso (G.mapDerivedCategoryHomologyIso n)
      (Dφ.map f)).2 (G.map_epi _)
  have h2 : Epi ((DerivedCategory.homologyFunctor _ n).map
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
        (Dφ.map f))) :=
    (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso (Functor.isoWhiskerRight
      (Dualizing.totalDerivedExtensionScalarsIsoExtendScalars ψ)
        (DerivedCategory.homologyFunctor _ n)) (Dφ.map f)).2 h1
  exact (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso (Functor.isoWhiskerRight
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp φ ψ)
      (DerivedCategory.homologyFunctor _ n)) f).1 h2

end StacksDraft.Perfect
