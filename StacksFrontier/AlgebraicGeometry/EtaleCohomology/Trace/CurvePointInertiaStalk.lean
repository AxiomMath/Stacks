module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsInjectionInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurvePointInertiaGeometry
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineOpenCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationGaloisInvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationSize
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDiscreteValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CurvePointInertia
public import StacksFrontier.RingTheory.Invariant.StrictHenselizationInertiaEmbedding

/-!
# `H⁰_loc` at a missing point of a curve is the module of inertia invariants

Let `W` be an open subscheme of the affine line over `k`, `j : V ⟶ W` an open immersion, `y` a
closed point of `W` outside `V`, and `ℱ` the `ℓ`-adic sheaf on `V` of an integral continuous
representation `ρ₀ : π₁(V, x̄) → GL_r(ℤ_ℓ)`. The stalk at `ȳ` of `j_*` of each level of `ℱ`
embeds `ℤ_ℓ`-semilinearly into `(ℤ/ℓⁿ⁺¹)^r`, compatibly with the transition maps, the
intertwiners of `ρ₀` and the geometric Frobenius, and the images contain the reductions of the
vectors of `ℤ_ℓ^r` fixed by the inertia at `y`.

## Main results

* `Stacks.EtaleCohomology.curvePointInertiaStalkInput`: the statement
  `Stacks.EtaleCohomology.CurvePointInertiaStalkInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.Scheme IsLocalRing
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  GeometricPoint.residueFieldAlgebra

/-- Ring homomorphisms whose induced maps on spectra satisfy a commutation relation satisfy
the reversed relation pointwise. -/
private theorem comp_apply_eq_of_specMap_comp_eq.{v} {R S S' T : CommRingCat.{v}} (f : R ⟶ S)
    (g : S ⟶ T) (f' : R ⟶ S') (g' : S' ⟶ T)
    (h : Spec.map g ≫ Spec.map f = Spec.map g' ≫ Spec.map f') (x : R) :
    g.hom (f.hom x) = g'.hom (f'.hom x) :=
  congrArg (fun φ => φ.hom x)
    (Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact h) : f ≫ g = f' ≫ g')

/-- The stalk at a missing point of `j_*` of the levels of the `ℓ`-adic sheaf of an integral
representation `ρ₀` is the module of inertia invariants, in the sense of
`Stacks.EtaleCohomology.CurvePointInertiaStalkInput`. -/
theorem curvePointInertiaStalkInput : CurvePointInertiaStalkInput.{u} := by
  intro B V ℓ i1 i2 i3 i4 i5 i6 i7 i8 k i9 i10 f i11 i12 i13 i14 j kbar i15 i16 i17 i18 p n i19
    i20 hcard hℓp W fW i21 i22 i23 i24 eW i25 heW jW i26 hjW y hyc hyV hy L Ω i27 i28 i29 i30 i31
    i32 i33 i34 i35 A i36 i37 i38 i39 i40 i41 i42 i43 eA hA P i44 Fr hFrD hFr r ρ₀ hρ₀ i45
  intro x ℱ stalk D
  let s : GeometricPoint W.1 := Stacks.Frobenius.geometricPointAt W.1 y
  have hcy : s.hom (closedPoint s.residueField) = y :=
    (congrArg (fun z => s.hom z) (Subsingleton.elim (closedPoint s.residueField) _)).trans
      (Stacks.Frobenius.geometricPointAt_liesOver W.1 y)
  let eAc : A ≃+* W.1.presheaf.stalk (s.hom (closedPoint s.residueField)) :=
    eA.trans (W.1.presheaf.stalkCongr (Inseparable.of_eq hcy.symm)).commRingCatIsoToRingEquiv
  have : IsDomain (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))) :=
    Function.Injective.isDomain (eAc.symm : _ →+* A) eAc.symm.injective
  have : IsDiscreteValuationRing (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eAc
  have : Nonempty W.1 := ⟨y⟩
  have : IrreducibleSpace W.1 := irreducibleSpace_of_isOpenImmersion_affineLine eW
  have hcV : s.hom (closedPoint s.residueField) ∉ Set.range jW.base := by rwa [hcy]
  have : IsNoetherianRing (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))) :=
    PrincipalIdealRing.isNoetherianRing
  have : QuasiCompact jW := quasiCompact_of_noetherianSpace_source jW
  obtain ⟨hHdom, hHdvr⟩ := @isDomain_and_isDiscreteValuationRing_etaleLocalRing B W.1 W.2 s
    inferInstance inferInstance inferInstance
  obtain ⟨ϖ, hϖ, e, he, -⟩ := @exists_directImageStalkIso_localizationAway B W.1 W.2 s
    inferInstance inferInstance inferInstance inferInstance V.1 jW inferInstance inferInstance
    ⟨genericPoint V.1⟩ hcV
    ((sheafCompose _ (forget (ModuleCat.{u + 1} ℤ_[ℓ]))).obj
      (padicLevelMathlib B V x ρ₀ hρ₀ 0))
  have hfr : IsFractionRing (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ) :=
    isFractionRing_localizationAway_of_irreducible (etaleLocalRing B W.1 W.2 s) hϖ
  let : Field (Localization.Away ϖ) := IsFractionRing.toField (etaleLocalRing B W.1 W.2 s)
  have hKc : B.Contains (Spec (.of (Localization.Away ϖ))) :=
    (Scheme.size_congr e).symm.trans_lt (Scheme.size_pullback_lt jW
      (strictHenselizationToBase B W.1 W.2 s) V.2 (contains_strictHenselization B W.1 W.2 s))
  let g : B.obj (Spec (.of (Localization.Away ϖ))) hKc ⟶ V :=
    ObjectProperty.homMk (e.inv ≫ pullback.fst jW (strictHenselizationToBase B W.1 W.2 s))
  have hg : B.inclusion.map g = e.inv ≫ pullback.fst jW (strictHenselizationToBase B W.1 W.2 s) :=
    rfl
  let : Algebra (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (etaleLocalRing B W.1 W.2 s) := etaleLocalRingAlgebra B W.1 W.2 s
  have : IsLocalHom (algebraMap (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (etaleLocalRing B W.1 W.2 s)) := isLocalHom_algebraMap_etaleLocalRing B W.1 W.2 s
  let : Algebra A (etaleLocalRing B W.1 W.2 s) :=
    ((algebraMap (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (etaleLocalRing B W.1 W.2 s)).comp eAc.toRingHom).toAlgebra
  have halgH : ∀ a : A, algebraMap A (etaleLocalRing B W.1 W.2 s) a =
      algebraMap (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
        (etaleLocalRing B W.1 W.2 s) (eAc a) := fun _ => rfl
  have : IsLocalHom (algebraMap A (etaleLocalRing B W.1 W.2 s)) := ⟨fun a ha => by
    rw [halgH] at ha
    exact (isUnit_map_iff eAc a).mp (isUnit_of_map_unit _ _ ha)⟩
  have hInd : StacksDraft.IndEtale A (etaleLocalRing B W.1 W.2 s) :=
    StacksDraft.indEtale_of_equiv eAc.symm (RingEquiv.refl (etaleLocalRing B W.1 W.2 s))
      (fun a => by
        rw [halgH, RingEquiv.apply_symm_apply]
        rfl)
      (indEtale_etaleLocalRing B W.1 W.2 s)
  have : IsSepClosure (ResidueField A) (ResidueField (etaleLocalRing B W.1 W.2 s)) := by
    have hsc := isSepClosure_residueField_etaleLocalRing B W.1 W.2 s
    have he1 : (algebraMap (ResidueField A) (ResidueField (etaleLocalRing B W.1 W.2 s))).comp
        ((ResidueField.mapEquiv eAc).symm : ResidueField (W.1.presheaf.stalk
          (s.hom (closedPoint s.residueField))) →+* ResidueField A) =
        ((RingEquiv.refl (ResidueField (etaleLocalRing B W.1 W.2 s))) :
          ResidueField (etaleLocalRing B W.1 W.2 s) →+* _).comp
          (algebraMap (ResidueField (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))))
            (ResidueField (etaleLocalRing B W.1 W.2 s))) := by
      refine RingHom.ext fun z => ?_
      obtain ⟨a, rfl⟩ := residue_surjective z
      have h1 : (ResidueField.mapEquiv eAc).symm (residue _ a) = residue A (eAc.symm a) :=
        ResidueField.map_residue _ _
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ResidueField.algebraMap_residue,
        RingEquiv.refl_apply, halgH, RingEquiv.apply_symm_apply]
    exact ⟨hsc.sep_closed, @Algebra.IsSeparable.of_equiv_equiv _ _ _ _ _ _ _ _ _ _
      (ResidueField.mapEquiv eAc).symm (RingEquiv.refl _) he1 hsc.separable⟩
  have : IsSepClosed L := IsSepClosure.sep_closed (V.1.residueField (genericPoint V.1))
  have hGal : IsGalois (V.1.residueField (genericPoint V.1)) L := IsSepClosure.isGalois
  have hNor : Normal (V.1.residueField (genericPoint V.1)) L := hGal.to_normal
  have : P.LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  let Φ : (etaleLocalRing B W.1 W.2 s) ≃ₐ[A]
      IsIntegralClosure.inertiaInvariants A (V.1.residueField (genericPoint V.1)) L P :=
    Classical.choice (IsIntegralClosure.nonempty_algEquiv_inertiaInvariants_of_indEtale A
      (V.1.residueField (genericPoint V.1)) L P (etaleLocalRing B W.1 W.2 s) hInd)
  obtain ⟨ι, hιH, hιrange⟩ :=
    IsIntegralClosure.exists_ringHom_fractionRing_range_eq_inertiaFixedField A
      (V.1.residueField (genericPoint V.1)) L P (etaleLocalRing B W.1 W.2 s) Φ
      (Localization.Away ϖ)
  let ι' : Localization.Away ϖ →+* Ω := (algebraMap L Ω).comp ι
  have hΦA : ∀ a : A, ((Φ (algebraMap A (etaleLocalRing B W.1 W.2 s) a) :
      IsIntegralClosure.localizedSubring P) : L) = algebraMap A L a := fun a => by
    rw [Φ.commutes]
    exact IsIntegralClosure.coe_algebraMap_inertiaInvariants A
      (V.1.residueField (genericPoint V.1)) L P a
  have hι'A : ∀ a : A, ι' (algebraMap (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ)
      (algebraMap A (etaleLocalRing B W.1 W.2 s) a)) =
      algebraMap (V.1.residueField (genericPoint V.1)) Ω
        (algebraMap A (V.1.residueField (genericPoint V.1)) a) := fun a => by
    simp only [ι', RingHom.comp_apply, hιH, hΦA]
    rw [IsScalarTower.algebraMap_apply A (V.1.residueField (genericPoint V.1)) L,
      ← IsScalarTower.algebraMap_apply (V.1.residueField (genericPoint V.1)) L Ω]
  let gA : A →+* Localization.Away ϖ := (algebraMap (etaleLocalRing B W.1 W.2 s)
    (Localization.Away ϖ)).comp (algebraMap A (etaleLocalRing B W.1 W.2 s))
  have hgA : Function.Injective gA := by
    intro a b hab
    have h := congrArg ι' hab
    simp only [gA, RingHom.comp_apply, hι'A] at h
    exact IsFractionRing.injective A (V.1.residueField (genericPoint V.1))
      ((algebraMap (V.1.residueField (genericPoint V.1)) Ω).injective h)
  let γ : V.1.residueField (genericPoint V.1) →+* Localization.Away ϖ :=
    IsFractionRing.lift (A := A) hgA
  have hγ : ι'.comp γ = algebraMap (V.1.residueField (genericPoint V.1)) Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, γ, IsFractionRing.lift_algebraMap, gA]
    exact hι'A a
  have halg : let := ι'.toAlgebra; Algebra.IsAlgebraic (Localization.Away ϖ) Ω := by
    let : Algebra (Localization.Away ϖ) Ω := ι'.toAlgebra
    let : Algebra (V.1.residueField (genericPoint V.1)) (Localization.Away ϖ) := γ.toAlgebra
    have : IsScalarTower (V.1.residueField (genericPoint V.1)) (Localization.Away ϖ) Ω :=
      IsScalarTower.of_algebraMap_eq fun z => (RingHom.congr_fun hγ z).symm
    exact Algebra.IsAlgebraic.tower_top (K := V.1.residueField (genericPoint V.1))
      (L := Localization.Away ϖ)
  let t : GeometricPoint (Spec (.of (Localization.Away ϖ))) :=
    ⟨Ω, Spec.map (CommRingCat.ofHom ι')⟩
  have ht : t.IsAlgebraic := isAlgebraic_specMap_geometricPoint ι' halg
  have hc' : jW.base (genericPoint V.1) ⤳ s.hom (closedPoint s.residueField) := by
    rwa [hcy]
  have hcomp : (W.1.presheaf.stalkCongr (Inseparable.of_eq hcy.symm)).hom ≫
      curveLocalRingToFunctionField jW hc' = curveLocalRingToFunctionField jW hy := by
    simp only [curveLocalRingToFunctionField, TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.stalkSpecializes_comp_assoc _ _ _ _
  have hring : ∀ r, ι' (algebraMap (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ)
      (structureSheafStalkFromLocalRing B W.1 W.2 s r)) =
      (CommRingCat.ofHom (algebraMap (V.1.residueField (genericPoint V.1)) Ω)).hom
        ((curveLocalRingToFunctionField jW hc').hom r) := by
    intro r
    obtain ⟨a, rfl⟩ := eAc.surjective r
    have h1 := congrArg (fun φ => φ.hom (eA a)) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
    show ι' (algebraMap (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ)
      (algebraMap A (etaleLocalRing B W.1 W.2 s) a)) = _
    rw [hι'A, hA a]
    exact congrArg _ h1.symm
  have hxg : t.hom ≫ B.inclusion.map g = x.hom := by
    rw [hg]
    exact specMap_comp_inv_fst_eq_of_ringHom jW hc' (structureSheafStalkFromLocalRing B W.1 W.2 s)
      (strictHenselizationToBase B W.1 W.2 s) rfl e he ι'
      (CommRingCat.ofHom (algebraMap (V.1.residueField (genericPoint V.1)) Ω)) hring
  have : ConnectedSpace (B.inclusion.obj V) := i6
  let : Algebra ((Spec (.of (Localization.Away ϖ))).residueField (t.hom default)) t.residueField :=
    GeometricPoint.residueFieldAlgebra t
  let pth : finiteEtaleFiberFunctor (t.map (B.inclusion.map g)) ≅ finiteEtaleFiberFunctor x :=
    eqToIso (congrArg (fun f => finiteEtaleFiberFunctor (⟨Ω, f⟩ : GeometricPoint V.1)) hxg)
  let H' : ∀ n : ℕ, _ := fun n => padicLevelDirectImageStalkHom B W.1 W.2 s B V x jW
    (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth n
  let ε : ∀ n : ℕ, stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n)) →+
      (Fin r → ZMod (ℓ ^ (n + 1))) := fun n =>
    (AddEquiv.ulift (α := Fin r → ZMod (ℓ ^ (n + 1)))).toAddMonoidHom.comp
      (ConcreteCategory.hom (H' n))
  have hε : ∀ n (z : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
      ε n z = (ConcreteCategory.hom (H' n) z).down := fun _ _ => rfl
  have hεinj : ∀ n, Function.Injective (ε n) := fun n => AddEquiv.ulift.injective.comp
    (padicLevelDirectImageStalkHom_injective B W.1 W.2 s B V x jW (Localization.Away ϖ) e hKc g
      hg t ρ₀ hρ₀ pth n)
  refine ⟨ε, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hεinj
  · intro n c w
    have htors : (ℓ ^ (n + 1)) • w = 0 := hεinj n (by
      rw [map_nsmul, map_zero]
      funext i
      simp)
    show ε n (c • w) = PadicInt.toZModPow (n + 1) c • ε n w
    rw [smul_eq_toZModPow_val_nsmul n w htors, map_nsmul,
      ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1))), ZMod.natCast_zmod_val]
  · intro n w
    have h := padicLevelDirectImageStalkHom_sheafFiber_padicTransition B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth n w
    have t1 : stalk.map (D.map (LAdicSheaf.padicTransition B V ℓ ℱ n)) =
        ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).map
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW).map
            (padicLevelMathlibTransition B V x ρ₀ hρ₀ n)) := rfl
    rw [t1, hε, hε]
    funext i
    have hi := congrFun h i
    rw [levelReduction_apply] at hi
    show (ConcreteCategory.hom (padicLevelDirectImageStalkHom B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth n) _).down i =
      (levelRingHom (n + 1)) ((ConcreteCategory.hom (padicLevelDirectImageStalkHom B W.1 W.2 s B V x
        jW (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth (n + 1)) w).down i)
    convert hi using 4
  · intro M hM n w
    have h := padicLevelDirectImageStalkHom_sheafFiber_padicLevelMap B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth M hM n w
    have t1 : stalk.map (D.map (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B V x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) hρ₀ hρ₀ M hM) n)) =
        ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).map
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW).map
            (padicLevelMathlibMap B V x ρ₀ hρ₀ M hM n)) := rfl
    rw [t1, hε, hε]
    convert h using 3
  · intro n w
    let a : GeometricPoint.Hom s s := Stacks.Frobenius.frobeniusPointHom W.1 y
    obtain ⟨ã, hã⟩ := exists_iso_comp_hom_eq_baseChangeStrictHenselizationEndomorphism B W.1 W.2 s
      B V jW (Localization.Away ϖ) e t ht a
    have hãg := comp_inclusion_map_of_comp_baseChangeStrictHenselizationEndomorphism B W.1 W.2 s B
      V jW (Localization.Away ϖ) e hKc g hg t a ã.hom hã
    have hF := padicLevelDirectImageStalkHom_sheafFiber_pointSmallEtaleHom B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth a ã.hom hã hãg
      (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) ã hãg)
      (GeometricPoint.sourceAutElement_hom_eq_finiteEtaleFiberMap (S := V.1)
        (t.map (B.inclusion.map g)) ã hãg _ rfl) n w
    have t1 : Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) W.1 y
        (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n)) =
        (pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW).obj (padicLevelMathlib B V x ρ₀ hρ₀ n)) := rfl
    rw [t1, hε, hε]
    let τ : Ω →+* Ω := (Spec.preimage ã.hom).hom
    let τi : Ω →+* Ω := (Spec.preimage ã.inv).hom
    have hτ : Spec.map (CommRingCat.ofHom τ) = ã.hom := Spec.map_preimage _
    have hτi : Spec.map (CommRingCat.ofHom τi) = ã.inv := Spec.map_preimage _
    have hτ1 : ∀ z, τi (τ z) = z := comp_apply_eq_of_specMap_comp_eq (CommRingCat.ofHom τ)
      (CommRingCat.ofHom τi) (𝟙 _) (𝟙 _) (by
        rw [hτ, hτi, ã.inv_hom_id, Spec.map_id, Category.id_comp])
    have hτ2 : ∀ z, τ (τi z) = z := comp_apply_eq_of_specMap_comp_eq (CommRingCat.ofHom τi)
      (CommRingCat.ofHom τ) (𝟙 _) (𝟙 _) (by
        rw [hτ, hτi, ã.hom_inv_id, Spec.map_id, Category.id_comp])
    let τe : Ω ≃+* Ω := RingEquiv.ofRingHom τ τi (RingHom.ext hτ2) (RingHom.ext hτ1)
    obtain ⟨c, hc1, hc2⟩ := exists_ringHom_specMap_eq_conj
      (pullback.snd jW (strictHenselizationToBase B W.1 W.2 s)) e he
      (baseChangeStrictHenselizationEndomorphism B W.1 W.2 s B V jW a)
      (etaleLocalRingEndomorphism B W.1 W.2 a).hom (pullback.lift_snd _ _ _)
    have hτc : ∀ k, τ (ι' k) = ι' (c k) := comp_apply_eq_of_specMap_comp_eq (CommRingCat.ofHom ι')
      (CommRingCat.ofHom τ) (CommRingCat.ofHom c) (CommRingCat.ofHom ι') (by
        rw [hτ, hc1]
        exact hã)
    let θA : etaleLocalRing B W.1 W.2 s →ₐ[A] etaleLocalRing B W.1 W.2 s :=
      { (etaleLocalRingEndomorphism B W.1 W.2 a).hom with
        commutes' := fun z => by
          show (etaleLocalRingEndomorphism B W.1 W.2 a).hom
            (structureSheafStalkFromLocalRing B W.1 W.2 s (eAc z)) =
            structureSheafStalkFromLocalRing B W.1 W.2 s (eAc z)
          exact RingHom.congr_fun
            (etaleLocalRingEndomorphism_comp_structureSheafStalkFromLocalRing B W.1 W.2 a) _ }
    have hθiso : IsIso (etaleLocalRingEndomorphism B W.1 W.2 a) := by
      have := geometricPointStalkMap_isIso B W.1 W.2 a RingCat.{u}
      exact NatIso.isIso_app_of_isIso _ _
    have : IsLocalHom θA := ⟨fun z hz => (isUnit_map_iff
      (asIso (etaleLocalRingEndomorphism B W.1 W.2 a)).ringCatIsoToRingEquiv z).mp hz⟩
    have hcardA : Nat.card (ResidueField A) = Nat.card (W.1.residueField y) :=
      Nat.card_congr (ResidueField.mapEquiv eA).toEquiv
    have hθres : ∀ h, residue _ (θA h) ^ Nat.card (ResidueField A) = residue _ h := fun h => by
      rw [hcardA]
      exact residue_etaleLocalRingEndomorphism_pow B W.1 W.2 a _
        (frobeniusPointHom_preimage_pow W.1 y) h
    let := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    have hFrq : Fr • P = P := MulAction.mem_stabilizer_iff.mp hFrD
    have hFrΦ := IsIntegralClosure.galAction_algEquiv_comp_eq_of_residue_pow A
      (V.1.residueField (genericPoint V.1)) L P (etaleLocalRing B W.1 W.2 s) hInd Φ θA Fr hFrq _
      hFr hθres
    have : IsAlgClosure (V.1.residueField (genericPoint V.1)) Ω := ⟨inferInstance, inferInstance⟩
    have : Normal (V.1.residueField (genericPoint V.1)) Ω := IsAlgClosure.normal _ _
    let G : Ω ≃ₐ[V.1.residueField (genericPoint V.1)] Ω := AlgEquiv.liftNormal Fr⁻¹ Ω
    have hG : ∀ l : L, G (algebraMap L Ω l) = algebraMap L Ω (Fr⁻¹ l) :=
      AlgEquiv.liftNormal_commutes Fr⁻¹ Ω
    let β : Ω ≃+* Ω := τe.trans G.symm.toRingEquiv
    have hβι : ∀ k, β (ι' k) = ι' k := by
      have hext : (β.toRingHom).comp ι' = ι' := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors (etaleLocalRing B W.1 W.2 s))
          (RingHom.ext fun h => ?_)
        show G.symm (τ (ι' (algebraMap _ _ h))) = ι' (algebraMap _ _ h)
        rw [hτc, hc2]
        show G.symm (algebraMap L Ω (ι (algebraMap _ _ (θA h)))) =
          algebraMap L Ω (ι (algebraMap _ _ h))
        rw [hιH, hιH]
        have h1 : ((Φ (θA h) : IsIntegralClosure.localizedSubring P) : L) =
            Fr⁻¹ ((Φ h : IsIntegralClosure.localizedSubring P) : L) := by
          rw [← hFrΦ h]; exact (Fr.symm_apply_apply _).symm
        rw [h1, ← hG, AlgEquiv.symm_apply_apply]
      exact fun k => RingHom.congr_fun hext k
    let αG : t.source ≅ t.source :=
      Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso G.toRingEquiv).op
    let αβ : t.source ≅ t.source := Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso β).op
    have hdec : ã.hom = (αG ≪≫ αβ).hom := by
      rw [← hτ]
      show Spec.map (CommRingCat.ofHom τ) =
        Spec.map (CommRingCat.ofHom (G.toRingEquiv : Ω →+* Ω)) ≫
          Spec.map (CommRingCat.ofHom (β : Ω →+* Ω))
      rw [← Spec.map_comp]
      congr 1
      ext z
      show τ z = G (G.symm (τ z))
      rw [AlgEquiv.apply_symm_apply]
    have hβt : αβ.hom ≫ t.hom = t.hom := by
      show Spec.map (CommRingCat.ofHom (β : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom ι') =
        Spec.map (CommRingCat.ofHom ι')
      rw [← Spec.map_comp]
      congr 1
      ext k
      exact hβι k
    have hGx : αG.hom ≫ x.hom = x.hom := by
      show Spec.map (CommRingCat.ofHom (G.toRingEquiv : Ω →+* Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (V.1.residueField (genericPoint V.1)) Ω)) ≫
          V.1.fromSpecResidueField (genericPoint V.1) = _
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      ext z
      exact G.commutes z
    have hGt : αG.hom ≫ (t.map (B.inclusion.map g)).hom = (t.map (B.inclusion.map g)).hom := by
      show αG.hom ≫ t.hom ≫ B.inclusion.map g = t.hom ≫ B.inclusion.map g
      rw [hxg]
      exact hGx
    have hβtg : αβ.hom ≫ (t.map (B.inclusion.map g)).hom = (t.map (B.inclusion.map g)).hom := by
      show αβ.hom ≫ t.hom ≫ B.inclusion.map g = t.hom ≫ B.inclusion.map g
      rw [← Category.assoc, hβt]
    have hσdec : GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) ã hãg =
        GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) αG hGt *
          GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) αβ hβtg := by
      rw [← GeometricPoint.sourceAutElement_trans]
      exact GeometricPoint.sourceAutElement_congr (S := V.1) _ hdec _
    have hres : G.restrictNormal L = Fr⁻¹ := AlgEquiv.ext fun l =>
      (algebraMap L Ω).injective ((G.restrictNormal_commutes L l).trans (hG l))
    have hGφ : etaleFundamentalGroupMulEquiv pth
        (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) αG hGt) =
        galoisToFundamentalGroup V.1 L Ω Fr⁻¹ := by
      rw [← hres, galoisToFundamentalGroup_restrictNormal_eq_sourceAutElement V.1 L Ω G hGx]
      exact (etaleFundamentalGroupMulEquiv_eqToIso_sourceAutElement (S := V.1) hxg αG hGt).trans
        rfl
    have hβfix : levelRepresentation ρ₀ (n + 1) (etaleFundamentalGroupMulEquiv pth
        (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) αβ hβtg))
        (ConcreteCategory.hom (H' n) w).down = (ConcreteCategory.hom (H' n) w).down := by
      obtain ⟨τ0, hτ0⟩ := GeometricPoint.exists_algEquiv_of_specMap_comp_hom t β hβt
      have : IsAlgClosure ((Spec (.of (Localization.Away ϖ))).residueField (t.hom default))
          t.residueField := ht
      have : Normal ((Spec (.of (Localization.Away ϖ))).residueField (t.hom default))
          t.residueField := IsAlgClosure.normal _ _
      have hmem := (mem_range_padicLevelDirectImageStalkHom_iff B W.1 W.2 s B V x jW
        (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth ht n
        (ULift.up (ConcreteCategory.hom (H' n) w).down)).mp ⟨w, rfl⟩
      have hαβ : αβ.hom = Spec.map (CommRingCat.ofHom τ0.toRingHom) := by
        show Spec.map (CommRingCat.ofHom (β : Ω →+* Ω)) = _
        rw [← hτ0]
        rfl
      exact hmem (τ0.restrictNormal _) τ0
        (fun z => AlgEquiv.restrictNormal_commutes τ0 _ z) αβ hαβ hβt
    have hlev : levelRepresentation ρ₀ (n + 1) (etaleFundamentalGroupMulEquiv pth
        (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) ã hãg))
        (ConcreteCategory.hom (H' n) w).down =
        levelRepresentation ρ₀ (n + 1) (galoisToFundamentalGroup V.1 L Ω Fr⁻¹)
          (ConcreteCategory.hom (H' n) w).down := by
      rw [hσdec, map_mul, map_mul, Module.End.mul_apply, hβfix, hGφ]
    convert hF.trans (hlev.trans (levelRepresentation_apply ρ₀ (n + 1) _ _)) using 3
    rfl
  · intro v hv n
    obtain ⟨z, hz⟩ := (mem_range_padicLevelDirectImageStalkHom_iff B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth ht n
      (ULift.up fun i => PadicInt.toZModPow (n + 1) (v i))).mpr (by
        intro σ0 τ0 hτ0 α hα hαt
        have hτι : ∀ k, τ0 (ι' k) = ι' k := by
          have h1 : Spec.map (CommRingCat.ofHom τ0.toRingHom) ≫ t.hom = t.hom := by
            rwa [← hα]
          exact comp_apply_eq_of_specMap_comp_eq (CommRingCat.ofHom ι')
            (CommRingCat.ofHom τ0.toRingHom) (CommRingCat.ofHom ι') (𝟙 _)
            (by rw [Spec.map_id, Category.id_comp]; exact h1)
        let τK : Ω ≃ₐ[V.1.residueField (genericPoint V.1)] Ω :=
          { τ0.toRingEquiv with
            commutes' := fun c => by
              show τ0 (algebraMap _ Ω c) = algebraMap _ Ω c
              rw [← RingHom.congr_fun hγ c, RingHom.comp_apply, hτι] }
        have hspec : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τK.toRingEquiv).op).hom =
            α.hom := by rw [hα]; rfl
        have hαx : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τK.toRingEquiv).op).hom ≫
            x.hom = x.hom := by
          rw [hspec, ← hxg, ← Category.assoc, hαt]
        have hσ : etaleFundamentalGroupMulEquiv pth
            (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) α (by
              show α.hom ≫ t.hom ≫ _ = t.hom ≫ _
              rw [← Category.assoc, hαt])) =
            galoisToFundamentalGroup V.1 L Ω (τK.restrictNormal L) := by
          rw [galoisToFundamentalGroup_restrictNormal_eq_sourceAutElement V.1 L Ω τK hαx]
          refine (etaleFundamentalGroupMulEquiv_eqToIso_sourceAutElement (S := V.1) hxg α
            _).trans ?_
          exact GeometricPoint.sourceAutElement_congr (S := V.1) x hspec.symm _
        let := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
          (integralClosure A L)
        have hI : τK.restrictNormal L ∈
            P.inertia Gal(L / V.1.residueField (genericPoint V.1)) := by
          rw [← IsIntegralClosure.fixingSubgroup_inertiaFixedField A
            (V.1.residueField (genericPoint V.1)) L P]
          intro ⟨z, hz⟩
          show (τK.restrictNormal L) z = z
          rw [← hιrange] at hz
          obtain ⟨k, rfl⟩ := hz
          exact (algebraMap L Ω).injective ((τK.restrictNormal_commutes L _).trans (hτι k))
        have hvσ := hv _ (Subgroup.mem_map_of_mem _ hI)
        rw [hσ]
        show levelRepresentation ρ₀ (n + 1) _ (fun i => PadicInt.toZModPow (n + 1) (v i)) = _
        rw [levelRepresentation_map_toZModPow]
        show (fun i => PadicInt.toZModPow (n + 1) (((ρ₀
          ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom (τK.restrictNormal L))).val *ᵥ v) i)) = _
        rw [hvσ])
    exact ⟨z, (hε n z).trans (congrArg ULift.down hz)⟩

end Stacks.EtaleCohomology

end
