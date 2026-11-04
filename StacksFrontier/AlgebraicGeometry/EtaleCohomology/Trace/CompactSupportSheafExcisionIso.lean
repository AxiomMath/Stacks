module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLimitWeights

/-!
# `Hⁱ_c` of an open and of a closed subscheme, as functors, Frobenius-equivariantly

Let `j : X ⟶ X̄` be a compactification of `X` over a finite field `k`, `j_U : U ⟶ X` an open
immersion and `i : Z ⟶ X` a closed immersion, with the induced compactifications of `U` and `Z`.
For sheaves `G` of `Λ`-modules,

`Hⁱ_c(U_k̄, G) ≅ Hⁱ_c(X_k̄, j_{U!} G)` and `Hⁱ_c(Z_k̄, G) ≅ Hⁱ_c(X_k̄, i_* G)`,

as natural isomorphisms of functors of `G`, carrying the canonical geometric Frobenius `π^*` of
the left hand side to that of the right hand side.  On a tower `T` of sheaves of `ℤ_ℓ`-modules
these turn the open and closed parts `Hⁱ_c(X_k̄, j_{U!} j_U⁻¹ Tₙ)` and `Hⁱ_c(X_k̄, i_* i⁻¹ Tₙ)` of
the excision sequence of
`Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_rationalLim_of_openClosed` into the compactly
supported cohomology of `U` and `Z` of the restricted towers. This is the excision step of the
reduction of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH);
Deligne, Weil II 3.3) to curves.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportFrobeniusFunctorRestrictOpenIso`,
  `Stacks.EtaleCohomology.compactSupportFrobeniusFunctorRestrictClosedIso`: the identifications
  of `RΓ_c` as natural isomorphisms.
* `Stacks.EtaleCohomology.compactSupportSheafCohomologyRestrictOpenIso`,
  `Stacks.EtaleCohomology.compactSupportSheafCohomologyRestrictClosedIso`: the identifications of
  `Hⁱ_c` of sheaves.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `isCharpolyNormMixedOfWeightLE_rationalLimMap_iff_of_iso`: the weight bound on the rational limit
  of a tower only depends on the tower with its endomorphism up to isomorphism.
* `towerOpenPartCohomologyIso_hom_frobenius`, `towerClosedPartCohomologyIso_hom_frobenius`: the
  identifications of the compactly supported cohomology of the open and closed parts of a tower
  with that of the towers restricted to `U` and `Z` commute with the Frobenius actions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Rational limits of isomorphic towers -/

section RationalLim

variable {ℓ : ℕ} [Fact ℓ.Prime] [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} ℤ_[ℓ])]
  {A A' : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}

/-- Finite dimensionality of the rational limit only depends on the tower up to isomorphism. -/
public theorem finiteDimensional_rationalLim_of_iso (e : A ≅ A')
    [hA : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)] :
    FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A') :=
  LinearEquiv.finiteDimensional ((rationalLim (ℓ := ℓ)).mapIso e).toLinearEquiv

/-- **The weight bound on the rational limit of a tower only depends on the tower with its
endomorphism up to isomorphism.** -/
public theorem isCharpolyNormMixedOfWeightLE_rationalLimMap_iff_of_iso (e : A ≅ A') (φ : A ⟶ A)
    (φ' : A' ⟶ A') (h : φ ≫ e.hom = e.hom ≫ φ')
    [hA : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)]
    [hA' : FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A')] {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ}
    {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q ι b ((rationalLim (ℓ := ℓ)).map φ).hom ↔
      IsCharpolyNormMixedOfWeightLE q ι b ((rationalLim (ℓ := ℓ)).map φ').hom := by
  let L := ((rationalLim (ℓ := ℓ)).mapIso e).toLinearEquiv
  have hcomm : ∀ v, L (((rationalLim (ℓ := ℓ)).map φ).hom v) =
      ((rationalLim (ℓ := ℓ)).map φ').hom (L v) := fun v => by
    have h' := congrArg (fun t => ((rationalLim (ℓ := ℓ)).map t).hom v) h
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h'
    exact h'
  have hcomm' : ∀ v, L.symm (((rationalLim (ℓ := ℓ)).map φ').hom v) =
      ((rationalLim (ℓ := ℓ)).map φ).hom (L.symm v) := fun v => L.injective <| by
    rw [LinearEquiv.apply_symm_apply, hcomm, LinearEquiv.apply_symm_apply]
  exact ⟨fun hw => hw.of_surjective (p := L.toLinearMap) hcomm L.surjective,
    fun hw => hw.of_surjective (p := L.symm.toLinearMap) hcomm' L.symm.surjective⟩

end RationalLim

/-! ### Placing a sheaf in degree zero commutes with an additive functor -/

section Single

variable {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] [Abelian 𝒜] [Abelian ℬ] (T : 𝒜 ⥤ ℬ)
  [T.Additive]

/-- An object placed in degree zero, as a bounded below complex. -/
public abbrev singlePlus (𝒞 : Type*) [Category* 𝒞] [Abelian 𝒞] : 𝒞 ⥤ CochainComplex.Plus 𝒞 :=
  ObjectProperty.lift _ (HomologicalComplex.single 𝒞 (ComplexShape.up ℤ) 0)
    (fun _ => ⟨0, inferInstance⟩)

/-- **An additive functor commutes with placing in degree zero**, on bounded below complexes. -/
public def singlePlusMapIso :
    singlePlus 𝒜 ⋙ T.mapCochainComplexPlus ≅ T ⋙ singlePlus ℬ :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _
      ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).app X))
    (fun f => by
      ext n : 2
      exact congrArg (fun t => HomologicalComplex.Hom.f t n)
        ((HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℤ) 0).hom.naturality f))

/-- **Sheaf-level cohomology from a functor-level comparison.**  A natural isomorphism
`α : Φ ≅ T⁺ ⋙ Ψ` of functors out of bounded below complexes induces, on objects placed in degree
zero and on `Hⁱ`, an isomorphism `Hⁱ(Φ(-[0])) ≅ T ⋙ Hⁱ(Ψ(-[0]))`. -/
public def singlePlusHomologyIso {𝒟 : Type*} [Category* 𝒟] [Abelian 𝒟] [HasDerivedCategory 𝒟]
    (Φ : CochainComplex.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒟)
    (Ψ : CochainComplex.Plus ℬ ⥤ DerivedCategory.Plus 𝒟) (α : Φ ≅ T.mapCochainComplexPlus ⋙ Ψ)
    (i : ℤ) :
    singlePlus 𝒜 ⋙ Φ ⋙ DerivedCategory.Plus.homologyFunctor 𝒟 i ≅
      T ⋙ singlePlus ℬ ⋙ Ψ ⋙ DerivedCategory.Plus.homologyFunctor 𝒟 i :=
  NatIso.ofComponents
    (fun X => (DerivedCategory.Plus.homologyFunctor 𝒟 i).mapIso
      (α.app ((singlePlus 𝒜).obj X) ≪≫ Ψ.mapIso ((singlePlusMapIso T).app X)))
    (fun {X Y} g => by
      have h₁ := α.hom.naturality ((singlePlus 𝒜).map g)
      have h₂ := (singlePlusMapIso T).hom.naturality g
      dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂ ⊢
      simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, ← Functor.map_comp]
      congr 1
      rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, Category.assoc])

/-- **The sheaf-level comparison intertwines endomorphisms intertwined by `α`.** -/
public theorem singlePlusHomologyIso_hom_comm {𝒟 : Type*} [Category* 𝒟] [Abelian 𝒟]
    [HasDerivedCategory 𝒟]
    (Φ : CochainComplex.Plus 𝒜 ⥤ DerivedCategory.Plus 𝒟)
    (Ψ : CochainComplex.Plus ℬ ⥤ DerivedCategory.Plus 𝒟) (α : Φ ≅ T.mapCochainComplexPlus ⋙ Ψ)
    (πΦ : Φ ⟶ Φ) (πΨ : Ψ ⟶ Ψ)
    (h : πΦ ≫ α.hom = α.hom ≫ Functor.whiskerLeft T.mapCochainComplexPlus πΨ) (i : ℤ) :
    Functor.whiskerLeft (singlePlus 𝒜)
        (Functor.whiskerRight πΦ (DerivedCategory.Plus.homologyFunctor 𝒟 i)) ≫
      (singlePlusHomologyIso T Φ Ψ α i).hom =
    (singlePlusHomologyIso T Φ Ψ α i).hom ≫
      Functor.whiskerLeft T (Functor.whiskerLeft (singlePlus ℬ)
        (Functor.whiskerRight πΨ (DerivedCategory.Plus.homologyFunctor 𝒟 i))) := by
  ext X
  have h₁ := congrArg (fun t => NatTrans.app t ((singlePlus 𝒜).obj X)) h
  have h₂ := πΨ.naturality ((singlePlusMapIso T).hom.app X)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₂
  simp only [singlePlusHomologyIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.trans_hom,
    Iso.app_hom, ← Functor.map_comp]
  congr 1
  rw [reassoc_of% h₁, ← h₂, Category.assoc]

end Single

/-! ### `RΓ_c` of an open and of a closed subscheme, as natural isomorphisms -/

section Functor

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

section Open

variable {U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]

/-- **`RΓ_c(U_k̄, -) ≅ RΓ_c(X_k̄, j_{U!} -)`**, as a natural isomorphism of functors of the bounded
below complex on `U`. -/
public def compactSupportFrobeniusFunctorRestrictOpenIso :
    compactSupportFrobeniusFunctor.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar ≅
      (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus ⋙
        compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar :=
  NatIso.ofComponents (compactSupportFrobeniusCohomologyRestrictOpenIso Λ f j jU kbar)
    (fun {K K'} φ => by
      have h : (etaleModuleExtensionByZero.{u, 0} Λ (jU ≫ j.immersion)).mapCochainComplexPlus.map
            φ ≫ (extensionByZeroCompPlusIso Λ f j jU K').hom =
          (extensionByZeroCompPlusIso Λ f j jU K).hom ≫
            (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
              ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.map φ) := by
        ext n : 2
        exact (etaleModuleExtensionByZeroCompIso.{u, 0} Λ jU j.immersion).hom.naturality
          (φ.hom.f n)
      have h₃ := congrArg (fun t =>
        (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).map
              ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).map t))) h
      simp only [Functor.map_comp] at h₃
      exact h₃)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The natural isomorphism `RΓ_c(U_k̄, -) ≅ RΓ_c(X_k̄, j_{U!} -)` carries the canonical
Frobenius of `U` to that of `X`. -/
public theorem compactSupportFrobeniusFunctorRestrictOpenIso_hom_frobenius :
    canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar p q hcard ≫
        (compactSupportFrobeniusFunctorRestrictOpenIso Λ f j kbar jU).hom =
      (compactSupportFrobeniusFunctorRestrictOpenIso Λ f j kbar jU).hom ≫
        Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard) := by
  ext K : 2
  exact compactSupportFrobeniusCohomologyRestrictOpenIso_hom_frobenius Λ f j jU kbar p q hcard K

end Open

section Closed

variable [QuasiCompact f] {Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]

/-- **`RΓ_c(Z_k̄, -) ≅ RΓ_c(X_k̄, i_* -)`**, as a natural isomorphism of functors of the bounded
below complex on `Z`. -/
public def compactSupportFrobeniusFunctorRestrictClosedIso :
    compactSupportFrobeniusFunctor.{u, 0} Λ (iZ ≫ f) (j.restrictClosed iZ) kbar ≅
      (etaleModuleDirectImage.{u, 0} Λ iZ).mapCochainComplexPlus ⋙
        compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar :=
  NatIso.ofComponents (compactSupportFrobeniusCohomologyRestrictClosedIso Λ f j iZ kbar)
    (fun φ => compactSupportFrobeniusCohomologyRestrictClosedIso_hom_naturality Λ f j iZ kbar φ)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The natural isomorphism `RΓ_c(Z_k̄, -) ≅ RΓ_c(X_k̄, i_* -)` carries the canonical Frobenius of
`Z` to that of `X`. -/
public theorem compactSupportFrobeniusFunctorRestrictClosedIso_hom_frobenius :
    canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ (iZ ≫ f) (j.restrictClosed iZ) kbar p q
        hcard ≫ (compactSupportFrobeniusFunctorRestrictClosedIso Λ f j kbar iZ).hom =
      (compactSupportFrobeniusFunctorRestrictClosedIso Λ f j kbar iZ).hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ iZ).mapCochainComplexPlus
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard) := by
  ext K : 2
  exact compactSupportFrobeniusCohomologyRestrictClosedIso_hom_frobenius Λ f j iZ kbar p q hcard K

end Closed

end Functor

/-! ### `Hⁱ_c` of sheaves on an open and on a closed subscheme -/

section Sheaf

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (i : ℤ)

section Open

variable {U : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]

/-- **`Hⁱ_c(U_k̄, G) ≅ Hⁱ_c(X_k̄, j_{U!} G)`**, naturally in the sheaf `G` on `U`. -/
public def compactSupportSheafCohomologyRestrictOpenIso :
    compactSupportSheafCohomology Λ (jU ≫ f) (j.restrictOpen jU) kbar i ≅
      etaleModuleExtensionByZero.{u, 0} Λ jU ⋙ compactSupportSheafCohomology Λ f j kbar i :=
  singlePlusHomologyIso (etaleModuleExtensionByZero.{u, 0} Λ jU) _ _
    (compactSupportFrobeniusFunctorRestrictOpenIso Λ f j kbar jU) i

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The identification `Hⁱ_c(U_k̄, -) ≅ Hⁱ_c(X_k̄, j_{U!} -)` carries `π_U^*` to `π_X^*`. -/
public theorem compactSupportSheafCohomologyRestrictOpenIso_hom_frobenius :
    compactSupportSheafFrobenius Λ (jU ≫ f) (j.restrictOpen jU) kbar p q hcard i ≫
        (compactSupportSheafCohomologyRestrictOpenIso Λ f j kbar i jU).hom =
      (compactSupportSheafCohomologyRestrictOpenIso Λ f j kbar i jU).hom ≫
        Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ jU)
          (compactSupportSheafFrobenius Λ f j kbar p q hcard i) :=
  singlePlusHomologyIso_hom_comm _ _ _ _ _ _
    (compactSupportFrobeniusFunctorRestrictOpenIso_hom_frobenius Λ f j kbar jU p q hcard) i

end Open

section Closed

variable [QuasiCompact f] {Z : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ]

/-- **`Hⁱ_c(Z_k̄, G) ≅ Hⁱ_c(X_k̄, i_* G)`**, naturally in the sheaf `G` on `Z`. -/
public def compactSupportSheafCohomologyRestrictClosedIso :
    compactSupportSheafCohomology Λ (iZ ≫ f) (j.restrictClosed iZ) kbar i ≅
      etaleModuleDirectImage.{u, 0} Λ iZ ⋙ compactSupportSheafCohomology Λ f j kbar i :=
  singlePlusHomologyIso (etaleModuleDirectImage.{u, 0} Λ iZ) _ _
    (compactSupportFrobeniusFunctorRestrictClosedIso Λ f j kbar iZ) i

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The identification `Hⁱ_c(Z_k̄, -) ≅ Hⁱ_c(X_k̄, i_* -)` carries `π_Z^*` to `π_X^*`. -/
public theorem compactSupportSheafCohomologyRestrictClosedIso_hom_frobenius :
    compactSupportSheafFrobenius Λ (iZ ≫ f) (j.restrictClosed iZ) kbar p q hcard i ≫
        (compactSupportSheafCohomologyRestrictClosedIso Λ f j kbar i iZ).hom =
      (compactSupportSheafCohomologyRestrictClosedIso Λ f j kbar i iZ).hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ iZ)
          (compactSupportSheafFrobenius Λ f j kbar p q hcard i) :=
  singlePlusHomologyIso_hom_comm _ _ _ _ _ _
    (compactSupportFrobeniusFunctorRestrictClosedIso_hom_frobenius Λ f j kbar iZ p q hcard) i

end Closed

end Sheaf

/-! ### Excision for towers, with the outer terms on `U` and on `Z` -/

section Tower

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  {Z U : Scheme.{u}} (iZ : Z ⟶ X) [IsClosedImmersion iZ] (jU : U ⟶ X) [IsOpenImmersion jU]
  (hij : Set.range jU.base = (Set.range iZ.base)ᶜ)
  {ℓ : ℕ} [Fact ℓ.Prime] (T : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X)

/-- Transport of an intertwining relation along the isomorphism built from `e` in
`towerOpenPartCohomologyIso` and `towerClosedPartCohomologyIso`. -/
private theorem whiskerLeft_comp_associator_isoWhiskerLeft_symm_hom
    {J C D C' H : Type*} [Category* J] [Category* C] [Category* D] [Category* C'] [Category* H]
    (T : J ⥤ C) (R : C ⥤ D) (E : D ⥤ C') {Cu : D ⥤ H} {Cf : C' ⥤ H} (e : Cu ≅ E ⋙ Cf)
    {φu : Cu ⟶ Cu} {φf : Cf ⟶ Cf} (h : φu ≫ e.hom = e.hom ≫ Functor.whiskerLeft E φf) :
    Functor.whiskerLeft (T ⋙ R ⋙ E) φf ≫ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft T (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft R e.symm) ≪≫
      (Functor.associator _ _ _).symm).hom =
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft R e.symm) ≪≫
      (Functor.associator _ _ _).symm).hom ≫ Functor.whiskerLeft (T ⋙ R) φu := by
  refine NatTrans.ext (funext fun n => ?_)
  have h' := congrArg (fun t => NatTrans.app t (R.obj (T.obj n))) h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h'
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj]
  exact comp_inv_eq_inv_comp_of_hom_comm (e.app _) (e.app _) _ _ h'

/-- The open part of the tower, read on `U`. -/
public def towerOpenPartCohomologyIso (i : ℤ) :
    (T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU) ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i ≅
      (T ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (jU ≫ f) (j.restrictOpen jU) kbar i :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft (etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU)
      (compactSupportSheafCohomologyRestrictOpenIso ℤ_[ℓ] f j kbar i jU).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- The closed part of the tower, read on `Z`. -/
public def towerClosedPartCohomologyIso (i : ℤ) :
    (T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ) ⋙ compactSupportSheafCohomology ℤ_[ℓ] f j kbar i ≅
      (T ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] iZ) ⋙
        compactSupportSheafCohomology ℤ_[ℓ] (iZ ≫ f) (j.restrictClosed iZ) kbar i :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft T (Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] iZ)
      (compactSupportSheafCohomologyRestrictClosedIso ℤ_[ℓ] f j kbar i iZ).symm) ≪≫
    (Functor.associator _ _ _).symm

omit [QuasiCompact f] in
/-- `towerOpenPartCohomologyIso` commutes with the Frobenius actions on the compactly supported
cohomology of the open part of the tower on `X` and of its restriction to `U`. -/
public theorem towerOpenPartCohomologyIso_hom_frobenius (i : ℤ) :
    Functor.whiskerLeft (T ⋙ etaleModuleOpenPart ℤ_[ℓ] jU)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i) ≫
      (towerOpenPartCohomologyIso f j kbar jU T i).hom =
    (towerOpenPartCohomologyIso f j kbar jU T i).hom ≫
      Functor.whiskerLeft (T ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] jU)
        (compactSupportSheafFrobenius ℤ_[ℓ] (jU ≫ f) (j.restrictOpen jU) kbar p q hcard i) := by
  exact whiskerLeft_comp_associator_isoWhiskerLeft_symm_hom T _ _
    (compactSupportSheafCohomologyRestrictOpenIso ℤ_[ℓ] f j kbar i jU)
    (compactSupportSheafCohomologyRestrictOpenIso_hom_frobenius ℤ_[ℓ] f j kbar i jU p q hcard)

/-- `towerClosedPartCohomologyIso` commutes with the Frobenius actions on the compactly supported
cohomology of the closed part of the tower on `X` and of its inverse image on `Z`. -/
public theorem towerClosedPartCohomologyIso_hom_frobenius (i : ℤ) :
    Functor.whiskerLeft (T ⋙ etaleModuleClosedPart ℤ_[ℓ] iZ)
        (compactSupportSheafFrobenius ℤ_[ℓ] f j kbar p q hcard i) ≫
      (towerClosedPartCohomologyIso f j kbar iZ T i).hom =
    (towerClosedPartCohomologyIso f j kbar iZ T i).hom ≫
      Functor.whiskerLeft (T ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] iZ)
        (compactSupportSheafFrobenius ℤ_[ℓ] (iZ ≫ f) (j.restrictClosed iZ) kbar p q hcard i) := by
  exact whiskerLeft_comp_associator_isoWhiskerLeft_symm_hom T _ _
    (compactSupportSheafCohomologyRestrictClosedIso ℤ_[ℓ] f j kbar i iZ)
    (compactSupportSheafCohomologyRestrictClosedIso_hom_frobenius ℤ_[ℓ] f j kbar i iZ p q hcard)

end Tower

end Stacks.EtaleCohomology

end
