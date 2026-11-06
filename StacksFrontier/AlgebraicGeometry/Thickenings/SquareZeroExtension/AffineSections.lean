module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension.Basic

/-!
# Square-zero extensions of the structure sheaf: sections over affine opens

Stalks of quasi-coherent modules at points of an affine open are localizations of the sections,
and the vanishing of higher cohomology of quasi-coherent modules on affine opens makes the
quotient map of a square-zero extension surjective on sections over every affine open. The file
ends with the affine charts of the locally ringed space defined by the extension.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-- The standard derived category of abelian groups. -/
noncomputable local instance instHasDerivedCategoryAddCommGrpCat :
    HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _

/-- The standard derived category of sheaves of abelian groups on `X`. -/
noncomputable local instance instHasDerivedCategorySheafAddCommGrpCat (X : Scheme.{u}) :
    HasDerivedCategory
      (Sheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}) := by
  letI : Abelian
      (Sheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}) := inferInstance
  exact HasDerivedCategory.standard _

/-- The category of sheaves of abelian groups on `X` has enough injectives. -/
noncomputable local instance instEnoughInjectivesSheafAddCommGrpCat (X : Scheme.{u}) :
    EnoughInjectives
      (Sheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}) :=
  (Sheaf.instIsGrothendieckAbelian
    (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat.{u}).enoughInjectives

private noncomputable def squareZero_stalkLinearEquiv
    {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (x : X) :
    letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) := by
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  letI : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) G.val x
  let ε := ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso e)
  let εG : TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x →
      TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x := ε.addCommGroupIsoToAddEquiv
  have key : ∀ (W : X.Opens) (hxW : x ∈ W) (r₀ : Γ(X, W)) (m₀ : Γ(F, W)),
      εG (X.presheaf.germ W x hxW r₀ • TopCat.Presheaf.germ F.val.presheaf W x hxW m₀) =
        X.presheaf.germ W x hxW r₀ •
          εG (TopCat.Presheaf.germ F.val.presheaf W x hxW m₀) := by
    intro W hxW r₀ m₀
    change ε.addCommGroupIsoToAddEquiv _ = _
    rw [show X.presheaf.germ W x hxW r₀ • TopCat.Presheaf.germ F.val.presheaf W x hxW m₀ =
        TopCat.Presheaf.germ F.val.presheaf W x hxW (r₀ • m₀) from
      (PresheafOfModules.germ_smul (R := X.presheaf) F.val x W hxW r₀ m₀).symm]
    change ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map e.hom.mapPresheaf)
      (TopCat.Presheaf.germ F.presheaf W x hxW _) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW e.hom.mapPresheaf _]
    change (TopCat.Presheaf.germ G.val.presheaf _ _ _) (e.hom.app _ (r₀ • m₀)) = _
    rw [Scheme.Modules.Hom.app_smul,
      show TopCat.Presheaf.germ G.val.presheaf W x hxW (r₀ • e.hom.app W m₀) =
          X.presheaf.germ W x hxW r₀ •
            TopCat.Presheaf.germ G.val.presheaf W x hxW (e.hom.app W m₀) from
        PresheafOfModules.germ_smul (R := X.presheaf) G.val x W hxW r₀ (e.hom.app W m₀)]
    congr 1
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW e.hom.mapPresheaf m₀).symm
  refine { ε.addCommGroupIsoToAddEquiv with map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  have hr := TopCat.Presheaf.germ_res_apply X.presheaf
    (homOfLE (inf_le_left : U ⊓ V ≤ U)) x ⟨hxU, hxV⟩ r
  have hm := TopCat.Presheaf.germ_res_apply F.val.presheaf
    (homOfLE (inf_le_right : U ⊓ V ≤ V)) x ⟨hxU, hxV⟩ m
  rw [← hr, ← hm]
  exact key (U ⊓ V) ⟨hxU, hxV⟩ _ _

private theorem restrictStalk_smul {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (G : Y.Modules) (x : X)
    (r : X.presheaf.stalk x) (m : (G.restrict j).presheaf.stalk x) :
    letI : Module (X.presheaf.stalk x) ((G.restrict j).presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (G.restrict j).val x
    letI : Module (Y.presheaf.stalk (j x)) (G.presheaf.stalk (j x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) G.val (j x)
    let e := (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv
    let t : (G.restrict j).presheaf.stalk x ≃+ G.presheaf.stalk (j x) :=
    ((Scheme.Modules.restrictStalkNatIso j x).app G).addCommGroupIsoToAddEquiv
    t (r • m) = e r • t m := by
  let : Module (X.presheaf.stalk x) ((G.restrict j).presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (G.restrict j).val x
  let : Module (Y.presheaf.stalk (j x)) (G.presheaf.stalk (j x)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val (j x)
  let e := (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv
  let t : (G.restrict j).presheaf.stalk x ≃+ G.presheaf.stalk (j x) :=
    ((Scheme.Modules.restrictStalkNatIso j x).app G).addCommGroupIsoToAddEquiv
  show t (r • m) = e r • t m
  obtain ⟨U₁, hx₁, a, ha⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨U₂, hx₂, b, hb⟩ := (G.restrict j).presheaf.exists_germ_eq m
  let U := U₁ ⊓ U₂
  have hx : x ∈ U := ⟨hx₁, hx₂⟩
  let a' := X.presheaf.map (homOfLE (inf_le_left : U ≤ U₁)).op a
  let b' := (G.restrict j).presheaf.map (homOfLE (inf_le_right : U ≤ U₂)).op b
  have ha' : X.presheaf.germ U x hx a' = r := by
    rw [TopCat.Presheaf.germ_res_apply]; exact ha
  have hb' : (G.restrict j).presheaf.germ U x hx b' = m := by
    rw [TopCat.Presheaf.germ_res_apply]; exact hb
  have ht (s : Γ(G.restrict j, U)) :
      t ((G.restrict j).presheaf.germ U x hx s) =
        G.presheaf.germ (j ''ᵁ U) (j x) (by simpa) s :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x G hx) s
  have he : e (X.presheaf.germ U x hx a') =
      Y.presheaf.germ (j ''ᵁ U) (j x) (by simpa) ((j.appIso U).inv a') := by
    apply e.symm.injective
    simp only [e.symm_apply_apply]
    show X.presheaf.germ U x hx a' = j.stalkMap x _
    rw [j.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
    exact (X.presheaf.germ_res_apply _ _ _ _).symm
  have hM : X.presheaf.germ U x hx a' • (G.restrict j).presheaf.germ U x hx b' =
      (G.restrict j).presheaf.germ U x hx (a' • b') :=
    (PresheafOfModules.germ_smul (R := X.presheaf)
      (G.restrict j).val x U hx a' b').symm
  rw [← ha', ← hb', hM, ht, he, ht]
  exact PresheafOfModules.germ_smul G.val (j x) (j ''ᵁ U)
    (by simpa) ((j.appIso U).inv a') b'

private theorem isLocalizedModule_tilde_toStalk {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (p : PrimeSpectrum R) :
    IsLocalizedModule p.asIdeal.primeCompl (tilde.toStalk M p).hom := inferInstance

theorem fromSpec_mem {X : Scheme.{u}} (U : X.affineOpens)
    (y : Spec Γ(X, U.1)) : U.2.fromSpec y ∈ U.1 := by
  have h : Set.range U.2.fromSpec = (U.1 : Set X) := U.2.range_fromSpec
  exact h.le (Set.mem_range_self y)

theorem fromSpec_stalkMap_germ {X : Scheme.{u}}
    (U : X.affineOpens) (y : Spec Γ(X, U.1)) (r : Γ(X, U.1)) :
    U.2.fromSpec.stalkMap y
        (X.presheaf.germ U.1 (U.2.fromSpec y)
          (fromSpec_mem U y) r) =
      StructureSheaf.toStalk Γ(X, U.1) y r := by
  rw [Scheme.Hom.germ_stalkMap_apply, U.2.fromSpec_app_self]
  show (Spec Γ(X, U.1)).presheaf.germ _ y _
      ((Spec Γ(X, U.1)).presheaf.map
        (eqToHom U.2.fromSpec_preimage_self).op
        ((Scheme.ΓSpecIso Γ(X, U.1)).inv r)) = _
  exact (TopCat.Presheaf.germ_res_apply (Spec Γ(X, U.1)).presheaf
    (eqToHom U.2.fromSpec_preimage_self) y _
    ((Scheme.ΓSpecIso Γ(X, U.1)).inv r)).trans rfl

noncomputable def affineModuleGermMap {X : Scheme.{u}} (F : X.Modules)
    (U : X.affineOpens) (y : Spec Γ(X, U.1)) :
    let x := U.2.fromSpec y
    letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      (X.presheaf.germ U.1 x (fromSpec_mem U y)).hom.toAlgebra
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module Γ(X, U.1) (F.presheaf.stalk x) :=
      Module.compHom _ (algebraMap Γ(X, U.1) (X.presheaf.stalk x))
    Γ(F, U.1) →ₗ[Γ(X, U.1)] F.presheaf.stalk x := by
  let x := U.2.fromSpec y
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x (fromSpec_mem U y)).hom.toAlgebra
  letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  letI : Module Γ(X, U.1) (F.presheaf.stalk x) :=
    Module.compHom _ (algebraMap Γ(X, U.1) (X.presheaf.stalk x))
  letI : IsScalarTower Γ(X, U.1) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact {
    toFun := fun s => F.presheaf.germ U.1 x (fromSpec_mem U y) s
    map_add' := by intro a b; simp
    map_smul' := by
      intro r m
      change F.presheaf.germ U.1 x (fromSpec_mem U y) (r • m) =
        algebraMap Γ(X, U.1) (X.presheaf.stalk x) r •
          F.presheaf.germ U.1 x (fromSpec_mem U y) m
      convert PresheafOfModules.germ_smul (R := X.presheaf)
        F.val x U.1 (fromSpec_mem U y) r m using 1 <;> rfl }

theorem affineModuleGermMap_isLocalized {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) (y : Spec Γ(X, U.1)) :
    let x := U.2.fromSpec y
    letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      (X.presheaf.germ U.1 x (fromSpec_mem U y)).hom.toAlgebra
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module Γ(X, U.1) (F.presheaf.stalk x) :=
      Module.compHom _ (algebraMap Γ(X, U.1) (X.presheaf.stalk x))
    letI : y.asIdeal.IsPrime := y.isPrime
    IsLocalizedModule y.asIdeal.primeCompl (affineModuleGermMap F U y) := by
  let : y.asIdeal.IsPrime := y.isPrime
  let A := Γ(X, U.1)
  let j := U.2.fromSpec
  let x := j y
  let B := X.presheaf.stalk x
  let C := (Spec A).presheaf.stalk y
  let : IsOpenImmersion j := U.2.isOpenImmersion_fromSpec
  let G := F.restrict j
  let M := moduleSpecΓFunctor.obj G
  let : Module B (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module C (G.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec A).presheaf) G.val y
  let : Module C ((tilde M).presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec A).presheaf) (tilde M).val y
  let : Algebra A B := (X.presheaf.germ U.1 x (fromSpec_mem U y)).hom.toAlgebra
  let : Algebra A C := StructureSheaf.stalkAlgebra A y
  let : Module A (F.presheaf.stalk x) := Module.compHom _ (algebraMap A B)
  let : IsScalarTower A B (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module A ((tilde M).presheaf.stalk y) := Module.compHom _ (algebraMap A C)
  let : IsScalarTower A C ((tilde M).presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eRing := (asIso (j.stalkMap y)).symm.commRingCatIsoToRingEquiv
  have heRing (r : A) : eRing (algebraMap A C r) = algebraMap A B r := by
    apply eRing.symm.injective
    simp only [RingEquiv.symm_apply_apply]
    show StructureSheaf.toStalk A y r = j.stalkMap y
      (X.presheaf.germ U.1 x (fromSpec_mem U y) r)
    exact (fromSpec_stalkMap_germ U y r).symm
  let : IsLocalization y.asIdeal.primeCompl C :=
    StructureSheaf.IsLocalization.to_stalk (R := A) y
  let eAlg : C ≃ₐ[A] B := { eRing with commutes' := heRing }
  let : IsLocalization y.asIdeal.primeCompl B :=
    IsLocalization.isLocalization_of_algEquiv _ eAlg
  let : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor j F
  let : IsIso G.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  let q : (tilde M).presheaf.stalk y ≃ₗ[C] G.presheaf.stalk y :=
    squareZero_stalkLinearEquiv (asIso G.fromTildeΓ) y
  let t : G.presheaf.stalk y ≃+ F.presheaf.stalk x :=
    ((Scheme.Modules.restrictStalkNatIso j y).app F).addCommGroupIsoToAddEquiv
  let eAdd := q.toAddEquiv.trans t
  let e : (tilde M).presheaf.stalk y ≃ₗ[A] F.presheaf.stalk x :=
    { eAdd with
      map_smul' := by
        intro r m
        show t (q (r • m)) = r • t (q m)
        rw [← IsScalarTower.algebraMap_smul C r m, q.map_smul,
          restrictStalk_smul, heRing]
        rfl }
  let es : M ≃ₗ[A] Γ(F, U.1) := affineSectionsLinearEquiv F U.2
  let g := e.toLinearMap.comp ((tilde.toStalk M y).hom.comp es.symm.toLinearMap)
  have hg : g = affineModuleGermMap F U y := by
    ext s
    show t (q ((tilde.toStalk M y).hom (es.symm s))) = affineModuleGermMap F U y s
    have hq (v : M) :
        q ((tilde.toStalk M y).hom v) =
          G.presheaf.germ ⊤ y (by simp) v := by
      dsimp [q, squareZero_stalkLinearEquiv, tilde.toStalk,
        StructureSheaf.toStalkₗ]
      show ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor Ab y).map
            ((Scheme.Modules.toPresheaf (Spec A)).map G.fromTildeΓ))
          (TopCat.Presheaf.germ
          ((Scheme.Modules.toPresheaf (Spec A)).obj (tilde M))
            ⊤ y (by simp) (ConcreteCategory.hom (tilde.toOpen M ⊤) v)) = _
      have h := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ y (by simp)
        ((Scheme.Modules.toPresheaf (Spec A)).map G.fromTildeΓ)
        (ConcreteCategory.hom (tilde.toOpen M ⊤) v)
      have htop : ConcreteCategory.hom
          (((Scheme.Modules.toPresheaf (Spec A)).map G.fromTildeΓ).app (Opposite.op ⊤))
            (ConcreteCategory.hom (tilde.toOpen M ⊤) v) =
          (show Γ(G, ⊤) from v) := by
        have htopMod := congrArg (fun f : M ⟶ M => ConcreteCategory.hom f v)
          (Scheme.Modules.toOpen_fromTildeΓ_app G ⊤)
        convert htopMod using 1
        simp [Scheme.Modules.toPresheaf, Scheme.Modules.toPresheafOfModules,
          tilde.toOpen, tilde.modulesSpecToSheafIso]
        rfl
      rw [htop] at h
      convert h using 1
      rfl
    rw [hq]
    dsimp [affineModuleGermMap]
    let hU : j ''ᵁ (⊤ : (Spec A).Opens) = U.1 := by
      rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
    let v : Γ(G, ⊤) := es.symm s
    have ht : t (G.presheaf.germ ⊤ y (by simp) v) =
        F.presheaf.germ (j ''ᵁ ⊤) (j y) (by simp)
          ((Scheme.Modules.restrictAppIso (f := j) F ⊤).inv v) :=
      ConcreteCategory.congr_hom
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j y F (by simp)) v
    rw [ht]
    have hsec : (Scheme.Modules.restrictAppIso (f := j) F ⊤).inv v =
        ConcreteCategory.hom (F.presheaf.map (eqToHom hU).op) s := by
      let e₁ := Scheme.Modules.restrictAppIso (f := j) F ⊤
      let e₂ := F.presheaf.mapIso (eqToIso hU).op
      have he : ConcreteCategory.hom (e₁.hom ≫ e₂.symm.hom) v = s := by
        show es v = s
        exact es.apply_symm_apply s
      have hh := congrArg (fun w => ConcreteCategory.hom e₂.hom w) he
      have hcomp : ConcreteCategory.hom e₁.hom v =
          ConcreteCategory.hom e₂.hom s := by
        simpa [e₁, e₂] using hh
      calc
        _ = ConcreteCategory.hom e₁.hom v := by
          simp [e₁, Scheme.Modules.restrictAppIso]
          rfl
        _ = ConcreteCategory.hom e₂.hom s := hcomp
    rw [hsec, TopCat.Presheaf.germ_res_apply]
  rw [← hg]
  exact IsLocalizedModule.of_linearEquiv _ _ e
    (hf := IsLocalizedModule.of_linearEquiv_right _ _ es.symm
      (hf := isLocalizedModule_tilde_toStalk M y))

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

private noncomputable def derivedPlusIsoNat
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (A : C) (n : ℕ) :
    (F.rightDerivedPlus (n : ℤ)).obj A ≅ (F.rightDerived n).obj A := by
  let I := injectiveResolution A
  let L := I.cocomplex.extend ComplexShape.embeddingUpNat
  let Lp : CochainComplex.Plus C := ⟨L, 0, inferInstance⟩
  let hp := (HomotopyCategory.Plus.quotient C).obj Lp
  let s : (CochainComplex.singleFunctor C 0).obj A ⟶ L :=
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A 0 0 rfl).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat
  have hs : QuasiIso s := by dsimp [s]; infer_instance
  let P : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩
  let sp : P ⟶ Lp := ⟨s⟩
  have hq : IsIso (DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.quotient C).map sp)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs)
  have hinj : ∀ i, Injective (hp.obj.as.X i) := fun i => inferInstanceAs (Injective (L.X i))
  have hunit : IsIso (F.rightDerivedFunctorPlusUnith.app hp) := by infer_instance
  refine (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
    ((F.rightDerivedFunctorPlus.mapIso
        ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).app A ≪≫
          @CategoryTheory.asIso _ _ _ _
            (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map sp)) hq)) ≪≫
      (@CategoryTheory.asIso _ _ _ _ (F.rightDerivedFunctorPlusUnith.app hp) hunit).symm) ≪≫ ?_
  · exact (DerivedCategory.homologyFunctor D (n : ℤ)).mapIso
      ((DerivedCategory.quotientCompQhIso D).app ((F.mapHomologicalComplex _).obj L)) ≪≫
      ((DerivedCategory.homologyFunctorFactors D (n : ℤ)).app
        ((F.mapHomologicalComplex _).obj L)) ≪≫
      HomologicalComplex.homologyMapIso
        (HomologicalComplex.mapHomologicalComplexExtendIso F I.cocomplex
          ComplexShape.embeddingUpNat).symm (n : ℤ) ≪≫
      (((F.mapHomologicalComplex _).obj I.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat (j := n) rfl) ≪≫
      (I.isoRightDerivedObj F n).symm

/-- Sections over an open subset preserve finite limits of sheaves of abelian groups. -/
private theorem sheafSections_preservesFiniteLimits {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits
      ((sheafSections (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat).obj
        (Opposite.op U)) := by
  let : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat) := by
    infer_instance
  let : PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op U)) := by
    infer_instance
  exact preservesFiniteLimits_of_natIso
    (sheafSectionsNatIsoEvaluation
      (J := Opens.grothendieckTopology (X : TopCat))
      (A := AddCommGrpCat) (X := U)).symm

/-- Quasi-coherent modules are right acyclic for sections over affine opens. -/
private theorem sections_rightAcyclic_of_isQuasicoherent
    {X : Scheme.{u}} (M : SheafOfModules.{u} X.ringCatSheaf) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (((sheafSections (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat).obj
      (Opposite.op U))).rightAcyclic
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  let : HasDerivedCategory
      (Sheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat) :=
    HasDerivedCategory.standard _
  let : EnoughInjectives
      (Sheaf (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat) :=
    (Sheaf.instIsGrothendieckAbelian _ _).enoughInjectives
  let Mab := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let F := (sheafSections (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat).obj
    (Opposite.op U)
  have hPFL : PreservesFiniteLimits F := sheafSections_preservesFiniteLimits U
  obtain ⟨-, -, hcmp⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying
    (Opens.grothendieckTopology (X : TopCat)) X.ringCatSheaf
  obtain ⟨eU, -⟩ := hcmp U
  have hvan : ∀ n : ℕ, 0 < n → IsZero ((F.rightDerived n).obj Mab) := by
    intro n hn
    have h := Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X M U hU n hn
    exact h.of_iso ((eU n).app M).symm
  have hchar :=
    (CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F Mab).2
  apply (hchar hPFL).2
  intro i hi
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hi)
  exact (hvan n (by omega)).of_iso (derivedPlusIsoNat F Mab n)

private theorem structureSheaf_sections_rightAcyclic
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U) :
    (((sheafSections (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat).obj
      (Opposite.op U))).rightAcyclic
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
    let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
        SheafOfModules.unit X.ringCatSheaf :=
      Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e
      (inferInstanceAs
        (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent)
  exact sections_rightAcyclic_of_isQuasicoherent _ U hU

private theorem squareZero_sectionSequence_shortExact
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) (hU : IsAffineOpen U) :
    (ShortComplex.mk (squareZero_kernelSheafInclusion E)
      (squareZero_quotientSheafMap E) (squareZero_kernel_quotient_comp_zero E)).map
        ((sheafSections (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat).obj
          (Opposite.op U)) |>.ShortExact := by
  let F := (sheafSections (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat).obj
    (Opposite.op U)
  let Q := ShortComplex.mk (squareZero_kernelSheafInclusion E)
    (squareZero_quotientSheafMap E) (squareZero_kernel_quotient_comp_zero E)
  have hPFL : PreservesFiniteLimits F := sheafSections_preservesFiniteLimits U
  let : E.I.IsQuasicoherent := E.quasicoherent
  have hI := sections_rightAcyclic_of_isQuasicoherent E.I U hU
  have hO := structureSheaf_sections_rightAcyclic U hU
  exact ((CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact
    F Q (squareZero_kernelSheaf_sequence_shortExact E)).1 hI hO).2

theorem squareZero_sectionMap_surjective_of_affine
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (E.π.hom.app (Opposite.op U)).hom := by
  let F := (sheafSections (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat).obj
    (Opposite.op U)
  have hsections := squareZero_sectionSequence_shortExact E U hU
  have hepi : Epi (F.map (squareZero_quotientSheafMap E)) := hsections.epi_g
  rw [AddCommGrpCat.epi_iff_surjective] at hepi
  intro b
  obtain ⟨a, ha⟩ := hepi b
  exact ⟨a, by
    change ((E.π.hom.app (Opposite.op U)).hom.toAddMonoidHom) a = b at ha
    exact ha⟩

theorem thickenedToBase_stalkMap_isLocalHom
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (x : X) :
    IsLocalHom ((E.toBase.hom.stalkMap x).hom) := by
  let q := canonicalInclusionSheafedSpace E
  let φ := (E.toBase.hom.stalkMap x).hom
  have hsh : q ≫ E.toBase = f.toLRSHom.toShHom :=
    canonicalInclusionSheafedSpace_toBase E
  have hlocal : IsLocalHom (((q.hom ≫ E.toBase.hom).stalkMap x).hom) :=
    LocallyRingedSpace.isLocalHom_stalkMap_congr _ _ hsh.symm x
      (LocallyRingedSpace.isLocalHomStalkMap f.toLRSHom x)
  have hstalk : ((q.hom ≫ E.toBase.hom).stalkMap x).hom =
      (q.hom.stalkMap x).hom.comp φ := by
    simp only [PresheafedSpace.stalkMap.comp, PresheafedSpace.comp_base]
    rfl
  have hcomp : IsLocalHom ((q.hom.stalkMap x).hom.comp φ) := by
    rw [← hstalk]
    exact hlocal
  let : IsLocalHom ((q.hom.stalkMap x).hom.comp φ) := hcomp
  exact isLocalHom_of_comp φ (q.hom.stalkMap x).hom

theorem locallyRingedSpace_hom_isIso_of_base_homeomorph
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (hbase : IsHomeomorph f.base)
    (hstalk : ∀ x : X, IsIso (f.stalkMap x)) : IsIso f := by
  let (x : X) : IsIso (f.stalkMap x) := hstalk x
  let : LocallyRingedSpace.IsOpenImmersion f :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso f
      (hbase.homeomorph f.base).isOpenEmbedding
  let : Epi f.base := (TopCat.epi_iff_surjective _).2 hbase.surjective
  exact LocallyRingedSpace.IsOpenImmersion.to_iso f

noncomputable def thickenedToBaseLocallyRingedSpace
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    thickenedLocallyRingedSpace E ⟶ S.toLocallyRingedSpace :=
  LocallyRingedSpace.homMk E.toBase (fun x => thickenedToBase_stalkMap_isLocalHom E x)

noncomputable def thickenedAffineChart
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (U : X.Opens) :
    LocallyRingedSpace.{u} :=
  (thickenedLocallyRingedSpace E).restrict (f := U.ι.base) U.ι.isOpenEmbedding

noncomputable def thickenedAffineChartToSpec
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) (U : X.Opens) :
    thickenedAffineChart E U ⟶
      Spec.toLocallyRingedSpace.obj
        (Opposite.op (LocallyRingedSpace.Γ.obj
          (Opposite.op (thickenedAffineChart E U)))) :=
  LocallyRingedSpace.toΓSpec (thickenedAffineChart E U)

noncomputable def squareZero_affineChartInclusion
    {X S : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f)
    (U : X.Opens) :
    (X.restrict U.ι.isOpenEmbedding).toLocallyRingedSpace ⟶
      thickenedAffineChart E U := by
  let h := U.ι.isOpenEmbedding
  let p : (X.restrict h).toSheafedSpace ⟶
      (thickenedAffineChart E U).toSheafedSpace :=
    InducedCategory.homMk {
      base := 𝟙 (TopCat.of U)
      c := Functor.whiskerLeft h.functor.op E.π.hom
    }
  refine LocallyRingedSpace.homMk p ?_
  intro x
  let xU : ↑U := x
  let eA := (thickenedLocallyRingedSpace E).restrictStalkIso h x
  let eX := X.toLocallyRingedSpace.restrictStalkIso h x
  have hstalk :
      p.hom.stalkMap x ≫ eX.hom =
        eA.hom ≫ (canonicalInclusionLocallyRingedSpace E).stalkMap (U.ι xU) := by
    apply TopCat.Presheaf.stalk_hom_ext
      (F := (thickenedAffineChart E U).presheaf) (x := p.hom.base x)
    intro V hxV
    have hmap := PresheafedSpace.stalkMap_germ p.hom V x hxV
    change ((thickenedAffineChart E U).presheaf.germ V (p.hom.base x) hxV ≫
        p.hom.stalkMap x) ≫ eX.hom = _
    rw [hmap]
    have hxV' : x ∈ (Opens.map p.hom.base).obj V := by
      change p.hom.base x ∈ V
      exact hxV
    have hres := LocallyRingedSpace.restrictStalkIso_hom_eq_germ
      (X := X.toLocallyRingedSpace) h ((Opens.map p.hom.base).obj V) x hxV'
    change p.hom.c.app (Opposite.op V) ≫
        ((X.restrict h).presheaf.germ ((Opens.map p.hom.base).obj V) x hxV' ≫
          (X.toLocallyRingedSpace.restrictStalkIso h x).hom) = _
    have hres' := congrArg (fun q => p.hom.c.app (Opposite.op V) ≫ q) hres
    calc
      _ = _ := hres'
      _ = _ := by
        have hresA := LocallyRingedSpace.restrictStalkIso_hom_eq_germ
          (X := thickenedLocallyRingedSpace E) h V xU hxV
        change p.hom.c.app (Opposite.op V) ≫
            TopCat.Presheaf.germ X.sheaf.presheaf
              (h.functor.obj ((Opens.map p.hom.base).obj V)) (U.ι x) _ =
          (((thickenedLocallyRingedSpace E).restrict h).presheaf.germ V xU hxV ≫
            ((thickenedLocallyRingedSpace E).restrictStalkIso h xU).hom) ≫
              (canonicalInclusionLocallyRingedSpace E).stalkMap (U.ι xU)
        rw [hresA]
        rw [canonicalInclusionLocallyRingedSpace_stalkMap]
        have hxV' : xU ∈ V := by
          change p.hom.base x ∈ V
          exact hxV
        have hxImage : U.ι xU ∈ h.functor.obj V := by
          change U.ι xU ∈ U.ι ''ᵁ V
          exact ⟨xU, hxV', rfl⟩
        change (h.functor.op.whiskerLeft E.π.hom).app (Opposite.op V) ≫
            TopCat.Presheaf.germ X.sheaf.presheaf
              (h.functor.obj ((Opens.map (𝟙 (TopCat.of U))).obj V)) (U.ι x) _ = _
        change E.π.hom.app (Opposite.op (h.functor.obj V)) ≫
            TopCat.Presheaf.germ X.sheaf.presheaf (h.functor.obj V) (U.ι x) _ =
          (TopCat.Presheaf.germ E.A.presheaf (h.functor.obj V) (U.ι xU) hxImage) ≫
            (TopCat.Presheaf.stalkFunctor CommRingCat (U.ι xU)).map E.π.hom
        exact (TopCat.Presheaf.stalkFunctor_map_germ
          (h.functor.obj V) (U.ι xU) hxImage E.π.hom).symm
  have hright : IsLocalHom
      (((canonicalInclusionLocallyRingedSpace E).stalkMap (U.ι xU)).hom.comp eA.hom.hom) := by
    let : IsLocalHom ((canonicalInclusionLocallyRingedSpace E).stalkMap (U.ι xU)).hom :=
      canonicalInclusionSheafedSpace_stalkMap_isLocalHom E (U.ι xU)
    refine ⟨fun a ha => ?_⟩
    have hfa : IsUnit (eA.hom.hom a) :=
      (isUnit_map_iff ((canonicalInclusionLocallyRingedSpace E).stalkMap (U.ι xU)).hom _).mp ha
    have hhom : eA.commRingCatIsoToRingEquiv.toRingHom = eA.hom.hom :=
      CategoryTheory.Iso.commRingCatIsoToRingEquiv_toRingHom eA
    have hfa' : IsUnit (eA.commRingCatIsoToRingEquiv.toRingHom a) := by
      rw [hhom]
      exact hfa
    exact (MulEquiv.isUnit_map eA.commRingCatIsoToRingEquiv).mp hfa'
  have hcomp : eX.hom.hom.comp (p.hom.stalkMap x).hom =
      ((canonicalInclusionLocallyRingedSpace E).stalkMap (U.ι xU)).hom.comp eA.hom.hom :=
    congrArg CommRingCat.Hom.hom hstalk
  let : IsLocalHom (eX.hom.hom.comp (p.hom.stalkMap x).hom) := hcomp ▸ hright
  exact isLocalHom_of_comp (p.hom.stalkMap x).hom eX.hom.hom

end Stacks.Thickenings
