module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RightDerivedRestrictionUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteSectionPullbackTransfer
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedRestrictionNatural

/-!
# Naturality of `RΓ_c(X_k̄, K)|_Λ ≅ RΓ_c(X_k̄, K|_Λ)` in endomorphisms of restriction of scalars

Let `ρ : Λ →+* Λ'` be a ring map and `θ` a natural endomorphism of restriction of scalars
`Mod Λ' ⥤ Mod Λ`, for instance multiplication by an element of `Λ'` commuting with the image of
`ρ`.  Applied sectionwise, `θ` is a natural endomorphism `Θ` of restriction of scalars of
sheaves of modules on small étale sites.  The comparison
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictScalarsIso` carries the action
of `θ` on the complex of `Λ`-modules `RΓ_c(X_k̄, K)|_Λ` to the action of `RΓ_c(X_k̄, -)` on the
endomorphism `Θ` of `K|_Λ`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleRestrictScalarsNatTrans`: the sectionwise `Θ`.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictScalarsIso_naturality`: the
  comparison `RΓ_c(X_k̄, K)|_Λ ≅ RΓ_c(X_k̄, K|_Λ)` carries the action of `θ` to that of `Θ`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Mates and compatible endomorphisms -/

section Mate

variable {S₁ S₂ T₁ T₂ : Type*} [Category* S₁] [Category* S₂] [Category* T₁] [Category* T₂]
  {L₁ : S₁ ⥤ T₁} {R₁ : T₁ ⥤ S₁} (adj₁ : L₁ ⊣ R₁) {L₂ : S₂ ⥤ T₂} {R₂ : T₂ ⥤ S₂} (adj₂ : L₂ ⊣ R₂)
  {Gs : S₁ ⥤ S₂} {Gt : T₁ ⥤ T₂}

/-- **A comparison `Gs ⋙ L₂ ⟶ L₁ ⋙ Gt` determined by the units commutes with compatible
endomorphisms of the coefficient functors.**  If `c` is adjoint to `Gs(unit₁)` followed by a
comparison `d : R₁ ⋙ Gs ⟶ Gt ⋙ R₂`, and `θs`, `θt` are endomorphisms of `Gs`, `Gt` that `d`
intertwines, then `c` intertwines `L₂(θs)` and `θt`. -/
theorem map_comp_app_eq_app_comp_of_unit (c : Gs ⋙ L₂ ⟶ L₁ ⋙ Gt) (d : R₁ ⋙ Gs ⟶ Gt ⋙ R₂)
    (hunit : ∀ x, adj₂.unit.app (Gs.obj x) ≫ R₂.map (c.app x) =
      Gs.map (adj₁.unit.app x) ≫ d.app (L₁.obj x))
    (θs : Gs ⟶ Gs) (θt : Gt ⟶ Gt)
    (hθ : ∀ y, θs.app (R₁.obj y) ≫ d.app y = d.app y ≫ R₂.map (θt.app y))
    (x : S₁) :
    L₂.map (θs.app x) ≫ c.app x = c.app x ≫ θt.app (L₁.obj x) := by
  apply (adj₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [adj₂.unit_naturality_assoc, hunit, reassoc_of% (hunit x), ← θs.naturality_assoc]
  exact congrArg (_ ≫ ·) (hθ (L₁.obj x))

end Mate

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')
  (θ : ModuleCat.restrictScalars.{u + 1} ρ ⟶ ModuleCat.restrictScalars.{u + 1} ρ)

/-- **A natural endomorphism of restriction of scalars of modules, applied sectionwise**: the
induced natural endomorphism of restriction of scalars of sheaves of modules on `X_étale`. -/
abbrev etaleModuleRestrictScalarsNatTrans (X : Scheme.{u}) :
    etaleModuleRestrictScalars ρ X ⟶ etaleModuleRestrictScalars ρ X :=
  sheafCompose_map X.smallEtaleTopology θ

/-! ### Compatibility with the underived functors -/

/-- `Θ` commutes with direct images. -/
theorem etaleModuleDirectImageRestrictScalars_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ' f)
        (etaleModuleRestrictScalarsNatTrans ρ θ Y) ≫
        (etaleModuleDirectImageRestrictScalars ρ f).hom =
      (etaleModuleDirectImageRestrictScalars ρ f).hom ≫
        Functor.whiskerRight (etaleModuleRestrictScalarsNatTrans ρ θ X)
          (etaleModuleDirectImage.{u, 0} Λ f) :=
  rfl

/-- `Θ` commutes with global sections. -/
theorem etaleModuleGlobalSectionsRestrictScalars_naturality (X : Scheme.{u}) :
    Functor.whiskerLeft (etaleModuleGlobalSections.{u, 0} Λ' X) θ ≫
        (etaleModuleGlobalSectionsRestrictScalars ρ X).hom =
      (etaleModuleGlobalSectionsRestrictScalars ρ X).hom ≫
        Functor.whiskerRight (etaleModuleRestrictScalarsNatTrans ρ θ X)
          (etaleModuleGlobalSections.{u, 0} Λ X) := by
  ext N : 2
  have h₁ := θ.naturality ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ') terminalIsTerminal).hom.app N)
  have h₂ := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    terminalIsTerminal).inv.naturality ((etaleModuleRestrictScalarsNatTrans ρ θ X).app N)
  simp only [etaleModuleGlobalSectionsRestrictScalars, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Category.assoc]
  rw [← reassoc_of% h₁]
  refine congrArg (_ ≫ ·) ?_
  exact h₂

/-- `Θ` commutes with inverse images, through the comparison
`f^{-1} ∘ res_ρ ≅ res_ρ ∘ f^{-1}`. -/
theorem etaleModuleInverseImageRestrictScalars_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : EtaleModules.{u, 0} Λ' Y) :
    (etaleModuleInverseImage.{u, 0} Λ f).map ((etaleModuleRestrictScalarsNatTrans ρ θ Y).app N) ≫
        (etaleModuleInverseImageRestrictScalars ρ f).hom.app N =
      (etaleModuleInverseImageRestrictScalars ρ f).hom.app N ≫
        (etaleModuleRestrictScalarsNatTrans ρ θ X).app
          ((etaleModuleInverseImage.{u, 0} Λ' f).obj N) :=
  map_comp_app_eq_app_comp_of_unit
    ((smallEtaleBaseChange f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ')
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtaleBaseChange f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology)
    (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange f) Y.smallEtaleTopology
      X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)).natTrans
    (coefficientPushforwardTwoSquare (smallEtaleBaseChange f) Y.smallEtaleTopology
      X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)).natTrans
    (fun c => (coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange f) Y.smallEtaleTopology
      X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ) c).symm.trans
        (Category.comp_id _).symm)
    (etaleModuleRestrictScalarsNatTrans ρ θ Y) (etaleModuleRestrictScalarsNatTrans ρ θ X)
    (fun _ => rfl) N

/-- `Θ` commutes with extension by zero, through the comparison
`j_! ∘ res_ρ ≅ res_ρ ∘ j_!`. -/
theorem etaleModuleExtensionByZeroRestrictScalars_naturality {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (N : EtaleModules.{u, 0} Λ' U) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map
        ((etaleModuleRestrictScalarsNatTrans ρ θ U).app N) ≫
        (etaleModuleExtensionByZeroRestrictScalars ρ j).hom.app N =
      (etaleModuleExtensionByZeroRestrictScalars ρ j).hom.app N ≫
        (etaleModuleRestrictScalarsNatTrans ρ θ X).app
          ((etaleModuleExtensionByZero.{u, 0} Λ' j).obj N) :=
  map_comp_app_eq_app_comp_of_unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.Etale.smallEtaleCompose j) (ModuleCat.{u + 1} Λ') U.smallEtaleTopology
      X.smallEtaleTopology)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.Etale.smallEtaleCompose j) (ModuleCat.{u + 1} Λ) U.smallEtaleTopology
      X.smallEtaleTopology)
    (coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
      X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)).natTrans
    (coefficientPushforwardTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
      X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ)).natTrans
    (fun c => (Stacks.Sites.coefficientPullbackTwoSquare_unit (Scheme.Etale.smallEtaleCompose j)
      U.smallEtaleTopology X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ρ) c).trans
        (Category.comp_id _).symm)
    (etaleModuleRestrictScalarsNatTrans ρ θ U) (etaleModuleRestrictScalarsNatTrans ρ θ X)
    (fun _ => rfl) N

/-- An endomorphism intertwined by an isomorphism is intertwined by its inverse. -/
theorem inv_comp_eq_of_comp_hom_eq {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y) (a : X ⟶ X)
    (b : Y ⟶ Y) (h : a ≫ e.hom = e.hom ≫ b) : b ≫ e.inv = e.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-! ### Compatibility with the derived functors -/

open Stacks.DerivedFunctor in
/-- `Θ` commutes with derived direct images, through
`Rf_* ∘ res_ρ ≅ res_ρ ∘ Rf_*`. -/
theorem etaleModuleDerivedDirectImageRestrictScalars_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ' X)) :
    (mapDerivedCategoryPlusNatTrans (etaleModuleRestrictScalarsNatTrans ρ θ Y)).app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ' f).obj K) ≫
        (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app K =
      (etaleModuleDerivedDirectImageRestrictScalars ρ f).hom.app K ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ f).map
          ((mapDerivedCategoryPlusNatTrans (etaleModuleRestrictScalarsNatTrans ρ θ X)).app K) :=
  Functor.rightDerivedRestrictionIso_hom_naturality _ _ _ _ _ _ _ _
    (etaleModuleDirectImageRestrictScalars_naturality ρ θ f) K

open Stacks.DerivedFunctor in
/-- `Θ` commutes with derived global sections, through
`RΓ(X, -) ∘ res_ρ ≅ res_ρ ∘ RΓ(X, -)`. -/
theorem etaleModuleDerivedGlobalSectionsRestrictScalars_naturality (X : Scheme.{u})
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ' X)) :
    (mapDerivedCategoryPlusNatTrans θ).app ((etaleModuleDerivedGlobalSections.{u, 0} Λ' X).obj K) ≫
        (etaleModuleDerivedGlobalSectionsRestrictScalars ρ X).hom.app K =
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ X).hom.app K ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ X).map
          ((mapDerivedCategoryPlusNatTrans (etaleModuleRestrictScalarsNatTrans ρ θ X)).app K) :=
  Functor.rightDerivedRestrictionIso_hom_naturality _ _ _ _ _ _ _ _
    (etaleModuleGlobalSectionsRestrictScalars_naturality ρ θ X) K

/-- `Θ` applied degreewise to a bounded below complex of sheaves of `Λ'`-modules, viewed over
`Λ`. -/
abbrev etaleModuleRestrictScalarsComplexEndo {X : Scheme.{u}}
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)) :
    (etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K ⟶
      (etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex (etaleModuleRestrictScalarsNatTrans ρ θ X)
    (ComplexShape.up ℤ)).app K.obj)

section Restriction

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

open Stacks.DerivedFunctor in
/-- `Θ` commutes with the restriction to `Y_k̄`, through
`Stacks.EtaleCohomology.fieldBaseChangeRestrictionRestrictScalarsIso`. -/
theorem fieldBaseChangeRestrictionRestrictScalarsIso_naturality
    (N : CochainComplex.Plus (EtaleModules.{u, 0} Λ' Y.left)) :
    (mapDerivedCategoryPlusNatTrans (etaleModuleRestrictScalarsNatTrans ρ θ
        (fieldBaseChange Y kbar))).app (fieldBaseChangeRestriction.{u, 0} Λ' Y kbar N) ≫
        (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom =
      (fieldBaseChangeRestrictionRestrictScalarsIso ρ Y kbar N).hom ≫
        (fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map
          (etaleModuleRestrictScalarsComplexEndo ρ θ N) := by
  rw [fieldBaseChangeRestrictionRestrictScalarsIso_hom,
    reassoc_of% (Functor.mapDerivedCategoryPlusNatTrans_app_Q_comp_mapDerivedCategoryPlusQIso
      (etaleModuleRestrictScalarsNatTrans ρ θ (fieldBaseChange Y kbar))
      ((etaleModuleInverseImage.{u, 0} Λ'
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj N)),
    Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  refine ((DerivedCategory.Plus.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Plus.Q.map ?_)).trans (DerivedCategory.Plus.Q.map_comp _ _)
  ext n : 2
  exact inv_comp_eq_of_comp_hom_eq
    ((etaleModuleInverseImageRestrictScalars ρ (fieldBaseChangeProj Y kbar)).app (N.obj.X n)) _ _
    (etaleModuleInverseImageRestrictScalars_naturality ρ θ (fieldBaseChangeProj Y kbar) (N.obj.X n))

end Restriction

/-- A chase through four commutative squares along a composite of two functors. -/
theorem comp_eq_of_four_squares_map_map {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] (Γ : C₂ ⥤ C₁) (P : C₃ ⥤ C₂) {X₀ : C₁} {Y₀ : C₂} {Z₀ Z₁ Z₂ : C₃}
    (t₀ : X₀ ⟶ X₀) (a : X₀ ⟶ Γ.obj Y₀) (t₁ : Y₀ ⟶ Y₀) (b : Y₀ ⟶ P.obj Z₀) (t₂ : Z₀ ⟶ Z₀)
    (c : Z₀ ⟶ Z₁) (t₃ : Z₁ ⟶ Z₁) (d : Z₁ ⟶ Z₂) (t₄ : Z₂ ⟶ Z₂)
    (h₀ : t₀ ≫ a = a ≫ Γ.map t₁) (h₁ : t₁ ≫ b = b ≫ P.map t₂) (h₂ : t₂ ≫ c = c ≫ t₃)
    (h₃ : t₃ ≫ d = d ≫ t₄) :
    t₀ ≫ ((a ≫ Γ.map (b ≫ P.map c)) ≫ Γ.map (P.map d)) =
      ((a ≫ Γ.map (b ≫ P.map c)) ≫ Γ.map (P.map d)) ≫ Γ.map (P.map t₄) := by
  simp only [Category.assoc, ← Γ.map_comp, ← P.map_comp]
  rw [reassoc_of% h₀, ← Γ.map_comp, reassoc_of% h₁, ← P.map_comp, reassoc_of% h₂, h₃]

section CompactSupport

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
open Stacks.DerivedFunctor in
/-- **`RΓ_c(X_k̄, K)|_Λ ≅ RΓ_c(X_k̄, K|_Λ)` is natural in endomorphisms of restriction of
scalars.**  For a natural endomorphism `θ` of restriction of scalars of modules along `ρ`, the
comparison carries the degreewise action of `θ` on the complex of `Λ`-modules `RΓ_c(X_k̄, K)|_Λ`
to `RΓ_c(X_k̄, -)` of the sectionwise endomorphism `Θ` of `K|_Λ`. -/
theorem compactSupportFrobeniusCohomologyRestrictScalarsIso_naturality
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)) :
    (mapDerivedCategoryPlusNatTrans θ).app
        (compactSupportFrobeniusCohomology.{u, 0} Λ' f j kbar K) ≫
        (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K).hom =
      (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K).hom ≫
        (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          (etaleModuleRestrictScalarsComplexEndo ρ θ K) := by
  have h₃ : (fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).map
        (etaleModuleRestrictScalarsComplexEndo ρ θ
          ((etaleModuleExtensionByZero.{u, 0} Λ' j.immersion).mapCochainComplexPlus.obj K)) ≫
      (fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).map
        (extensionByZeroRestrictScalarsComplexIso ρ f j K).hom =
      (fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).map
        (extensionByZeroRestrictScalarsComplexIso ρ f j K).hom ≫
      (fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map
          (etaleModuleRestrictScalarsComplexEndo ρ θ K)) := by
    refine (Functor.map_comp _ _ _).symm.trans ((congrArg _ ?_).trans (Functor.map_comp _ _ _))
    ext n : 2
    exact inv_comp_eq_of_comp_hom_eq
      ((etaleModuleExtensionByZeroRestrictScalars ρ j.immersion).app (K.obj.X n)) _ _
      (etaleModuleExtensionByZeroRestrictScalars_naturality ρ θ j.immersion (K.obj.X n))
  exact comp_eq_of_four_squares_map_map _ _ _ _ _ _ _ _ _ _ _
    (etaleModuleDerivedGlobalSectionsRestrictScalars_naturality ρ θ (Spec (.of kbar)) _)
    (etaleModuleDerivedDirectImageRestrictScalars_naturality ρ θ _ _)
    (fieldBaseChangeRestrictionRestrictScalarsIso_naturality ρ θ (Over.mk j.toBase) kbar _) h₃

end CompactSupport

end Stacks.EtaleCohomology

end
