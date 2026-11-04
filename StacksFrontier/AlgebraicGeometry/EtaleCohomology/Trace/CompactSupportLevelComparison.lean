module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectImageSectionsRestrictScalarsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleTorsionReduction
public import StacksFrontier.Homology.Perfect.ZModPrimePowerBaseChange
public import StacksFrontier.CategoryTheory.Abelian.PowExactTorsionLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# `RΓ_c(X_k̄, F'ₙ₊₁) ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ ≅ RΓ_c(X_k̄, F'ₙ)` for a flat level

Let `F` be a sheaf of `ℤ/ℓⁿ⁺²ℤ`-modules on `X_étale` which is flat (pow-exact), `G` a sheaf of
`ℤ/ℓⁿ⁺¹ℤ`-modules, and `t : F ⟶ G` a morphism exhibiting `G` as `F / ℓⁿ⁺¹ F`.  Then the
morphism `RΓ_c(X_k̄, F) ⟶ RΓ_c(X_k̄, G)` of `D(ℤ/ℓⁿ⁺²ℤ)` induced by `t` (and the comparison of
`RΓ_c` with restriction of scalars) is adjoint to an isomorphism
`RΓ_c(X_k̄, F) ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ ≅ RΓ_c(X_k̄, G)`, provided `RΓ_c(X_k̄, F)` is perfect.

This is item (2) of the proof of [Tag 03V2](https://stacks.math.columbia.edu/tag/03V2), the
identification `Kₙ₊₁ ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ = Kₙ` of SGA 4½ Rapport 4.12.

The proof reads everything on an injective resolution `I` of the restriction of `j_! F` to
`X̄_k̄`: its `ℓⁿ⁺¹`-torsion `I[ℓⁿ⁺¹]` is an injective resolution of the restriction of `j_! G`,
the map induced by `t` is multiplication by `ℓ` from `I` to `I[ℓⁿ⁺¹]`, which is termwise the
quotient by `ℓⁿ⁺¹` on global sections, and the algebraic statement
`Stacks.InverseSystem.isIso_levelAdjunction_homEquiv_symm_of_flat` applies.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_eq`: the
  comparison of `RΓ_c` with restriction of scalars, unfolded.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Unfold

/-- `c⁻¹ ≫ t = z⁻¹` when `c = t ≫ z`, on variables. -/
private lemma inv_comp_eq_of_hom_eq_comp {C : Type*} [Category* C] {A B B' : C} (c : A ≅ B')
    (t : A ⟶ B) (z : B ≅ B') (h : c.hom = t ≫ z.hom) : c.inv ≫ t = z.inv := by
  rw [Iso.inv_comp_eq, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A naturality square and a factorization, transported through a functor, on variables. -/
private lemma comp_eq_of_map_comp {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D)
    {E N Nr Bc I : C} {Dr DC : D} (et : E ⟶ Nr) (ci : Nr ⟶ N) (rb : N ⟶ Bc) (ia : E ⟶ I)
    (m : I ⟶ Bc) (pN : Q.obj N ⟶ Dr) (pC : Q.obj Bc ⟶ DC) (rq : Dr ⟶ DC)
    (hψ : Q.map rb ≫ pC = pN ≫ rq) (hμ : et ≫ ci ≫ rb = ia ≫ m) :
    Q.map et ≫ (Q.map ci ≫ pN) ≫ rq = Q.map ia ≫ Q.map m ≫ pC := by
  rw [Category.assoc, ← hψ, ← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, hμ,
    Q.map_comp, Category.assoc]

/-- The final assembly of `compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv`, on
variables: `H` is `RΓ(Rg_* -)`. -/
private lemma final_assembly {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {X₀ X₁ X₂ X₃ X₄ : C} {T₁ T₂ T₂' : D}
    (et : X₀ ⟶ X₁) (x' : X₁ ⟶ X₂) (qb : X₂ ⟶ X₃) (qa : X₀ ⟶ X₄) (w : X₄ ⟶ X₃)
    (θi : H.obj X₁ ⟶ T₁) (rb : T₁ ⟶ T₂) (c₁ : T₂ ⟶ T₂') (c₂ : T₂' ⟶ H.obj X₃)
    (tN : T₁ ⟶ H.obj X₂)
    (hθΨ : rb ≫ c₁ ≫ c₂ = tN ≫ H.map qb) (hθ' : θi ≫ tN = H.map x')
    (hμ : et ≫ x' ≫ qb = qa ≫ w) :
    H.map et ≫ θi ≫ rb ≫ c₁ ≫ c₂ = H.map qa ≫ H.map w := by
  rw [hθΨ, ← Category.assoc θi, hθ', ← H.map_comp, ← H.map_comp, hμ, H.map_comp]

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')
  {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The restriction to `X̄_k̄` of the extension by zero along the compactification, termwise on
bounded below complexes. -/
abbrev compactSupportRestriction (Λ : Type) [Ring Λ] :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ X) ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)) :=
  (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus ⋙
    (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus

/-- The termwise commutation of `compactSupportRestriction` with restriction of scalars. -/
def compactSupportRestrictionRestrictScalarsIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)) :
    (etaleModuleRestrictScalars ρ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((compactSupportRestriction f j kbar Λ').obj K) ≅
      (compactSupportRestriction f j kbar Λ).obj
        ((etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K) :=
  inverseImageRestrictScalarsComplexIso ρ (Over.mk j.toBase) kbar
      ((etaleModuleExtensionByZero.{u, 0} Λ' j.immersion).mapCochainComplexPlus.obj K) ≪≫
    (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso
        (extensionByZeroRestrictScalarsComplexIso ρ f j K)

/-- **The comparison `RΓ_c(X_k̄, K)|_Λ ≅ RΓ_c(X_k̄, res_ρ K)` unfolded**: the comparisons of
`RΓ` and `Rf_*` with `res_ρ`, followed by the commutation of `Q` with `res_ρ` and the termwise
commutation of the restriction to `X̄_k̄` of the extension by zero. -/
theorem compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_eq
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X)) :
    (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K).hom =
      (etaleModuleDerivedGlobalSectionsRestrictScalars ρ (Spec (.of kbar))).hom.app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd (Over.mk j.toBase).hom
            (specAlgebraMap k kbar))).obj
            (DerivedCategory.Plus.Q.obj ((compactSupportRestriction f j kbar Λ').obj K))) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd (Over.mk j.toBase).hom
            (specAlgebraMap k kbar))).hom.app
            (DerivedCategory.Plus.Q.obj ((compactSupportRestriction f j kbar Λ').obj K)) ≫
          (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom
            (specAlgebraMap k kbar))).map
            ((Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
              (fieldBaseChange (Over.mk j.toBase) kbar))).hom.app
              ((compactSupportRestriction f j kbar Λ').obj K) ≫
              DerivedCategory.Plus.Q.map
                (compactSupportRestrictionRestrictScalarsIso ρ f j kbar K).hom)) := by
  simp only [compactSupportFrobeniusCohomologyRestrictScalarsIso,
    fieldBaseChangeCohomologyRestrictScalarsIso,
    fieldBaseChangeRestrictionRestrictScalarsIso, compactSupportRestrictionRestrictScalarsIso,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rfl

/-- **The map of `RΓ_c(X_k̄, -)` induced by `t : K ⟶ res_ρ K'`, read on resolutions.** Let
`a : K|_{X̄_k̄} ⟶ I` and `b : K'|_{X̄_k̄} ⟶ C` be morphisms of bounded below complexes (in
practice injective resolutions), and `μ : I ⟶ res_ρ C` lie over `t`.  Then the composite of
`RΓ_c(t)` with the comparison `RΓ_c(X_k̄, res_ρ K') ≅ RΓ_c(X_k̄, K')|_Λ`, followed by `b` and
the comparison of `RΓ(Spec k̄, Rg_* -)` with `res_ρ` at `C`, is `RΓ(Spec k̄, Rg_*(a ≫ μ))`. -/
theorem compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (K' : CochainComplex.Plus (EtaleModules.{u, 0} Λ' X))
    (tc : K ⟶ (etaleModuleRestrictScalars ρ X).mapCochainComplexPlus.obj K')
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)))
    (a : (compactSupportRestriction f j kbar Λ).obj K ⟶ I)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ' (fieldBaseChange (Over.mk j.toBase) kbar)))
    (b : (compactSupportRestriction f j kbar Λ').obj K' ⟶ C)
    (μ : I ⟶ (etaleModuleRestrictScalars ρ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj C)
    (hμ : (compactSupportRestriction f j kbar Λ).map tc ≫
      (compactSupportRestrictionRestrictScalarsIso ρ f j kbar K').inv ≫
      (etaleModuleRestrictScalars ρ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map b =
      a ≫ μ) :
    (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map tc ≫
        (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K').inv ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus.map
          ((etaleModuleDerivedGlobalSections.{u, 0} Λ' (Spec (.of kbar))).map
            ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd (Over.mk j.toBase).hom
              (specAlgebraMap k kbar))).map (DerivedCategory.Plus.Q.map b))) ≫
        (etaleModuleDerivedGlobalSectionsRestrictScalars ρ (Spec (.of kbar))).hom.app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ' (pullback.snd (Over.mk j.toBase).hom
            (specAlgebraMap k kbar))).obj (DerivedCategory.Plus.Q.obj C)) ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImageRestrictScalars ρ (pullback.snd (Over.mk j.toBase).hom
            (specAlgebraMap k kbar))).hom.app (DerivedCategory.Plus.Q.obj C)) =
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom
          (specAlgebraMap k kbar))).map (DerivedCategory.Plus.Q.map a)) ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd (Over.mk j.toBase).hom
          (specAlgebraMap k kbar))).map (DerivedCategory.Plus.Q.map μ ≫
          (Functor.mapDerivedCategoryPlusQIso (etaleModuleRestrictScalars ρ
            (fieldBaseChange (Over.mk j.toBase) kbar))).inv.app C)) := by
  let gk := pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)
  let RΓ := etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))
  let RΓ' := etaleModuleDerivedGlobalSections.{u, 0} Λ' (Spec (.of kbar))
  let Rg := etaleModuleDerivedDirectImage.{u, 0} Λ gk
  let Rg' := etaleModuleDerivedDirectImage.{u, 0} Λ' gk
  let rY := etaleModuleRestrictScalars ρ (fieldBaseChange (Over.mk j.toBase) kbar)
  let rM := (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus
  let θΓ := etaleModuleDerivedGlobalSectionsRestrictScalars ρ (Spec (.of kbar))
  let θg := etaleModuleDerivedDirectImageRestrictScalars ρ gk
  let ψ := Functor.mapDerivedCategoryPlusQIso rY
  let N' := (compactSupportRestriction f j kbar Λ').obj K'
  let χ := compactSupportRestrictionRestrictScalarsIso ρ f j kbar K'
  -- the comparison `θΨ` of `RΓ(Rg_* -)` with `res_ρ`, and its naturality in `b`
  let θΨ : ∀ D, rM.obj (RΓ'.obj (Rg'.obj D)) ⟶ RΓ.obj (Rg.obj (rY.mapDerivedCategoryPlus.obj D)) :=
    fun D => θΓ.hom.app (Rg'.obj D) ≫ RΓ.map (θg.hom.app D)
  have hθΨ : rM.map (RΓ'.map (Rg'.map (DerivedCategory.Plus.Q.map b))) ≫
      θΨ (DerivedCategory.Plus.Q.obj C) = θΨ (DerivedCategory.Plus.Q.obj N') ≫
        RΓ.map (Rg.map (rY.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Q.map b))) := by
    have h₁ : rM.map (RΓ'.map (Rg'.map (DerivedCategory.Plus.Q.map b))) ≫
        θΓ.hom.app (Rg'.obj (DerivedCategory.Plus.Q.obj C)) =
        θΓ.hom.app (Rg'.obj (DerivedCategory.Plus.Q.obj N')) ≫
          RΓ.map ((etaleModuleRestrictScalars ρ (Spec (.of kbar))).mapDerivedCategoryPlus.map
            (Rg'.map (DerivedCategory.Plus.Q.map b))) :=
      θΓ.hom.naturality (Rg'.map (DerivedCategory.Plus.Q.map b))
    have h₂ : (etaleModuleRestrictScalars ρ (Spec (.of kbar))).mapDerivedCategoryPlus.map
          (Rg'.map (DerivedCategory.Plus.Q.map b)) ≫ θg.hom.app (DerivedCategory.Plus.Q.obj C) =
        θg.hom.app (DerivedCategory.Plus.Q.obj N') ≫
          Rg.map (rY.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Q.map b)) :=
      θg.hom.naturality (DerivedCategory.Plus.Q.map b)
    calc rM.map (RΓ'.map (Rg'.map (DerivedCategory.Plus.Q.map b))) ≫
          (θΓ.hom.app (Rg'.obj (DerivedCategory.Plus.Q.obj C)) ≫
            RΓ.map (θg.hom.app (DerivedCategory.Plus.Q.obj C)))
        = (rM.map (RΓ'.map (Rg'.map (DerivedCategory.Plus.Q.map b))) ≫
          θΓ.hom.app (Rg'.obj (DerivedCategory.Plus.Q.obj C))) ≫
            RΓ.map (θg.hom.app (DerivedCategory.Plus.Q.obj C)) := (Category.assoc _ _ _).symm
      _ = θΓ.hom.app (Rg'.obj (DerivedCategory.Plus.Q.obj N')) ≫
          RΓ.map ((etaleModuleRestrictScalars ρ (Spec (.of kbar))).mapDerivedCategoryPlus.map
            (Rg'.map (DerivedCategory.Plus.Q.map b)) ≫
              θg.hom.app (DerivedCategory.Plus.Q.obj C)) := by
          rw [h₁, Category.assoc, RΓ.map_comp]
      _ = _ := by
          rw [h₂, RΓ.map_comp, ← Category.assoc]
  -- the unfolded comparison
  have hθ : (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K').hom =
      θΨ (DerivedCategory.Plus.Q.obj N') ≫ RΓ.map (Rg.map (ψ.hom.app N' ≫
        DerivedCategory.Plus.Q.map χ.hom)) := by
    rw [compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_eq]
    exact (whisker_eq _ (RΓ.map_comp _ _)).trans (Category.assoc _ _ _).symm
  -- the naturality of `ψ⁻¹` in `b`
  have hψ : DerivedCategory.Plus.Q.map (rY.mapCochainComplexPlus.map b) ≫ ψ.inv.app C =
      ψ.inv.app N' ≫ rY.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Q.map b) :=
    ψ.inv.naturality b
  let X := ψ.app N' ≪≫ DerivedCategory.Plus.Q.mapIso χ
  let Z := RΓ.mapIso (Rg.mapIso X)
  have hθ' : (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ f j kbar K').inv ≫
      θΨ (DerivedCategory.Plus.Q.obj N') = Z.inv :=
    inv_comp_eq_of_hom_eq_comp _ _ Z hθ
  have hZ : Z.inv = RΓ.map (Rg.map (DerivedCategory.Plus.Q.map χ.inv ≫ ψ.inv.app N')) := rfl
  have hμ' : DerivedCategory.Plus.Q.map ((compactSupportRestriction f j kbar Λ).map tc) ≫
      (DerivedCategory.Plus.Q.map χ.inv ≫ ψ.inv.app N') ≫
      rY.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Q.map b) =
      DerivedCategory.Plus.Q.map a ≫ DerivedCategory.Plus.Q.map μ ≫ ψ.inv.app C :=
    comp_eq_of_map_comp DerivedCategory.Plus.Q _ _ _ _ _ _ _ _ hψ hμ
  exact final_assembly (Rg ⋙ RΓ) _ _ _ _ _ _ _ _ _ _ hθΨ (hθ'.trans hZ) hμ'

end Unfold

section Torsion

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (Y : Scheme.{u})

/-- Restriction of scalars of sheaves of modules reflects isomorphisms. -/
instance etaleModuleRestrictScalars_reflectsIsomorphisms :
    (etaleModuleRestrictScalars ρ Y).ReflectsIsomorphisms where
  reflects {F G} φ h := by
    have : ∀ U, IsIso (φ.hom.app U) := fun U => by
      have : IsIso ((etaleModuleRestrictScalars ρ Y).map φ).hom :=
        (sheafToPresheaf _ _).map_isIso ((etaleModuleRestrictScalars ρ Y).map φ)
      have : IsIso ((ModuleCat.restrictScalars.{u + 1} ρ).map (φ.hom.app U)) :=
        NatIso.isIso_app_of_isIso ((etaleModuleRestrictScalars ρ Y).map φ).hom U
      exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars.{u + 1} ρ)
    have : IsIso φ.hom := NatIso.isIso_of_isIso_app _
    have : IsIso ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')).map φ) := this
    exact isIso_of_reflects_iso φ (sheafToPresheaf _ _)

variable {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ)

local notation "ρₙ" => Stacks.InverseSystem.levelCast ℓ n

/-- The `ℓⁿ⁺¹`-torsion `F[ℓⁿ⁺¹] ⟶ F` of a sheaf of `ℤ/ℓⁿ⁺²ℤ`-modules is a torsion kernel. -/
theorem isTorsionKernel_levelTorsion (F : EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Y) :
    IsTorsionKernel (ℓ ^ (n + 1)) ((etaleModuleCoextendScalarsAdj ρₙ Y).counit.app F) :=
  isTorsionKernel_etaleModuleTorsionι (N := ℓ ^ (n + 1)) (hN := pow_dvd_pow ℓ (by omega)) F

/-- Multiplication by `ℓ`, from a complex of sheaves of `ℤ/ℓⁿ⁺²ℤ`-modules to its `ℓⁿ⁺¹`-torsion. -/
def levelTorsionLift (I : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Y) ℤ) :
    I ⟶ ((etaleModuleRestrictScalars ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((etaleModuleCoextendScalars ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) where
  f k := (isTorsionKernel_levelTorsion Y n (I.X k)).torsionLift (etaleModules_pow_nsmul_id _)
    (Nat.le_succ _)
  comm' k k' _ := by
    have := (isTorsionKernel_levelTorsion Y n (I.X k')).mono
    rw [← cancel_mono ((etaleModuleCoextendScalarsAdj ρₙ Y).counit.app (I.X k')), Category.assoc,
      Category.assoc, IsTorsionKernel.torsionLift_comp]
    change _ ≫ (etaleModuleRestrictScalars ρₙ Y).map
      ((etaleModuleCoextendScalars ρₙ Y).map (I.d k k')) ≫ _ = _
    have hn := (etaleModuleCoextendScalarsAdj ρₙ Y).counit.naturality (I.d k k')
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn, ← Category.assoc, IsTorsionKernel.torsionLift_comp, nsmul_id_comp]
    rfl

/-- On a complex of flat sheaves, multiplication by `ℓ` into the `ℓⁿ⁺¹`-torsion is termwise a
cokernel of `ℓⁿ⁺¹`. -/
def isColimitLevelTorsionLift
    (I : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Y) ℤ)
    (hI : ∀ i, PowExact ℓ (n + 1 + 1) (I.X i)) (i : ℤ) :
    IsColimit (CokernelCofork.ofπ ((levelTorsionLift Y n I).f i)
      ((isTorsionKernel_levelTorsion Y n (I.X i)).nsmul_comp_torsionLift
        (etaleModules_pow_nsmul_id _) (Nat.le_succ _))) :=
  (isTorsionKernel_levelTorsion Y n (I.X i)).isColimitTorsionLift (etaleModules_pow_nsmul_id _)
    (Nat.le_succ _) (hI i)

variable {Y n}

/-- `ℓⁿ⁺¹ · ℓ = 0` on a sheaf of `ℤ/ℓⁿ⁺²ℤ`-modules. -/
theorem levelPow_nsmul_comp_nsmul (F : EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Y) :
    ((ℓ ^ (n + 1)) • 𝟙 F) ≫ ((ℓ ^ (n + 1 + 1 - (n + 1))) • 𝟙 F) = 0 := by
  rw [show n + 1 + 1 - (n + 1) = 1 by omega, Preadditive.nsmul_comp, Category.id_comp, smul_smul,
    ← pow_add, etaleModules_pow_nsmul_id]

/-- For `t : N ⟶ res N'` termwise a cokernel of `ℓⁿ⁺¹`, multiplication by `ℓ` on `N` factors
through `t`: the map `res N' ≅ N / ℓⁿ⁺¹ N ⟶ N`. -/
def levelMultiplication {N : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Y) ℤ}
    {N' : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) Y) ℤ}
    (t : N ⟶ ((etaleModuleRestrictScalars ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
    (w : ∀ i, ((ℓ ^ (n + 1)) • 𝟙 (N.X i)) ≫ t.f i = 0)
    (ht : ∀ i, IsColimit (CokernelCofork.ofπ (t.f i) (w i))) :
    ((etaleModuleRestrictScalars ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N' ⟶ N where
  f i := Cofork.IsColimit.desc (ht i) _ ((levelPow_nsmul_comp_nsmul (N.X i)).trans zero_comp.symm)
  comm' i i' _ := by
    refine Cofork.IsColimit.hom_ext (ht i) ?_
    have h₁ : t.f i ≫ Cofork.IsColimit.desc (ht i) _
        ((levelPow_nsmul_comp_nsmul (N.X i)).trans zero_comp.symm) =
        (ℓ ^ (n + 1 + 1 - (n + 1))) • 𝟙 (N.X i) :=
      Cofork.IsColimit.π_desc' (ht i) _ ((levelPow_nsmul_comp_nsmul (N.X i)).trans zero_comp.symm)
    have h₂ : t.f i' ≫ Cofork.IsColimit.desc (ht i') _
        ((levelPow_nsmul_comp_nsmul (N.X i')).trans zero_comp.symm) =
        (ℓ ^ (n + 1 + 1 - (n + 1))) • 𝟙 (N.X i') :=
      Cofork.IsColimit.π_desc' (ht i') _ ((levelPow_nsmul_comp_nsmul (N.X i')).trans zero_comp.symm)
    change t.f i ≫ _ ≫ _ = t.f i ≫ _ ≫ _
    rw [← Category.assoc, h₁, nsmul_id_comp, ← Category.assoc, t.comm i i', Category.assoc, h₂]

/-- In each degree, `t` followed by `levelMultiplication t w ht` is multiplication by `ℓ`. -/
theorem levelMultiplication_f
    {N : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Y) ℤ}
    {N' : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) Y) ℤ}
    (t : N ⟶ ((etaleModuleRestrictScalars ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
    (w : ∀ i, ((ℓ ^ (n + 1)) • 𝟙 (N.X i)) ≫ t.f i = 0)
    (ht : ∀ i, IsColimit (CokernelCofork.ofπ (t.f i) (w i))) (i : ℤ) :
    t.f i ≫ (levelMultiplication t w ht).f i = (ℓ ^ (n + 1 + 1 - (n + 1))) • 𝟙 (N.X i) :=
  Cofork.IsColimit.π_desc' (ht i) _ ((levelPow_nsmul_comp_nsmul (N.X i)).trans zero_comp.symm)

/-- The adjoint `N' ⟶ N[ℓⁿ⁺¹]` of `levelMultiplication` is an isomorphism when `N` has flat
terms: termwise, `t` and multiplication by `ℓ` into the `ℓⁿ⁺¹`-torsion are both cokernels of
`ℓⁿ⁺¹`. -/
theorem isIso_levelMultiplication_adjoint
    {N : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Y) ℤ}
    {N' : CochainComplex (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) Y) ℤ}
    (t : N ⟶ ((etaleModuleRestrictScalars ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj N')
    (w : ∀ i, ((ℓ ^ (n + 1)) • 𝟙 (N.X i)) ≫ t.f i = 0)
    (ht : ∀ i, IsColimit (CokernelCofork.ofπ (t.f i) (w i)))
    (hN : ∀ i, PowExact ℓ (n + 1 + 1) (N.X i)) :
    IsIso ((((etaleModuleCoextendScalarsAdj ρₙ Y).mapHomologicalComplex
      (ComplexShape.up ℤ)).homEquiv _ _) (levelMultiplication t w ht)) := by
  let adj := (etaleModuleCoextendScalarsAdj ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)
  let ν := levelMultiplication t w ht
  let β := adj.homEquiv _ _ ν
  have hβ : ((etaleModuleRestrictScalars ρₙ Y).mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫
      adj.counit.app N = ν :=
    (adj.homEquiv_counit N' N β).symm.trans ((adj.homEquiv N' N).symm_apply_apply ν)
  have : ∀ i, IsIso (β.f i) := fun i => by
    have hk := isTorsionKernel_levelTorsion Y n (N.X i)
    have := hk.mono
    have hc : t.f i ≫ (etaleModuleRestrictScalars ρₙ Y).map (β.f i) =
        (levelTorsionLift Y n N).f i := by
      refine hk.eq_torsionLift (etaleModules_pow_nsmul_id _) (Nat.le_succ _) ?_
      have := HomologicalComplex.congr_hom hβ i
      show t.f i ≫ (etaleModuleRestrictScalars ρₙ Y).map (β.f i) ≫
        (etaleModuleCoextendScalarsAdj ρₙ Y).counit.app (N.X i) = _
      rw [show (etaleModuleRestrictScalars ρₙ Y).map (β.f i) ≫
          (etaleModuleCoextendScalarsAdj ρₙ Y).counit.app (N.X i) = ν.f i from this]
      exact levelMultiplication_f t w ht i
    let e := IsColimit.coconePointUniqueUpToIso (ht i) (isColimitLevelTorsionLift Y n N hN i)
    have he : (etaleModuleRestrictScalars ρₙ Y).map (β.f i) = e.hom :=
      Cofork.IsColimit.hom_ext (ht i) (hc.trans
        (IsColimit.comp_coconePointUniqueUpToIso_hom (ht i) (isColimitLevelTorsionLift Y n N hN i)
          WalkingParallelPair.one).symm)
    have : IsIso ((etaleModuleRestrictScalars ρₙ Y).map (β.f i)) := by
      rw [he]
      exact e.isIso_hom
    exact isIso_of_reflects_iso _ (etaleModuleRestrictScalars ρₙ Y)
  exact HomologicalComplex.Hom.isIso_of_components β

end Torsion

section Helpers

variable {C : Type*} [Category* C] [Abelian C]

/-- A cokernel cofork of `f` is one of any `f'` equal to `f`. -/
def isColimitCokernelCoforkOfEq {X Y : C} {f f' : X ⟶ X} (hf : f = f') {g : X ⟶ Y} (w : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ g w)) :
    IsColimit (CokernelCofork.ofπ (f := f') g (hf ▸ w)) := by
  subst hf
  exact h

/-- A cokernel cofork is one for any equal projection. -/
def isColimitCokernelCoforkOfEqπ {X Y : C} {f : X ⟶ X} {g g' : X ⟶ Y} (hg : g = g') (w : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ g w)) :
    IsColimit (CokernelCofork.ofπ (f := f) g' (hg ▸ w)) := by
  subst hg
  exact h

/-- A cokernel followed by an isomorphism is a cokernel. -/
def isColimitCokernelCoforkCompIso {X Y Y' : C} {f : X ⟶ X} {g : X ⟶ Y} (w : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ g w)) {e : Y ⟶ Y'} (he : IsIso e) :
    IsColimit (CokernelCofork.ofπ (f := f) (g ≫ e) (by rw [← Category.assoc, w, zero_comp])) :=
  IsColimit.ofIsoColimit h (Cofork.ext (asIso e) rfl)

/-- `t ≫ r ≫ θ = P ≫ W` and `U ≫ W = G ≫ V₁ ≫ V₂ ≫ θ` with `r`, `θ`, `U` invertible give
`t = P ≫ U⁻¹ ≫ G ≫ V₁ ≫ V₂ ≫ r⁻¹`. -/
theorem eq_of_two_squares {D : Type*} [Category* D] {A B C₁ C₂ E F H H' : D} (t : A ⟶ B)
    (r : B ⟶ C₁) (θ : C₁ ⟶ C₂) (P : A ⟶ E) (W : E ⟶ C₂) (U : F ⟶ E) (G : F ⟶ H) (V₁ : H ⟶ H')
    (V₂ : H' ⟶ C₁) [IsIso r] [IsIso θ] [IsIso U]
    (h₁ : t ≫ r ≫ θ = P ≫ W) (h₂ : U ≫ W = G ≫ V₁ ≫ V₂ ≫ θ) :
    t = P ≫ inv U ≫ G ≫ V₁ ≫ V₂ ≫ inv r := by
  have hW : W = inv U ≫ G ≫ V₁ ≫ V₂ ≫ θ := by rw [← h₂, IsIso.inv_hom_id_assoc]
  rw [hW] at h₁
  have h₁' : t ≫ r = P ≫ inv U ≫ G ≫ V₁ ≫ V₂ := by
    rw [← cancel_mono θ]
    simpa only [Category.assoc] using h₁
  rw [← cancel_mono r]
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h₁'

/-- The decomposition of the image of a five-fold composite, on variables. -/
theorem iota_decomp {C E : Type*} [Category* C] [Category* E] (F : C ⥤ E)
    {X₀ X₁ X₂ X₃ X₄ X₅ : C} (p₁ : X₀ ⟶ X₁) (p₂ : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (v : X₃ ⟶ X₄)
    (w : X₄ ⟶ X₅) (G' : F.obj X₂ ⟶ F.obj X₃) (hG : F.map g = G') (V' : F.obj X₃ ⟶ F.obj X₄)
    (hv : F.map v = V') (W' : F.obj X₄ ⟶ F.obj X₅) (hw : F.map w = W') :
    F.map (p₁ ≫ p₂ ≫ g ≫ v ≫ w) = F.map (p₁ ≫ p₂) ≫ (G' ≫ V') ≫ W' := by
  rw [← hG, ← hv, ← hw]
  simp only [Functor.map_comp, Category.assoc]

/-- The adjoint of `a ≫ x ≫ R(c)` with `a`, `c` invertible is invertible when that of `x` is. -/
theorem isIso_homEquiv_symm_comp {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {X X' : C} {Y Y' : D} (a : X ⟶ X') (x : X' ⟶ R.obj Y) (c : Y ⟶ Y')
    [IsIso a] [IsIso c] [IsIso ((adj.homEquiv _ _).symm x)] :
    IsIso ((adj.homEquiv _ _).symm (a ≫ x ≫ R.map c)) := by
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
  infer_instance

/-- If `m • 𝟙 A ≫ g = 0`, then `m • 𝟙 (F A) ≫ F g ≫ e = 0` for an additive functor `F`. -/
private theorem nsmul_id_comp_map_comp_eq_zero {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {A B : C} {E : D} (m : ℕ)
    (g : A ⟶ B) (e : F.obj B ⟶ E) (h : (m • 𝟙 A) ≫ g = 0) :
    (m • 𝟙 (F.obj A)) ≫ F.map g ≫ e = 0 := by
  rw [← Category.assoc, ← F.map_id, ← F.map_nsmul, ← F.map_comp, h, F.map_zero, zero_comp]

/-- A quasi-isomorphism of bounded below complexes becomes invertible in `D⁺`. -/
private theorem isIso_plus_Q_map_of_quasiIso {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {K L : CochainComplex.Plus A} (φ : K.obj ⟶ L.obj) [QuasiIso φ] :
    IsIso (DerivedCategory.Plus.Q.map (ObjectProperty.homMk φ : K ⟶ L)) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
    (ObjectProperty.homMk φ : K ⟶ L))) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).2 ‹_›
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

end Helpers

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Main

open Stacks.InverseSystem

variable {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ)
  {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

local notation "ρₙ" => Stacks.InverseSystem.levelCast ℓ n

/-- **[Tag 03V2, item (2)] `RΓ_c(X_k̄, K) ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ ≅ RΓ_c(X_k̄, K')`.** Let `K` be a bounded
below complex of flat sheaves of `ℤ/ℓⁿ⁺²ℤ`-modules on `X_étale`, `K'` one of sheaves of
`ℤ/ℓⁿ⁺¹ℤ`-modules and `t : K ⟶ K'` termwise a cokernel of `ℓⁿ⁺¹`.  If `RΓ_c(X_k̄, K)` is perfect,
the morphism `RΓ_c(X_k̄, K) ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ ⟶ RΓ_c(X_k̄, K')` adjoint to the map
`RΓ_c(X_k̄, K) ⟶ RΓ_c(X_k̄, K')` induced by `t` is an isomorphism. -/
theorem isIso_levelAdjunction_homEquiv_symm_compactSupport
    (K : CochainComplex.Plus (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) X))
    (K' : CochainComplex.Plus (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) X))
    (tc : K ⟶ (etaleModuleRestrictScalars ρₙ X).mapCochainComplexPlus.obj K')
    (hK : ∀ i, PowExact ℓ (n + 1 + 1) (K.obj.X i))
    (w : ∀ i, ((ℓ ^ (n + 1)) • 𝟙 (K.obj.X i)) ≫ tc.hom.f i = 0)
    (ht : ∀ i, IsColimit (CokernelCofork.ofπ (tc.hom.f i) (w i)))
    (hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) f j kbar K))) :
    IsIso (((levelAdjunction.{u + 1} ℓ n).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map tc ≫
        (compactSupportFrobeniusCohomologyRestrictScalarsIso ρₙ f j kbar K').inv))) := by
  -- notation
  let Yb := fieldBaseChange (Over.mk j.toBase) kbar
  let gk := pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)
  let E := compactSupportRestriction f j kbar (ZMod (ℓ ^ (n + 1 + 1)))
  let E' := compactSupportRestriction f j kbar (ZMod (ℓ ^ (n + 1)))
  let rY := etaleModuleRestrictScalars ρₙ Yb
  let χ := compactSupportRestrictionRestrictScalarsIso ρₙ f j kbar K'
  let N := E.obj K
  let N' := E'.obj K'
  -- the termwise map `t` on `X̄_k̄`, a termwise cokernel of `ℓⁿ⁺¹`
  let tN : N.obj ⟶ (rY.mapHomologicalComplex (ComplexShape.up ℤ)).obj N'.obj :=
    (E.map tc ≫ χ.inv).hom
  let Esh := etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) j.immersion ⋙
    etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  have : PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)) :=
    etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) _
  have : (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).IsLeftAdjoint :=
    (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).isLeftAdjoint
  have : (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) j.immersion).IsLeftAdjoint :=
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) j.immersion).isLeftAdjoint
  have h₁ : PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)) :=
    have := (etaleModuleInverseImageAdj.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).isLeftAdjoint
    inferInstance
  have h₂ : PreservesFiniteColimits (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      j.immersion) :=
    have := (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
      j.immersion).isLeftAdjoint
    inferInstance
  have hN : ∀ i, PowExact ℓ (n + 1 + 1) (N.obj.X i) := fun i =>
    ((hK i).map (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) j.immersion)
        (etaleModules_pow_nsmul_id _)).map
      (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1)))
        (fieldBaseChangeProj (Over.mk j.toBase) kbar))
      (etaleModules_pow_nsmul_id _)
  have hEsh : ∀ i, Esh.map ((ℓ ^ (n + 1)) • 𝟙 (K.obj.X i)) = (ℓ ^ (n + 1)) • 𝟙 (N.obj.X i) :=
    fun i => by rw [Esh.map_nsmul, Esh.map_id]; rfl
  have wN : ∀ i, ((ℓ ^ (n + 1)) • 𝟙 (N.obj.X i)) ≫ tN.f i = 0 := fun i =>
    nsmul_id_comp_map_comp_eq_zero Esh _ _ _ (w i)
  have : PreservesFiniteColimits Esh := @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h₂ h₁
  have hχi : ∀ i, IsIso (χ.inv.hom.f i) := fun i =>
    ((HomologicalComplex.eval _ _ i).mapIso ((ObjectProperty.ι _).mapIso χ.symm)).isIso_hom
  have htN : ∀ i, IsColimit (CokernelCofork.ofπ (tN.f i) (wN i)) := fun i =>
    isColimitCokernelCoforkCompIso _ (isColimitCokernelCoforkOfEq (hEsh i) _
      (isColimitCoforkMapOfIsColimit' Esh (w i) (ht i))) (e := χ.inv.hom.f i) (hχi i)
  -- an injective resolution `I` of `N`, and its `ℓⁿ⁺¹`-torsion `C`
  obtain ⟨a₀, ha₀⟩ := (CochainComplex.plus_iff _ N.obj).1 N.property
  obtain ⟨Rs, -, hRs⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a₀ N.obj
  let coext := etaleModuleCoextendScalars ρₙ Yb
  let adj := (etaleModuleCoextendScalarsAdj ρₙ Yb).mapHomologicalComplex (ComplexShape.up ℤ)
  let Ip : CochainComplex.Plus (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) Yb) :=
    ⟨Rs.cocomplex, Rs.boundedBelow⟩
  have hCs : CochainComplex.IsStrictlyGE
      ((coext.mapHomologicalComplex (ComplexShape.up ℤ)).obj Rs.cocomplex) a₀ := inferInstance
  let Cp : CochainComplex.Plus (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) Yb) :=
    ⟨(coext.mapHomologicalComplex (ComplexShape.up ℤ)).obj Rs.cocomplex,
      (CochainComplex.plus_iff _ _).2 ⟨a₀, hCs⟩⟩
  let ν := levelMultiplication tN wN htN
  let β := adj.homEquiv _ _ ν
  have hβiso : IsIso β := isIso_levelMultiplication_adjoint tN wN htN hN
  let b₀ : N'.obj ⟶ Cp.obj := β ≫ (coext.mapHomologicalComplex (ComplexShape.up ℤ)).map Rs.ι
  let μ₀ : Ip.obj ⟶ (rY.mapHomologicalComplex (ComplexShape.up ℤ)).obj Cp.obj :=
    levelTorsionLift Yb n Rs.cocomplex
  -- `μ` lies over `t`
  have hμ₀ : tN ≫ (rY.mapHomologicalComplex (ComplexShape.up ℤ)).map b₀ = Rs.ι ≫ μ₀ := by
    have hmono : Mono (adj.counit.app Rs.cocomplex) := by
      have : ∀ q, Mono ((adj.counit.app Rs.cocomplex).f q) := fun q =>
        (isTorsionKernel_levelTorsion Yb n (Rs.cocomplex.X q)).mono
      exact HomologicalComplex.mono_of_mono_f _ this
    rw [← cancel_mono (adj.counit.app Rs.cocomplex)]
    have hβ : (rY.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫ adj.counit.app N.obj = ν :=
      (adj.homEquiv_counit _ _ β).symm.trans ((adj.homEquiv _ _).symm_apply_apply ν)
    have hc := adj.counit.naturality Rs.ι
    have hl : tN ≫ ν = (ℓ ^ (n + 1 + 1 - (n + 1))) • 𝟙 N.obj := by
      ext q : 1
      simp only [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply,
        HomologicalComplex.id_f]
      exact levelMultiplication_f tN wN htN q
    have hr : μ₀ ≫ adj.counit.app Rs.cocomplex = (ℓ ^ (n + 1 + 1 - (n + 1))) • 𝟙 Rs.cocomplex := by
      ext q : 1
      simp only [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply,
        HomologicalComplex.id_f]
      exact IsTorsionKernel.torsionLift_comp (isTorsionKernel_levelTorsion Yb n (Rs.cocomplex.X q))
        (etaleModules_pow_nsmul_id _) (Nat.le_succ _)
    dsimp only [Functor.comp_map, Functor.id_map] at hc
    calc (tN ≫ (rY.mapHomologicalComplex (ComplexShape.up ℤ)).map b₀) ≫ adj.counit.app Rs.cocomplex
        = tN ≫ (rY.mapHomologicalComplex (ComplexShape.up ℤ)).map β ≫
          ((rY.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((coext.mapHomologicalComplex (ComplexShape.up ℤ)).map Rs.ι) ≫
            adj.counit.app Rs.cocomplex) := by
          simp only [b₀, Functor.map_comp, Category.assoc]
      _ = (tN ≫ ν) ≫ Rs.ι := by rw [hc, ← Category.assoc ((rY.mapHomologicalComplex _).map β), hβ,
          Category.assoc]
      _ = _ := by rw [hl, Category.assoc, hr, nsmul_id_comp]
  let a' : N ⟶ Ip := ObjectProperty.homMk Rs.ι
  let b' : N' ⟶ Cp := ObjectProperty.homMk b₀
  let μ' : Ip ⟶ rY.mapCochainComplexPlus.obj Cp := ObjectProperty.homMk μ₀
  have hμ' : E.map tc ≫ χ.inv ≫ rY.mapCochainComplexPlus.map b' = a' ≫ μ' :=
    ObjectProperty.hom_ext _ ((Category.assoc _ _ _).symm.trans hμ₀)
  have E1 := compactSupportFrobeniusFunctor_map_comp_restrictScalarsIso_inv ρₙ f j kbar K K' tc
    Ip a' Cp b' μ' hμ'
  have E2 := directImageSectionsDerivedUnit_comp_map_restrictScalars ρₙ gk Ip Cp μ'
  -- the invertible pieces
  have hb₀ : QuasiIso b₀ := by
    have : QuasiIso ((coext.mapHomologicalComplex (ComplexShape.up ℤ)).map Rs.ι) :=
      quasiIso_map_coextendScalars (p := ℓ) (m := n + 1 + 1) (N := ℓ ^ (n + 1))
        (pow_dvd_pow ℓ (by omega)) (a := n + 1) (Nat.le_succ _) rfl Rs.ι a₀ hN
        (fun q => have := Rs.injective q; powExact_of_injective _)
    infer_instance
  have hQb : IsIso (DerivedCategory.Plus.Q.map b') := isIso_plus_Q_map_of_quasiIso b₀
  have hU : IsIso ((directImageSectionsDerivedUnit (ZMod (ℓ ^ (n + 1 + 1))) gk).app Ip) :=
    isIso_directImageSectionsDerivedUnit_app _ gk Ip (fun q => Rs.injective q)
  have key := eq_of_two_squares _ _ _ _ _ _ _ _ _ ((Category.assoc _ _ _).trans E1) E2
  -- the termwise model of the transition
  let Γ := etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) (Spec (.of kbar))
  let Γ' := etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ (n + 1))) (Spec (.of kbar))
  let gs := etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) gk
  let gs' := etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ (n + 1))) gk
  let gμ := Γ.mapCochainComplexPlus.map (gs.mapCochainComplexPlus.map μ') ≫
    (directImageSectionsRestrictScalarsComplexIso ρₙ gk Cp).inv
  let Jp := Γ.mapCochainComplexPlus.obj (gs.mapCochainComplexPlus.obj Ip)
  let Mp := Γ'.mapCochainComplexPlus.obj (gs'.mapCochainComplexPlus.obj Cp)
  let rM := ModuleCat.restrictScalars.{u + 1} ρₙ
  let α := (etaleModuleDerivedGlobalSections.{u, 0} _ (Spec (.of kbar))).map
      ((etaleModuleDerivedDirectImage.{u, 0} _ gk).map (DerivedCategory.Plus.Q.map a')) ≫
    inv ((directImageSectionsDerivedUnit (ZMod (ℓ ^ (n + 1 + 1))) gk).app Ip)
  let γ := (directImageSectionsDerivedUnit (ZMod (ℓ ^ (n + 1))) gk).app Cp ≫
    inv ((etaleModuleDerivedGlobalSections.{u, 0} _ (Spec (.of kbar))).map
      ((etaleModuleDerivedDirectImage.{u, 0} _ gk).map (DerivedCategory.Plus.Q.map b')))
  have hV : DerivedCategory.Plus.ι.map
      ((Functor.mapDerivedCategoryPlusQIso rM).inv.app Mp) =
        rM.mapDerivedCategoryFactors.inv.app Mp.obj := by
    have e : DerivedCategory.Plus.ι.mapIso ((Functor.mapDerivedCategoryPlusQIso rM).app Mp) =
        rM.mapDerivedCategoryFactors.app Mp.obj :=
      Iso.ext (Functor.ι_map_mapDerivedCategoryPlusQIso_hom_app rM Mp)
    exact congrArg Iso.inv e
  have hι : DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map tc ≫
      (compactSupportFrobeniusCohomologyRestrictScalarsIso ρₙ f j kbar K').inv) =
      DerivedCategory.Plus.ι.map α ≫ (DerivedCategory.Q.map gμ.hom ≫
        rM.mapDerivedCategoryFactors.inv.app Mp.obj) ≫
        (levelRestrict.{u + 1} ℓ n).map (DerivedCategory.Plus.ι.map γ) := by
    rw [key]
    have hw : DerivedCategory.Plus.ι.map (rM.mapDerivedCategoryPlus.map
        ((directImageSectionsDerivedUnit (ZMod (ℓ ^ (n + 1))) gk).app Cp) ≫
        inv (rM.mapDerivedCategoryPlus.map
        ((etaleModuleDerivedGlobalSections.{u, 0} _ (Spec (.of kbar))).map
          ((etaleModuleDerivedDirectImage.{u, 0} _ gk).map (DerivedCategory.Plus.Q.map b'))))) =
        (levelRestrict.{u + 1} ℓ n).map (DerivedCategory.Plus.ι.map γ) := by
      rw [← Functor.map_inv, ← Functor.map_comp]
      rfl
    exact iota_decomp DerivedCategory.Plus.ι _ _ _ _ _ _ rfl _ hV _ hw
  -- the algebraic statement
  have hQa : IsIso (DerivedCategory.Plus.Q.map a') :=
    isIso_plus_Q_map_of_quasiIso (K := N) (L := Ip) Rs.ι
  have hCinj : ∀ q, Injective (Cp.obj.X q) := fun q => by
    have : (etaleModuleRestrictScalars ρₙ Yb).PreservesMonomorphisms :=
      preservesMonomorphisms_of_preservesLimitsOfShape _
    exact (etaleModuleCoextendScalarsAdj ρₙ Yb).map_injective _ (Rs.injective q)
  have hU' : IsIso ((directImageSectionsDerivedUnit (ZMod (ℓ ^ (n + 1))) gk).app Cp) :=
    isIso_directImageSectionsDerivedUnit_app _ gk Cp hCinj
  have hα : IsIso α := inferInstance
  have hγ : IsIso γ := inferInstance
  have hJs : CochainComplex.IsStrictlyGE Jp.obj a₀ :=
    inferInstanceAs (CochainComplex.IsStrictlyGE ((Γ.mapHomologicalComplex (.up ℤ)).obj
      ((gs.mapHomologicalComplex (.up ℤ)).obj Rs.cocomplex)) a₀)
  have hJ : ∀ q, Stacks.ZModPrimePower.IsPowExact ℓ (n + 1 + 1) (Jp.obj.X q) := fun q => by
    have := Rs.injective q
    have : Injective (gs.obj (Rs.cocomplex.X q)) :=
      Functor.PreservesInjectiveObjects.injective_obj this
    exact (isPowExact_sections_of_injective (gs.obj (Rs.cocomplex.X q))
      (⊤_ (Spec (.of kbar)).Etale)).of_addEquiv
      ((Sheaf.ΓNatIsoSheafSections (Spec (.of kbar)).smallEtaleTopology
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) terminalIsTerminal).app
        (gs.obj (Rs.cocomplex.X q))).symm.toLinearEquiv.toAddEquiv
  have hPJ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj Jp.obj) := by
    obtain ⟨P, a, b, h₁, h₂, h₃, h₄, ⟨e'⟩⟩ := hP
    exact ⟨P, a, b, h₁, h₂, h₃, h₄, ⟨(DerivedCategory.Plus.ι.mapIso (asIso α)).symm ≪≫ e'⟩⟩
  let G := gs ⋙ Γ
  let eS := etaleModuleGlobalSectionsRestrictScalars ρₙ (Spec (.of kbar))
  have hgf : ∀ q, gμ.hom.f q = G.map (μ₀.f q) ≫ eS.inv.app (gs'.obj (Cp.obj.X q)) := fun q => rfl
  have hwg : ∀ q, ((ℓ ^ (n + 1)) • 𝟙 (Jp.obj.X q)) ≫ gμ.hom.f q = 0 := fun q =>
    nsmul_id_comp_map_comp_eq_zero G _ _ _
      ((isTorsionKernel_levelTorsion Yb n (Rs.cocomplex.X q)).nsmul_comp_torsionLift
        (etaleModules_pow_nsmul_id _) (Nat.le_succ _))
  have hg : ∀ q, IsColimit (CokernelCofork.ofπ (gμ.hom.f q) (hwg q)) := fun q => by
    have hk := isTorsionKernel_levelTorsion Yb n (Rs.cocomplex.X q)
    have hkG := hk.map G
    have hX' : (ℓ ^ (n + 1 + 1)) • 𝟙 (G.obj (Rs.cocomplex.X q)) = 0 :=
      Stacks.InverseSystem.pow_nsmul_id_eq_zero _
    have h1 := hkG.isColimitTorsionLift hX' (Nat.le_succ _)
      (Stacks.InverseSystem.powExact_of_isPowExact (hJ q))
    have heq : hkG.torsionLift hX' (Nat.le_succ _) ≫ eS.inv.app (gs'.obj (Cp.obj.X q)) =
        gμ.hom.f q := by
      rw [hgf, ← hk.map_torsionLift (etaleModules_pow_nsmul_id _) (Nat.le_succ _) G hX']
      rfl
    exact isColimitCokernelCoforkOfEqπ heq _
      (isColimitCokernelCoforkCompIso _ h1 (inferInstance : IsIso (eS.inv.app _)))
  have hB := isIso_levelAdjunction_homEquiv_symm_of_flat n Jp.obj a₀ hJ hPJ Mp.obj gμ.hom hwg hg
  have hια : IsIso (DerivedCategory.Plus.ι.map α) := Functor.map_isIso _ α
  have hιγ : IsIso (DerivedCategory.Plus.ι.map γ) := Functor.map_isIso _ γ
  rw [hι]
  exact @isIso_homEquiv_symm_comp _ _ _ _ _ _ (levelAdjunction.{u + 1} ℓ n) _ _ _ _
    (DerivedCategory.Plus.ι.map α)
    (DerivedCategory.Q.map gμ.hom ≫ rM.mapDerivedCategoryFactors.inv.app Mp.obj)
    (DerivedCategory.Plus.ι.map γ) hια hιγ hB

end Main

end Stacks.EtaleCohomology
