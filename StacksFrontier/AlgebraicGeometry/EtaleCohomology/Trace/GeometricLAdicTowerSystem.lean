module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLimitStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsComp
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of the tower `Kₙ = RΓ_c(X_k̄, Fₙ)` and `Hⁱ_c(X_k̄, Fₙ)` with `ℤ_ℓ`-coefficients

The level `n` cohomology `Hⁱ(Kₙ)` of `Stacks.EtaleCohomology.LAdicSheaf.geometricPerfectTower`,
a `ℤ/ℓⁿ⁺¹ℤ`-module viewed as a `ℤ_ℓ`-module, is the `n`-th term
`Hⁱ_c(X_k̄, Fₙ)` of the inverse system whose limit is `Hⁱ_c(X_k̄, F)` (Tag 03UT): computing
`RΓ_c` with `ℤ_ℓ`- or with `ℤ/ℓⁿ⁺¹ℤ`-coefficients gives the same result.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.padicCoefficientComplexLevelIso`: the level `Fₙ`, as a
  complex of sheaves of `ℤ_ℓ`-modules, is the restriction of scalars of `levelComplex`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section SheafEquiv

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of reading sheaves on Mathlib's small étale site with `res_ρ`, read back on the
site of Stacks 021B: the units of the two equivalences. -/
theorem sheafEquiv_inverse_map_sheafEquivRestrictScalarsIso_hom_app {Λ Λ' : Type} [CommRing Λ]
    [CommRing Λ'] (ρ : Λ →+* Λ') (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Λ')) :
    (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.map
        ((sheafEquivRestrictScalarsIso B S hS ρ).hom.app G) =
      (sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ)).map
          ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ')).unitIso.inv.app G) ≫
        (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).unitIso.hom.app
          ((sheafCompose (SmallEtale.topology B S hS)
            (ModuleCat.restrictScalars.{u + 1} ρ)).obj G) := by
  let e := SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)
  let e' := SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ')
  let sc := sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ)
  have h₀ : (sheafEquivRestrictScalarsIso B S hS ρ).hom.app G =
      e.counitIso.inv.app ((etaleModuleRestrictScalars ρ S).obj (e'.functor.obj G)) ≫
        e.functor.map (sc.map (e'.unitIso.inv.app G)) := by
    dsimp only [sheafEquivRestrictScalarsIso]
    rw [CatCommSq.hInv_iso_hom_app]
    simp only [Functor.comp_obj, Equivalence.symm_inverse, Equivalence.symm_functor,
      Equivalence.symm_unitIso, Iso.symm_hom, sheafEquivInverseRestrictScalarsIso, Iso.refl_inv,
      NatTrans.id_app, Equivalence.symm_counitIso, Functor.id_obj, NatIso.cancel_natIso_inv_left,
      e', e, sc]
    exact (eq_whisker (CategoryTheory.Functor.map_id _ _) _).trans (Category.id_comp _)
  have h₁ : e.inverse.map
      (e.counitIso.inv.app ((etaleModuleRestrictScalars ρ S).obj (e'.functor.obj G))) =
      e.unitIso.hom.app (e.inverse.obj ((etaleModuleRestrictScalars ρ S).obj (e'.functor.obj G))) :=
    (e.unit_app_inverse _).symm
  rw [h₀, Functor.map_comp, h₁]
  exact (e.unitIso.hom.naturality (sc.map (e'.unitIso.inv.app G))).symm

/-- The coherence of the comparison of reading sheaves on Mathlib's site, on variables. -/
theorem sheafEquiv_comp_aux {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (cB₀ : X₀ ⟶ X₁) (scu : X₁ ⟶ X₂) (uσ : X₂ ⟶ X₃) (ssu : X₀ ⟶ X₄) (cB : X₄ ⟶ X₂)
    (s₁θ : X₀ ⟶ X₅) (uR : X₄ ⟶ X₅) (uRi : X₅ ⟶ X₄) (s₁θ₁ : X₅ ⟶ X₆) (uΛ : X₄ ⟶ X₆)
    (iff : X₆ ⟶ X₃) (uΛi : X₆ ⟶ X₄)
    (hc : cB₀ ≫ scu = ssu ≫ cB) (h₂ : s₁θ = ssu ≫ uR) (h₁ : s₁θ₁ = uRi ≫ uΛ)
    (hRR : uR ≫ uRi = 𝟙 _) (hΛ : uΛ ≫ uΛi = 𝟙 _) (hf : iff = uΛi ≫ cB ≫ uσ) :
    cB₀ ≫ scu ≫ uσ = s₁θ ≫ s₁θ₁ ≫ iff := by
  rw [h₂, h₁, hf, ← Category.assoc cB₀, hc]
  simp only [Category.assoc]
  rw [reassoc_of% hRR, reassoc_of% hΛ]

/-- **Reading sheaves on Mathlib's small étale site commutes with restriction of scalars
compatibly with composites.** -/
theorem sheafEquivRestrictScalarsIso_comp {Λ R Sr : Type} [CommRing Λ] [CommRing R] [CommRing Sr]
    (ρ₁ : Λ →+* R) (ρ₂ : R →+* Sr) (σ : Λ →+* Sr) (w : σ = ρ₂.comp ρ₁)
    (G : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{u + 1} Sr)) :
    (etaleModuleRestrictScalarsComp ρ₁ ρ₂ σ w S).hom.app
        ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Sr)).functor.obj G) ≫
      (sheafEquivRestrictScalarsIso B S hS σ).hom.app G =
    (etaleModuleRestrictScalars ρ₁ S).map ((sheafEquivRestrictScalarsIso B S hS ρ₂).hom.app G) ≫
      (sheafEquivRestrictScalarsIso B S hS ρ₁).hom.app
        ((sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ₂)).obj G) ≫
      (SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).functor.map
        ((sheafCompose_map (SmallEtale.topology B S hS)
          (ModuleCat.restrictScalarsComp'.{u + 1} ρ₁ ρ₂ σ w).inv).app G) := by
  let e := SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)
  let eR := SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} R)
  let eS := SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Sr)
  let sc₁ := sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ₁)
  let sc₂ := sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} ρ₂)
  let scσ := sheafCompose (SmallEtale.topology B S hS) (ModuleCat.restrictScalars.{u + 1} σ)
  let cB := sheafCompose_map (SmallEtale.topology B S hS)
    (ModuleCat.restrictScalarsComp'.{u + 1} ρ₁ ρ₂ σ w).inv
  apply e.inverse.map_injective
  simp only [Functor.map_comp]
  have h₂ : e.inverse.map ((etaleModuleRestrictScalars ρ₁ S).map
      ((sheafEquivRestrictScalarsIso B S hS ρ₂).hom.app G)) =
      sc₁.map (sc₂.map (eS.unitIso.inv.app G)) ≫ sc₁.map (eR.unitIso.hom.app (sc₂.obj G)) :=
    (congrArg sc₁.map
      (sheafEquiv_inverse_map_sheafEquivRestrictScalarsIso_hom_app B S hS ρ₂ G)).trans
      (sc₁.map_comp _ _)
  have h₁ := sheafEquiv_inverse_map_sheafEquivRestrictScalarsIso_hom_app B S hS ρ₁ (sc₂.obj G)
  have hσ := sheafEquiv_inverse_map_sheafEquivRestrictScalarsIso_hom_app B S hS σ G
  have hc := cB.naturality (eS.unitIso.inv.app G)
  have hRR : sc₁.map (eR.unitIso.hom.app (sc₂.obj G)) ≫
      sc₁.map (eR.unitIso.inv.app (sc₂.obj G)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have hΛ : e.unitIso.hom.app (sc₁.obj (sc₂.obj G)) ≫
      e.unitIso.inv.app (sc₁.obj (sc₂.obj G)) = 𝟙 _ :=
    Iso.hom_inv_id_app _ _
  have hf : e.inverse.map (e.functor.map (cB.app G)) =
      e.unitIso.inv.app (sc₁.obj (sc₂.obj G)) ≫ cB.app G ≫ e.unitIso.hom.app (scσ.obj G) := by
    rw [Equivalence.inv_fun_map]
    rfl
  rw [hσ]
  exact sheafEquiv_comp_aux _ _ _ _ _ _ _ _ _ _ _ _ hc.symm h₂ h₁ hRR hΛ hf

end SheafEquiv

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- The level `Fₙ` as a complex of sheaves of `ℤ_ℓ`-modules on Mathlib's small étale site is the
restriction of scalars of `levelComplex`. -/
def LAdicSheaf.padicCoefficientComplexLevelIso (F : LAdicSheaf B X ℓ) (n : ℕ) :
    (padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n) ≅
      (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) X.1).mapCochainComplexPlus.obj
        (LAdicSheaf.levelComplex B X ℓ F n) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        ((sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (n + 1))).app
          (F.level n)).symm ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) X.1) (ComplexShape.up ℤ) 0).app
          (LAdicSheaf.etaleLevel B X ℓ F n)).symm)

/-- `b⁻¹ ≫ t⁻¹ ≫ a = c ≫ s⁻¹` from `t ≫ b ≫ c = a ≫ s`, on variables. -/
theorem inv_comp_inv_comp_eq_of_eq {C : Type*} [Category* C] {P P' Q M N : C} (a : P ⟶ P')
    (s : P' ≅ Q) (b : P ≅ M) (t : M ≅ N) (c : N ⟶ Q) (h : b.hom ≫ t.hom ≫ c = a ≫ s.hom) :
    t.inv ≫ b.inv ≫ a = c ≫ s.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, Category.assoc, ← h, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_assoc]

/-- The transition identity, on variables. -/
theorem transition_aux {C : Type*} [Category* C] {A B D E G M N : C} (P : A ⟶ B) (m : A ⟶ D)
    (c : D ⟶ B) (t' : D ⟶ M) (b' : M ⟶ N) (a : N ⟶ G) (s' : B ⟶ G) (θ : A ⟶ E) (u : E ⟶ M)
    (Ee : E ⟶ N) (hp : P = m ≫ c) (hc : t' ≫ b' ≫ a = c ≫ s') (hn : m ≫ t' = θ ≫ u)
    (he : Ee = u ≫ b') : P ≫ s' = θ ≫ Ee ≫ a := by
  rw [hp, he, Category.assoc, ← hc, ← Category.assoc m, hn]
  simp only [Category.assoc]

/-- **The transition of the levels, read on Mathlib's site, is the transition of the
`ℤ_[ℓ]`-sheaves `Fₙ`**, up to the comparisons of reading sheaves with restriction of scalars. -/
theorem LAdicSheaf.sheafEquiv_map_padicTransition (F : LAdicSheaf B X ℓ) (n : ℕ) :
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicTransition B X ℓ F n) ≫
      (sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (n + 1))).inv.app
        (F.level n) =
    (sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (n + 1 + 1))).inv.app
        (F.level (n + 1)) ≫
      (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1).map
        (LAdicSheaf.etaleTransition B X ℓ F n) ≫
      (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n)
        (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) X.1).hom.app
        (LAdicSheaf.etaleLevel B X ℓ F n) := by
  have hc := inv_comp_inv_comp_eq_of_eq
    (s := (sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (n + 1))).app
      (F.level n))
    (b := (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1).mapIso
      ((sheafEquivRestrictScalarsIso B X.1 X.property (levelCast ℓ n)).app (F.level n)))
    (t := (sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (n + 1 + 1))).app
      ((sheafCompose (SmallEtale.topology B X.1 X.property)
        (ModuleCat.restrictScalars.{u + 1} (levelCast ℓ n))).obj (F.level n)))
    _ _ (sheafEquivRestrictScalarsIso_comp B X.1 X.property
    (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n) (PadicInt.toZModPow (n + 1))
    (toZModPow_succ_comp ℓ n) (F.level n)).symm
  have hn :=
    (sheafEquivRestrictScalarsIso B X.1 X.property (PadicInt.toZModPow (n + 1 + 1))).inv.naturality
      (F.transition n)
  exact transition_aux _ _ _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _) hc hn (Functor.map_comp _ _ _)

/-- The commutation of `single` with a composite of functors, through a comparison. -/
theorem singleMapHomologicalComplex_inv_comp {V W Z : Type*} [Category* V] [Category* W]
    [Category* Z] [Abelian V] [Abelian W] [Abelian Z] (F₂ : V ⥤ W) (F₁ : W ⥤ Z) (F₃ : V ⥤ Z)
    [F₁.Additive] [F₂.Additive] [F₃.Additive] (τ : F₂ ⋙ F₁ ⟶ F₃) (L : V) :
    (HomologicalComplex.singleMapHomologicalComplex F₁ (ComplexShape.up ℤ) 0).inv.app (F₂.obj L) ≫
        (F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F₂ (ComplexShape.up ℤ) 0).inv.app L) ≫
        (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single V (ComplexShape.up ℤ) 0).obj L) =
      (HomologicalComplex.single Z (ComplexShape.up ℤ) 0).map (τ.app L) ≫
        (HomologicalComplex.singleMapHomologicalComplex F₃ (ComplexShape.up ℤ) 0).inv.app L := by
  refine HomologicalComplex.from_single_hom_ext ?_
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.comp_obj, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Functor.mapHomologicalComplex_map_f, Functor.map_comp, NatTrans.mapHomologicalComplex_app_f,
    Category.assoc, Iso.inv_hom_id_map_assoc, HomologicalComplex.single_map_f_self,
    Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
  exact τ.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).inv

/-- The transition identity for complexes, on variables. -/
theorem single_transition_aux {C' C : Type*} [Category* C'] [Category* C] (Sg : C' ⥤ C)
    {a b d e d' : C'} (x : a ⟶ b) (y : b ⟶ d) (p : a ⟶ e) (q : e ⟶ d') (r : d' ⟶ d)
    {G H M N : C} (mσ : Sg.obj d ⟶ N) (m₁ : Sg.obj e ⟶ G) (rT : G ⟶ M) (rm : M ⟶ H) (cc : H ⟶ N)
    (m₁' : Sg.obj d' ⟶ M) (rTm : G ⟶ H) (ha : x ≫ y = p ≫ q ≫ r) (hb : m₁ ≫ rT = Sg.map q ≫ m₁')
    (hc : m₁' ≫ rm ≫ cc = Sg.map r ≫ mσ) (hr : rTm = rT ≫ rm) :
    Sg.map x ≫ Sg.map y ≫ mσ = Sg.map p ≫ m₁ ≫ rTm ≫ cc := by
  rw [hr, ← Category.assoc, ← Sg.map_comp, ha, Sg.map_comp, Sg.map_comp, Category.assoc,
    Category.assoc, ← hc, ← Category.assoc (Sg.map q), ← hb]
  simp only [Category.assoc]

/-- **The transition of the levels, as complexes.** -/
theorem LAdicSheaf.padicCoefficientComplex_map_padicTransition (F : LAdicSheaf B X ℓ) (n : ℕ) :
    (padicCoefficientComplex B X ℓ).map (LAdicSheaf.padicTransition B X ℓ F n) ≫
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n).hom =
      (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F (n + 1)).hom ≫
        (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1).mapCochainComplexPlus.map
          (LAdicSheaf.levelComplexTransition B X ℓ F n) ≫
        (etaleModuleRestrictScalarsCompPlus (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n)
          (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) X.1
          (LAdicSheaf.levelComplex B X ℓ F n)).hom := by
  have ha := LAdicSheaf.sheafEquiv_map_padicTransition B X ℓ F n
  have hb := (HomologicalComplex.singleMapHomologicalComplex
    (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1)
      (ComplexShape.up ℤ) 0).inv.naturality (LAdicSheaf.etaleTransition B X ℓ F n)
  have hc := singleMapHomologicalComplex_inv_comp (etaleModuleRestrictScalars (levelCast ℓ n) X.1)
    (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1)
    (etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1)) X.1)
    (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n)
      (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) X.1).hom
    (LAdicSheaf.etaleLevel B X ℓ F n)
  have key := single_transition_aux
    (HomologicalComplex.single (EtaleModules.{u, 0} ℤ_[ℓ] X.1) (ComplexShape.up ℤ) 0)
    _ _ _ _ _ _ _ _ _ _ _ _ ha hb.symm hc
    (Functor.map_comp
      ((etaleModuleRestrictScalars (PadicInt.toZModPow (n + 1 + 1)) X.1).mapHomologicalComplex
        (ComplexShape.up ℤ))
      ((HomologicalComplex.single (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1 + 1))) X.1)
        (ComplexShape.up ℤ) 0).map (LAdicSheaf.etaleTransition B X ℓ F n))
      ((HomologicalComplex.singleMapHomologicalComplex
        (etaleModuleRestrictScalars (levelCast ℓ n) X.1) (ComplexShape.up ℤ) 0).inv.app
          (LAdicSheaf.etaleLevel B X ℓ F n)))
  exact ObjectProperty.hom_ext _ key

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`Hⁱ_c(X_k̄, Fₙ)` with `ℤ_ℓ`-coefficients is the level `n` cohomology of the tower.** -/
def LAdicSheaf.geometricLevelCohomologyIso (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).obj (op n) ≅
      (levelCohomologySystem
        (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP) i).obj (op n) :=
  (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).mapIso
      (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n) ≪≫
    (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1)) f j kbar
      (LAdicSheaf.levelComplex B X ℓ F n) i).symm

/-- Transport of an endomorphism along a natural square and an isomorphism, on variables. -/
theorem endo_transport_aux {C : Type*} [Category* C] {A A' B : C} (fA : A ⟶ A) (fA' : A' ⟶ A')
    (x : A ⟶ A') (hx : x ≫ fA' = fA ≫ x) (g : B ≅ A') (fB : B ⟶ B)
    (hg : fB ≫ g.hom = g.hom ≫ fA') : fA ≫ x ≫ g.inv = (x ≫ g.inv) ≫ fB := by
  have h₃ : fA' ≫ g.inv = g.inv ≫ fB := by
    rw [Iso.comp_inv_eq, Category.assoc, hg, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← hx, Category.assoc, h₃, Category.assoc]

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The level isomorphisms carry `π_X^*` to the endomorphisms of the tower.** -/
theorem LAdicSheaf.geometricLevelCohomologyIso_frobenius (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).app (op n) ≫
      (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom =
    (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom ≫
      (levelCohomologyEndoSystem (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP)
        i).app (op n) := by
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i
  have h₁ := (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard).naturality
    (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n).hom
  have h₁' := (H.map_comp _ _).symm.trans ((congrArg H.map h₁).trans (H.map_comp _ _))
  have h₂ := restrictScalars_canonicalCompactSupportFrobeniusGroup (PadicInt.toZModPow (n + 1)) f j
    kbar p q hcard (LAdicSheaf.levelComplex B X ℓ F n) i
  exact endo_transport_aux _ _ _ h₁' _ _ h₂

/-- A composite of three, through two functors. -/
theorem map_map_comp₃ {C D E : Type*} [Category* C] [Category* D] [Category* E] (G : C ⥤ D)
    (H : D ⥤ E) {X₀ X₁ X₂ X₃ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) :
    H.map (G.map ((a ≫ b) ≫ c)) = H.map (G.map a) ≫ H.map (G.map b) ≫ H.map (G.map c) := by
  simp only [Functor.map_comp, Category.assoc]

/-- A composite of two, through two functors. -/
theorem map_map_comp₂ {C D E : Type*} [Category* C] [Category* D] [Category* E] (G : C ⥤ D)
    (H : D ⥤ E) {X₀ X₁ X₂ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) :
    H.map (G.map (a ≫ b)) = H.map (G.map a) ≫ H.map (G.map b) := by
  simp only [Functor.map_comp]

/-- The square of the level isomorphisms on cohomology, on variables. -/
theorem level_square_aux {D D' A A' : Type*} [Category* D] [Category* D'] [Category* A]
    [Category* A'] (H : D ⥤ A) (G : A' ⥤ A) (Fn : D' ⥤ D) (HR : D' ⥤ A') {X₀ X₃ : D} {Y₀ Y₁ : D'}
    {Z₃ : A} {W₁ : A'}
    (L : X₀ ⟶ X₃) (M : X₀ ⟶ Fn.obj Y₀) (t : Y₀ ⟶ Y₁) (d : Fn.obj Y₁ ⟶ X₃)
    (r₁ : H.obj (Fn.obj Y₀) ⟶ G.obj (HR.obj Y₀))
    (r₁' : H.obj (Fn.obj Y₁) ⟶ G.obj (HR.obj Y₁)) (rσ : H.obj X₃ ⟶ Z₃) (r₂ : HR.obj Y₁ ⟶ W₁)
    (c : G.obj W₁ ⟶ Z₃)
    (n1 : r₁ ≫ G.map (HR.map t) = H.map (Fn.map t) ≫ r₁') (n2 : H.map d ≫ rσ = r₁' ≫ G.map r₂ ≫ c)
    (n3 : M ≫ Fn.map t ≫ d = L) :
    H.map L ≫ rσ = H.map M ≫ r₁ ≫ G.map (HR.map t ≫ r₂) ≫ c := by
  rw [← n3, G.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, n2]

/-- The composite identity behind the square, on variables. -/
theorem level_square_n3 {C D : Type*} [Category* C] [Category* D] (ι' : C ⥤ D) {A B E E' G T : C}
    (p : A ⟶ B) (l : B ⟶ E') (l' : A ⟶ G) (q : G ⟶ E') (s : E' ⟶ T) (θ₁ : G ⟶ E)
    (rest : ι'.obj E ⟶ ι'.obj T) (hS : p ≫ l = l' ≫ q)
    (hD : ι'.map (q ≫ s) = ι'.map θ₁ ≫ rest) :
    ι'.map (l' ≫ θ₁) ≫ rest = ι'.map ((p ≫ l) ≫ s) := by
  rw [hS, Category.assoc, ι'.map_comp, ι'.map_comp, Category.assoc, ← hD, ι'.map_comp]

section Naturality

variable {k : Type u} [Field k] [Fintype k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  {Λ R Sr : Type} [CommRing Λ] [CommRing R] [CommRing Sr]
  (ρ₁ : Λ →+* R) (ρ₂ : R →+* Sr) (σ : Λ →+* Sr) (w : σ = ρ₂.comp ρ₁)

/-- The comparison of `RΓ_c` along a composite, rearranged, on variables. -/
theorem comp_restrict_rearrange {C : Type*} [Category* C] {A B D E E' T : C}
    (L : A ⟶ T) (x : A ⟶ B) (y : B ⟶ T) (θ : A ⟶ D) (Fm : D ⟶ E') (Dd : E' ⟶ T) (r : D ⟶ E)
    (q : E ⟶ E') (θ' : B ⟶ E) (hL : L = x ≫ y) (hFm : Fm = r ≫ q)
    (hc : θ' ≫ q ≫ Dd = y) (hn : x ≫ θ' = θ ≫ r) :
    L = θ ≫ Fm ≫ Dd := by
  rw [hL, hFm, ← hc, ← Category.assoc x, hn]
  simp only [Category.assoc]

/-- A naturality square of isomorphisms, inverted and mapped, on variables. -/
theorem map_inv_naturality {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X X' Y Y' : C}
    (a : X ≅ X') (b : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : f ≫ b.hom = a.hom ≫ g) :
    F.map g ≫ F.map b.inv = F.map a.inv ≫ F.map f := by
  rw [← F.map_comp, ← F.map_comp]
  congr 1
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [Fintype k] in
/-- **`RΓ_c(X_k̄, t)` for `t : K ⟶ res_ρ₂ K'`, along a composite**: the map induced on `RΓ_c` with
`Λ`-coefficients by `res_ρ₁ t`, followed by the comparison along `σ`, is the comparison along
`ρ₁` followed by `res_ρ₁` of the map induced by `t` on `RΓ_c` with `R`-coefficients and the
comparison along `ρ₂`. -/
theorem compactSupportFrobeniusFunctor_map_restrictScalars_comp [Finite k]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} R Y))
    (K' : CochainComplex.Plus (EtaleModules.{u, 0} Sr Y))
    (tc : K ⟶ (etaleModuleRestrictScalars ρ₂ Y).mapCochainComplexPlus.obj K') :
    DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        ((etaleModuleRestrictScalars ρ₁ Y).mapCochainComplexPlus.map tc ≫
          (etaleModuleRestrictScalarsCompPlus ρ₁ ρ₂ σ w Y K').hom) ≫
      (compactSupportFrobeniusCohomologyRestrictScalarsIso σ f j kbar K').inv) =
    DerivedCategory.Plus.ι.map
        (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₁ f j kbar K).inv ≫
      (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ((compactSupportFrobeniusFunctor.{u, 0} R f j kbar).map tc ≫
          (compactSupportFrobeniusCohomologyRestrictScalarsIso ρ₂ f j kbar K').inv)) ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{0, u + 1} ρ₁ ρ₂ σ w).hom.app
        (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Sr f j kbar K')) := by
  have := Fintype.ofFinite k
  have hc := compactSupportFrobeniusCohomologyRestrictScalarsIso_comp ρ₁ ρ₂ σ w f j kbar K'
  have hn := compactSupportFrobeniusCohomologyRestrictScalarsIso_hom_naturality (ρ := ρ₁) (f := f)
    (j := j) (kbar := kbar) tc
  have hn' := map_inv_naturality DerivedCategory.Plus.ι _ _ _ _ hn
  rw [ι_map_mapDerivedCategoryPlus_map] at hn'
  exact comp_restrict_rearrange _ _ _ _ _ _ _ _ _
    (by
      rw [Functor.map_comp]
      exact (congrArg (fun z => DerivedCategory.Plus.ι.map z) (Category.assoc _ _ _)).trans
        (DerivedCategory.Plus.ι.map_comp _ _))
    ((congrArg (fun z => (ModuleCat.restrictScalars.{u + 1} ρ₁).mapDerivedCategory.map z)
      (DerivedCategory.Plus.ι.map_comp _ _)).trans (Functor.map_comp _ _ _)) hc hn'

end Naturality

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The level isomorphisms are natural in `n`**: they carry the transitions of the inverse system
`n ↦ Hⁱ_c(X_k̄, Fₙ)` to those of the cohomology of the tower. -/
theorem LAdicSheaf.geometricLevelCohomologyIso_naturality (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).map
        (homOfLE (n.le_add_right 1)).op ≫
      (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom =
    (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i (n + 1)).hom ≫
      (levelCohomologySystem
        (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP) i).map
          (homOfLE (n.le_add_right 1)).op := by
  have hS := congrArg (fun z => (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar).map z)
    (LAdicSheaf.padicCoefficientComplex_map_padicTransition B X ℓ F n)
  simp only [Functor.map_comp] at hS
  have hD := compactSupportFrobeniusFunctor_map_restrictScalars_comp f j kbar
    (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n) (PadicInt.toZModPow (n + 1))
    (toZModPow_succ_comp ℓ n) (LAdicSheaf.levelComplex B X ℓ F (n + 1))
    (LAdicSheaf.levelComplex B X ℓ F n)
    (LAdicSheaf.levelComplexTransition B X ℓ F n)
  rw [Functor.map_comp] at hD
  have n3 := level_square_n3 DerivedCategory.Plus.ι _ _ _ _ _ _ _ hS hD
  have n1 := ((restrictHomologyIsoOfHom.{u + 1} (PadicInt.toZModPow (n + 1 + 1)) i).hom.naturality
    ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).transition n)).symm
  have n2 := restrictHomologyIsoOfHom_comp.{u + 1} (PadicInt.toZModPow (n + 1 + 1)) (levelCast ℓ n)
    (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n) i
    (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j
      kbar (LAdicSheaf.levelComplex B X ℓ F n)))
  have key := level_square_aux (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i)
    (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1 + 1)))
    (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1 + 1))).mapDerivedCategory
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) i)
    _ _ _ _ _ _ _ _ _ n1 n2 n3
  rw [LAdicSheaf.geometricCompactlySupportedCohomologySystem_map_succ,
    levelCohomologySystem_map_succ]
  ext x
  exact congrArg (fun φ => φ.hom x) (((eq_whisker (map_map_comp₃ _ _ _ _ _) _).symm.trans
    key).trans (eq_whisker (map_map_comp₂ _ _ _ _) _))

/-- **The inverse system `n ↦ Hⁱ_c(X_k̄, Fₙ)` is the cohomology system of the tower
`Kₙ = RΓ_c(X_k̄, Fₙ)`**, for an ℓ-adic sheaf with flat levels whose `Kₙ` are perfect. -/
def LAdicSheaf.geometricLevelCohomologySystemIso (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i ≅
      levelCohomologySystem (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP) i :=
  haveI : ∀ n : ℕᵒᵖ, IsIso ((NatTrans.ofOpSequence
      (fun n => (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom)
      (LAdicSheaf.geometricLevelCohomologyIso_naturality B X ℓ f j kbar p q hcard F hF hP i)).app
        n) :=
    fun n => by
      rw [NatTrans.ofOpSequence_app]
      infer_instance
  haveI : IsIso (NatTrans.ofOpSequence
      (fun n => (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom)
      (LAdicSheaf.geometricLevelCohomologyIso_naturality B X ℓ f j kbar p q hcard F hF hP i)) :=
    NatIso.isIso_of_isIso_app _
  asIso (NatTrans.ofOpSequence
    (fun n => (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard F hF hP i n).hom)
    (LAdicSheaf.geometricLevelCohomologyIso_naturality B X ℓ f j kbar p q hcard F hF hP i))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The system isomorphism carries `π_X^*` to the endomorphisms of the tower. -/
theorem LAdicSheaf.geometricLevelCohomologySystemIso_frobenius (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard) ≫
      (LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i).hom =
    (LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i).hom ≫
      levelCohomologyEndoSystem
        (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP) i := by
  ext ⟨n⟩ : 2
  exact LAdicSheaf.geometricLevelCohomologyIso_frobenius B X ℓ f j kbar p q hcard F hF hP i n

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is finite-dimensional** for an ℓ-adic sheaf with flat levels whose
`RΓ_c(X_k̄, Fₙ)` are perfect. -/
@[sga "4½ Rapport 4.11" "partial"]
theorem LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_flat
    (F : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (i : ℤ) :
    Module.Finite ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
  LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_iso B X ℓ f j kbar F _ i
    (LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes in all but finitely many degrees** for an ℓ-adic sheaf with
flat levels whose `RΓ_c(X_k̄, Fₙ)` are perfect. -/
theorem LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_flat
    (F : LAdicSheaf B X ℓ) (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) :
    {i : ℤ | Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)}.Finite :=
  LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_iso B X ℓ f j kbar
    F _
    (fun i => LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The alternating trace of `π_X^*` on `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is the ℓ-adic trace of the tower
`Kₙ = RΓ_c(X_k̄, Fₙ)`**, for an ℓ-adic sheaf with flat levels whose `Kₙ` are perfect. -/
theorem LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedFrobenius_of_flat
    (F : LAdicSheaf B X ℓ) (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
            (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).hom =
      (padicTrace (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP) : ℚ_[ℓ]) :=
  LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedCohomology_of_iso B X ℓ f j kbar
    F _ _
    (fun i => LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i)
    (fun i =>
      LAdicSheaf.geometricLevelCohomologySystemIso_frobenius B X ℓ f j kbar p q hcard F hF hP i)

end Stacks.EtaleCohomology
