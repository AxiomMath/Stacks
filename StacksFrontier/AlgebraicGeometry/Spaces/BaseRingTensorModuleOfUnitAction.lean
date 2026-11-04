module

public import StacksFrontier.Algebra.Category.ModuleCat.LeftAdjointOfUnitAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback

/-!
# A left adjoint `A`-modules ⥤ `𝒪_X`-modules carrying `A` to `𝒪_X` is `𝒪_X ⊗_A -`

Let `X` be an algebraic space, `A` a commutative ring and `Φ : ModuleCat A ⥤ Mod(𝒪_X)` an additive
functor with a right adjoint, together with an isomorphism `θ : Φ(A) ≅ 𝒪_X`. Multiplication by
`a ∈ A` on `A` induces through `Φ` and `θ` an endomorphism of `𝒪_X`, which is multiplication by a
global function; this is a ring map `φ : A →+* Γ(X, 𝒪_X)`
(`Stacks.Cohomology.SiteModules.unitActionGlobalFunctionsHom`, read on the model of the small
étale site). Then `Φ` is the module `𝒪_X ⊗_A -` of Stacks 0D3F for this base-ring datum
(`AlgebraicGeometry.Space.baseRingTensorModuleIsoOfUnitIso`): both right adjoints are global
sections, identified with morphisms out of `𝒪_X`, with the same action of `A`.

## Main definitions

* `Stacks.Cohomology.SiteModules.unitActionGlobalFunctionsHom`: the ring map
  `A →+* Γ(C, O)` given by the action of `A` on `Φ(A) ≅ 𝒪`.
* `AlgebraicGeometry.Space.baseRingTensorModuleIsoOfUnitIso`: `𝒪_X ⊗_A - ≅ Φ`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] {O : Sheaf J CommRingCat.{u}}
  {A : Type u} [CommRing A] (Φ : ModuleCat.{u} A ⥤ SheafOfModules.{u} (ringSheafOfSite O))
  [Φ.Additive] (θ : Φ.obj (ModuleCat.of A A) ≅ SheafOfModules.unit (ringSheafOfSite O))

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- A morphism out of the free module of rank one is multiplication of its value on `1`. -/
theorem unit_hom_val_app_eq_mul {M : SheafOfModules.{u} (ringSheafOfSite O)}
    (v : SheafOfModules.unit (ringSheafOfSite O) ⟶ M) (W : Cᵒᵖ) (c : O.obj.obj W) :
    v.val.app W c = c • v.val.app W (1 : O.obj.obj W) := by
  have h : v.val.app W (c • (1 : O.obj.obj W)) = c • v.val.app W (1 : O.obj.obj W) :=
    map_smul _ _ _
  rwa [smul_eq_mul, mul_one] at h

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] [Φ.Additive] in
/-- Multiplication by `1` on `A` induces the identity of `𝒪`. -/
theorem moduleCatUnitAction_one :
    Adjunction.moduleCatUnitAction θ (1 : A) = 𝟙 _ := by
  rw [Adjunction.moduleCatUnitAction, one_smul, Φ.map_id, Category.id_comp, Iso.inv_hom_id]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] [Φ.Additive] in
/-- The endomorphism of `𝒪` induced by multiplication by `a * b` is the one induced by `b`
followed by the one induced by `a`. -/
theorem moduleCatUnitAction_mul (a b : A) :
    Adjunction.moduleCatUnitAction θ (a * b) =
      Adjunction.moduleCatUnitAction θ b ≫ Adjunction.moduleCatUnitAction θ a := by
  have h : (a * b) • 𝟙 (ModuleCat.of A A) = (b • 𝟙 (ModuleCat.of A A)) ≫ (a • 𝟙 _) := by
    rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp, smul_smul]
  simp only [Adjunction.moduleCatUnitAction, h, Φ.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- The endomorphism of `𝒪` induced by multiplication by `a + b` is the sum of those induced by
`a` and by `b`. -/
theorem moduleCatUnitAction_add (a b : A) :
    Adjunction.moduleCatUnitAction θ (a + b) =
      Adjunction.moduleCatUnitAction θ a + Adjunction.moduleCatUnitAction θ b := by
  simp only [Adjunction.moduleCatUnitAction, add_smul, Φ.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Multiplication by `0` on `A` induces the zero endomorphism of `𝒪`. -/
theorem moduleCatUnitAction_zero :
    Adjunction.moduleCatUnitAction θ (0 : A) = 0 := by
  simp only [Adjunction.moduleCatUnitAction, zero_smul, Φ.map_zero, Limits.zero_comp,
    Limits.comp_zero]

/-- The value on `1` of an endomorphism of the free module of rank one. -/
def unitEndValue (v : SheafOfModules.unit (ringSheafOfSite O) ⟶ SheafOfModules.unit _)
    (W : Cᵒᵖ) : O.obj.obj W :=
  v.val.app W (1 : O.obj.obj W)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- The value on `1` of a composite of endomorphisms of the free module of rank one is the
product of their values on `1`. -/
theorem unitEndValue_comp (v w : SheafOfModules.unit (ringSheafOfSite O) ⟶ SheafOfModules.unit _)
    (W : Cᵒᵖ) : unitEndValue (v ≫ w) W = unitEndValue v W * unitEndValue w W :=
  unit_hom_val_app_eq_mul w W (unitEndValue v W)

/-- **The action of `A` on `Φ(A) ≅ 𝒪` is multiplication by global functions.** The global
function attached to `a` is the value on `1` of the endomorphism of `𝒪` induced by
multiplication by `a`. -/
def unitActionGlobalFunctionsHom : A →+* GlobalFunctionRing O where
  toFun a := ⟨((SheafOfModules.unitHomEquiv _) (Adjunction.moduleCatUnitAction θ a)).1,
    ((SheafOfModules.unitHomEquiv _) (Adjunction.moduleCatUnitAction θ a)).2⟩
  map_one' := Subtype.ext (funext fun W => by
    change unitEndValue (Adjunction.moduleCatUnitAction θ (1 : A)) W = (1 : O.obj.obj W)
    rw [moduleCatUnitAction_one]
    rfl)
  map_mul' a b := Subtype.ext (funext fun W => by
    change unitEndValue (Adjunction.moduleCatUnitAction θ (a * b)) W =
      unitEndValue (Adjunction.moduleCatUnitAction θ a) W *
        unitEndValue (Adjunction.moduleCatUnitAction θ b) W
    rw [moduleCatUnitAction_mul, unitEndValue_comp]
    exact mul_comm _ _)
  map_zero' := Subtype.ext (funext fun W => by
    change unitEndValue (Adjunction.moduleCatUnitAction θ (0 : A)) W = (0 : O.obj.obj W)
    rw [moduleCatUnitAction_zero]
    rfl)
  map_add' a b := Subtype.ext (funext fun W => by
    change unitEndValue (Adjunction.moduleCatUnitAction θ (a + b)) W =
      unitEndValue (Adjunction.moduleCatUnitAction θ a) W +
        unitEndValue (Adjunction.moduleCatUnitAction θ b) W
    rw [moduleCatUnitAction_add]
    rfl)

omit [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Multiplication by the global function attached to `a` is the endomorphism of `𝒪` induced by
multiplication by `a`. -/
theorem unitHomEquiv_symm_unitSection_unitActionGlobalFunctionsHom (a : A) :
    (SheafOfModules.unitHomEquiv _).symm (unitSection (unitActionGlobalFunctionsHom Φ θ a)) =
      Adjunction.moduleCatUnitAction θ a :=
  (SheafOfModules.unitHomEquiv _).symm_apply_apply _

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.SiteModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  {A : Type u} [CommRing A]

/-- **The inverse of `AlgebraicGeometry.Space.modelSectionsHomEquiv` is linear for any base-ring
datum**: precomposing with an endomorphism `w` of `𝒪_X` that is multiplication by `φ a` on the
model is multiplication by `a`. -/
theorem modelSectionsHomEquiv_symm_comp_of_map (φ : A →+* modelGlobalFunctions B S hS X)
    (F : Modules.{u, u} B S hS X.1 X.2) (a : A) (w : unitModule B S hS X.2 ⟶ unitModule B S hS X.2)
    (hw : (smallEtaleModelModulesEquiv B S hS X).functor.map w =
      (SheafOfModules.unitHomEquiv _).symm (unitSection (φ a)))
    (v : unitModule B S hS X.2 ⟶ F) :
    (modelSectionsHomEquiv B S hS X φ F).symm (w ≫ v) =
      a • (modelSectionsHomEquiv B S hS X φ F).symm v := by
  refine Eq.trans ?_ (ModuleCat.restrictScalars.smul_def φ
    (M := (globalSectionsFunctor (ringSheafOfSite.{u, u, u}
      (smallEtaleModelStructureSheaf B S hS X))).obj
        ((smallEtaleModelModulesEquiv B S hS X).functor.obj F)) a _).symm
  refine (SheafOfModules.unitHomEquiv
    ((smallEtaleModelModulesEquiv B S hS X).functor.obj F)).symm.injective ?_
  refine Eq.trans ?_ (unitHomEquiv_symm_smul
    (R := ringSheafOfSite.{u, u, u} (smallEtaleModelStructureSheaf B S hS X))
    ((smallEtaleModelModulesEquiv B S hS X).functor.obj F) _ _).symm
  have h := fun u : unitModule B S hS X.2 ⟶ F => Equiv.symm_apply_apply (SheafOfModules.unitHomEquiv
      ((smallEtaleModelModulesEquiv B S hS X).functor.obj F))
      ((smallEtaleModelModulesEquiv B S hS X).functor.map u)
  exact ((h (w ≫ v)).trans ((smallEtaleModelModulesEquiv B S hS X).functor.map_comp _ _)).trans
    (congrArg₂ (· ≫ ·) hw (h v).symm)

variable {B S hS X} (Φ : ModuleCat.{u} A ⥤ Modules.{u, u} B S hS X.1 X.2) [Φ.Additive]
  (θ : Φ.obj (ModuleCat.of A A) ≅ unitModule B S hS X.2)

/-- The restriction of modules to the model of the small étale site is additive. -/
instance smallEtaleModelModulesEquiv_functor_additive :
    (smallEtaleModelModulesEquiv B S hS X).functor.Additive :=
  Stacks.SheafOfModules.pushforward_additive _

/-- `Φ` followed by the restriction to the model of the small étale site. -/
def modelModulesFunctorOf : ModuleCat.{u} A ⥤ SheafOfModules.{u}
    (Stacks.Cohomology.SiteModules.ringSheafOfSite.{u, u, u}
      (smallEtaleModelStructureSheaf B S hS X)) :=
  Φ ⋙ (smallEtaleModelModulesEquiv B S hS X).functor

/-- `Φ` followed by the restriction to the model of the small étale site is additive. -/
instance additive_modelModulesFunctorOf : (modelModulesFunctorOf Φ).Additive where
  map_add {_ _ f g} := by
    change (smallEtaleModelModulesEquiv B S hS X).functor.map (Φ.map (f + g)) = _
    rw [Φ.map_add, Functor.map_add]
    rfl

/-- The isomorphism `θ : Φ(A) ≅ 𝒪_X` read on the model of the small étale site. -/
def unitIsoOnModel :
    (modelModulesFunctorOf Φ).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit (ringSheafOfSite.{u, u, u} (smallEtaleModelStructureSheaf B S hS X)) :=
  (smallEtaleModelModulesEquiv B S hS X).functor.mapIso θ

/-- The base-ring datum `A →+* Γ(X, 𝒪_X)` given by the action of `A` on `Φ(A) ≅ 𝒪_X`. -/
def unitActionBaseRingHom : A →+* modelGlobalFunctions B S hS X :=
  unitActionGlobalFunctionsHom (O := smallEtaleModelStructureSheaf B S hS X)
    (modelModulesFunctorOf Φ) (unitIsoOnModel Φ θ)

/-- Read on the model of the small étale site, the endomorphism of `𝒪_X` induced by
multiplication by `a` is multiplication by the global function `unitActionBaseRingHom Φ θ a`. -/
theorem map_moduleCatUnitAction (a : A) :
    (smallEtaleModelModulesEquiv B S hS X).functor.map (Adjunction.moduleCatUnitAction θ a) =
      (SheafOfModules.unitHomEquiv (SheafOfModules.unit (ringSheafOfSite.{u, u, u}
        (smallEtaleModelStructureSheaf B S hS X)))).symm
          (unitSection (unitActionBaseRingHom Φ θ a)) := by
  refine Eq.trans ?_ (unitHomEquiv_symm_unitSection_unitActionGlobalFunctionsHom
    (O := smallEtaleModelStructureSheaf B S hS X) (modelModulesFunctorOf Φ)
    (unitIsoOnModel Φ θ) a).symm
  simp only [Adjunction.moduleCatUnitAction, Functor.map_comp, unitIsoOnModel,
    Functor.mapIso_inv, Functor.mapIso_hom]
  rfl

/-- **A left adjoint `Φ : ModuleCat A ⥤ Mod(𝒪_X)` with `Φ(A) ≅ 𝒪_X` is `𝒪_X ⊗_A -`** for the
base-ring datum given by the action of `A` on `Φ(A)`: both right adjoints are global sections,
identified with morphisms out of `𝒪_X` compatibly with the action of `A`. -/
def baseRingTensorModuleIsoOfUnitIso {G : Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u} A}
    (adj : Φ ⊣ G) :
    baseRingTensorModule B S hS X (unitActionBaseRingHom Φ θ) ≅ Φ :=
  ModuleCat.leftAdjointIsoOfSectionsHomEquiv (Adjunction.moduleCatUnitAction θ)
    (modelSectionsHomEquiv B S hS X (unitActionBaseRingHom Φ θ))
    (adj.moduleCatSectionsHomEquiv θ)
    (fun f x => modelSectionsHomEquiv_naturality B S hS X _ f x)
    (fun f x => adj.moduleCatSectionsHomEquiv_naturality θ f x)
    (fun F x y => modelSectionsHomEquiv_add B S hS X _ F x y)
    (fun F x y => adj.moduleCatSectionsHomEquiv_add θ F x y)
    (fun F a x => by
      refine (modelSectionsHomEquiv B S hS X (unitActionBaseRingHom Φ θ) F).symm.injective ?_
      rw [Equiv.symm_apply_apply, modelSectionsHomEquiv_symm_comp_of_map B S hS X
        (unitActionBaseRingHom Φ θ) F a _ (map_moduleCatUnitAction Φ θ a), Equiv.symm_apply_apply])
    (fun F a x => adj.moduleCatSectionsHomEquiv_smul θ F a x)
    (baseRingTensorModuleAdjunction B S hS X _) adj

end AlgebraicGeometry.Space

end
