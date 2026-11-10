module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules

/-!
# Tensoring a sheaf of modules with a module

Let `Λ` be a commutative ring and `J` a Grothendieck topology on a category `C`. For a sheaf
`S` of `Λ`-modules and a `Λ`-module `M`, the sheaf `S ⊗_Λ M` is the sheafification of the
presheaf `U ↦ M ⊗_Λ S(U)`; it is the tensor product of `S` with the constant sheaf `M̲`. This
file constructs it as a bifunctor, additive and `Λ`-linear in each variable.

## Main definitions

* `Stacks.ConstantModuleTensor.presheafTensor`: `(P, M) ↦ (U ↦ M ⊗_Λ P(U))` on presheaves.
* `Stacks.ConstantModuleTensor.sheafTensor`: its sheafification, `(S, M) ↦ S ⊗_Λ M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v₁ u₁

namespace Stacks.ConstantModuleTensor

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]

/-- The presheaf-level bifunctor `(P, M) ↦ (U ↦ M ⊗_Λ P(U))`. -/
@[simps]
def presheafTensor :
    (Cᵒᵖ ⥤ ModuleCat.{w} Λ) ⥤ ModuleCat.{w} Λ ⥤ (Cᵒᵖ ⥤ ModuleCat.{w} Λ) where
  obj P :=
    { obj M := P ⋙ tensorLeft M
      map g :=
        { app U := g ▷ P.obj U
          naturality _ _ f := by dsimp; exact whisker_exchange _ _ }
      map_id M := by ext U : 2; simp
      map_comp f g := by ext U : 2; simp }
  map a :=
    { app M := { app U := M ◁ a.app U, naturality _ _ φ := by simp [← whiskerLeft_comp] }
      naturality _ _ g := by ext U : 2; simp [whisker_exchange] }
  map_id P := NatTrans.ext <| funext fun M => NatTrans.ext <| funext fun U => by simp
  map_comp a b := NatTrans.ext <| funext fun M => NatTrans.ext <| funext fun U => by simp

variable [HasSheafify J (ModuleCat.{w} Λ)]

/-- **The tensor product `S ⊗_Λ M` of a sheaf of `Λ`-modules with a `Λ`-module**: the
sheafification of `U ↦ M ⊗_Λ S(U)`. -/
@[simps]
def sheafTensor :
    Sheaf J (ModuleCat.{w} Λ) ⥤ ModuleCat.{w} Λ ⥤ Sheaf J (ModuleCat.{w} Λ) where
  obj S := (presheafTensor Λ).obj S.obj ⋙ presheafToSheaf J _
  map s := Functor.whiskerRight ((presheafTensor Λ).map s.hom) (presheafToSheaf J _)
  map_id S := by ext M : 2; simp
  map_comp a b := by ext M : 2; simp

/-- For a fixed presheaf `P`, the functor `M ↦ (U ↦ M ⊗_Λ P(U))` is additive. -/
instance additive_obj_presheafTensor (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    ((presheafTensor Λ).obj P).Additive where
  map_add {M M'} a b := by
    ext U : 2
    simp [NatTrans.app_add, MonoidalPreadditive.add_whiskerRight]
    rfl

/-- For a fixed presheaf `P`, the functor `M ↦ (U ↦ M ⊗_Λ P(U))` is `Λ`-linear. -/
instance linear_obj_presheafTensor (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    ((presheafTensor Λ).obj P).Linear Λ where
  map_smul {M M'} a r := by
    ext U : 2
    simp [NatTrans.app_smul, MonoidalLinear.smul_whiskerRight]
    rfl

/-- The bifunctor `presheafTensor` is additive in the presheaf variable. -/
instance additive_presheafTensor : (presheafTensor (C := C) Λ).Additive where
  map_add {P P'} a b := NatTrans.ext <| funext fun M => NatTrans.ext <| funext fun U => by
    simp [NatTrans.app_add, MonoidalPreadditive.whiskerLeft_add]
    rfl

/-- The bifunctor `presheafTensor` is `Λ`-linear in the presheaf variable. -/
theorem presheafTensor_map_smul {P P' : Cᵒᵖ ⥤ ModuleCat.{w} Λ} (r : Λ) (a : P ⟶ P') :
    (presheafTensor (C := C) Λ).map (r • a) = r • (presheafTensor (C := C) Λ).map a :=
  NatTrans.ext <| funext fun M => NatTrans.ext <| funext fun U => by
    simp [NatTrans.app_smul, MonoidalLinear.whiskerLeft_smul]
    rfl

/-- For a fixed sheaf `S`, the functor `M ↦ S ⊗_Λ M` is additive. -/
instance additive_obj_sheafTensor (S : Sheaf J (ModuleCat.{w} Λ)) :
    ((sheafTensor J Λ).obj S).Additive :=
  inferInstanceAs (((presheafTensor Λ).obj S.obj ⋙ presheafToSheaf J _).Additive)

/-- For a fixed sheaf `S`, the functor `M ↦ S ⊗_Λ M` is `Λ`-linear. -/
instance linear_obj_sheafTensor (S : Sheaf J (ModuleCat.{w} Λ)) :
    ((sheafTensor J Λ).obj S).Linear Λ :=
  inferInstanceAs (((presheafTensor Λ).obj S.obj ⋙ presheafToSheaf J _).Linear Λ)

/-- The bifunctor `sheafTensor` is additive in the sheaf variable. -/
instance additive_sheafTensor : (sheafTensor J Λ).Additive where
  map_add {S S'} a b := NatTrans.ext <| funext fun M => by
    change (presheafToSheaf J _).map (((presheafTensor Λ).map (a.hom + b.hom)).app M) =
      (presheafToSheaf J _).map (((presheafTensor Λ).map a.hom).app M) +
        (presheafToSheaf J _).map (((presheafTensor Λ).map b.hom).app M)
    rw [Functor.map_add, NatTrans.app_add, Functor.map_add]

/-- The bifunctor `sheafTensor` is `Λ`-linear in the sheaf variable. -/
theorem sheafTensor_map_smul {S S' : Sheaf J (ModuleCat.{w} Λ)} (r : Λ) (a : S ⟶ S') :
    (sheafTensor J Λ).map (r • a) = r • (sheafTensor J Λ).map a := by
  refine NatTrans.ext <| funext fun M => ?_
  change (presheafToSheaf J _).map (((presheafTensor Λ).map (r • a.hom)).app M) =
    r • (presheafToSheaf J _).map (((presheafTensor Λ).map a.hom).app M)
  rw [presheafTensor_map_smul, NatTrans.app_smul, Functor.map_smul]


/-- Tensoring with a fixed module is composing with `M ⊗ -` and sheafifying. -/
def flipObjIso (M : ModuleCat.{w} Λ) :
    (sheafTensor J Λ).flip.obj M ≅ Sheaf.composeAndSheafify J (tensorLeft M) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    simp only [Functor.flip_obj_obj, Functor.flip_obj_map, Iso.refl_hom]
    rfl)

/-- `- ⊗_Λ M` is left adjoint to the sheaf `Hom_Λ(M, -)`. -/
def flipObjAdjunction (M : ModuleCat.{w} Λ) :
    (sheafTensor J Λ).flip.obj M ⊣ sheafCompose J (ihom M) :=
  (Sheaf.adjunction J (ihom.adjunction M)).ofNatIsoLeft (flipObjIso J Λ M).symm

/-- The functor `- ⊗_Λ M` on sheaves of `Λ`-modules is a left adjoint. -/
instance isLeftAdjoint_flipObj (M : ModuleCat.{w} Λ) :
    ((sheafTensor J Λ).flip.obj M).IsLeftAdjoint :=
  (flipObjAdjunction J Λ M).isLeftAdjoint

/-- For a flat `Λ`-module `M`, the functor `- ⊗_Λ M` on sheaves of `Λ`-modules preserves finite
limits. -/
instance preservesFiniteLimits_flipObj (M : ModuleCat.{w} Λ) [Module.Flat Λ M] :
    PreservesFiniteLimits ((sheafTensor J Λ).flip.obj M) := by
  have hW : PreservesFiniteLimits
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{w} Λ) (ModuleCat.{w} Λ)).obj (tensorLeft M)) := by
    constructor
    intro K _ _
    apply preservesLimitsOfShape_of_evaluation
    intro U
    exact preservesLimitsOfShape_of_natIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by simp) :
        (evaluation _ _).obj U ⋙ tensorLeft M ≅
          (Functor.whiskeringRight _ _ _).obj (tensorLeft M) ⋙ (evaluation _ _).obj U)
  have : PreservesFiniteLimits (Sheaf.composeAndSheafify J (tensorLeft M)) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ (sheafToPresheaf J _)
      ((Functor.whiskeringRight _ _ _).obj (tensorLeft M) ⋙ presheafToSheaf J _) inferInstance
      (@comp_preservesFiniteLimits _ _ _ _ _ _ _ (presheafToSheaf J _) hW inferInstance)
  exact preservesFiniteLimits_of_natIso (flipObjIso J Λ M).symm

/-- Tensoring with a flat module carries acyclic complexes of sheaves to acyclic complexes. -/
theorem acyclic_mapHomologicalComplex_flipObj (M : ModuleCat.{w} Λ) [Module.Flat Λ M]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (Sheaf J (ModuleCat.{w} Λ)) c)
    (hK : K.Acyclic) :
    (((sheafTensor J Λ).flip.obj M).mapHomologicalComplex c |>.obj K).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff]
  exact (hK i).map ((sheafTensor J Λ).flip.obj M)

/-- `S ⊗_Λ -` preserves colimits: it is the sheafification of the pointwise functors
`- ⊗_Λ S(U)`, which are left adjoints. -/
instance preservesColimitsOfSize_obj (S : Sheaf J (ModuleCat.{w} Λ)) :
    PreservesColimitsOfSize.{0, 0} ((sheafTensor J Λ).obj S) := by
  have : PreservesColimitsOfSize.{0, 0} ((presheafTensor Λ).obj S.obj) := by
    apply preservesColimits_of_evaluation
    intro U
    exact preservesColimits_of_natIso
      (NatIso.ofComponents (fun M => (β_ (S.obj.obj U) M))
        (fun g => BraidedCategory.braiding_naturality_right _ _) :
        tensorLeft (S.obj.obj U) ≅ (presheafTensor Λ).obj S.obj ⋙ (evaluation _ _).obj U)
  exact inferInstanceAs (PreservesColimitsOfSize.{0, 0} ((presheafTensor Λ).obj S.obj ⋙
    presheafToSheaf J _))

/-- A `ℤ`-indexed cochain complex of sheaves of `Λ`-modules and one of `Λ`-modules have a tensor
product complex with respect to `sheafTensor`. -/
instance hasMapBifunctor (K₁ : HomologicalComplex (Sheaf J (ModuleCat.{w} Λ)) (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex (ModuleCat.{w} Λ) (ComplexShape.up ℤ)) :
    K₁.HasMapBifunctor K₂ (sheafTensor J Λ) (ComplexShape.up ℤ) := inferInstance

/-- A `ℤ × ℤ`-indexed double complex of sheaves of `Λ`-modules has a total complex. -/
instance hasTotal (K : HomologicalComplex₂ (Sheaf J (ModuleCat.{w} Λ)) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)) : K.HasTotal (ComplexShape.up ℤ) := inferInstance

end Stacks.ConstantModuleTensor
