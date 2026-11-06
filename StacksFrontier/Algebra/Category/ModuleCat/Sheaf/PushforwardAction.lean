module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.PresheafAlgebraMonObj
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing

/-!
# The action of a pushforward of the structure sheaf on the pushforward of a module

Let `F : C ⥤ D` be a functor, `R` and `S` presheaves of commutative rings on `D` and `C` and
`φ : S ⟶ F.op ⋙ R`. For a presheaf of `R`-modules `N`, the pushforward `F_*N` is a module over
the presheaf of `S`-algebras `F_*R : X ↦ R(F X)`: the action
`F_*N ⊗_S F_*R ⟶ F_*N` is, on sections over `X`, `n ⊗ s ↦ s • n`
(`PresheafOfModules.pushforwardAct`). It is natural in `N`, and on `N = R` it is the
multiplication of `F_*R` (`PresheafOfModules.pushforwardAct_unit`).

For sheaves of modules, maps out of a tensor product sheaf are induced by maps of presheaves out
of the objectwise tensor product. This file records how such induced maps behave:
`Stacks.SheafOfModules.whiskerRight_comp_sheafify_map_comp` (naturality from objectwise
naturality), `Stacks.SheafOfModules.tensorObjIso_inv_comp_mul` (the multiplication of a sheafified
algebra, read on the tensor product sheaf) and
`Stacks.SheafOfModules.whiskerRight_comp_tensorObjIso_hom` (naturality of the comparison of the
localized and the strict tensor products). These are the inputs of the `C`-linearity of the
isomorphism of Stacks 0GRK
(`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageAction`).

## Main definitions

* `ModuleCat.restrictScalarsAct`: the action `N ⊗_A B ⟶ N` of `B` on a `B`-module seen as an
  `A`-module.
* `ModuleCat.extendScalarsSMul`: multiplication by `c ∈ C` on `M ⊗_A C`, natural in `M`.
* `PresheafOfModules.pushforwardAct`: the action `F_*N ⊗_S F_*R ⟶ F_*N`.

## References

* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w v₁ v₂ u₁ u₂

namespace ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (N : ModuleCat.{u} B)

/-- The action `N ⊗_A B ⟶ N`, `n ⊗ b ↦ b • n`, of `B` on a `B`-module seen as an `A`-module:
the tensorator of the lax monoidal functor `restrictScalars f`, then the right unitor. -/
def restrictScalarsAct :
    (restrictScalars f).obj N ⊗ (restrictScalars f).obj (𝟙_ (ModuleCat.{u} B)) ⟶
      (restrictScalars f).obj N :=
  Functor.LaxMonoidal.μ (restrictScalars f) N (𝟙_ _) ≫ (restrictScalars f).map (ρ_ N).hom

theorem restrictScalarsAct_tmul (n : N) (b : B) :
    (restrictScalarsAct f N).hom (n ⊗ₜ b) = b • n := by
  simp only [restrictScalarsAct, hom_comp, LinearMap.comp_apply, restrictScalars_μ_tmul]
  exact MonoidalCategory.rightUnitor_hom_apply n b

end ModuleCat

namespace ModuleCat

variable {A C R : Type u} [CommRing A] [CommRing C] [CommRing R] (φ : A →+* C) (f : R →+* C)

/-- **Multiplication by `c ∈ C` on `M ⊗_A C`**, natural in the `A`-module `M`, seen as an
endomorphism of `M ↦ M ⊗_A C` viewed as an `R`-module along `f : R ⟶ C`. -/
def extendScalarsSMul (c : C) :
    extendScalars φ ⋙ restrictScalars f ⟶ extendScalars φ ⋙ restrictScalars f where
  app M := (restrictScalars f).map (ModuleCat.ofHom (X := (extendScalars φ).obj M)
    (Y := (extendScalars φ).obj M) (c • LinearMap.id))
  naturality {M M'} k := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact (((extendScalars φ).map k).hom.map_smul c y).symm

/-- `C ≅ A ⊗_A C` is `C`-linear: `(y * c) ⊗ 1 = c • (y ⊗ 1)`. -/
theorem ExtendScalars.objSelfIso_inv_hom_mul (y c : C) :
    (ExtendScalars.objSelfIso φ).inv.hom (y * c) = c • (ExtendScalars.objSelfIso φ).inv.hom y :=
  (congrArg (ExtendScalars.objSelfIso φ).inv.hom (mul_comm y c)).trans
    ((ExtendScalars.objSelfIso φ).inv.hom.map_smul c y)

theorem extendScalarsSMul_app_apply (c : C) (M : ModuleCat.{u} A) (y : (extendScalars φ).obj M) :
    ((extendScalarsSMul φ f c).app M).hom y = c • y :=
  rfl

end ModuleCat

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The pushforward of presheaves of modules along `φ : S ⟶ F.op ⋙ R`, for presheaves of
commutative rings. -/
abbrev pushforwardComm : PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤
    PresheafOfModules.{u} (S ⋙ forget₂ _ _) :=
  pushforward (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))

/-- **The action of the pushforward of the structure sheaf on the pushforward of a module**:
`F_*N ⊗_S F_*R ⟶ F_*N`, on sections over `X` the action
`N(F X) ⊗_{S(X)} R(F X) ⟶ N(F X)`, `n ⊗ s ↦ s • n`. -/
def pushforwardAct (N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := S) ((pushforwardComm φ).obj N)
        ((pushforwardComm φ).obj (unit _)) ⟶ (pushforwardComm φ).obj N where
  app X := ModuleCat.restrictScalarsAct (φ.app X).hom (N.obj (op (F.obj X.unop)))
  naturality {X X'} k := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun n s => ?_
    exact (congrArg (ModuleCat.restrictScalarsAct (φ.app X').hom (N.obj (op (F.obj X'.unop)))).hom
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul k n s)).trans
        ((ModuleCat.restrictScalarsAct_tmul (φ.app X').hom (N.obj (op (F.obj X'.unop))) _ _).trans
          ((N.map_smul (F.op.map k) s n).symm.trans (congrArg (N.map (F.op.map k)).hom
            (ModuleCat.restrictScalarsAct_tmul (φ.app X).hom (N.obj (op (F.obj X.unop))) n
              s).symm)))

theorem pushforwardAct_app_tmul (N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ)
    (n : N.obj (op (F.obj X.unop))) (s : R.obj (op (F.obj X.unop))) :
    ((pushforwardAct φ N).app X).hom (n ⊗ₜ s) = s • n :=
  ModuleCat.restrictScalarsAct_tmul _ _ n s

/-- The action is natural in the module. -/
theorem pushforwardAct_naturality {N N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') :
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := S) ((pushforwardComm φ).map ψ) (𝟙 _) ≫
        pushforwardAct φ N' =
      pushforwardAct φ N ≫ (pushforwardComm φ).map ψ := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.MonoidalCategory.tensor_ext fun n s => ?_
  exact (pushforwardAct_app_tmul φ N' X _ s).trans
    (((ψ.app _).hom.map_smul s n).symm.trans
      (congrArg (ψ.app _).hom (pushforwardAct_app_tmul φ N X n s).symm))

/-- **On the structure sheaf the action is the multiplication**: `F_*R ⊗_S F_*R ⟶ F_*R` is the
multiplication of the presheaf of `S`-algebras `X ↦ R(F X)`. -/
theorem pushforwardAct_unit :
    pushforwardAct φ (unit (R ⋙ forget₂ _ _)) = algebraPresheafMul φ := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.MonoidalCategory.tensor_ext fun a b => ?_
  exact (pushforwardAct_app_tmul φ _ X a b).trans (mul_comm (toRingElem φ b) (toRingElem φ a))

end PresheafOfModules

namespace Stacks.SheafOfModules

attribute [local implicit_reducible]
  TensorSheafification.structureSheaf TensorSheafification.sheafify Tensor.ringSheaf

attribute [local instance] monoidalCategoryPresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

section Strict

attribute [local instance] Strict.monoidalCategory

/-- **Naturality of a map out of a tensor product sheaf, from naturality of its objectwise
version.** For maps `α : M ⊗_p G ⟶ T` and `α' : M' ⊗_p G ⟶ T'` of presheaves of modules out of
the objectwise tensor products, compatible with `f : M ⟶ M'` and `t : T ⟶ T'`, the induced maps
out of the tensor product sheaves are compatible with `f ▷ G` and `t`. -/
theorem whiskerRight_comp_homEquiv_symm
    {M M' G T T' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (f : M ⟶ M') (t : T ⟶ T')
    (α : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) M.val G.val ⟶ T.val)
    (α' : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) M'.val G.val ⟶ T'.val)
    (h : PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := O) f.val (𝟙 G.val) ≫ α' = α ≫ t.val) :
    f ▷ G ≫ ((TensorSheafification.sheafifyAdjunction O hO).homEquiv _ _).symm α' =
      ((TensorSheafification.sheafifyAdjunction O hO).homEquiv _ _).symm α ≫ t := by
  refine (congrArg (· ≫ ((TensorSheafification.sheafifyAdjunction O hO).homEquiv _ _).symm α')
    (whiskerRight_eq_sheafify_map O hO f G)).trans ?_
  refine (((TensorSheafification.sheafifyAdjunction O hO).homEquiv_naturality_left_symm _
    _).symm.trans (Eq.trans ?_
      ((TensorSheafification.sheafifyAdjunction O hO).homEquiv_naturality_right_symm _ _)))
  exact congrArg _ h

/-- `Stacks.SheafOfModules.whiskerRight_comp_homEquiv_symm` with the induced maps written as the
sheafification of the presheaf maps followed by the counit. -/
theorem whiskerRight_comp_sheafify_map_comp
    {M M' G T T' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (f : M ⟶ M') (t : T ⟶ T')
    (α : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) M.val G.val ⟶ T.val)
    (α' : PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) M'.val G.val ⟶ T'.val)
    (h : PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := O) f.val (𝟙 G.val) ≫ α' = α ≫ t.val) :
    f ▷ G ≫ (sheafifyFunctor O hO).map α' ≫ (sheafifyValIso O hO T').hom =
      ((sheafifyFunctor O hO).map α ≫ (sheafifyValIso O hO T).hom) ≫ t :=
  (congrArg (f ▷ G ≫ ·) (Adjunction.homEquiv_counit (TensorSheafification.sheafifyAdjunction O hO)
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) M'.val G.val) T' α').symm).trans
    ((whiskerRight_comp_homEquiv_symm O hO f t α α' h).trans
      (congrArg (· ≫ t) (Adjunction.homEquiv_counit (TensorSheafification.sheafifyAdjunction O hO)
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := O) M.val G.val) T α)))

end Strict

section Localized

attribute [local instance] monoidalCategory sheafifyMonoidal

/-- **The multiplication of a sheafified algebra, read on the tensor product sheaf.** Let `G` be
a sheaf of modules whose underlying presheaf is a monoid, and give `G` the monoid structure of
its sheafification (for the localized monoidal structure). Then the multiplication of `G`,
read on the tensor product sheaf through `Stacks.SheafOfModules.tensorObjIso`, is the map out of
the sheafification induced by the multiplication of the presheaf. -/
theorem tensorObjIso_inv_comp_mul
    (G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) [hG : MonObj G.val] :
    letI : MonObj G := @MonObj.ofIso _ _ _ _ _
      (Functor.monObjObj (F := sheafifyFunctor O hO) (X := G.val)) (sheafifyValIso O hO G)
    (tensorObjIso O hO G G).inv ≫ MonObj.mul =
      (sheafifyFunctor O hO).map (MonObj.mul (X := G.val)) ≫ (sheafifyValIso O hO G).hom := by
  let : MonObj G := @MonObj.ofIso _ _ _ _ _
    (Functor.monObjObj (F := sheafifyFunctor O hO) (X := G.val)) (sheafifyValIso O hO G)
  have h : ((sheafifyValIso O hO G).inv ⊗ₘ (sheafifyValIso O hO G).inv) ≫
      Functor.LaxMonoidal.μ (sheafifyFunctor O hO) G.val G.val = (tensorObjIso O hO G G).hom :=
    rfl
  change (tensorObjIso O hO G G).inv ≫
      ((sheafifyValIso O hO G).inv ⊗ₘ (sheafifyValIso O hO G).inv) ≫
      (Functor.LaxMonoidal.μ (sheafifyFunctor O hO) G.val G.val ≫
        (sheafifyFunctor O hO).map (MonObj.mul (X := G.val))) ≫ (sheafifyValIso O hO G).hom = _
  have h2 : ((sheafifyValIso O hO G).inv ⊗ₘ (sheafifyValIso O hO G).inv) ≫
      Functor.LaxMonoidal.μ (sheafifyFunctor O hO) G.val G.val ≫
        (sheafifyFunctor O hO).map (MonObj.mul (X := G.val)) =
      (tensorObjIso O hO G G).hom ≫ (sheafifyFunctor O hO).map (MonObj.mul (X := G.val)) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h)
  refine (congrArg (fun k => (tensorObjIso O hO G G).inv ≫ k ≫ (sheafifyValIso O hO G).hom)
    h2).trans ?_
  exact (congrArg ((tensorObjIso O hO G G).inv ≫ ·) (Category.assoc _ _ _)).trans
    (Iso.inv_hom_id_assoc _ _)

/-- **`Stacks.SheafOfModules.tensorObjIso` is natural in the left factor**, with the whiskering
of the localized structure on the left and of the strict structure on the right. -/
theorem whiskerRight_comp_tensorObjIso_hom
    {M M' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)} (f : M ⟶ M')
    (G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) :
    f ▷ G ≫ (tensorObjIso O hO M' G).hom =
      (tensorObjIso O hO M G).hom ≫
        @MonoidalCategoryStruct.whiskerRight _ _
          (Strict.monoidalCategory O hO).toMonoidalCategoryStruct _ _ f G := by
  rw [← tensorHom_id, tensorObjIso_naturality]
  refine congrArg ((tensorObjIso O hO M G).hom ≫ ·) ?_
  exact (congrArg (sheafifyFunctor O hO).map (MonoidalCategory.tensorHom_id f.val G.val)).trans
    (@whiskerRight_eq_sheafify_map _ _ _ O hO _ _ _ _ f G).symm

end Localized

end Stacks.SheafOfModules
