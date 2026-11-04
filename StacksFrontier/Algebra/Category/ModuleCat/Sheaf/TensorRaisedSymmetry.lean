module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedUnitor

/-!
# Symmetry of the Stacks 0GMW tensor product, and the right unitor

`Stacks.SheafOfModules.Tensor.sheafTensor`, the tensor product of sheaves of modules whose module
universes are independent of the universe of the ring sheaf, is symmetric in its two arguments
when the two module universes agree.  This file proves that, and draws the two consequences the
presentation of a tensor product needs: the tensor product is right exact in its *first*
variable, and tensoring with the universe-lifted structure sheaf on the right changes nothing.

Mathlib's monoidal structure on presheaves of modules requires the module universe to contain the
universe of the ring, so its braiding is unavailable here.  The symmetry is therefore built by
hand from `PresheafOfModules.tensorMk`: on sections it is `x ⊗ₜ y ↦ y ⊗ₜ x`, and that it is an
isomorphism and that it is natural are both `PresheafOfModules.tensorObj_hom_ext` on pure
tensors.

## Main definitions

* `Stacks.SheafOfModules.TensorRaised.presheafTensorSwapIso`: the symmetry of the objectwise
  tensor product of presheaves of modules.
* `Stacks.SheafOfModules.TensorRaised.tensorRightRaised`: the Stacks 0GMW tensor product with its
  *second* argument fixed.

## Main results

* `Stacks.SheafOfModules.TensorRaised.tensorSwapRaisedIso` and
  `Stacks.SheafOfModules.TensorRaised.tensorSwapRaised_naturality`: the symmetry of the tensor
  product of sheaves of modules, and its naturality.
* `Stacks.SheafOfModules.TensorRaised.tensorRightRaised_preservesColimits`: **Stacks 05NB in the
  first variable** — tensoring on the right by a fixed sheaf of modules preserves colimits.
* `Stacks.SheafOfModules.TensorRaised.rightUnitorRaisedIso`: **the right unitor** at the raised
  universe.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u v w z t colimitMorphismUniverse

namespace Stacks.SheafOfModules.TensorRaised

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

section Presheaf

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The symmetry of the objectwise tensor product of presheaves of modules: on sections it sends
a pure tensor `x ⊗ₜ y` to `y ⊗ₜ x`. -/
noncomputable def presheafTensorSwap
    (F G : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.tensorObj F G ⟶ PresheafOfModules.tensorObj G F :=
  PresheafOfModules.tensorMk (fun _ x y ↦ y ⊗ₜ x)
    (fun _ _ _ _ ↦ TensorProduct.tmul_add _ _ _)
    (fun _ _ _ _ ↦ TensorProduct.tmul_smul _ _ _)
    (fun _ _ _ _ ↦ TensorProduct.add_tmul _ _ _)
    (fun _ _ _ _ ↦ TensorProduct.smul_tmul' _ _ _)
    (fun _ _ f x y ↦ PresheafOfModules.tensorObj_restrictₛₗ_tmul (F := G) (G := F) f y x)

@[simp]
lemma presheafTensorSwap_tmul
    (F G : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)) (X : Cᵒᵖ)
    (x : F.obj X) (y : G.obj X) :
    PresheafOfModules.Hom.app (presheafTensorSwap F G) X (x ⊗ₜ y) = y ⊗ₜ x :=
  PresheafOfModules.tensorMk_tmul (P := PresheafOfModules.tensorObj G F)
    (fun _ x y ↦ y ⊗ₜ x) _ _ _ _ _ X x y

/-- The objectwise tensor product of presheaves of modules is symmetric. -/
noncomputable def presheafTensorSwapIso
    (F G : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.tensorObj F G ≅ PresheafOfModules.tensorObj G F where
  hom := presheafTensorSwap F G
  inv := presheafTensorSwap G F
  hom_inv_id := PresheafOfModules.tensorObj_hom_ext fun X x y ↦ by
    rw [show PresheafOfModules.Hom.app (presheafTensorSwap F G ≫ presheafTensorSwap G F) X
        (x ⊗ₜ y) = PresheafOfModules.Hom.app (presheafTensorSwap G F) X
          (PresheafOfModules.Hom.app (presheafTensorSwap F G) X (x ⊗ₜ y)) from rfl,
      presheafTensorSwap_tmul, presheafTensorSwap_tmul]
    rfl
  inv_hom_id := PresheafOfModules.tensorObj_hom_ext fun X x y ↦ by
    rw [show PresheafOfModules.Hom.app (presheafTensorSwap G F ≫ presheafTensorSwap F G) X
        (x ⊗ₜ y) = PresheafOfModules.Hom.app (presheafTensorSwap F G) X
          (PresheafOfModules.Hom.app (presheafTensorSwap G F) X (x ⊗ₜ y)) from rfl,
      presheafTensorSwap_tmul, presheafTensorSwap_tmul]
    rfl

/-- The symmetry of the objectwise tensor product is natural in both variables. -/
theorem presheafTensorSwap_naturality
    {F F' G G' : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
    (uu : F ⟶ F') (vv : G ⟶ G') :
    PresheafOfModules.tensorHom uu vv ≫ presheafTensorSwap F' G' =
      presheafTensorSwap F G ≫ PresheafOfModules.tensorHom vv uu :=
  PresheafOfModules.tensorObj_hom_ext fun X x y ↦ by
    rw [show PresheafOfModules.Hom.app
        (PresheafOfModules.tensorHom uu vv ≫ presheafTensorSwap F' G') X (x ⊗ₜ y) =
      PresheafOfModules.Hom.app (presheafTensorSwap F' G') X
        (PresheafOfModules.Hom.app (PresheafOfModules.tensorHom uu vv) X (x ⊗ₜ y)) from rfl,
      show PresheafOfModules.Hom.app
        (presheafTensorSwap F G ≫ PresheafOfModules.tensorHom vv uu) X (x ⊗ₜ y) =
      PresheafOfModules.Hom.app (PresheafOfModules.tensorHom vv uu) X
        (PresheafOfModules.Hom.app (presheafTensorSwap F G) X (x ⊗ₜ y)) from rfl,
      PresheafOfModules.tensorHom_tmul, presheafTensorSwap_tmul, presheafTensorSwap_tmul,
      PresheafOfModules.tensorHom_tmul]

end Presheaf

section Sheaf

variable [HasWeakSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- **The tensor product of sheaves of modules is symmetric**, at a module universe independent
of the universe of the ring sheaf. -/
noncomputable def tensorSwapRaisedIso (R : Sheaf J CommRingCat.{w})
    (F G : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj F).obj G ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj G).obj F :=
  (PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).mapIso
      (presheafTensorSwapIso.{u, v, w, z} (O := R.obj) F.val G.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The symmetry of the tensor product of sheaves of modules is natural. -/
theorem tensorSwapRaised_naturality (R : Sheaf J CommRingCat.{w})
    {F F' G G' : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).map f).app G ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj F').map g) ≫
        (tensorSwapRaisedIso.{u, v, w, z} R F' G').hom =
      (tensorSwapRaisedIso.{u, v, w, z} R F G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).map g).app F ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj G').map f := by
  refine (congrArg (fun morphism ↦ morphism ≫ (tensorSwapRaisedIso R F' G').hom)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map R f g)).trans ?_
  refine Eq.trans ?_ (congrArg (fun morphism ↦
    (tensorSwapRaisedIso R F G).hom ≫ morphism)
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map R g f).symm)
  exact (((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map_comp _ _).symm.trans
    (congrArg (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
      (presheafTensorSwap_naturality.{u, v, w, z} (O := R.obj) f.val g.val))).trans
    ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map_comp _ _)

/-- Tensoring on the right by a fixed sheaf of modules is tensoring on the left by it. -/
noncomputable def tensorRightRaisedIso (R : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (R)).flip.obj F ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (R)).obj F :=
  NatIso.ofComponents (fun G ↦ tensorSwapRaisedIso.{u, v, w, z} R G F)
    (fun {_G _H} g ↦ by
      have naturality := tensorSwapRaised_naturality.{u, v, w, z} R g (𝟙 F)
      rw [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).obj _H).map_id F,
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} R).map_id F] at naturality
      simp only [NatTrans.id_app, Category.comp_id, Category.id_comp] at naturality
      exact naturality)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Tensoring on the right by a fixed sheaf of modules preserves colimits**, at a module
universe independent of the ring universe.  This is Stacks 05NB in the first variable. -/
theorem tensorRightRaised_preservesColimits (R : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{colimitMorphismUniverse, z}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (R)).flip.obj F) := by
  have h : PreservesColimitsOfSize.{colimitMorphismUniverse, z}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (R)).obj F) :=
    TensorColimits.tensorLeft_preservesColimits J R F
  exact @preservesColimits_of_natIso _ _ _ _ _ _
    (tensorRightRaisedIso.{u, v, w, z} R F).symm h

attribute [instance] tensorRightRaised_preservesColimits

end Sheaf

section Unitor

variable [HasWeakSheafify J AddCommGrpCat.{max t w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}]

/-- **The right unitor at the raised universe.**  Tensoring a sheaf of modules on the right with
the universe-lifted structure sheaf is that sheaf. -/
noncomputable def rightUnitorRaisedIso (R : Sheaf J CommRingCat.{w})
    (N : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} (R)).flip.obj
      (liftedUnit.{u, v, w, t} R)).obj N ≅ N :=
  tensorSwapRaisedIso.{u, v, w, max t w} R N (liftedUnit.{u, v, w, t} R) ≪≫
    unitorIso.{u, v, w, t} R N

end Unitor

end Stacks.SheafOfModules.TensorRaised

end
