module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient

/-!
# Tensoring a quotient by a fixed module, and pullback

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `L` a sheaf of
`O_D`-modules.  The comparison of Stacks 03EL at the pairs `(M, L)` is a natural isomorphism

`f^*(- ⊗ L) ≅ f^*(-) ⊗ f^*L`

of functors of `M`, `AlgebraicGeometry.RingedToposHom.pullbackTensorRightIso` below.  Conjugating a
quotient of `f^*F` by it gives a quotient of `f^*(F ⊗ L)`: if `f^*F ⟶ Q` is the quotient, the new
one is `f^*(F ⊗ L) ≅ f^*F ⊗ f^*L ⟶ Q ⊗ f^*L`.

This file proves that this operation commutes with pulling back quotients along a further
morphism: for `φ : X₂ ⟶ X₁` and `ψ : X₁ ⟶ X₀` with composite `χ`, tensoring a quotient of
`ψ^*F` by `ψ^*L` and then pulling it back to `X₂` gives the same quotient of `χ^*(F ⊗ L)` as
pulling it back first and then tensoring by `χ^*L`.  The content is the composition law of the
comparison of Stacks 03EL, `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp`.

## Main definitions

* `Stacks.SheafOfModules.tensorRightFunctorOf`: right tensoring by a sheaf of modules,
  `M ↦ M ⊗ L`.
* `AlgebraicGeometry.RingedToposHom.pullbackTensorRightIso`: the comparison
  `f^*(- ⊗ L) ≅ f^*(-) ⊗ f^*L`.

## Main results

* `CategoryTheory.Functor.conjSubobject_eq_of_hom_app_eq`: conjugating a quotient does not see a
  change of the comparison by a natural isomorphism of the further functor.
* `Stacks.Sheaves.RingedToposModules.conjSubobject_pullbackTensorRightIso_pullbackModulesCompIso`:
  tensoring a quotient commutes with pulling it back.

## Implementation notes

Everything here is stated with the ringed topoi as variables.  The statements are instantiated at
the small étale ringed topoi of algebraic spaces in
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorTensorInvertible.lean`; carrying out the same
computations at those concrete topoi makes the elaborator unfold the topoi to reach their category
instances, which it does not finish.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe w w' w'' v u v' u' v'' u''

namespace CategoryTheory.Functor

variable {C : Type*} {D₀ : Type*} {D₁ : Type*} [Category* C] [Category* D₀] [Category* D₁]
  [Abelian D₀] [Abelian D₁]

/-- **Conjugating a quotient does not see a change of comparison by an isomorphism of the
further functor.**  If two comparisons `c : P₂ ≅ P₁ ⋙ L` and `c' : P₂ ≅ P₁ ⋙ L'` differ at `M` by
an isomorphism `σ : L ≅ L'`, then they conjugate every quotient of `P₁ M` to the same quotient of
`P₂ M`. -/
theorem conjSubobject_eq_of_hom_app_eq {P₁ : C ⥤ D₀} {P₂ : C ⥤ D₁} {L L' : D₀ ⥤ D₁}
    (c : P₂ ≅ P₁ ⋙ L) (c' : P₂ ≅ P₁ ⋙ L') (σ : L ≅ L') {M : C}
    (h : c'.hom.app M = c.hom.app M ≫ σ.hom.app (P₁.obj M)) (K : Subobject (P₁.obj M)) :
    conjSubobject c K = conjSubobject c' K := by
  refine (kernelSubobject_eq_of_comp_mono (conjQuotientProjection c K)
    (conjQuotientProjection c' K) (σ.hom.app (cokernel K.arrow)) ?_).symm
  simp only [conjQuotientProjection, h, Category.assoc]
  exact congrArg (c.hom.app M ≫ ·) (σ.hom.naturality (cokernel.π K.arrow))

/-- **Conjugating a quotient along a whiskered comparison.**  Conjugating a quotient of
`P₁ (G M)` by `c : P₂ ≅ P₁ ⋙ L` is conjugating it by the comparison `G ⋙ P₂ ≅ (G ⋙ P₁) ⋙ L`
obtained by whiskering `c` with `G`. -/
theorem conjSubobject_isoWhiskerLeft_trans_associator_symm {C' : Type*} [Category* C']
    {P₁ : C ⥤ D₀} {P₂ : C ⥤ D₁} {L : D₀ ⥤ D₁} (G : C' ⥤ C) (c : P₂ ≅ P₁ ⋙ L) (M : C')
    (K : Subobject (P₁.obj (G.obj M))) :
    conjSubobject (isoWhiskerLeft G c ≪≫ (associator G P₁ L).symm) (M := M) K =
      conjSubobject c (M := G.obj M) K := by
  simp only [conjSubobject, conjQuotientProjection, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, associator_inv_app, Category.comp_id]

end CategoryTheory.Functor

namespace Stacks.SheafOfModules

variable {X : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Right tensoring by a sheaf of modules, `M ↦ M ⊗_{O} L`. -/
abbrev tensorRightFunctorOf (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj L

end Stacks.SheafOfModules

namespace Stacks.Sheaves.RingedToposModules.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **Stacks 03EL with one factor fixed.**  For a morphism `f` of ringed topoi and a sheaf of
`O_D`-modules `L`, the comparison of Stacks 03EL at the pairs `(M, L)` is a natural isomorphism
`f^*(M ⊗ L) ≅ f^*M ⊗ f^*L` of functors of `M`. -/
def pullbackTensorRightIso (f : RingedToposHom X Y)
    (L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    Stacks.SheafOfModules.tensorRightFunctorOf L ⋙ f.pullbackModules ≅
      f.pullbackModules ⋙ Stacks.SheafOfModules.tensorRightFunctorOf (f.pullbackModules.obj L) :=
  NatIso.ofComponents (fun M ↦ (Stacks.SheafOfModules.pullbackTensorIso f).app (M, L))
    (fun {M M'} α ↦ by
      have h := (Stacks.SheafOfModules.pullbackTensorIso f).hom.naturality
        ((α, 𝟙 L) : ((M, L) : _ × _) ⟶ (M', L))
      simp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
        CategoryTheory.Functor.map_id, Category.comp_id] at h
      exact h)

@[simp]
theorem pullbackTensorRightIso_hom_app (f : RingedToposHom X Y)
    (L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackTensorRightIso f L).hom.app M =
      (Stacks.SheafOfModules.pullbackTensorIso f).hom.app (M, L) :=
  rfl

end Stacks.Sheaves.RingedToposModules.RingedToposHom

namespace Stacks.Sheaves.RingedToposModules

variable {X₀ : RingedTopos.{v, u, w}} {X₁ : RingedTopos.{v', u', w'}}
  {X₂ : RingedTopos.{v'', u'', w''}}
  [X₀.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X₀.J.HasSheafCompose (forget RingCat.{w})] [X₁.J.HasSheafCompose (forget RingCat.{w'})]
  [X₂.J.HasSheafCompose (forget RingCat.{w''})]
  [X₀.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X₀.J AddCommGrpCat.{w}] [X₀.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w'}] [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify X₂.J AddCommGrpCat.{w''}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [Abelian (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₀.O))]
  [Abelian (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))]
  [Abelian (SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O))]

omit [Abelian (SheafOfModules (SheafOfModules.Tensor.ringSheaf X₀.O))]
  [Abelian (SheafOfModules (SheafOfModules.Tensor.ringSheaf X₁.O))]
  [Abelian (SheafOfModules (SheafOfModules.Tensor.ringSheaf X₂.O))] in
/-- The composition law of the comparison of Stacks 03EL with the second factor fixed and read
back through the comparison of pullbacks in that factor. -/
theorem pullbackTensorIso_hom_app_comp_inv
    (ψ : RingedToposHom X₁ X₀) (φ : RingedToposHom X₂ X₁) (χ : RingedToposHom X₂ X₀)
    (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
    (hτ : fSharpSetComp φ ψ ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)) = fSharpSet χ)
    (F L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₀.O)) :
    (Stacks.SheafOfModules.pullbackTensorIso χ).hom.app (F, L) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X₂.O).map
        ((pullbackModulesCompIso φ ψ χ τ hτ).hom.app F)).app (χ.pullbackModules.obj L) =
    (pullbackModulesCompIso φ ψ χ τ hτ).hom.app
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X₀.O)).obj (F, L)) ≫
      φ.pullbackModules.map ((Stacks.SheafOfModules.pullbackTensorIso ψ).hom.app (F, L)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso φ).hom.app
          (ψ.pullbackModules.obj F, ψ.pullbackModules.obj L) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X₂.O).obj
            (φ.pullbackModules.obj (ψ.pullbackModules.obj F))).map
              ((pullbackModulesCompIso φ ψ χ τ hτ).inv.app L) := by
  have h := Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp φ ψ χ τ hτ F L
  simp only [Functor.uncurry_obj_map] at h
  have h2 := h =≫ ((Stacks.SheafOfModules.Tensor.sheafTensor X₂.O).obj
    (φ.pullbackModules.obj (ψ.pullbackModules.obj F))).map
      ((pullbackModulesCompIso φ ψ χ τ hτ).inv.app L)
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Functor.prod_obj] at h2
  exact h2

omit [Abelian (SheafOfModules (SheafOfModules.Tensor.ringSheaf X₀.O))] in
/-- **Tensoring a quotient by a fixed module commutes with pulling it back.**  Let
`φ : X₂ ⟶ X₁` and `ψ : X₁ ⟶ X₀` be morphisms of ringed topoi and let `χ = χ₀ : X₂ ⟶ X₀` play the
role of their composite, joined to it by a comparison `τ` of the geometric direct images.  For
sheaves of `O_{X₀}`-modules `F` and `L` and a quotient of `ψ^*F`, recorded by its kernel `K`:
tensoring the quotient by `ψ^*L` and pulling the result back along `φ`, through the comparison
of pullbacks at `F ⊗ L`, gives the same quotient of `χ^*(F ⊗ L)` as pulling the quotient back
first and then tensoring it by `χ^*L`. -/
theorem conjSubobject_pullbackTensorRightIso_pullbackModulesCompIso
    (ψ : RingedToposHom X₁ X₀) (φ : RingedToposHom X₂ X₁) (χ χ₀ : RingedToposHom X₂ X₀)
    (hχ : χ = χ₀)
    (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ₀.toToposHom.pushforward)
    (hτ : fSharpSetComp φ ψ ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X₂.O)) = fSharpSet χ₀)
    (F L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X₀.O))
    (K : Subobject (ψ.pullbackModules.obj F))
    (hepi₁ :
      (Stacks.SheafOfModules.tensorRightFunctorOf (ψ.pullbackModules.obj L)).PreservesEpimorphisms)
    (hepi₂ : φ.pullbackModules.PreservesEpimorphisms) :
    Functor.conjSubobject
        (eqToIso (congrArg (fun χ' : RingedToposHom X₂ X₀ ↦ χ'.pullbackModules) hχ) ≪≫
          pullbackModulesCompIso φ ψ χ₀ τ hτ)
        (M := (Stacks.SheafOfModules.tensorRightFunctorOf L).obj F)
        (Functor.conjSubobject (RingedToposHom.pullbackTensorRightIso ψ L) K) =
      Functor.conjSubobject (RingedToposHom.pullbackTensorRightIso χ L)
        (Functor.conjSubobject
          (eqToIso (congrArg (fun χ' : RingedToposHom X₂ X₀ ↦ χ'.pullbackModules) hχ) ≪≫
            pullbackModulesCompIso φ ψ χ₀ τ hτ) K) := by
  subst hχ
  have := hepi₁
  have := hepi₂
  rw [← Functor.conjSubobject_isoWhiskerLeft_trans_associator_symm
    (Stacks.SheafOfModules.tensorRightFunctorOf L)]
  rw [eqToIso_refl, Iso.refl_trans,
    ← Functor.conjSubobject_comp (RingedToposHom.pullbackTensorRightIso ψ L)
      (Functor.isoWhiskerLeft (Stacks.SheafOfModules.tensorRightFunctorOf L)
        (pullbackModulesCompIso φ ψ χ τ hτ) ≪≫
          (Functor.associator _ ψ.pullbackModules φ.pullbackModules).symm) _ (Iso.refl _) rfl,
    ← Functor.conjSubobject_comp (pullbackModulesCompIso φ ψ χ τ hτ)
      (RingedToposHom.pullbackTensorRightIso χ L) _ (Iso.refl _) rfl]
  refine Functor.conjSubobject_eq_of_hom_app_eq _ _
    (RingedToposHom.pullbackTensorRightIso φ (ψ.pullbackModules.obj L) ≪≫
      Functor.isoWhiskerLeft φ.pullbackModules
        ((Stacks.SheafOfModules.Tensor.sheafTensor X₂.O).flip.mapIso
          ((pullbackModulesCompIso φ ψ χ τ hτ).app L).symm)) ?_ K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Iso.refl_inv, Functor.isoWhiskerLeft_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    RingedToposHom.pullbackTensorRightIso_hom_app, Functor.mapIso_hom, Iso.app_inv,
    Functor.flip_map_app, Functor.comp_obj, Functor.associator_inv_app, Functor.flip_obj_map]
  exact pullbackTensorIso_hom_app_comp_inv ψ φ χ τ hτ F L

end Stacks.Sheaves.RingedToposModules

end
