module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep2CompositionLaw

/-!
# The composition law for the adjunction bijection at a tensor product

For a morphism of ringed topoi `χ : (Sh(C), O_C) ⟶ (Sh(E), O_E)`,
`Stacks.SheafOfModules.pullbackTensorStep1` is the adjunction bijection

`Hom_{O_C}(χ^*(F ⊗ G), N) = Hom_{O_E}(F ⊗ G, χ_*N)`.

This file computes it for a composite `χ = ψ ∘ φ`.

## Main definitions

* `Stacks.SheafOfModules.pullbackModulesCompAdjIso`: the comparison `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of
  pullbacks of sheaves of modules.

## Main results

* `Stacks.SheafOfModules.pullbackTensorStep1_comp'`: **the composition law for
  `pullbackTensorStep1`.** The bijection for a composite `ψ ∘ φ` is: transport along the
  comparison `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of pullbacks, transpose across `φ^* ⊣ φ_*`, transpose
  across `ψ^* ⊣ ψ_*`, and finally compose with the comparison `ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of direct
  images.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

/-- **The transpose of a morphism out of a left adjoint presented as a composite.** Let
`adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` be adjunctions, let `adj : L ⊣ R` be a third, and let
`e : R₂ ⋙ R₁ ≅ R` identify the composite right adjoint with `R`. Then `L` and `L₁ ⋙ L₂` are
both left adjoint to `R₂ ⋙ R₁`, so `CategoryTheory.Adjunction.leftAdjointUniq` compares them,
and transposing a morphism `f : L.obj X ⟶ Y` across `adj` is the same as transporting it along
that comparison, transposing across `adj₂` and then across `adj₁`, and finally composing
with `e`. -/
private theorem homEquiv_comp_leftAdjointUniq_ofNatIsoRight_inv_app_comp
    {A : Type*} [Category A] {B : Type*} [Category B] {C : Type*} [Category C]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L : A ⥤ C} {R : C ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (e : R₂ ⋙ R₁ ≅ R)
    {X : A} {Y : C} (f : L.obj X ⟶ Y) :
    adj₁.homEquiv X (R₂.obj Y)
          (adj₂.homEquiv (L₁.obj X) Y
            (((adj.ofNatIsoRight e.symm).leftAdjointUniq (adj₁.comp adj₂)).inv.app X ≫ f)) ≫
        e.hom.app Y =
      adj.homEquiv X Y f := by
  have huniq : (adj₁.comp adj₂).homEquiv X Y
        (((adj.ofNatIsoRight e.symm).leftAdjointUniq (adj₁.comp adj₂)).inv.app X ≫ f) =
      (adj.ofNatIsoRight e.symm).homEquiv X Y f := by
    rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rfl
  rw [Adjunction.comp_homEquiv] at huniq
  simp only [Equiv.trans_apply] at huniq
  rw [huniq, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

section Step1

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The comparison `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of sheaves of modules**: the
comparison `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` at the comparison
`Stacks.SheafOfModules.compPushforwardToposIso` of the geometric direct images. -/
def pullbackModulesCompAdjIso :
    (ψ.comp φ).toModulesHom.pullbackModules ≅
      ψ.toModulesHom.pullbackModules ⋙ φ.toModulesHom.pullbackModules :=
  pullbackModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
    (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)

/-- **The composition law for `Stacks.SheafOfModules.pullbackTensorStep1`.** Let
`φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of ringed
topoi, let `F` and `G` be sheaves of `O_E`-modules and `N` a sheaf of `O_C`-modules. A morphism
`u : (ψ ∘ φ)^*(F ⊗_{O_E} G) ⟶ N` is carried by `pullbackTensorStep1` for the composite to the
morphism obtained in four stages: transport `u` along the comparison `(ψ ∘ φ)^* ≅ ψ^* ⋙ φ^*` of
pullbacks, transpose across the adjunction `φ^* ⊣ φ_*`, transpose across `ψ^* ⊣ ψ_*` (which at
a tensor product is `pullbackTensorStep1` for `ψ`), and compose with the comparison
`ψ_*(φ_*N) ≅ (ψ ∘ φ)_*N` of direct images. -/
theorem pullbackTensorStep1_comp'
    (F G : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (u : ((ψ.comp φ).toModulesHom.pullbackModules).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ⟶ N) :
    pullbackTensorStep1 (ψ.comp φ).toModulesHom F G N u =
      pullbackTensorStep1 ψ.toModulesHom F G ((pushforwardModules φ.toModulesHom).obj N)
          ((pullbackAdjPushforwardModules φ.toModulesHom).homEquiv
            ((ψ.toModulesHom.pullbackModules).obj
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))) N
            ((pullbackModulesCompAdjIso φ ψ).inv.app
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ≫
                u)) ≫
        (pushforwardModulesCompAppIso φ ψ N).hom := by
  have hpb : (pullbackModulesCompAdjIso φ ψ).inv.app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) =
      (((pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom).ofNatIsoRight
          (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
            (compPushforwardToposIso φ ψ)
            (compPushforwardToposIso_fSharpSet φ ψ)).symm).leftAdjointUniq
        ((pullbackAdjPushforwardModules ψ.toModulesHom).comp
          (pullbackAdjPushforwardModules φ.toModulesHom))).inv.app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) := rfl
  have hpf : (pushforwardModulesCompAppIso φ ψ N).hom =
      (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
        (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)).hom.app N := rfl
  have hstep1 : pullbackTensorStep1 (ψ.comp φ).toModulesHom F G N u =
      (pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom).homEquiv
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) N u :=
    rfl
  have hstep1' : ∀ v : (ψ.toModulesHom.pullbackModules).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G)) ⟶
      (pushforwardModules φ.toModulesHom).obj N,
      pullbackTensorStep1 ψ.toModulesHom F G ((pushforwardModules φ.toModulesHom).obj N) v =
        (pullbackAdjPushforwardModules ψ.toModulesHom).homEquiv
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O))).obj (F, G))
          ((pushforwardModules φ.toModulesHom).obj N) v := fun _ ↦ rfl
  have hadj := homEquiv_comp_leftAdjointUniq_ofNatIsoRight_inv_app_comp
    (pullbackAdjPushforwardModules ψ.toModulesHom)
    (pullbackAdjPushforwardModules φ.toModulesHom)
    (pullbackAdjPushforwardModules (ψ.comp φ).toModulesHom)
    (pushforwardModulesCompIso φ.toModulesHom ψ.toModulesHom (ψ.comp φ).toModulesHom
      (compPushforwardToposIso φ ψ) (compPushforwardToposIso_fSharpSet φ ψ)) u
  rw [hpb, hpf, hstep1, hstep1', hadj]

end Step1

end Stacks.SheafOfModules

end

