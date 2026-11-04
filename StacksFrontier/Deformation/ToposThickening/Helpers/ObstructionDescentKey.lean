module

public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionDescentKeyPairing
public import StacksFrontier.Deformation.ToposThickening.Helpers.ThickeningTargetModulesIso

/-!
# The compatibility of the actions on two thickenings related by a morphism of their targets

For first order thickenings `i₁ : X ⟶ Y₁`, `i₂ : X ⟶ Y₂` and a morphism `j : Y₂ ⟶ Y₁` of their
targets, and `E : Ψ₀ ∘ i₂_* ≅ i₁_*` an isomorphism of direct images of modules which is a
comparison `θ : j_*i₂_* ≅ i₁_*` on underlying sheaves of sets (for instance
`ThickeningTargetMorphism.thickenedModulesCompIso`), this file
proves the compatibility of the actions which
`ThickeningTargetMorphism.extDescentAddEquiv_symm_existenceObstructionClass_eq_comp` takes as its
hypothesis, from the compatibility of the identifications `eₖ : iₖ_*Jₖ ≅ ℐₖ` with the map of ideals
(`ThickeningTargetMorphism.hkey_of_idealMap`). Both sides are computed on the universal pairing.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.SheafOfModules

universe v u v₁ u₁ v₂ u₂ w

namespace Stacks.SheafOfModules

/-- A pairing followed by three morphisms, the first and the last acting on the first factor. -/
theorem pairing_comp_three_prodMap {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    [HasBinaryProducts 𝒟] (G : 𝒞 ⥤ 𝒟) {P₀ P₁ P₂ Q : 𝒟} {T₀ T₁ T₂ T₃ : 𝒞}
    (t₀ : P₀ ⨯ Q ⟶ G.obj T₀) (a₁ : T₀ ⟶ T₁) (a₂ : T₁ ⟶ T₂) (a₃ : T₂ ⟶ T₃) (f₁ : P₀ ⟶ P₁)
    (t₁ : P₁ ⨯ Q ⟶ G.obj T₁) (s₁ : t₀ ≫ G.map a₁ = prod.map f₁ (𝟙 Q) ≫ t₁)
    (t₂ : P₁ ⨯ Q ⟶ G.obj T₂) (s₂ : t₁ ≫ G.map a₂ = t₂) (f₃ : P₁ ⟶ P₂)
    (t₃ : P₂ ⨯ Q ⟶ G.obj T₃) (s₃ : t₂ ≫ G.map a₃ = prod.map f₃ (𝟙 Q) ≫ t₃) :
    t₀ ≫ G.map (a₁ ≫ a₂ ≫ a₃) = prod.map (f₁ ≫ f₃) (𝟙 Q) ≫ t₃ := by
  rw [G.map_comp, G.map_comp, ← Category.assoc, s₁, Category.assoc, ← Category.assoc t₁, s₂, s₃,
    ← Category.assoc, prod.map_map, Category.id_comp]

/-- A functor carrying the forward map of an isomorphism to the forward map of another carries
the inverse to the inverse. -/
theorem map_inv_eq_of_map_hom_eq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟)
    {A B : 𝒞} (e : A ≅ B) (f : G.obj A ≅ G.obj B) (h : G.map e.hom = f.hom) :
    G.map e.inv = f.inv :=
  (Iso.inv_ext (by rw [← h, ← G.map_comp, e.hom_inv_id, G.map_id])).symm

/-- A pairing followed by four morphisms, the first acting on the second factor and the second
on the first. -/
theorem pairing_comp_four_prodMap {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    [HasBinaryProducts 𝒟] (G : 𝒞 ⥤ 𝒟) {P P' Q Q' : 𝒟} {T₀ T₁ T₂ T₃ T₄ : 𝒞}
    (t₀ : P ⨯ Q ⟶ G.obj T₀) (a₁ : T₀ ⟶ T₁) (a₂ : T₁ ⟶ T₂) (a₃ : T₂ ⟶ T₃) (a₄ : T₃ ⟶ T₄)
    (g : Q ⟶ Q') (t₁ : P ⨯ Q' ⟶ G.obj T₁) (s₁ : t₀ ≫ G.map a₁ = prod.map (𝟙 P) g ≫ t₁)
    (f : P ⟶ P') (t₂ : P' ⨯ Q' ⟶ G.obj T₂) (s₂ : t₁ ≫ G.map a₂ = prod.map f (𝟙 Q') ≫ t₂)
    (t₃ : P' ⨯ Q' ⟶ G.obj T₃) (s₃ : t₂ ≫ G.map a₃ = t₃) (t₄ : P' ⨯ Q' ⟶ G.obj T₄)
    (s₄ : t₃ ≫ G.map a₄ = t₄) :
    t₀ ≫ G.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄) = prod.map f g ≫ t₄ := by
  rw [G.map_comp, G.map_comp, G.map_comp, ← Category.assoc, s₁, Category.assoc,
    ← Category.assoc t₁, s₂, Category.assoc, ← Category.assoc t₂, s₃, s₄, ← Category.assoc,
    prod.map_map, Category.id_comp, Category.comp_id]

end Stacks.SheafOfModules

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₁, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} (hi : FirstOrderThickening i)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `i_*` of a morphism of modules, on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_thickenedModulesFunctor_map
    {M M' : SheafOfModules.{w} (Tensor.ringSheaf X.O)} (m : M ⟶ M') :
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map ((thickenedModulesFunctor i).map m) =
      i.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map m) :=
  Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMap _ _ _ m

/-- **The pairing of the action `(e ⊗ 1) ≫ t ≫ i_*(λ ⊗ F)`** on `I ⊗ i_*F`, for `e : I ⟶ i_*J`
and `λ : J ⟶ J'`: two local sections are paired by `i_*` of the universal pairing of `J'` and
`F`, applied to the image of the first under `e` and `i_*λ`. -/
theorem tensorSectionPairing_comp_map_pushforwardModuleTensorIso_hom_map
    (F J J' : SheafOfModules.{w} (Tensor.ringSheaf X.O)) (lam : J ⟶ J')
    {I : SheafOfModules.{w} (Tensor.ringSheaf (baseRing i))}
    (e : I ⟶ (thickenedModulesFunctor i).obj J) :
    tensorSectionPairing I ((thickenedModulesFunctor i).obj F) ≫
        (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
          (((Tensor.sheafTensor (baseRing i)).flip.obj ((thickenedModulesFunctor i).obj F)).map e ≫
            (pushforwardModuleTensorIso hi F J).hom ≫
              (thickenedModulesFunctor i).map (((Tensor.sheafTensor X.O).flip.obj F).map lam)) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map e ≫
          i.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map lam))
          (𝟙 (i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) F))) ≫
        (PreservesLimitPair.iso i.toToposHom.pushforward (moduleSheaf (Tensor.ringSheaf X.O) J')
          (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
        i.toToposHom.pushforward.map (tensorSectionPairing J' F) := by
  exact pairing_comp_three_prodMap _ _ _ _ _ _
    (P₁ := i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) J))
    (Q := i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) F)) _
    (tensorSectionPairing_comp_map_left (B := (thickenedModulesFunctor i).obj F) e) _
    (tensorSectionPairing_comp_pushforwardModuleTensorIso_hom hi F J) _ _
    (by
      rw [moduleSheafFunctor_map_thickenedModulesFunctor_map]
      exact preservesLimitPair_iso_inv_comp_map_comp_left _ _ _ _ _
        (tensorSectionPairing_comp_map_left (B := F) lam))

/-- Two consecutive images under a functor, recombined through an identity of their source. -/
theorem _root_.Stacks.SheafOfModules.comp_map_comp_map_eq {𝒞 𝒟 : Type*} [Category* 𝒞]
    [Category* 𝒟] (G : 𝒞 ⥤ 𝒟) {P : 𝒟} {A B C : 𝒞} (p : P ⟶ G.obj A) (t : A ⟶ B) (m : B ⟶ C)
    (x : A ⟶ C) (h : t ≫ m = x) : (p ≫ G.map t) ≫ G.map m = p ≫ G.map x := by
  rw [Category.assoc, ← G.map_comp, h]

/-- The image under a functor of an identity `a₁ ≫ a₂ = b₁ ≫ b₂ ≫ b₃`, with three of the images
replaced by given morphisms. -/
theorem _root_.Stacks.SheafOfModules.map_comp_eq_map_comp_comp {𝒞 𝒟 : Type*} [Category* 𝒞]
    [Category* 𝒟] (G : 𝒞 ⥤ 𝒟) {A B C B' C' : 𝒞} (a₁ : A ⟶ B) (a₂ : B ⟶ C) (b₁ : A ⟶ B')
    (b₂ : B' ⟶ C') (b₃ : C' ⟶ C) (h : a₁ ≫ a₂ = b₁ ≫ b₂ ≫ b₃) {x₂ : G.obj B ⟶ G.obj C}
    {y₂ : G.obj B' ⟶ G.obj C'} {y₃ : G.obj C' ⟶ G.obj C} (hx₂ : G.map a₂ = x₂)
    (hy₂ : G.map b₂ = y₂) (hy₃ : G.map b₃ = y₃) :
    G.map a₁ ≫ x₂ = G.map b₁ ≫ y₂ ≫ y₃ := by
  rw [← hx₂, ← hy₂, ← hy₃, ← G.map_comp, ← G.map_comp, ← G.map_comp, h]

/-- A pairing followed by two morphisms, the first acting on the first factor. -/
theorem _root_.Stacks.SheafOfModules.pairing_comp_two {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    (G : 𝒞 ⥤ 𝒟) {P P' : 𝒟} {T₀ T₁ T₂ : 𝒞} (t₀ : P ⟶ G.obj T₀) (a₁ : T₀ ⟶ T₁) (a₂ : T₁ ⟶ T₂)
    (p : P ⟶ P') (t₁ : P' ⟶ G.obj T₁) (s₁ : t₀ ≫ G.map a₁ = p ≫ t₁) (t₂ : P' ⟶ G.obj T₂)
    (s₂ : t₁ ≫ G.map a₂ = t₂) : t₀ ≫ G.map (a₁ ≫ a₂) = p ≫ t₂ := by
  rw [G.map_comp, ← Category.assoc, s₁, Category.assoc, s₂]

/-- **The pairing of the action `(e ⊗ 1) ≫ t`** on `I ⊗ i_*F`, for `e : I ⟶ i_*J`. -/
theorem tensorSectionPairing_comp_map_pushforwardModuleTensorIso_hom
    (F J : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    {I : SheafOfModules.{w} (Tensor.ringSheaf (baseRing i))}
    (e : I ⟶ (thickenedModulesFunctor i).obj J) :
    tensorSectionPairing I ((thickenedModulesFunctor i).obj F) ≫
        (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
          (((Tensor.sheafTensor (baseRing i)).flip.obj ((thickenedModulesFunctor i).obj F)).map e ≫
            (pushforwardModuleTensorIso hi F J).hom) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map e)
          (𝟙 (i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) F))) ≫
        (PreservesLimitPair.iso i.toToposHom.pushforward (moduleSheaf (Tensor.ringSheaf X.O) J)
          (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
        i.toToposHom.pushforward.map (tensorSectionPairing J F) :=
  pairing_comp_two _ _ _ _ _ _
    (tensorSectionPairing_comp_map_left (B := (thickenedModulesFunctor i).obj F) e) _
    (tensorSectionPairing_comp_pushforwardModuleTensorIso_hom hi F J)

namespace ThickeningTargetMorphism

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)
  (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)
  (E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁)
  (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
    (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
  (hE : ∀ M : SheafOfModules.{w} (Tensor.ringSheaf X.O),
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map (E.hom.app M) =
      θ.hom.app (moduleSheaf (Tensor.ringSheaf X.O) M))

omit [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
include hE in
/-- `E : Ψ₀ ∘ i₂_* ≅ i₁_*` is `θ` on underlying sheaves of sets also in the inverse direction. -/
theorem moduleSheafFunctor_map_inv_app_of_hom_app
    (M : SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map (E.inv.app M) =
      θ.inv.app (moduleSheaf (Tensor.ringSheaf X.O) M) :=
  map_inv_eq_of_map_hom_eq (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁)))
    (E.app M) (θ.app (moduleSheaf (Tensor.ringSheaf X.O) M)) (hE M)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- `Ψ₀` of a morphism of modules, on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_basePushforward_map
    {M M' : SheafOfModules.{w} (Tensor.ringSheaf (baseRing i₂))} (m : M ⟶ M') :
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map (D.basePushforward.map m) =
      D.j.toToposHom.pushforward.map
        ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₂))).map m) :=
  RingedToposHom.moduleSheafFunctor_map_pushforwardModules_map D.baseHom m

include hE in
/-- **The pairing of the action `(1 ⊗ E⁻¹) ≫ θ_F ≫ Ψ₀((e₂ ⊗ 1) ≫ t₂) ≫ E`** on `ℐ₁ ⊗ i₁_*F`. -/
theorem tensorSectionPairing_comp_idealTensorMap_action
    (F J₂ : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (e₂ : hi₂.I ⟶ (thickenedModulesFunctor i₂).obj J₂) :
    tensorSectionPairing hi₁.I ((thickenedModulesFunctor i₁).obj F) ≫
        (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map
          (((Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map
              (E.inv.app F) ≫
            D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F) ≫
            D.basePushforward.map
              (((Tensor.sheafTensor (baseRing i₂)).flip.obj
                  ((thickenedModulesFunctor i₂).obj F)).map e₂ ≫
                (pushforwardModuleTensorIso hi₂ F J₂).hom) ≫
            E.hom.app
              (((Tensor.sheafTensor X.O).flip.obj F).obj J₂)) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map (D.idealMap hi₁ hi₂))
          (θ.inv.app (moduleSheaf (Tensor.ringSheaf X.O) F)) ≫
        (PreservesLimitPair.iso D.j.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf (baseRing i₂)) hi₂.I)
          (i₂.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) F))).inv ≫
        D.j.toToposHom.pushforward.map
          (prod.map ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₂))).map e₂)
              (𝟙 (i₂.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) F))) ≫
            (PreservesLimitPair.iso i₂.toToposHom.pushforward
              (moduleSheaf (Tensor.ringSheaf X.O) J₂) (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
            i₂.toToposHom.pushforward.map (tensorSectionPairing J₂ F)) ≫
        θ.hom.app (moduleSheaf (Tensor.ringSheaf X.O)
          (((Tensor.sheafTensor X.O).flip.obj F).obj J₂)) := by
  have r₁ := tensorSectionPairing_comp_map_right (A := hi₁.I)
    (E.inv.app F)
  rw [D.moduleSheafFunctor_map_inv_app_of_hom_app E θ hE F] at r₁
  have r₂ : tensorSectionPairing hi₁.I
      (D.basePushforward.obj ((thickenedModulesFunctor i₂).obj F)) ≫
      (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map
        (D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F)) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map (D.idealMap hi₁ hi₂))
          (𝟙 _) ≫
        (PreservesLimitPair.iso D.j.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf (baseRing i₂)) hi₂.I)
          (moduleSheaf (Tensor.ringSheaf (baseRing i₂)) ((thickenedModulesFunctor i₂).obj F))).inv ≫
        D.j.toToposHom.pushforward.map
          (tensorSectionPairing hi₂.I ((thickenedModulesFunctor i₂).obj F)) := by
    refine (tensorSectionPairing_comp_bilinearEquivTensorHom _
      (D.isBilinearPairing_idealTensorPairing hi₁ hi₂ _)).trans ?_
    simp only [idealTensorPairing, CategoryTheory.Functor.map_id]
    rfl
  have r₄ := tensorSectionPairing_comp_map_pushforwardModuleTensorIso_hom hi₂ F J₂ e₂
  have s₃ : ((PreservesLimitPair.iso D.j.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf (baseRing i₂)) hi₂.I)
          (moduleSheaf (Tensor.ringSheaf (baseRing i₂)) ((thickenedModulesFunctor i₂).obj F))).inv ≫
        D.j.toToposHom.pushforward.map
          (tensorSectionPairing hi₂.I ((thickenedModulesFunctor i₂).obj F))) ≫
      (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map
        (D.basePushforward.map
          (((Tensor.sheafTensor (baseRing i₂)).flip.obj
              ((thickenedModulesFunctor i₂).obj F)).map e₂ ≫
            (pushforwardModuleTensorIso hi₂ F J₂).hom)) =
      (PreservesLimitPair.iso D.j.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf (baseRing i₂)) hi₂.I)
          (moduleSheaf (Tensor.ringSheaf (baseRing i₂)) ((thickenedModulesFunctor i₂).obj F))).inv ≫
        D.j.toToposHom.pushforward.map
          (prod.map ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₂))).map e₂)
              (𝟙 (i₂.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) F))) ≫
            (PreservesLimitPair.iso i₂.toToposHom.pushforward
              (moduleSheaf (Tensor.ringSheaf X.O) J₂) (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
            i₂.toToposHom.pushforward.map (tensorSectionPairing J₂ F)) := by
    refine (congrArg (_ ≫ ·) (D.moduleSheafFunctor_map_basePushforward_map _)).trans ?_
    exact comp_map_comp_map_eq D.j.toToposHom.pushforward _ _ _ _ r₄
  refine (pairing_comp_four_prodMap _ _ _ _ _ _ _ _ r₁ _ _ r₂ _ s₃ _
    (congrArg (_ ≫ ·) (hE _))).trans ?_
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _)

include hE in
/-- **The compatibility of the actions** that
`ThickeningTargetMorphism.extDescentAddEquiv_symm_existenceObstructionClass_eq_comp` takes as its
hypothesis, for any `E : Ψ₀ ∘ i₂_* ≅ i₁_*` which is `θ` on underlying sheaves of sets, from the
compatibility of `eₖ : iₖ_*Jₖ ≅ ℐₖ` with the map of ideals `ℐ₁ ⟶ Ψ₀ℐ₂` and `λ : J₁ ⟶ J₂`. -/
theorem hkey_of_idealMap (F J₁ J₂ : SheafOfModules.{w} (Tensor.ringSheaf X.O)) (lam : J₁ ⟶ J₂)
    (e₁ : (thickenedModulesFunctor i₁).obj J₁ ≅ hi₁.I)
    (e₂ : (thickenedModulesFunctor i₂).obj J₂ ≅ hi₂.I)
    (H : e₁.inv ≫ (thickenedModulesFunctor i₁).map lam =
      D.idealMap hi₁ hi₂ ≫ D.basePushforward.map e₂.inv ≫
        E.hom.app J₂) :
    ((Tensor.sheafTensor (baseRing i₁)).flip.obj
          ((thickenedModulesFunctor i₁).obj F)).map e₁.inv ≫
        (pushforwardModuleTensorIso hi₁ F J₁).hom ≫
          (thickenedModulesFunctor i₁).map (((Tensor.sheafTensor X.O).flip.obj F).map lam) =
      ((Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map
          (E.inv.app F) ≫
        D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F) ≫
          D.basePushforward.map
            (((Tensor.sheafTensor (baseRing i₂)).flip.obj
                ((thickenedModulesFunctor i₂).obj F)).map e₂.inv ≫
              (pushforwardModuleTensorIso hi₂ F J₂).hom) ≫
          E.hom.app
            (((Tensor.sheafTensor X.O).flip.obj F).obj J₂) := by
  have hH := map_comp_eq_map_comp_comp (moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁)))
    _ _ _ _ _ H (moduleSheafFunctor_map_thickenedModulesFunctor_map lam)
    (D.moduleSheafFunctor_map_basePushforward_map e₂.inv)
    (hE J₂)
  refine hom_ext_of_tensorSectionPairing (O := baseRing i₁) (A := hi₁.I)
    (B := (thickenedModulesFunctor i₁).obj F)
    (N := (thickenedModulesFunctor i₁).obj (((Tensor.sheafTensor X.O).flip.obj F).obj J₂)) ?_
  refine (tensorSectionPairing_comp_map_pushforwardModuleTensorIso_hom_map hi₁ F J₁ J₂ lam
    e₁.inv).trans ?_
  refine Eq.trans ?_ (D.tensorSectionPairing_comp_idealTensorMap_action hi₁ hi₂ E θ hE F J₂
    e₂.inv).symm
  exact prodMap_comp_pushPairing_eq_of_natIso i₂.toToposHom.pushforward D.j.toToposHom.pushforward
    i₁.toToposHom.pushforward θ (A := moduleSheaf (Tensor.ringSheaf X.O) J₂)
    (B := moduleSheaf (Tensor.ringSheaf X.O) F)
    (N := moduleSheaf (Tensor.ringSheaf X.O) (((Tensor.sheafTensor X.O).flip.obj F).obj J₂))
    (tensorSectionPairing J₂ F) (I₁ := moduleSheaf (Tensor.ringSheaf (baseRing i₁)) hi₁.I)
    (I₂ := moduleSheaf (Tensor.ringSheaf (baseRing i₂)) hi₂.I)
    ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map (D.idealMap hi₁ hi₂))
    ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₂))).map e₂.inv)
    ((moduleSheafFunctor (Tensor.ringSheaf (baseRing i₁))).map e₁.inv ≫
      i₁.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map lam)) hH

end ThickeningTargetMorphism

end Deformation.ToposThickening

end
