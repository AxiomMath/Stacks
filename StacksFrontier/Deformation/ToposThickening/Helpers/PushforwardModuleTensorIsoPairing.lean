module

public import StacksFrontier.Deformation.ToposThickening.Helpers.ExtDescentTensorPairing
public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffinePushforwardTilde

/-!
# The pairing of the descent of tensor products along a first order thickening

For a first order thickening `i : X ⟶ Y`, the identification
`i_*J ⊗_{i_*O} i_*F ≅ i_*(J ⊗_O F)` of `Deformation.ToposThickening.pushforwardModuleTensorIso`
pairs two local sections of `i_*J` and `i_*F` by `i_*` of the universal pairing of `J` and `F`
(`Deformation.ToposThickening.tensorSectionPairing_comp_pushforwardModuleTensorIso_hom`).

The computation goes through the projection-formula map of a morphism of ringed topoi followed
by `f_*` of a map `f^*A ⟶ J` tensored with `F`
(`Stacks.SheafOfModules.tensorSectionPairing_comp_pushforwardTensorMap_comp_map_flip_map`), which
is stated for an arbitrary morphism so that only one spelling of each ring occurs in it.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 01E6](https://stacks.math.columbia.edu/tag/01E6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry (RingedTopos)

universe v u v' u' w w'

namespace Stacks.SheafOfModules

section ProjectionFormula

open Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- `f_*` of a morphism of modules, on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModules_map
    {M M' : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (m : M ⟶ M') :
    (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map ((pushforwardModules f).map m) =
      f.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map m) :=
  Sheaf.hom_ext_sections fun _ _ => rfl

/-- **The pairing of the projection-formula map followed by `f_*(c ⊗ F)`**, for `c : f^*A ⟶ J`:
two local sections of `A` and `f_*F` are paired by `f_*` of the universal pairing of `J` and
`F`, applied to the image of the first under the adjunct `A ⟶ f_*J` of `c` and to the second. -/
theorem tensorSectionPairing_comp_pushforwardTensorMap_comp_map_flip_map
    (A : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (F J : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) (c : f.pullbackModules.obj A ⟶ J) :
    tensorSectionPairing A ((pushforwardModules f).obj F) ≫
        (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map (pushforwardTensorMap f A F ≫
          (pushforwardModules f).map (((Tensor.sheafTensor X.O).flip.obj F).map c)) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app A ≫ (pushforwardModules f).map c)) (𝟙 _) ≫
        (PreservesLimitPair.iso f.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf X.O) J) (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
        f.toToposHom.pushforward.map (tensorSectionPairing J F) := by
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    tensorSectionPairing_comp_pushforwardTensorMap, moduleSheafFunctor_map_pushforwardModules_map,
    CategoryTheory.Functor.map_comp, moduleSheafFunctor_map_pushforwardModules_map]
  exact prodMap_comp_preservesLimitPair_iso_inv_comp_map_comp_left _ _ _ _ _ _ _
    (tensorSectionPairing_comp_map_left (B := F) c)

/-- A pairing followed by four morphisms, computed in three steps. -/
theorem pairing_comp_four {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (G : 𝒞 ⥤ 𝒟) {P P₁ : 𝒟}
    {T₀ T₁ T₂ T₃ T₄ : 𝒞} (t₀ : P ⟶ G.obj T₀) (a₁ : T₀ ⟶ T₁) (a₂ : T₁ ⟶ T₂) (a₃ : T₂ ⟶ T₃)
    (a₄ : T₃ ⟶ T₄) (p : P ⟶ P₁) (t₁ : P₁ ⟶ G.obj T₁) (s₁ : t₀ ≫ G.map a₁ = p ≫ t₁)
    (r : P₁ ⟶ G.obj T₃) (s₂ : t₁ ≫ G.map (a₂ ≫ a₃) = r) (r' : P ⟶ G.obj T₄)
    (s₃ : p ≫ r ≫ G.map a₄ = r') :
    t₀ ≫ G.map (a₁ ≫ a₂ ≫ a₃ ≫ a₄) = r' := by
  rw [← Category.assoc a₂ a₃ a₄, G.map_comp, G.map_comp, ← Category.assoc, s₁, Category.assoc,
    ← Category.assoc t₁, s₂, s₃]

/-- Two maps of products that are the identity in each factor cancel in front of a morphism. -/
theorem prodMap_id_comp_prodMap_comp_id {𝒟 : Type*} [Category* 𝒟] {A B Z : 𝒟}
    [HasBinaryProduct A B] (a : A ⟶ A) (b : B ⟶ B) (ha : a = 𝟙 A) (hb : b = 𝟙 B)
    (q : A ⨯ B ⟶ Z) : prod.map (𝟙 A) b ≫ prod.map a (𝟙 B) ≫ q = q := by
  subst ha hb
  simp only [prod.map_id_id, Category.id_comp]

/-- A morphism followed by an endomorphism that is the identity. -/
theorem comp_comp_eq_of_eq_id {𝒟 : Type*} [Category* 𝒟] {P Q W : 𝒟} (p : P ⟶ Q) (r : Q ⟶ W)
    (m : W ⟶ W) (hm : m = 𝟙 W) (r' : P ⟶ W) (h : p ≫ r = r') : p ≫ r ≫ m = r' := by
  subst hm
  rw [Category.comp_id, h]

end ProjectionFormula

section TwoField

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- The comparison `f_*M ⟶ π_*M` of the two direct images of modules along a morphism of
ringed topoi is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_toModulesPushforwardIso_inv_app_eq_id
    (M : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map (f.toModulesPushforwardIso.inv.app M) =
      𝟙 (f.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) M)) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _

/-- The comparison `π_*M ⟶ f_*M` of the two direct images of modules along a morphism of
ringed topoi is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id
    (M : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map (f.toModulesPushforwardIso.hom.app M) =
      𝟙 (f.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) M)) :=
  Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _

end TwoField

end Stacks.SheafOfModules

namespace Deformation.ToposThickening

open Stacks.SheafOfModules Stacks.Sheaves.ToposPushforward

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : AlgebraicGeometry.RingedToposHom X Y} (hi : FirstOrderThickening i)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- `π^*i_*J ≅ J` is `π^*` of `i_*J ≅ π_*J` followed by the counit of `π^* ⊣ π_*`. -/
theorem pullbackPushforwardModuleNatIso_hom_app
    (J : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (pullbackPushforwardModuleNatIso hi).hom.app J =
      (pushforwardModulesHom i).pullbackModules.map ((pushforwardModulesHomIso i).inv.app J) ≫
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          (pushforwardModulesHom i)).counit.app J :=
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison `i_*M ⟶ π_*M` is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesHomIso_inv_app
    (M : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
      ((pushforwardModulesHomIso i).inv.app M) =
      𝟙 (i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) M)) :=
  moduleSheafFunctor_map_toModulesPushforwardIso_inv_app_eq_id (pushforwardRingToposHom i X.O) M

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison `π_*M ⟶ i_*M` is the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesHomIso_hom_app
    (M : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
      ((pushforwardModulesHomIso i).hom.app M) =
      𝟙 (i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) M)) :=
  moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id (pushforwardRingToposHom i X.O) M

/-- **The pairing of `i_*J ⊗ i_*F ≅ i_*(J ⊗ F)`**: two local sections of `i_*J` and `i_*F` are
paired by `i_*` of the universal pairing of `J` and `F`. -/
theorem tensorSectionPairing_comp_pushforwardModuleTensorIso_hom
    (F J : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    tensorSectionPairing ((thickenedModulesFunctor i).obj J) ((thickenedModulesFunctor i).obj F) ≫
        (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
          (pushforwardModuleTensorIso hi F J).hom =
      (PreservesLimitPair.iso i.toToposHom.pushforward (moduleSheaf (Tensor.ringSheaf X.O) J)
          (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
        i.toToposHom.pushforward.map (tensorSectionPairing J F) := by
  rw [pushforwardModuleTensorIso_hom_eq hi F J, pullbackPushforwardModuleNatIso_hom_app hi J]
  set c := (pushforwardModulesHom i).pullbackModules.map ((pushforwardModulesHomIso i).inv.app J) ≫
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (pushforwardModulesHom i)).counit.app J with hcdef
  have S2 := tensorSectionPairing_comp_pushforwardTensorMap_comp_map_flip_map
    (pushforwardModulesHom i) ((thickenedModulesFunctor i).obj J) F J c
  have hc : (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          (pushforwardModulesHom i)).unit.app ((thickenedModulesFunctor i).obj J) ≫
        (Stacks.Sheaves.RingedToposModules.pushforwardModules (pushforwardModulesHom i)).map c) =
      𝟙 (i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) J)) := by
    rw [hcdef, CategoryTheory.Adjunction.unit_app_comp_map_map_comp_counit_app]
    exact moduleSheafFunctor_map_pushforwardModulesHomIso_inv_app J
  refine pairing_comp_four _ _ _ _ _ _ _ _ (tensorSectionPairing_comp_map_right _) _ S2 _ ?_
  refine comp_comp_eq_of_eq_id
    (W := i.toToposHom.pushforward.obj
      (moduleSheaf (Tensor.ringSheaf X.O) (((Tensor.sheafTensor X.O).flip.obj F).obj J))) _ _ _
    (moduleSheafFunctor_map_pushforwardModulesHomIso_hom_app _) _ ?_
  exact prodMap_id_comp_prodMap_comp_id
    (A := i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) J))
    (B := i.toToposHom.pushforward.obj (moduleSheaf (Tensor.ringSheaf X.O) F)) _ _ hc
    (moduleSheafFunctor_map_pushforwardModulesHomIso_inv_app F) _

end Deformation.ToposThickening

end
