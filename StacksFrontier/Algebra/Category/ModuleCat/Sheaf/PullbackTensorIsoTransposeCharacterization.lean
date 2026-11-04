module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorToposCompBilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep1Apply
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep2Apply

/-!
# The comparison of Tag 03EL characterized by its adjoint transpose

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `F`, `G` two sheaves of
`O_D`-modules. The comparison `c : f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` of [Stacks, Tag 03EL]
(`Stacks.SheafOfModules.pullbackTensorIso`) is the isomorphism determined by the bilinear map
`(s, t) ↦ f^*s ⊗ f^*t`: a morphism `h : f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` is the comparison exactly when
its adjoint transpose `F ⊗ G ⟶ f_*(f^*F ⊗ f^*G)`, read as a bilinear pairing of `F` and `G`, is
the pairing `(s, t) ↦ η(s) ⊗ η(t)`, i.e. the units `η_F × η_G` followed by the direct image of
the universal pairing of `f^*F` and `f^*G`. The condition involves no section of a direct image.

## Main results

* `Stacks.SheafOfModules.eq_pullbackTensorIso_hom_app_iff`: a morphism
  `f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` is the comparison of Tag 03EL if and only if the pairing of its
  adjoint transpose is `(η_F × η_G) ≫ f_*(universal pairing)`.
* `Stacks.SheafOfModules.homEquiv_comp_hom_app_eq_homEquiv_leftAdjointUniq_inv` and
  `Stacks.SheafOfModules.unit_app_comp_hom_app_eq_unit_app_comp_map_leftAdjointUniq_inv`:
  transposes and units across two adjunctions with isomorphic right adjoints.
* `Stacks.SheafOfModules.uncurry_map_inv_comp_map_hom_app_comp_obj_map_hom`: a bifunctor carries a
  pair of inverses followed by the pair of isomorphisms to the identity.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

section Transpose

variable {C : Type*} [Category C] {D : Type*} [Category D] {L L' : C ⥤ D} {R R' : D ⥤ C}

/-- **Transposes across two adjunctions with isomorphic right adjoints.** If `L ⊣ R`,
`L' ⊣ R'` and `β : R ≅ R'`, so that `L ≅ L'` by uniqueness of left adjoints, then the transpose of
`k : L M ⟶ N` along `L ⊣ R`, carried by `β`, is the transpose along `L' ⊣ R'` of `k` precomposed
with the comparison `L' M ⟶ L M`. -/
theorem homEquiv_comp_hom_app_eq_homEquiv_leftAdjointUniq_inv (adj : L ⊣ R) (β : R ≅ R')
    (adj' : L' ⊣ R') (M : C) (N : D) (k : L.obj M ⟶ N) :
    adj.homEquiv M N k ≫ β.hom.app N =
      adj'.homEquiv M N
        ((Adjunction.leftAdjointUniq (adj.ofNatIsoRight β) adj').inv.app M ≫ k) := by
  rw [← Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

/-- **Units across two adjunctions with isomorphic right adjoints.** With the notation of
`homEquiv_comp_hom_app_eq_homEquiv_leftAdjointUniq_inv`, the unit of `L ⊣ R` carried by `β` is the
unit of `L' ⊣ R'` followed by the image of the comparison `L' M ⟶ L M`. -/
theorem unit_app_comp_hom_app_eq_unit_app_comp_map_leftAdjointUniq_inv (adj : L ⊣ R) (β : R ≅ R')
    (adj' : L' ⊣ R') (M : C) :
    adj.unit.app M ≫ β.hom.app (L.obj M) =
      adj'.unit.app M ≫
        R'.map ((Adjunction.leftAdjointUniq (adj.ofNatIsoRight β) adj').inv.app M) := by
  have h := homEquiv_comp_hom_app_eq_homEquiv_leftAdjointUniq_inv adj β adj' M (L.obj M) (𝟙 _)
  rwa [Adjunction.homEquiv_id, Category.comp_id, Adjunction.homEquiv_unit] at h

/-- The image under an uncurried bifunctor of a pair of inverses of isomorphisms, followed by the
images of the isomorphisms one variable at a time, is the identity. -/
theorem uncurry_map_inv_comp_map_hom_app_comp_obj_map_hom {C' E : Type*} [Category C']
    [Category E] (S : C ⥤ C' ⥤ E) {a a' : C} {b b' : C'} (e₁ : a ≅ a') (e₂ : b ≅ b') :
    (Functor.uncurry.obj S).map ((e₁.inv, e₂.inv) : ((a', b') : C × C') ⟶ (a, b)) ≫
        (S.map e₁.hom).app b ≫ (S.obj a').map e₂.hom = 𝟙 _ := by
  show ((S.map e₁.inv).app b' ≫ (S.obj a).map e₂.inv) ≫ (S.map e₁.hom).app b ≫
    (S.obj a').map e₂.hom = 𝟙 _
  rw [Category.assoc, ← Category.assoc ((S.obj a).map e₂.inv), (S.map e₁.hom).naturality e₂.inv,
    Category.assoc, ← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, ← Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end Transpose

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **The comparison of Tag 03EL is characterized by its adjoint transpose.** A morphism
`h : f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` is the comparison of Stacks 03EL if and only if its adjoint
transpose under Stacks 03D7, restricted along the sheafification unit and read as a bilinear
pairing of `F` and `G`, is the pairing that sends two local sections to the tensor of their images
under the unit `η` of Stacks 03D7: the product of the two units followed by the direct image of
the universal pairing of `f^*F` and `f^*G`. -/
theorem eq_pullbackTensorIso_hom_app_iff
    (h : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        f.pullbackModules).obj (F, G) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G)) :
    h = (pullbackTensorIso f).hom.app (F, G) ↔
      pairingOfTensorHom (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
          ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (𝟙 _)).unit.app
              (F.val ⊗ G.val) ≫
            ((pullbackAdjPushforwardModules f).unit.app
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj
                  (F, G)) ≫
              (pushforwardModules f).map h).val) =
        prod.map
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
              ((pullbackAdjPushforwardModules f).unit.app F))
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
              ((pullbackAdjPushforwardModules f).unit.app G)) ≫
          ((PreservesLimitPair.iso f.toToposHom.pushforward
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                  ((f.pullbackModules).obj F))
                (moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                  ((f.pullbackModules).obj G))).inv ≫
            f.toToposHom.pushforward.map
              (tensorSectionPairing ((f.pullbackModules).obj F) ((f.pullbackModules).obj G))) := by
  let N := ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
    ((f.pullbackModules).obj F, (f.pullbackModules).obj G)
  have hc := pullbackTensorHomEquiv_pullbackTensorIso_hom f F G
  have hT : ((pullbackTensorStepTarget f F G N).symm (𝟙 N)).1 =
      tensorSectionPairing ((f.pullbackModules).obj F) ((f.pullbackModules).obj G) :=
    bilinearEquivTensorSheafHom_symm_id_coe
      (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
      (F := (f.pullbackModules).obj F) (G := (f.pullbackModules).obj G)
  have hB := pullbackTensorBilinEquiv_symm_apply_coe_eq_prodMap_unit f F G N
    ((pullbackTensorStepTarget f F G N).symm (𝟙 N))
  rw [hT] at hB
  have key : h = (pullbackTensorIso f).hom.app (F, G) ↔
      pullbackTensorStep2 f F G N (pullbackTensorStep1 f F G N h) =
        (pullbackTensorBilinEquiv f F G N).symm
          ((pullbackTensorStepTarget f F G N).symm (𝟙 N)) := by
    rw [← (pullbackTensorHomEquiv f F G N).apply_eq_iff_eq, hc, pullbackTensorHomEquiv_apply,
      ← (pullbackTensorStepTarget f F G N).eq_symm_apply,
      ← (pullbackTensorBilinEquiv f F G N).eq_symm_apply]
  rw [key, pullbackTensorStep1_apply, pullbackTensorStep2_apply, Subtype.ext_iff, hB]
  exact Iff.rfl

end Stacks.SheafOfModules

end
