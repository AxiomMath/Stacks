module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIsoTransposeCharacterization
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackRestrictionUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackPushforwardUnitTensorMul
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartSectionsTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnitTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeChartIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProjectionSpellingAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartSectionMul

/-!
# The affine base change isomorphism of `π_*𝒪_Y` respects the multiplications

For a cartesian square of algebraic spaces with `π : Y ⟶ X` affine, the affine base change
isomorphism `β : g^*(π_*𝒪_Y) ≅ π'_*𝒪_{Y'}`
(`AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso`) carries the
pullback of the multiplication of the algebra `π_*𝒪_Y` to the multiplication of `π'_*𝒪_{Y'}`,
through the comparison `g^*(F ⊗ F) ≅ g^*F ⊗ g^*F` of Stacks 03EL:
`AlgebraicGeometry.Space.modulePullback_map_pushforwardUnitTensorMulHom_comp_unitIso_hom`.

The proof passes to the transpose `β♭ : π_*𝒪_Y ⟶ g_*(π'_*𝒪_{Y'})` along the adjunction of
Stacks 03D7 and to the pairings of the tensor products: it suffices that `β♭` is multiplicative
on local sections, and this is checked after the jointly injective chart projections of the
direct image along `g`. At a chart diagram `d` over `g`, the chart projection of `β♭` is pullback
of regular functions along the morphism of base-changed charts `d.U ×_{X'} Y' ⟶ d.V ×_X Y`,
a ring homomorphism.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
  CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

section Site

universe v₀ u₀ w₀

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [J.HasSheafCompose (forget RingCat.{w₀})] [J.HasSheafCompose (forget AddCommGrpCat.{w₀})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w₀}] [HasWeakSheafify J AddCommGrpCat.{w₀}]
  {O : Sheaf J CommRingCat.{w₀}}

/-- The pairing of a morphism out of a tensor product sheaf: two local sections are paired to the
value of the morphism on the sheafification-unit image of their tensor. -/
private abbrev tensorHomPairing {A B N : SheafOfModules.{w₀} (Tensor.ringSheaf O)}
    (t : ((Tensor.sheafTensor O).obj A).obj B ⟶ N) :
    moduleSheaf (Tensor.ringSheaf O) A ⨯ moduleSheaf (Tensor.ringSheaf O) B ⟶
      moduleSheaf (Tensor.ringSheaf O) N :=
  pairingOfTensorHom (hO := (Tensor.ringSheaf O).property) (tensorHomEquivPresheafTensorHom t)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.HasSheafCompose (forget RingCat)]
  [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The morphism of presheaves out of the presheaf tensor product attached to a morphism out of
the tensor product sheaf is its composite with the sheafification unit. -/
private theorem tensorHomEquivPresheafTensorHom_eq_unit_comp
    {A B N : SheafOfModules.{w₀} (Tensor.ringSheaf O)}
    (t : ((Tensor.sheafTensor O).obj A).obj B ⟶ N) :
    tensorHomEquivPresheafTensorHom t =
      (PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O) (𝟙 _)).unit.app
        (A.val ⊗ B.val) ≫ t.val :=
  (PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O) (𝟙 _)).homEquiv_unit _ _ t

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A morphism out of a tensor product sheaf is determined by its pairing. -/
private theorem eq_of_tensorHomPairing_eq {A B N : SheafOfModules.{w₀} (Tensor.ringSheaf O)}
    {t₁ t₂ : ((Tensor.sheafTensor O).obj A).obj B ⟶ N}
    (h : tensorHomPairing t₁ = tensorHomPairing t₂) : t₁ = t₂ :=
  tensorHomEquivPresheafTensorHom.injective
    ((bilinearEquivPresheafTensorHom (hO := (Tensor.ringSheaf O).property)
      (A := A) (B := B) (N := N)).symm.injective (Subtype.ext h))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The pairing of a composite `t ≫ m` is the pairing of `t` followed by `m`. -/
private theorem tensorHomPairing_comp {A B N N' : SheafOfModules.{w₀} (Tensor.ringSheaf O)}
    (t : ((Tensor.sheafTensor O).obj A).obj B ⟶ N) (m : N ⟶ N') :
    tensorHomPairing (t ≫ m) =
      tensorHomPairing t ≫ (moduleSheafFunctor (Tensor.ringSheaf O)).map m :=
  (congrArg (pairingOfTensorHom (hO := (Tensor.ringSheaf O).property))
    ((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O)
      (𝟙 _)).homEquiv_naturality_right t m)).trans
    (pairingOfTensorHom_comp (hO := (Tensor.ringSheaf O).property) _ m)

section Pairing

variable {P : Cᵒᵖ ⥤ CommRingCat.{w₀}}
  {hP : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf P)}

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify J AddCommGrpCat] in
/-- The pairing of `(u ⊗ v) ≫ t` is `u × v` followed by the pairing of `t`. -/
private theorem pairingOfTensorHom_tensorHom_comp
    {A A' B B' N : SheafOfModules.{w₀} (commRingSheaf J P hP)}
    (u : A ⟶ A') (v : B ⟶ B') (t : A'.val ⊗ B'.val ⟶ N.val) :
    pairingOfTensorHom (hO := hP) (PresheafOfModules.tensorHom (O := P) u.val v.val ≫ t) =
      prod.map ((moduleSheafFunctor (commRingSheaf J P hP)).map u)
          ((moduleSheafFunctor (commRingSheaf J P hP)).map v) ≫
        pairingOfTensorHom (hO := hP) t := by
  refine hom_ext_prod fun V a b ↦ ?_
  have e1 : (sectionsFunctor J V).map (pairingOfTensorHom (hO := hP)
        (PresheafOfModules.tensorHom (O := P) u.val v.val ≫ t)) (Functor.prodObjMk a b) =
      t.app V (u.val.app V a ⊗ₜ[(P ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀}).obj V]
        v.val.app V b) :=
    pairingApp_pairingOfTensorHom (hO := hP) _ V a b
  have e2 : (sectionsFunctor J V).map (pairingOfTensorHom (hO := hP) t)
        (Functor.prodObjMk ((sectionsFunctor J V).map
          ((moduleSheafFunctor (commRingSheaf J P hP)).map u) a)
          ((sectionsFunctor J V).map ((moduleSheafFunctor (commRingSheaf J P hP)).map v) b)) =
      t.app V (u.val.app V a ⊗ₜ[(P ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀}).obj V]
        v.val.app V b) :=
    pairingApp_pairingOfTensorHom (hO := hP) t V _ _
  have hp : (sectionsFunctor J V).map (prod.map ((moduleSheafFunctor (commRingSheaf J P hP)).map u)
        ((moduleSheafFunctor (commRingSheaf J P hP)).map v)) (Functor.prodObjMk a b) =
      Functor.prodObjMk ((sectionsFunctor J V).map
          ((moduleSheafFunctor (commRingSheaf J P hP)).map u) a)
        ((sectionsFunctor J V).map ((moduleSheafFunctor (commRingSheaf J P hP)).map v) b) := by
    rw [Functor.map_prodMap_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
  refine e1.trans (e2.symm.trans ?_)
  refine Eq.trans ?_ ((sectionsFunctor J V).map_comp_apply _ _ _).symm
  exact congrArg ((sectionsFunctor J V).map (pairingOfTensorHom (hO := hP) t)) hp.symm

end Pairing

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The pairing of `(u ⊗ 𝟙) ≫ (𝟙 ⊗ v) ≫ t` is `u × v` followed by the pairing of `t`. -/
private theorem tensorHomPairing_map_comp_obj_map_comp
    {A A' B B' N : SheafOfModules.{w₀} (Tensor.ringSheaf O)}
    (u : A ⟶ A') (v : B ⟶ B') (t : ((Tensor.sheafTensor O).obj A').obj B' ⟶ N) :
    tensorHomPairing (((Tensor.sheafTensor O).map u).app B ≫
        ((Tensor.sheafTensor O).obj A').map v ≫ t) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf O)).map u)
          ((moduleSheafFunctor (Tensor.ringSheaf O)).map v) ≫ tensorHomPairing t := by
  have h1 : tensorHomEquivPresheafTensorHom (((Tensor.sheafTensor O).map u).app B ≫
        ((Tensor.sheafTensor O).obj A').map v ≫ t) =
      PresheafOfModules.tensorHom (O := O.obj) u.val (𝟙 B.val) ≫
        tensorHomEquivPresheafTensorHom (((Tensor.sheafTensor O).obj A').map v ≫ t) :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Tensor.ringSheaf O).obj)).homEquiv_naturality_left _ _
  have h2 : tensorHomEquivPresheafTensorHom (((Tensor.sheafTensor O).obj A').map v ≫ t) =
      PresheafOfModules.tensorHom (O := O.obj) (𝟙 A'.val) v.val ≫
        tensorHomEquivPresheafTensorHom t :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Tensor.ringSheaf O).obj)).homEquiv_naturality_left _ _
  have h3 : PresheafOfModules.tensorHom (O := O.obj) u.val (𝟙 B.val) ≫
        PresheafOfModules.tensorHom (O := O.obj) (𝟙 A'.val) v.val =
      PresheafOfModules.tensorHom (O := O.obj) u.val v.val := by
    ext U : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun a b => ?_
    rfl
  exact (congrArg (pairingOfTensorHom (hO := (Tensor.ringSheaf O).property))
    (h1.trans ((congrArg (_ ≫ ·) h2).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) h3))))).trans
      (pairingOfTensorHom_tensorHom_comp (hP := (Tensor.ringSheaf O).property) u v _)

end Site


section Iso

universe v₁ v₂ u₁ u₂

/-- The inverse of the product comparison is natural. -/
private theorem preservesLimitPair_iso_inv_comp_map_prodMap {C₁ : Type u₁} [Category.{v₁} C₁]
    {D₁ : Type u₂} [Category.{v₂} D₁] (G : C₁ ⥤ D₁) {A A' B B' : C₁} [HasBinaryProduct A B]
    [HasBinaryProduct A' B'] [HasBinaryProduct (G.obj A) (G.obj B)]
    [HasBinaryProduct (G.obj A') (G.obj B')] [PreservesLimit (pair A B) G]
    [PreservesLimit (pair A' B') G] (p : A ⟶ A') (q : B ⟶ B') :
    (PreservesLimitPair.iso G A B).inv ≫ G.map (prod.map p q) =
      prod.map (G.map p) (G.map q) ≫ (PreservesLimitPair.iso G A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, PreservesLimitPair.iso_hom,
    PreservesLimitPair.iso_hom, prodComparison_natural]

/-- A pairing transported through a product-preserving functor, followed by the image of a
morphism, when the pairing followed by that morphism factors through a product map. -/
private theorem prodMap_comp_iso_inv_comp_map_comp_map {C₁ : Type u₁} [Category.{v₁} C₁]
    {D₁ : Type u₂} [Category.{v₂} D₁] (G : C₁ ⥤ D₁) [HasBinaryProducts C₁]
    [HasBinaryProducts D₁] [PreservesLimitsOfShape (Discrete WalkingPair) G]
    {P Q T M : C₁} {W : D₁} (a : W ⟶ G.obj P) (b : P ⟶ Q) (t : P ⨯ P ⟶ T)
    (m : T ⟶ M) (n : Q ⨯ Q ⟶ M) (h : t ≫ m = prod.map b b ≫ n) :
    (prod.map a a ≫ (PreservesLimitPair.iso G P P).inv ≫ G.map t) ≫ G.map m =
      prod.map (a ≫ G.map b) (a ≫ G.map b) ≫ (PreservesLimitPair.iso G Q Q).inv ≫ G.map n := by
  rw [Category.assoc, Category.assoc, ← G.map_comp, h, G.map_comp,
    reassoc_of% (preservesLimitPair_iso_inv_comp_map_prodMap G b b), prod.map_map_assoc]

end Iso

section RingedTopos

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

omit [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [Y.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- On underlying sheaves of sets, the direct image of a morphism of modules is the direct image
of the underlying morphism. -/
private theorem moduleSheafFunctor_map_pushforwardModules_map_eq_pushforward_map
    {M N : SheafOfModules.{w} (Tensor.ringSheaf X.O)}
    (α : M ⟶ N) :
    (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map ((pushforwardModules f).map α) =
      f.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map α) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The pairing of the transpose of `f^*μ ≫ β`. -/
private theorem tensorHomPairing_homEquiv_pullbackModules_map_comp
    (F : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (F' : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (μ : ((Tensor.sheafTensor Y.O).obj F).obj F ⟶ F) (β : f.pullbackModules.obj F ⟶ F') :
    tensorHomPairing ((pullbackAdjPushforwardModules f).homEquiv _ _
        (f.pullbackModules.map μ ≫ β)) =
      tensorHomPairing μ ≫ (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β) :=
  (congrArg tensorHomPairing (((pullbackAdjPushforwardModules f).homEquiv_naturality_left μ β).trans
    (congrArg (μ ≫ ·) ((pullbackAdjPushforwardModules f).homEquiv_unit F F' β)))).trans
    (tensorHomPairing_comp μ _)

/-- The pairing of the transpose of `δ ≫ (β ⊗ β) ≫ μ'`, `δ` the comparison of Stacks 03EL. -/
private theorem tensorHomPairing_homEquiv_pullbackTensorIso_comp
    (F : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (F' : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (β : f.pullbackModules.obj F ⟶ F') (μ' : ((Tensor.sheafTensor X.O).obj F').obj F' ⟶ F') :
    tensorHomPairing ((pullbackAdjPushforwardModules f).homEquiv _ _
        ((pullbackTensorIso f).hom.app (F, F) ≫
          ((Tensor.sheafTensor X.O).map β).app (f.pullbackModules.obj F) ≫
          ((Tensor.sheafTensor X.O).obj F').map β ≫ μ')) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β))
          ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β)) ≫
        (PreservesLimitPair.iso f.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf X.O) F') (moduleSheaf (Tensor.ringSheaf X.O) F')).inv ≫
        f.toToposHom.pushforward.map (tensorHomPairing μ') := by
  have s1 := (pullbackAdjPushforwardModules f).homEquiv_naturality_right
    ((pullbackTensorIso f).hom.app (F, F))
    (((Tensor.sheafTensor X.O).map β).app (f.pullbackModules.obj F) ≫
      ((Tensor.sheafTensor X.O).obj F').map β ≫ μ')
  have s2 :=
    (pullbackAdjPushforwardModules f).homEquiv_unit _ _ ((pullbackTensorIso f).hom.app (F, F))
  have s3 := (eq_pullbackTensorIso_hom_app_iff f F F ((pullbackTensorIso f).hom.app (F, F))).mp rfl
  have s3' : tensorHomPairing ((pullbackAdjPushforwardModules f).unit.app _ ≫
      (pushforwardModules f).map ((pullbackTensorIso f).hom.app (F, F))) = _ :=
    (congrArg (pairingOfTensorHom (hO := (Tensor.ringSheaf Y.O).property))
      (tensorHomEquivPresheafTensorHom_eq_unit_comp _)).trans s3
  have s5 : tensorSectionPairing (f.pullbackModules.obj F) (f.pullbackModules.obj F) ≫
      (moduleSheafFunctor (Tensor.ringSheaf X.O)).map
        (((Tensor.sheafTensor X.O).map β).app (f.pullbackModules.obj F) ≫
          ((Tensor.sheafTensor X.O).obj F').map β ≫ μ') =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map β)
        ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map β) ≫ tensorHomPairing μ' :=
    (pairingOfTensorHom_comp (hO := (Tensor.ringSheaf X.O).property) _ _).symm.trans
      ((congrArg (pairingOfTensorHom (hO := (Tensor.ringSheaf X.O).property))
        (tensorHomEquivPresheafTensorHom_eq_unit_comp _).symm).trans
        (tensorHomPairing_map_comp_obj_map_comp β β μ'))
  refine ((congrArg tensorHomPairing s1).trans ((tensorHomPairing_comp _ _).trans
    ((congrArg (fun z => tensorHomPairing z ≫ _) s2).trans ((congrArg (· ≫ _) s3').trans
      (congrArg (_ ≫ ·)
        (moduleSheafFunctor_map_pushforwardModules_map_eq_pushforward_map f _)))))).trans ?_
  have hf : (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F) ≫
      f.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map β) =
      (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β) :=
    (congrArg (_ ≫ ·)
        (moduleSheafFunctor_map_pushforwardModules_map_eq_pushforward_map f β).symm).trans
      ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map_comp _ _).symm
  refine (prodMap_comp_iso_inv_comp_map_comp_map f.toToposHom.pushforward _ _ _ _ _ s5).trans ?_
  exact congrArg (fun z => prod.map z z ≫ _) hf

/-- **A morphism `β : f^*F ⟶ F'` respects two multiplications as soon as its transpose does.**
For multiplications `μ : F ⊗ F ⟶ F` and `μ' : F' ⊗ F' ⟶ F'`, if the transpose `β♭ : F ⟶ f_*F'`
carries the product of two local sections to the product, under `f_*μ'`, of their images, then
`f^*μ ≫ β = δ ≫ (β ⊗ β) ≫ μ'`, `δ` the comparison of Stacks 03EL. -/
private theorem pullbackModules_map_comp_eq_pullbackTensorIso_comp_of_tensorHomPairing
    (F : SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (F' : SheafOfModules.{w} (Tensor.ringSheaf X.O))
    (μ : ((Tensor.sheafTensor Y.O).obj F).obj F ⟶ F)
    (μ' : ((Tensor.sheafTensor X.O).obj F').obj F' ⟶ F') (β : f.pullbackModules.obj F ⟶ F')
    (h : tensorHomPairing μ ≫ (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β))
          ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β)) ≫
        (PreservesLimitPair.iso f.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf X.O) F') (moduleSheaf (Tensor.ringSheaf X.O) F')).inv ≫
        f.toToposHom.pushforward.map (tensorHomPairing μ')) :
    f.pullbackModules.map μ ≫ β =
      (pullbackTensorIso f).hom.app (F, F) ≫
        ((Tensor.sheafTensor X.O).map β).app (f.pullbackModules.obj F) ≫
        ((Tensor.sheafTensor X.O).obj F').map β ≫ μ' :=
  ((pullbackAdjPushforwardModules f).homEquiv _ _).injective
    (eq_of_tensorHomPairing_eq
      ((tensorHomPairing_homEquiv_pullbackModules_map_comp f F F' μ β).trans
        (h.trans (tensorHomPairing_homEquiv_pullbackTensorIso_comp f F F' β μ').symm)))

end RingedTopos

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules

section NaturalFamily

universe v₁ v₂ u₁ u₂ w₁

variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {J : GrothendieckTopology C₁} {K : GrothendieckTopology D₁}
  (G : Sheaf K (Type w₁) ⥤ Sheaf J (Type w₁)) [PreservesLimitsOfShape (Discrete WalkingPair) G]

/-- A natural family of maps out of the sections of `G` carries the product comparison of `G` to
the pairing of sections. -/
private theorem natural_family_iso_inv_prodObjMk {U : C₁ᵒᵖ} {Q : D₁ᵒᵖ}
    (θ : ∀ F : Sheaf K (Type w₁), (G.obj F).obj.obj U → F.obj.obj Q)
    (hθ : ∀ {F F' : Sheaf K (Type w₁)} (m : F ⟶ F') (x : (G.obj F).obj.obj U),
      θ F' ((G.map m).hom.app U x) = m.hom.app Q (θ F x))
    {F : Sheaf K (Type w₁)} (x y : (G.obj F).obj.obj U) :
    θ (F ⨯ F) ((PreservesLimitPair.iso G F F).inv.hom.app U
        (Functor.prodObjMk (P := sectionsFunctor.{w₁} J U) x y)) =
      Functor.prodObjMk (P := sectionsFunctor.{w₁} K Q) (θ F x) (θ F y) := by
  refine Functor.prodObjMk_ext (P := sectionsFunctor.{w₁} K Q) ?_ ?_
  · refine (hθ prod.fst _).symm.trans ?_
    refine Eq.trans ?_ (Functor.map_fst_prodObjMk (P := sectionsFunctor.{w₁} K Q) _ _).symm
    refine congrArg (θ F) ?_
    have h := congrArg (fun t => (sectionsFunctor.{w₁} J U).map t
      (Functor.prodObjMk (P := sectionsFunctor.{w₁} J U) x y))
      (PreservesLimitPair.iso_inv_fst G F F)
    exact h.trans (Functor.map_fst_prodObjMk (P := sectionsFunctor.{w₁} J U) x y)
  · refine (hθ prod.snd _).symm.trans ?_
    refine Eq.trans ?_ (Functor.map_snd_prodObjMk (P := sectionsFunctor.{w₁} K Q) _ _).symm
    refine congrArg (θ F) ?_
    have h := congrArg (fun t => (sectionsFunctor.{w₁} J U).map t
      (Functor.prodObjMk (P := sectionsFunctor.{w₁} J U) x y))
      (PreservesLimitPair.iso_inv_snd G F F)
    exact h.trans (Functor.map_snd_prodObjMk (P := sectionsFunctor.{w₁} J U) x y)

/-- **A morphism into `G` of sheaves of sets is multiplicative as soon as it is so after a jointly
injective natural family of projections.**  For pairings `m : A ⨯ A ⟶ A` and
`m' : A' ⨯ A' ⟶ A'` and `ξ : A ⟶ G A'`, if every projection `θ_j` of `ξ(m(a, b))` is
`m'(θ_j(ξ a), θ_j(ξ b))`, then `m ≫ ξ = (ξ × ξ) ≫ G(A' ⨯ A') ≅ G A' ⨯ G A' ≫ G m'`. -/
private theorem comp_eq_prodMap_comp_iso_inv_comp_map_of_natural_family
    (ι : C₁ᵒᵖ → Type*) (Qj : ∀ U, ι U → D₁ᵒᵖ)
    (θ : ∀ (U : C₁ᵒᵖ) (j : ι U) (F : Sheaf K (Type w₁)), (G.obj F).obj.obj U → F.obj.obj (Qj U j))
    (hθ : ∀ (U : C₁ᵒᵖ) (j : ι U) {F F' : Sheaf K (Type w₁)} (m : F ⟶ F')
      (x : (G.obj F).obj.obj U), θ U j F' ((G.map m).hom.app U x) = m.hom.app (Qj U j) (θ U j F x))
    (hinj : ∀ (U : C₁ᵒᵖ) {F : Sheaf K (Type w₁)} (x y : (G.obj F).obj.obj U),
      (∀ j, θ U j F x = θ U j F y) → x = y)
    {A : Sheaf J (Type w₁)} {A' : Sheaf K (Type w₁)} (m : A ⨯ A ⟶ A) (m' : A' ⨯ A' ⟶ A')
    (ξ : A ⟶ G.obj A')
    (h : ∀ (U : C₁ᵒᵖ) (j : ι U) (a b : A.obj.obj U),
      θ U j A' (ξ.hom.app U (m.hom.app U (Functor.prodObjMk (P := sectionsFunctor.{w₁} J U) a b))) =
        m'.hom.app (Qj U j) (Functor.prodObjMk (P := sectionsFunctor.{w₁} K (Qj U j))
          (θ U j A' (ξ.hom.app U a)) (θ U j A' (ξ.hom.app U b)))) :
    m ≫ ξ = prod.map ξ ξ ≫ (PreservesLimitPair.iso G A' A').inv ≫ G.map m' := by
  refine Sheaf.hom_ext_sections fun U s => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b, s = Functor.prodObjMk (P := sectionsFunctor.{w₁} J U) a b :=
    ⟨_, _, (Functor.prodObjMk_map_fst_map_snd s).symm⟩
  refine hinj U _ _ fun j => ?_
  refine (h U j a b).trans ?_
  have hp : (sectionsFunctor.{w₁} J U).map (prod.map ξ ξ)
      (Functor.prodObjMk (P := sectionsFunctor.{w₁} J U) a b) =
      Functor.prodObjMk (P := sectionsFunctor.{w₁} J U) (ξ.hom.app U a) (ξ.hom.app U b) := by
    rw [Functor.map_prodMap_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
    rfl
  rw [Functor.map_comp_apply, Functor.map_comp_apply, hp]
  exact ((hθ U j m' _).trans (congrArg (m'.hom.app (Qj U j))
    (natural_family_iso_inv_prodObjMk G (θ U j) (hθ U j) _ _))).symm

end NaturalFamily

section Combined

universe v₃ u₃ v₄ u₄ w₃

variable {X : RingedTopos.{v₃, u₃, w₃}} {Y : RingedTopos.{v₄, u₄, w₃}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget RingCat.{w₃})] [Y.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X.J AddCommGrpCat.{w₃}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w₃}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₃}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **A morphism `β : f^*F ⟶ F'` respects two multiplications as soon as its transpose does
after a jointly injective natural family of projections of the direct image.** -/
private theorem pullbackModules_map_comp_eq_pullbackTensorIso_comp_of_natural_family
    (F : SheafOfModules.{w₃} (Tensor.ringSheaf Y.O))
    (F' : SheafOfModules.{w₃} (Tensor.ringSheaf X.O))
    (μ : ((Tensor.sheafTensor Y.O).obj F).obj F ⟶ F)
    (μ' : ((Tensor.sheafTensor X.O).obj F').obj F' ⟶ F') (β : f.pullbackModules.obj F ⟶ F')
    (ι : Y.Cᵒᵖ → Type*) (Qj : ∀ U, ι U → X.Cᵒᵖ)
    (θ : ∀ (U : Y.Cᵒᵖ) (j : ι U) (P : Sheaf X.J (Type w₃)),
      (f.toToposHom.pushforward.obj P).obj.obj U → P.obj.obj (Qj U j))
    (hθ : ∀ (U : Y.Cᵒᵖ) (j : ι U) {P P' : Sheaf X.J (Type w₃)} (m : P ⟶ P')
      (x : (f.toToposHom.pushforward.obj P).obj.obj U),
        θ U j P' ((f.toToposHom.pushforward.map m).hom.app U x) = m.hom.app (Qj U j) (θ U j P x))
    (hinj : ∀ (U : Y.Cᵒᵖ) {P : Sheaf X.J (Type w₃)}
      (x y : (f.toToposHom.pushforward.obj P).obj.obj U),
      (∀ j, θ U j P x = θ U j P y) → x = y)
    (h : ∀ (U : Y.Cᵒᵖ) (j : ι U) (a b : (moduleSheaf (Tensor.ringSheaf Y.O) F).obj.obj U),
      θ U j _ (((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β)).hom.app U
        ((tensorHomPairing μ).hom.app U
          (Functor.prodObjMk (P := sectionsFunctor.{w₃} Y.J U) a b))) =
        (tensorHomPairing μ').hom.app (Qj U j)
          (Functor.prodObjMk (P := sectionsFunctor.{w₃} X.J (Qj U j))
            (θ U j _ (((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
              ((pullbackAdjPushforwardModules f).unit.app F ≫
                (pushforwardModules f).map β)).hom.app U a))
            (θ U j _ (((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
              ((pullbackAdjPushforwardModules f).unit.app F ≫
                (pushforwardModules f).map β)).hom.app U b)))) :
    f.pullbackModules.map μ ≫ β =
      (pullbackTensorIso f).hom.app (F, F) ≫
        ((Tensor.sheafTensor X.O).map β).app (f.pullbackModules.obj F) ≫
        ((Tensor.sheafTensor X.O).obj F').map β ≫ μ' :=
  pullbackModules_map_comp_eq_pullbackTensorIso_comp_of_tensorHomPairing f F F' μ μ' β
    (comp_eq_prodMap_comp_iso_inv_comp_map_of_natural_family f.toToposHom.pushforward ι Qj θ hθ
      hinj (tensorHomPairing μ) (tensorHomPairing μ')
      ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app F ≫ (pushforwardModules f).map β)) h)

end Combined

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Charts

variable {X Y : AlgebraicSpaces B S hS}

/-- The cartesian index of the base-changed chart diagram is the base-changed chart. -/
private theorem indexOfChartDiagram_smallBaseChangeDiagram (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    indexOfChartDiagram B S hS f (smallBaseChangeDiagram f hf V) =
      smallBaseChangeIndex B S hS f hf V := by
  unfold indexOfChartDiagram smallBaseChangeIndex
  rw [← chartLift_smallBaseChangeDiagram]

/-- The canonical map of sections of a direct image at the base-changed chart diagram is the
comparison `AlgebraicGeometry.Space.modulePushforwardChartIso` with the base-change direct
image. -/
private theorem modulePushforwardCounitApp_smallBaseChangeDiagram (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (K : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1) (x : ((modulePushforward B S hS f).obj K).val.obj (op V)) :
    modulePushforwardCounitApp B S hS f K (smallBaseChangeDiagram f hf V) x =
      ((modulePushforwardChartIso B S hS f hf).hom.app K).val.app (op V) x := by
  refine Eq.trans ?_ (modulePushforwardChartIso_hom_app_chartSetProj B S hS f hf K V x).symm
  refine Eq.trans ?_ (chartSetProj_eq_moduleChartProjection B S hS f hf _ V x).symm
  have key : ∀ (j j' : StructuredArrow (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op) (_ : j = j'),
      HEq ((moduleChartProjection B S hS f V j).app (moduleSetSheaf B S hS X K) x)
        ((moduleChartProjection B S hS f V j').app (moduleSetSheaf B S hS X K) x) := by
    intro j j' e; subst e; rfl
  exact eq_of_heq (key _ _ (indexOfChartDiagram_smallBaseChangeDiagram f hf V))

end Charts

section Pairing

variable {X Y : AlgebraicSpaces B S hS}

/-- **The pairing of the multiplication of `f_*𝒪_Y` is the product of sections.** -/
private theorem tensorHomPairing_pushforwardUnitTensorMulHom_hom_app (f : Y ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : (chartBaseChangeStructureModule B S hS f hf).val.obj V) :
    (Stacks.SheafOfModules.tensorHomPairing (O := (smallEtaleRingedTopos B S hS X).O)
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f hf)))).hom.app V
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS X.1) V)
          a b) =
      pushforwardUnitScale (𝟙 (chartBaseChangeStructureModule B S hS f hf)) (V := V.unop) a b := by
  have h1 : Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom
      (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS f hf))) =
        pushforwardUnitTensorMulPresheafHom (𝟙 (chartBaseChangeStructureModule B S hS f hf)) :=
    Equiv.apply_symm_apply Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom _
  refine (Stacks.SheafOfModules.pairingApp_pairingOfTensorHom (J := SmallEtale.topology B S hS X.1)
    (O := (smallEtaleRingedTopos B S hS X).O.obj) _ V a b).trans ?_
  exact congrArg (fun t => t.app V (a ⊗ₜ[(smallEtaleRingedTopos B S hS X).O.obj.obj V] b)) h1

end Pairing

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {π : Y ⟶ X} {g : X' ⟶ X} {π' : Y' ⟶ X'}
  {g' : Y' ⟶ Y}

/-- A composite of morphisms of modules on a section. -/
private theorem comp_val_app_apply_ringedSiteObj {Z : AlgebraicSpaces B S hS}
    {M N P : Modules.{u, u} B S hS Z.1 Z.2}
    (b : M ⟶ N) (c : N ⟶ P) (U : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ) (x : M.val.obj U) :
    (b ≫ c).val.app U x = c.val.app U (b.val.app U x) := rfl

/-- **Reading a factored morphism on a section**, with every morphism a variable: if
`β = (b₁ ≫ b₂ ≫ b₃) ≫ b₄` and `b₃ ≫ b₄ = c₃ ≫ c₄`, then `β x = c₄ (c₃ (b₂ (b₁ x)))`. -/
private theorem val_app_eq_of_eq_comp {Z : AlgebraicSpaces B S hS}
    {M₁ M₂ M₃ M₄ M₅ N : Modules.{u, u} B S hS Z.1 Z.2} (β : M₁ ⟶ M₅)
    (b₁ : M₁ ⟶ M₂) (b₂ : M₂ ⟶ M₃) (b₃ : M₃ ⟶ M₄) (b₄ : M₄ ⟶ M₅) (c₃ : M₃ ⟶ N) (c₄ : N ⟶ M₅)
    (h : β = (b₁ ≫ b₂ ≫ b₃) ≫ b₄) (hn : c₃ ≫ c₄ = b₃ ≫ b₄)
    (U : (smallEtaleRingedSite B S hS Z.1 Z.2).Cᵒᵖ)
    (x : M₁.val.obj U) (z : M₃.val.obj U) (hz : b₂.val.app U (b₁.val.app U x) = z) :
    β.val.app U x = c₄.val.app U (c₃.val.app U z) := by
  subst h hz
  exact (congrArg (fun t : M₃ ⟶ M₅ => t.val.app U (b₂.val.app U (b₁.val.app U x))) hn).symm

/-- The comparison `AlgebraicGeometry.Space.modulePushforwardChartIso` after its inverse, on a
section over a chart. -/
private theorem chartIso_hom_app_val_app_inv_app_val_app (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (K : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS Y.1)
    (y : ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj K).val.obj (op V)) :
    ((modulePushforwardChartIso B S hS f hf).hom.app K).val.app (op V)
      (((modulePushforwardChartIso B S hS f hf).inv.app K).val.app (op V) y) = y := by
  exact congrArg (fun t => t.val.app (op V) y)
    (Iso.inv_hom_id_app (modulePushforwardChartIso B S hS f hf) K)

/-- The unit section of a module pullback is natural in the module. -/
private theorem modulePullbackUnitSection_val_app_eq_modulePullback_map_val_app
    {Z W : AlgebraicSpaces B S hS}
    (f : Z ⟶ W) {M N : Modules.{u, u} B S hS W.1 W.2} (φ : M ⟶ N)
    (d : ChartDiagram B S hS Z.1 W.1 f.hom) (s : M.val.obj (op d.V)) :
    modulePullbackUnitSection B S hS f N d (φ.val.app (op d.V) s) =
      ((modulePullback B S hS f).map φ).val.app (op d.U)
        (modulePullbackUnitSection B S hS f M d s) := by
  have hunit := congrArg
    (fun a : M ⟶ (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj N) =>
      a.val.app (op d.V) s) ((modulePullbackAdjunction B S hS f).unit.naturality φ)
  exact (congrArg (modulePushforwardCounitApp B S hS f
      ((modulePullback B S hS f).obj N) d) hunit).trans
    (modulePushforwardCounitApp_map B S hS f ((modulePullback B S hS f).map φ) d _)

/-- **The affine base change map on the unit section of a chart section, read at the
base-changed chart**: through the comparisons with the base-change direct images, the base
change map `g^*(π_*K) ⟶ π'_*((g')^*K)` sends the unit section along `g` at `d` of a section `y`
over `d.V ×_X Y` to the unit section along `g'` of `y` at the chart square of `d`. -/
private theorem chartIso_moduleBaseChangeMap_modulePullbackUnitSection
    (comm : g' ≫ π = π' ≫ g) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) (K : Modules.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS X'.1 X.1 g.hom)
    (y : ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).obj K).val.obj (op d.V)) :
    ((modulePushforwardChartIso B S hS π' hπ').hom.app ((modulePullback B S hS g').obj K)).val.app
        (op d.U) (((moduleBaseChangeMap π g π' g' comm).app K).val.app (op d.U)
          (((modulePullback B S hS g).map
            ((modulePushforwardChartIso B S hS π hπ).inv.app K)).val.app
              (op d.U) (modulePullbackUnitSection B S hS g _ d y))) =
      modulePullbackUnitSection B S hS g' K
        (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d comm) y := by
  obtain ⟨s, hs⟩ :
      ∃ s, ((modulePushforwardChartIso B S hS π hπ).inv.app K).val.app (op d.V) y = s :=
    ⟨_, rfl⟩
  have e2 : ((modulePullback B S hS g).map
        ((modulePushforwardChartIso B S hS π hπ).inv.app K)).val.app
        (op d.U) (modulePullbackUnitSection B S hS g _ d y) =
      modulePullbackUnitSection B S hS g ((modulePushforward B S hS π).obj K) d s :=
    hs ▸ (modulePullbackUnitSection_val_app_eq_modulePullback_map_val_app g _ d y).symm
  have e3 := (modulePushforwardCounitApp_smallBaseChangeDiagram π' hπ'
    ((modulePullback B S hS g').obj K) d.U (((moduleBaseChangeMap π g π' g' comm).app K).val.app
      (op d.U) (modulePullbackUnitSection B S hS g ((modulePushforward B S hS π).obj K) d s))).symm
  have e4 := counitApp_val_app_moduleBaseChangeMap_modulePullbackUnitSection B S hS g' π' π g K
    hπ hπ' d comm s
  have e5 : modulePushforwardCounitApp B S hS π K (smallBaseChangeDiagram π hπ d.V) s = y := by
    rw [modulePushforwardCounitApp_smallBaseChangeDiagram π hπ K d.V s, ← hs]
    exact chartIso_hom_app_val_app_inv_app_val_app π hπ K d.V y
  refine (congrArg (fun z => ((modulePushforwardChartIso B S hS π' hπ').hom.app
    ((modulePullback B S hS g').obj K)).val.app (op d.U)
      (((moduleBaseChangeMap π g π' g' comm).app K).val.app (op d.U) z)) e2).trans ?_
  exact e3.trans (e4.trans (congrArg (modulePullbackUnitSection B S hS g' K
    (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d comm)) e5))

/-- The direct image of `(g')^*𝒪_Y ≅ 𝒪_{Y'}` read at the base-changed chart. -/
private theorem chartIso_modulePushforward_map_modulePullbackUnitIso_hom
    (comm : g' ≫ π = π' ≫ g) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) (d : ChartDiagram B S hS X'.1 X.1 g.hom)
    (a : ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y))).val.obj (op d.V))
    (z : ((modulePushforward B S hS π').obj
      ((modulePullback B S hS g').obj (SheafOfModules.unit (structureRingSheaf B S hS Y)))).val.obj
        (op d.U))
    (hL : ((modulePushforwardChartIso B S hS π' hπ').hom.app
      ((modulePullback B S hS g').obj (SheafOfModules.unit (structureRingSheaf B S hS Y)))).val.app
        (op d.U) z = modulePullbackUnitSection B S hS g'
          (SheafOfModules.unit (structureRingSheaf B S hS Y))
          (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d comm) a) :
    ((modulePushforwardChartIso B S hS π' hπ').hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y'.1 Y'.2).O))).val.app (op d.U)
        (((modulePushforward B S hS π').map (modulePullbackUnitIso B S hS g').hom).val.app
          (op d.U) z) =
      chartDiagramPullback B S hS g' (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d comm) a := by
  have e6 := (modulePushforwardCounitApp_smallBaseChangeDiagram π' hπ'
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y'.1 Y'.2).O)) d.U
    (((modulePushforward B S hS π').map (modulePullbackUnitIso B S hS g').hom).val.app
      (op d.U) z)).symm
  have e6' := modulePushforwardCounitApp_map B S hS π' (modulePullbackUnitIso B S hS g').hom
    (smallBaseChangeDiagram π' hπ' d.U) z
  have e6'' := modulePushforwardCounitApp_smallBaseChangeDiagram π' hπ'
    ((modulePullback B S hS g').obj (SheafOfModules.unit (structureRingSheaf B S hS Y))) d.U z
  have e7 := modulePullbackUnitIso_hom_val_app_modulePullbackUnitSection B S hS g'
    (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d comm) a
  exact e6.trans (e6'.trans ((congrArg (fun w => (modulePullbackUnitIso B S hS g').hom.val.app
    (op ((smallBaseChange B S hS π' hπ').obj d.U)) w) (e6''.trans hL)).trans e7))

/-- **The transpose of the affine base change isomorphism of the structure sheaf, on chart
sections, is pullback of regular functions.**  For a chart diagram `d` over `g`, the chart
component at `d` of the transpose `π_*𝒪_Y ⟶ g_*(π'_*𝒪_{Y'})` of
`AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso` sends a regular
function on `d.V ×_X Y` to its pullback along the morphism of base-changed charts
`d.U ×_{X'} Y' ⟶ d.V ×_X Y`. -/
private theorem modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom_val_app_unitSection
    (sq : IsPullback g' π' π g) (hπa : IsAffineHom B S hS π.hom)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom)
    (d : ChartDiagram B S hS X'.1 X.1 g.hom)
    (a : ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y))).val.obj (op d.V)) :
    (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom.val.app (op d.U)
        (modulePullbackUnitSection B S hS g
          ((smallBaseChangeModulePushforward.{u, u} B S hS π hπ).obj
            (SheafOfModules.unit (structureRingSheaf B S hS Y))) d a) =
      chartDiagramPullback B S hS g' (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) a := by
  have hβ := (modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom sq hπa hπ hπ').trans
    (congrArg (· ≫ (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').map
          (modulePullbackUnitIso B S hS g').hom)
      ((smallBaseChangeModuleAffineBaseChangeIso_hom sq hπa hπ hπ'
          (SheafOfModules.unit (structureRingSheaf B S hS Y))
          (SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS Y))).trans
        (smallBaseChangeModuleBaseChangeMap_app sq.w hπ hπ'
          (SheafOfModules.unit (structureRingSheaf B S hS Y)))))
  have hn := (modulePushforwardChartIso B S hS π' hπ').hom.naturality
    (modulePullbackUnitIso B S hS g').hom
  have t2 := val_app_eq_of_eq_comp _ _ _ _ _ _ _ hβ hn
  have t4 := t2 (op d.U) (modulePullbackUnitSection B S hS g _ d a) _ rfl
  refine t4.trans ?_
  have h1 := chartIso_moduleBaseChangeMap_modulePullbackUnitSection sq.w hπ hπ'
      (SheafOfModules.unit (structureRingSheaf B S hS Y)) d a
  have h2 := chartIso_modulePushforward_map_modulePullbackUnitIso_hom sq.w hπ hπ' d a _ h1
  exact h2

/-- The comparison of the two direct images of modules is the identity on sections, at an object
of the site spelled through the small étale ringed site. -/
private theorem modulePushforwardIso_hom_app_val_app_ringedSiteObj
    {Z W : AlgebraicSpaces B S hS} (k : Z ⟶ W)
    (N : Modules.{u, u} B S hS Z.1 Z.2) (U : (smallEtaleRingedSite B S hS W.1 W.2).Cᵒᵖ)
    (y : ((modulePushforward B S hS k).obj N).val.obj U) :
    ((modulePushforwardIso B S hS k).hom.app N).val.app U y = y :=
  modulePushforwardIso_hom_app_val_app B S hS k N U y

open Stacks.Sheaves.RingedToposModules in
/-- The chart reading of a transpose along the adjunction of Stacks 03D7 for the morphism of
small étale ringed topoi is the value of the morphism on a unit section. -/
private theorem counitApp_unit_comp_pushforwardModules_map
    {Z W : AlgebraicSpaces B S hS} (k : Z ⟶ W)
    {M : Modules.{u, u} B S hS W.1 W.2} {N : Modules.{u, u} B S hS Z.1 Z.2}
    (ψ : (modulePullback B S hS k).obj M ⟶ N) (d : ChartDiagram B S hS Z.1 W.1 k.hom)
    (x : M.val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS k N d
        (((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS k)).unit.app M ≫
          (pushforwardModules (smallEtaleRingedToposModulesHom B S hS k)).map ψ).val.app
          (op d.V) x) =
      ψ.val.app (op d.U) (modulePullbackUnitSection B S hS k M d x) := by
  have h1 :=
    (pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS k)).homEquiv_unit _ _ ψ
  have h2 := Adjunction.homEquiv_ofNatIsoRight_apply
    (pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS k))
    (modulePushforwardIso B S hS k) ψ
  refine Eq.trans ?_ (modulePushforwardCounitApp_homEquiv_app B S hS k M N ψ d x)
  refine congrArg (modulePushforwardCounitApp B S hS k N d) ?_
  refine Eq.trans (modulePushforwardIso_hom_app_val_app_ringedSiteObj k N (op d.V) _).symm ?_
  exact (comp_val_app_apply_ringedSiteObj _ _ _ x).symm.trans
    (congrArg (fun t => t.val.app (op d.V) x)
      ((congrArg (· ≫ (modulePushforwardIso B S hS k).hom.app N) h1.symm).trans h2.symm))

open Stacks.Sheaves.RingedToposModules in
/-- The chart reading of the transpose along the adjunction of Stacks 03D7 for the morphism of
ringed topoi, in the form the pairing of Stacks 03EL is stated in. -/
private theorem counitApp_unit_comp_pushforwardModules_map_unitIso_hom
    (sq : IsPullback g' π' π g) (hπa : IsAffineHom B S hS π.hom)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom)
    (d : ChartDiagram B S hS X'.1 X.1 g.hom)
    (x : (chartBaseChangeStructureModule B S hS π hπ).val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS g ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y'))) d
        (((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
            (chartBaseChangeStructureModule B S hS π hπ) ≫
          (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
            (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom).val.app
          (op d.V) x) =
      chartDiagramPullback B S hS g' (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) x := by
  have t5 : modulePullbackUnitSection B S hS g (chartBaseChangeStructureModule B S hS π hπ) d x =
      modulePullbackUnitSection B S hS g ((smallBaseChangeModulePushforward.{u,u} B S hS π hπ).obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y))) d x := rfl
  exact (counitApp_unit_comp_pushforwardModules_map g _ d x).trans
    ((congrArg (fun z => (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ
      hπ').hom.val.app (op d.U) z) t5).trans
    (modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom_val_app_unitSection sq hπa hπ hπ'
      d x))

open Stacks.Sheaves.RingedToposModules in
/-- The chart projection at a chart diagram `d` over `g` of the transpose of
`AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso` is pullback of
regular functions along the chart square of `d`. -/
private theorem moduleChartProjection_transpose_unitIso_hom
    (sq : IsPullback g' π' π g) (hπa : IsAffineHom B S hS π.hom)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom)
    (d : ChartDiagram B S hS X'.1 X.1 g.hom) (z : (Sheaf.moduleSheaf.{u, u, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        (chartBaseChangeStructureModule B S hS π hπ)).obj.obj (op d.V)) :
    (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
            (smallEtaleRingedToposModulesHom B S hS g).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
          ((SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage).obj
              ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
                (SheafOfModules.unit (structureRingSheaf B S hS Y')))))
        (((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
            ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
                (chartBaseChangeStructureModule B S hS π hπ) ≫
              (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
                (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom)).hom.app
          (op d.V) z) =
      chartDiagramPullback B S hS g' (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) z := by
  exact counitApp_unit_comp_pushforwardModules_map_unitIso_hom sq hπa hπ hπ' d z

open Stacks.Sheaves.RingedToposModules in
/-- **The transpose of the affine base change isomorphism is multiplicative after the chart
projection at a chart diagram.**  The transpose along the adjunction of Stacks 03D7 of
`AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso`, read at the
chart projection of a chart diagram `d` over `g`, carries the pairing of the multiplication of
`π_*𝒪_Y` to the pairing of the multiplication of `π'_*𝒪_{Y'}`. -/
private theorem moduleChartProjection_transpose_unitIso_hom_tensorHomPairing
    (sq : IsPullback g' π' π g) (hπa : IsAffineHom B S hS π.hom)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom)
    (d : ChartDiagram B S hS X'.1 X.1 g.hom) (a b : (Sheaf.moduleSheaf.{u, u, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        (chartBaseChangeStructureModule B S hS π hπ)).obj.obj (op d.V)) :
    (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
            (smallEtaleRingedToposModulesHom B S hS g).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
          ((SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage).obj
              ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
                (SheafOfModules.unit (structureRingSheaf B S hS Y')))))
        (((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
            ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
                (chartBaseChangeStructureModule B S hS π hπ) ≫
              (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
                (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom)).hom.app
          (op d.V)
          ((Stacks.SheafOfModules.tensorHomPairing (O := (smallEtaleRingedTopos B S hS X).O)
            (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π hπ)))).hom.app
              (op d.V) (Functor.prodObjMk
                (P := Sheaf.sectionsFunctor.{u} (smallEtaleRingedTopos B S hS X).J (op d.V))
                a b))) =
      (Stacks.SheafOfModules.tensorHomPairing (O := (smallEtaleRingedTopos B S hS X').O)
        (A := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (B := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (N := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π' hπ')))).hom.app
          (indexOfChartDiagram B S hS g d).right
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} (smallEtaleRingedTopos B S hS X').J
              (indexOfChartDiagram B S hS g d).right)
            ((moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
            (smallEtaleRingedToposModulesHom B S hS g).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
          ((SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage).obj
              ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
                (SheafOfModules.unit (structureRingSheaf B S hS Y')))))
        (((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
            ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
                (chartBaseChangeStructureModule B S hS π hπ) ≫
              (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
                (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom)).hom.app
          (op d.V) a))
            ((moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
            (smallEtaleRingedToposModulesHom B S hS g).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
          ((SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage).obj
              ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
                (SheafOfModules.unit (structureRingSheaf B S hS Y')))))
        (((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
            ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
                (chartBaseChangeStructureModule B S hS π hπ) ≫
              (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
                (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom)).hom.app
          (op d.V) b))) := by
  refine (moduleChartProjection_transpose_unitIso_hom sq hπa hπ hπ' d _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun x y => (Stacks.SheafOfModules.tensorHomPairing
      (O := (smallEtaleRingedTopos B S hS X').O)
        (A := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (B := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (N := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π' hπ')))).hom.app
          (indexOfChartDiagram B S hS g d).right
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} (smallEtaleRingedTopos B S hS X').J
              (indexOfChartDiagram B S hS g d).right) x y))
    (moduleChartProjection_transpose_unitIso_hom sq hπa hπ hπ' d a)
    (moduleChartProjection_transpose_unitIso_hom sq hπa hπ hπ' d b)).symm
  refine (congrArg (fun z => chartDiagramPullback B S hS g'
      (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) z)
    (tensorHomPairing_pushforwardUnitTensorMulHom_hom_app π hπ (op d.V) a b)).trans ?_
  have e : (Stacks.SheafOfModules.tensorHomPairing (O := (smallEtaleRingedTopos B S hS X').O)
        (A := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (B := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (N := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π' hπ')))).hom.app
          (op d.U) (Functor.prodObjMk
              (P := Sheaf.sectionsFunctor.{u} (smallEtaleRingedTopos B S hS X').J
              (op d.U))
            (chartDiagramPullback B S hS g'
              (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) a)
            (chartDiagramPullback B S hS g'
              (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) b)) =
      pushforwardUnitScale (𝟙 (chartBaseChangeStructureModule B S hS π' hπ')) (V := d.U)
        (chartDiagramPullback B S hS g'
          (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) a)
        (chartDiagramPullback B S hS g'
          (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w) b) :=
    tensorHomPairing_pushforwardUnitTensorMulHom_hom_app π' hπ' (op d.U) _ _
  refine Eq.trans ?_ e.symm
  exact (chartDiagramPullback B S hS g'
      (chartDiagramOfSquare B S hS g' π' π g hπ hπ' d sq.w)).hom.map_mul b a

open Stacks.Sheaves.RingedToposModules in
/-- `AlgebraicGeometry.Space.moduleChartProjection_transpose_unitIso_hom_tensorHomPairing` at
every index of the chart projections. -/
private theorem moduleChartProjection_transpose_unitIso_hom_tensorHomPairing_index
    (sq : IsPullback g' π' π g) (hπa : IsAffineHom B S hS π.hom)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom)
    (U : (smallEtaleRingedTopos B S hS X).Cᵒᵖ)
    (j : StructuredArrow (op (chartBaseChange B S hS g U.unop)) (comparisonFunctor B S hS X').op)
    (a b : (Sheaf.moduleSheaf.{u, u, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)
        (chartBaseChangeStructureModule B S hS π hπ)).obj.obj U) :
    (moduleChartProjection B S hS g U.unop j).app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
            (smallEtaleRingedToposModulesHom B S hS g).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
          ((SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage).obj
              ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
                (SheafOfModules.unit (structureRingSheaf B S hS Y')))))
        (((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
            ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
                (chartBaseChangeStructureModule B S hS π hπ) ≫
              (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
                (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom)).hom.app
          U ((Stacks.SheafOfModules.tensorHomPairing (O := (smallEtaleRingedTopos B S hS X).O)
            (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π hπ)))).hom.app
              U (Functor.prodObjMk
                (P := Sheaf.sectionsFunctor.{u} (smallEtaleRingedTopos B S hS X).J U) a b))) =
      (Stacks.SheafOfModules.tensorHomPairing (O := (smallEtaleRingedTopos B S hS X').O)
        (A := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (B := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (N := (smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Y')))
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π' hπ')))).hom.app
          j.right
          (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{u} (smallEtaleRingedTopos B S hS X').J
              j.right)
            ((moduleChartProjection B S hS g U.unop j).app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
            (smallEtaleRingedToposModulesHom B S hS g).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
          ((SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage).obj
              ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
                (SheafOfModules.unit (structureRingSheaf B S hS Y')))))
        (((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
            ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
                (chartBaseChangeStructureModule B S hS π hπ) ≫
              (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
                (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom)).hom.app
          U a))
            ((moduleChartProjection B S hS g U.unop j).app
        (Sheaf.moduleSheaf.{u, u, u + 1}
          (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
            (smallEtaleRingedToposModulesHom B S hS g).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
          ((SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS g).fSharpInverseImage).obj
              ((smallBaseChangeModulePushforward.{u, u} B S hS π' hπ').obj
                (SheafOfModules.unit (structureRingSheaf B S hS Y')))))
        (((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).map
            ((pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).unit.app
                (chartBaseChangeStructureModule B S hS π hπ) ≫
              (pushforwardModules (smallEtaleRingedToposModulesHom B S hS g)).map
                (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom)).hom.app
          U b))) := by
  induction U with | op V₀ => ?_
  rw [← indexOfChartDiagram_chartDiagramOfIndex B S hS g V₀ j]
  exact moduleChartProjection_transpose_unitIso_hom_tensorHomPairing sq hπa hπ hπ'
    (chartDiagramOfIndex B S hS g V₀ j) a b

/-- **The affine base change isomorphism of `π_*𝒪_Y` is multiplicative.**  For a cartesian square
`g' ≫ π = π' ≫ g` of algebraic spaces with `π` affine, the affine base change isomorphism
`β : g^*(π_*𝒪_Y) ≅ π'_*𝒪_{Y'}` carries the pullback `g^*μ` of the multiplication of `π_*𝒪_Y` to
the multiplication `μ'` of `π'_*𝒪_{Y'}`: `g^*μ ≫ β = δ ≫ (β ⊗ β) ≫ μ'`, where `δ` is the
comparison `g^*(F ⊗ F) ≅ g^*F ⊗ g^*F` of Stacks 03EL. -/
theorem modulePullback_map_pushforwardUnitTensorMulHom_comp_unitIso_hom
    (sq : IsPullback g' π' π g) (hπa : IsAffineHom B S hS π.hom)
    (hπ : yoneda.relativelyRepresentable π.hom) (hπ' : yoneda.relativelyRepresentable π'.hom) :
    (modulePullback B S hS g).map
        (pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π hπ))) ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom =
      (Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS g)).hom.app
          (chartBaseChangeStructureModule B S hS π hπ, chartBaseChangeStructureModule B S hS π hπ) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).map
          (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom).app
            ((modulePullback B S hS g).obj (chartBaseChangeStructureModule B S hS π hπ)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X'.1 X'.2).O).obj
          (chartBaseChangeStructureModule B S hS π' hπ')).map
            (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa hπ hπ').hom ≫
          pushforwardUnitTensorMulHom (𝟙 (chartBaseChangeStructureModule B S hS π' hπ')) :=
  Stacks.SheafOfModules.pullbackModules_map_comp_eq_pullbackTensorIso_comp_of_natural_family
    (smallEtaleRingedToposModulesHom B S hS g) _ _ _ _ _
    (fun U => StructuredArrow (op (chartBaseChange B S hS g U.unop))
      (comparisonFunctor B S hS X').op)
    (fun _ j => j.right)
    (fun U j F => (moduleChartProjection B S hS g U.unop j).app F)
    (fun U j _ _ m x => moduleChartProjection_app_hom_app B S hS g U.unop j m x)
    (fun U _ _ _ hxy => moduleChartProjection_ext B S hS g U.unop _ hxy)
    (moduleChartProjection_transpose_unitIso_hom_tensorHomPairing_index sq hπa hπ hπ')

end Square

end AlgebraicGeometry.Space
