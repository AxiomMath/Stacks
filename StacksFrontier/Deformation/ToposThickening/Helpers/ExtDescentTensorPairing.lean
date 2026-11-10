module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearSourceNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIsoTransposeCharacterization
public import StacksFrontier.Deformation.ToposThickening.Helpers.ExtDescentAlongThickening

/-!
# The descent of tensor products along a first order thickening, on pairings

A morphism out of a tensor product sheaf `A ⊗ B` is determined by the bilinear pairing it
induces, the universal pairing `A × B ⟶ A ⊗ B` followed by the morphism
(`Stacks.SheafOfModules.hom_ext_of_tensorSectionPairing`). This file computes the pairings of the
canonical maps through which the deformation theory of modules on a first order thickening
`i : X ⟶ Y` is read on `X`:

* the projection-formula map `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)` of a morphism of ringed topoi pairs two
  local sections to `f_*` of the universal pairing of `f^*F` and `G` applied to the unit image of
  the first and to the second
  (`Stacks.SheafOfModules.tensorSectionPairing_comp_pushforwardTensorMap`);
* the identification `i_*J ⊗ i_*F ≅ i_*(J ⊗ F)` of
  `Deformation.ToposThickening.pushforwardModuleTensorIso` is written out as the projection-formula
  map of `(Sh(C), O) ⟶ (Sh(D), i_*O)` read through the counit
  (`Deformation.ToposThickening.pushforwardModuleTensorIso_hom_eq`).

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01E6](https://stacks.math.columbia.edu/tag/01E6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf MonoidalCategory
open AlgebraicGeometry (RingedTopos)
open scoped CategoryTheory.Prod

universe v u v' u' w w'

namespace Stacks.SheafOfModules

section Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Tensoring on the right with a morphism acts on the image of a pure tensor by applying the
morphism to the second factor. -/
theorem sheafTensor_obj_map_unit_tmul
    {A B B' : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)} (g : B ⟶ B') (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    (((Tensor.sheafTensor O).obj A).map g).val.app U
        (((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O)
          (𝟙 (Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj A.val B.val)).app U (a ⊗ₜ[O.obj.obj U] b)) =
      ((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O)
        (𝟙 (Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj A.val B'.val)).app U (a ⊗ₜ[O.obj.obj U] g.val.app U b) :=
  (congrArg (fun φ => φ.app U (a ⊗ₜ[O.obj.obj U] b))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Tensor.ringSheaf O).obj)).unit.naturality
        (PresheafOfModules.tensorHom (𝟙 A.val) g.val))).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Tensoring on the left with a morphism acts on the image of a pure tensor by applying the
morphism to the first factor. -/
theorem sheafTensor_map_app_unit_tmul
    {A A' B : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)} (f : A ⟶ A') (U : Cᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) :
    (((Tensor.sheafTensor O).map f).app B).val.app U
        (((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O)
          (𝟙 (Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj A.val B.val)).app U (a ⊗ₜ[O.obj.obj U] b)) =
      ((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O)
        (𝟙 (Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj A'.val B.val)).app U (f.val.app U a ⊗ₜ[O.obj.obj U] b) :=
  (congrArg (fun φ => φ.app U (a ⊗ₜ[O.obj.obj U] b))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Tensor.ringSheaf O).obj)).unit.naturality
        (PresheafOfModules.tensorHom f.val (𝟙 B.val)))).symm

variable {A A' B B' N : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] in
/-- **A morphism out of a tensor product sheaf is determined by its pairing**: two morphisms
`A ⊗ B ⟶ N` agree as soon as they agree after the universal pairing `A × B ⟶ A ⊗ B`. -/
theorem hom_ext_of_tensorSectionPairing {f g : ((Tensor.sheafTensor O).obj A).obj B ⟶ N}
    (h : tensorSectionPairing A B ≫ (moduleSheafFunctor (Tensor.ringSheaf O)).map f =
      tensorSectionPairing A B ≫ (moduleSheafFunctor (Tensor.ringSheaf O)).map g) : f = g := by
  apply tensorHomEquivPresheafTensorHom.injective
  refine PresheafOfModules.hom_ext fun U => ModuleCat.MonoidalCategory.tensor_ext fun a b => ?_
  have h' := congrArg (fun q => pairingApp (Tensor.ringSheaf O) q U a b) h
  have e1 := pairingApp_comp (tensorSectionPairing A B) f U a b
  have e2 := pairingApp_comp (tensorSectionPairing A B) g U a b
  have e3 := pairingApp_tensorSectionPairing A B U a b
  exact (congrArg ((sectionsFunctor J U).map ((moduleSheafFunctor (Tensor.ringSheaf O)).map f))
    e3).symm.trans ((e1.symm.trans (h'.trans e2)).trans
      (congrArg ((sectionsFunctor J U).map ((moduleSheafFunctor (Tensor.ringSheaf O)).map g)) e3))

/-- A morphism of tensor product sheaves acting on unit images of pure tensors by `f ⊗ g` is
compatible with the universal pairings. -/
private theorem tensorSectionPairing_comp_map_of_unit_tmul {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}] {O : Sheaf J CommRingCat.{w}}
    {A A' B B' : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)} (f : A ⟶ A') (g : B ⟶ B')
    (φ : ((Tensor.sheafTensor O).obj A).obj B ⟶ ((Tensor.sheafTensor O).obj A').obj B')
    (h : ∀ (U : Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U),
      φ.val.app U (((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O)
          (𝟙 (Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj A.val B.val)).app U (a ⊗ₜ[O.obj.obj U] b)) =
        ((PresheafOfModules.sheafificationAdjunction (R := Tensor.ringSheaf O)
          (𝟙 (Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj A'.val B'.val)).app U
          (f.val.app U a ⊗ₜ[O.obj.obj U] g.val.app U b)) :
    tensorSectionPairing A B ≫ (moduleSheafFunctor (Tensor.ringSheaf O)).map φ =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf O)).map f)
        ((moduleSheafFunctor (Tensor.ringSheaf O)).map g) ≫ tensorSectionPairing A' B' := by
  refine pairing_ext (Tensor.ringSheaf O) fun U a b => ?_
  refine (pairingApp_comp _ _ U a b).trans (Eq.trans ?_ (pairingApp_prodMap_comp _ _ _ U a b).symm)
  refine (congrArg _ (pairingApp_tensorSectionPairing A B U a b)).trans
    (Eq.trans ?_ (pairingApp_tensorSectionPairing A' B' U _ _).symm)
  exact h U a b

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **The universal pairing is natural in the second factor.** -/
theorem tensorSectionPairing_comp_map_right (g : B ⟶ B') :
    tensorSectionPairing A B ≫
        (moduleSheafFunctor (Tensor.ringSheaf O)).map (((Tensor.sheafTensor O).obj A).map g) =
      prod.map (𝟙 _) ((moduleSheafFunctor (Tensor.ringSheaf O)).map g) ≫
        tensorSectionPairing A B' := by
  simpa using tensorSectionPairing_comp_map_of_unit_tmul (𝟙 A) g _
    fun U a b => sheafTensor_obj_map_unit_tmul g U a b

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **The universal pairing is natural in the first factor.** -/
theorem tensorSectionPairing_comp_map_left (f : A ⟶ A') :
    tensorSectionPairing A B ≫
        (moduleSheafFunctor (Tensor.ringSheaf O)).map (((Tensor.sheafTensor O).map f).app B) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf O)).map f) (𝟙 _) ≫
        tensorSectionPairing A' B := by
  simpa using tensorSectionPairing_comp_map_of_unit_tmul f (𝟙 B) _
    fun U a b => sheafTensor_map_app_unit_tmul f U a b

end Tensor

section Products

variable {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] [HasBinaryProducts 𝒞] [HasBinaryProducts 𝒟]
  (Φ : 𝒞 ⥤ 𝒟) [PreservesFiniteProducts Φ]

omit [HasBinaryProducts 𝒟] in
/-- The inverse of the comparison `Φ(A × B) ≅ ΦA × ΦB` of a finite-product-preserving functor
is natural. -/
theorem preservesLimitPair_iso_inv_naturality {A A' B B' : 𝒞} (f : A ⟶ A') (g : B ⟶ B') :
    (PreservesLimitPair.iso Φ A B).inv ≫ Φ.map (prod.map f g) =
      prod.map (Φ.map f) (Φ.map g) ≫ (PreservesLimitPair.iso Φ A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  apply prod.hom_ext <;>
    simp [PreservesLimitPair.iso_hom, ← CategoryTheory.Functor.map_comp]

/-- Pushing a pairing `T` forward along `Φ` and composing with `Φ m`, when `T ≫ m` is a pairing
`T'` precomposed with a map on the second factor. -/
theorem prodMap_comp_preservesLimitPair_iso_inv_comp_map_comp {A B B' N N' : 𝒞}
    {W₁ W₂ : 𝒟} (p : W₁ ⟶ Φ.obj A) (q : W₂ ⟶ Φ.obj B') (e : B' ⟶ B) (T : A ⨯ B' ⟶ N)
    (m : N ⟶ N') (T' : A ⨯ B ⟶ N') (hR : T ≫ m = prod.map (𝟙 A) e ≫ T') :
    (prod.map p q ≫ (PreservesLimitPair.iso Φ A B').inv ≫ Φ.map T) ≫ Φ.map m =
      prod.map p (q ≫ Φ.map e) ≫ (PreservesLimitPair.iso Φ A B).inv ≫ Φ.map T' := by
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, hR,
    CategoryTheory.Functor.map_comp, ← Category.assoc (PreservesLimitPair.iso Φ A B').inv,
    preservesLimitPair_iso_inv_naturality, ← Category.assoc, ← Category.assoc, prod.map_map,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]

/-- Pushing a pairing `T` forward along `Φ` and composing with `Φ m`, when `T ≫ m` is a pairing
`T'` precomposed with a map on the first factor. -/
theorem prodMap_comp_preservesLimitPair_iso_inv_comp_map_comp_left {A A' B N N' : 𝒞}
    {W₁ W₂ : 𝒟} (p : W₁ ⟶ Φ.obj A) (q : W₂ ⟶ Φ.obj B) (e : A ⟶ A') (T : A ⨯ B ⟶ N)
    (m : N ⟶ N') (T' : A' ⨯ B ⟶ N') (hR : T ≫ m = prod.map e (𝟙 B) ≫ T') :
    (prod.map p q ≫ (PreservesLimitPair.iso Φ A B).inv ≫ Φ.map T) ≫ Φ.map m =
      prod.map (p ≫ Φ.map e) q ≫ (PreservesLimitPair.iso Φ A' B).inv ≫ Φ.map T' := by
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp, hR,
    CategoryTheory.Functor.map_comp, ← Category.assoc (PreservesLimitPair.iso Φ A B).inv,
    preservesLimitPair_iso_inv_naturality, ← Category.assoc, ← Category.assoc, prod.map_map,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]

omit [HasBinaryProducts 𝒟] in
/-- Pushing a pairing `T` forward along `Φ` and composing with `Φ m`, when `T ≫ m` is a pairing
`T'` precomposed with a map on the first factor. -/
theorem preservesLimitPair_iso_inv_comp_map_comp_left {A A' B N N' : 𝒞} (e : A ⟶ A')
    (T : A ⨯ B ⟶ N) (m : N ⟶ N') (T' : A' ⨯ B ⟶ N') (hR : T ≫ m = prod.map e (𝟙 B) ≫ T') :
    ((PreservesLimitPair.iso Φ A B).inv ≫ Φ.map T) ≫ Φ.map m =
      prod.map (Φ.map e) (𝟙 _) ≫ (PreservesLimitPair.iso Φ A' B).inv ≫ Φ.map T' := by
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hR, CategoryTheory.Functor.map_comp,
    ← Category.assoc, preservesLimitPair_iso_inv_naturality, CategoryTheory.Functor.map_id,
    Category.assoc]

/-- A chain of four morphisms after a pairing, computed link by link. -/
theorem pairing_comp_chain {𝒟 : Type*} [Category* 𝒟] [HasBinaryProducts 𝒟]
    {P P' Q T₀ T₁ T₂ T₃ : 𝒟} (t₀ : P ⨯ Q ⟶ T₀) (m₁ : T₀ ⟶ T₁) (m₂ : T₁ ⟶ T₂)
    (m₄ : T₂ ⟶ T₃) (m₆ : T₃ ⟶ T₃) (h : Q ⟶ Q) (t₁ : P ⨯ Q ⟶ T₁)
    (s₁ : t₀ ≫ m₁ = prod.map (𝟙 P) h ≫ t₁) (hh : h = 𝟙 Q) (p : P ⟶ P') (r : P' ⨯ Q ⟶ T₂)
    (s₂ : t₁ ≫ m₂ = prod.map p (𝟙 Q) ≫ r) (e : P' ⟶ P) (r' : P ⨯ Q ⟶ T₃)
    (s₄ : r ≫ m₄ = prod.map e (𝟙 Q) ≫ r') (hpe : p ≫ e = 𝟙 P) (h₆ : m₆ = 𝟙 T₃) :
    t₀ ≫ m₁ ≫ m₂ ≫ m₄ ≫ m₆ = r' ≫ 𝟙 T₃ := by
  rw [h₆, ← Category.assoc t₀, s₁, hh, prod.map_id_id, Category.id_comp, ← Category.assoc t₁, s₂,
    Category.assoc, ← Category.assoc r, s₄]
  simp only [← Category.assoc, prod.map_map, hpe, Category.id_comp, prod.map_id_id,
    Category.comp_id]

end Products

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

/-- **The pairing of the projection-formula map** `F ⊗ f_*G ⟶ f_*(f^*F ⊗ G)`: two local
sections are paired by `f_*` of the universal pairing of `f^*F` and `G`, applied to the unit
image of the first and to the second. -/
theorem tensorSectionPairing_comp_pushforwardTensorMap
    (F : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (G : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    tensorSectionPairing F ((pushforwardModules f).obj G) ≫
        (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map (pushforwardTensorMap f F G) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app F)) (𝟙 _) ≫
        (PreservesLimitPair.iso f.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf X.O) ((f.pullbackModules).obj F))
          (moduleSheaf (Tensor.ringSheaf X.O) G)).inv ≫
        f.toToposHom.pushforward.map (tensorSectionPairing ((f.pullbackModules).obj F) G) := by
  have hc := (eq_pullbackTensorIso_hom_app_iff f F ((pushforwardModules f).obj G)
    ((pullbackTensorIso f).hom.app (F, (pushforwardModules f).obj G))).1 rfl
  have hX : tensorSectionPairing F ((pushforwardModules f).obj G) ≫
      (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app
            (((Functor.uncurry.obj (Tensor.sheafTensor Y.O))).obj (F, (pushforwardModules f).obj
                G)) ≫
          (pushforwardModules f).map ((pullbackTensorIso f).hom.app
            (F, (pushforwardModules f).obj G))) =
      prod.map ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
          ((pullbackAdjPushforwardModules f).unit.app F))
          ((moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
            ((pullbackAdjPushforwardModules f).unit.app ((pushforwardModules f).obj G))) ≫
        (PreservesLimitPair.iso f.toToposHom.pushforward
          (moduleSheaf (Tensor.ringSheaf X.O) ((f.pullbackModules).obj F))
          (moduleSheaf (Tensor.ringSheaf X.O)
            ((f.pullbackModules).obj ((pushforwardModules f).obj G)))).inv ≫
        f.toToposHom.pushforward.map (tensorSectionPairing ((f.pullbackModules).obj F)
          ((f.pullbackModules).obj ((pushforwardModules f).obj G))) := by
    refine Eq.trans ?_ hc
    refine pairing_ext _ fun U a b => ?_
    refine (pairingApp_comp _ _ U a b).trans (Eq.trans ?_
      (pairingApp_pairingOfTensorHom _ U a b).symm)
    exact congrArg _ (pairingApp_tensorSectionPairing F _ U a b)
  have hB : ((Functor.uncurry.obj (Tensor.sheafTensor X.O))).map
      (𝟙 ((f.pullbackModules).obj F) ×ₘ (pullbackAdjPushforwardModules f).counit.app G) =
      ((Tensor.sheafTensor X.O).obj ((f.pullbackModules).obj F)).map
        ((pullbackAdjPushforwardModules f).counit.app G) := by
    simp
  have hR := tensorSectionPairing_comp_map_right (A := (f.pullbackModules).obj F)
    ((pullbackAdjPushforwardModules f).counit.app G)
  have htri := congrArg (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map
    ((pullbackAdjPushforwardModules f).right_triangle_components G)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at htri
  rw [pushforwardTensorMap_eq, Stacks.ProjectionFormula.adjunctionTensorMapSnd,
    Adjunction.homEquiv_unit, hB, CategoryTheory.Functor.map_comp (pushforwardModules f),
    ← Category.assoc, CategoryTheory.Functor.map_comp (moduleSheafFunctor _), ← Category.assoc, hX]
  have hpf : ∀ {M M' : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (m : M ⟶ M'),
      (moduleSheafFunctor (Tensor.ringSheaf Y.O)).map ((pushforwardModules f).map m) =
        f.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map m) :=
    fun _ => Sheaf.hom_ext_sections fun _ _ => rfl
  rw [hpf] at htri
  rw [hpf]
  refine (prodMap_comp_preservesLimitPair_iso_inv_comp_map_comp _ _ _ _ _ _ _ hR).trans ?_
  exact congrArg (fun z => prod.map _ z ≫ _) htri

end ProjectionFormula

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

/-- The identification `i_*J ⊗ i_*F ≅ i_*(J ⊗ F)` as the projection-formula map of
`(Sh(C), O) ⟶ (Sh(D), i_*O)` read through the comparisons of direct images and the counit. -/
theorem pushforwardModuleTensorIso_hom_eq
    (F J : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) :
    (pushforwardModuleTensorIso hi F J).hom =
    ((Tensor.sheafTensor (baseRing i)).obj ((thickenedModulesFunctor i).obj J)).map
        ((pushforwardModulesHomIso i).inv.app F) ≫
      pushforwardTensorMap (pushforwardModulesHom i) ((thickenedModulesFunctor i).obj J) F ≫
      (Stacks.Sheaves.RingedToposModules.pushforwardModules (pushforwardModulesHom i)).map
        (((Tensor.sheafTensor X.O).flip.obj F).map
          ((pullbackPushforwardModuleNatIso hi).hom.app J)) ≫
      (pushforwardModulesHomIso i).hom.app (((Tensor.sheafTensor X.O).flip.obj F).obj J) := by
  simp only [pushforwardModuleTensorIso, pushforwardModuleTensorNatIso, Iso.app_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.leftUnitor_hom_app, Functor.comp_map]
  have h1 : ((pushforwardModuleFunctor i.toToposHom (Tensor.ringSheaf X.O)).isoWhiskerLeft
      ((Tensor.sheafTensor ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.mapIso
        ((pushforwardModulesHomIso i).app F).symm)).hom.app J =
      ((Tensor.sheafTensor (baseRing i)).obj ((thickenedModulesFunctor i).obj J)).map
        ((pushforwardModulesHomIso i).inv.app F) := rfl
  have hiso : ∀ G, IsIso (pushforwardTensorMap (pushforwardModulesHom i) G F) := by
    have := isEquivalence_pushforwardModules_pushforwardModulesHom hi
    have := (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (pushforwardModulesHom i)).isEquivalence_left_of_isEquivalence_right
    exact fun G => isIso_pushforwardTensorMap (pushforwardModulesHom i) G F
      inferInstance inferInstance
  have h2 : ((pushforwardModuleFunctor i.toToposHom (Tensor.ringSheaf X.O)).isoWhiskerLeft
      (pushforwardTensorNatIso (pushforwardModulesHom i) F hiso)).hom.app J =
      pushforwardTensorMap (pushforwardModulesHom i) ((thickenedModulesFunctor i).obj J) F := by
    change (pushforwardTensorNatIso (pushforwardModulesHom i) F hiso).hom.app
      ((pushforwardModuleFunctor i.toToposHom (Tensor.ringSheaf X.O)).obj J) = _
    exact (NatIso.ofComponents_hom_app _ _ _).trans (@asIso_hom _ _ _ _ _ (hiso _))
  have h3 : ((pushforwardModuleFunctor i.toToposHom (Tensor.ringSheaf X.O)).associator
      (pushforwardModulesHom i).pullbackModules
      ((Tensor.sheafTensor X.O).flip.obj F ⋙
        Stacks.Sheaves.RingedToposModules.pushforwardModules (pushforwardModulesHom i))).inv.app J =
      𝟙 _ := rfl
  have h6 : (((Tensor.sheafTensor X.O).flip.obj F).isoWhiskerLeft
      (pushforwardModulesHomIso i)).hom.app J =
      (pushforwardModulesHomIso i).hom.app (((Tensor.sheafTensor X.O).flip.obj F).obj J) := rfl
  rw [h1, h2, h3, h6]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ((Category.id_comp _).trans
    (congrArg (_ ≫ ·) (Category.id_comp _))))

omit hi [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The underlying morphism of sheaves of sets of `π_*` of a morphism is `i_*` of it. -/
theorem moduleSheafFunctor_map_pushforwardModules_map_pushforwardModulesHom
    {M M' : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (m : M ⟶ M') :
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules (pushforwardModulesHom i)).map m) =
      i.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map m) :=
  Sheaf.hom_ext_sections fun _ _ => rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The pushed universal pairing followed by `π_*` of `π^*i_*J ⊗ F ≅ J ⊗ F`. -/
theorem pushforward_tensorSectionPairing_comp_map_pullbackPushforwardModuleNatIso_hom
    (F J : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)) : ((PreservesLimitPair.iso
        i.toToposHom.pushforward
    (moduleSheaf (Tensor.ringSheaf X.O)
      ((pushforwardModulesHom i).pullbackModules.obj ((thickenedModulesFunctor i).obj J)))
    (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
    i.toToposHom.pushforward.map (tensorSectionPairing
      ((pushforwardModulesHom i).pullbackModules.obj ((thickenedModulesFunctor i).obj J)) F)) ≫
    (moduleSheafFunctor (Tensor.ringSheaf (baseRing i))).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules (pushforwardModulesHom i)).map
        (((Tensor.sheafTensor X.O).flip.obj F).map
          ((pullbackPushforwardModuleNatIso hi).hom.app J))) =
    prod.map (i.toToposHom.pushforward.map ((moduleSheafFunctor (Tensor.ringSheaf X.O)).map
        ((pullbackPushforwardModuleNatIso hi).hom.app J))) (𝟙 _) ≫
      (PreservesLimitPair.iso i.toToposHom.pushforward (moduleSheaf (Tensor.ringSheaf X.O) J)
        (moduleSheaf (Tensor.ringSheaf X.O) F)).inv ≫
      i.toToposHom.pushforward.map (tensorSectionPairing J F) := by
  rw [moduleSheafFunctor_map_pushforwardModules_map_pushforwardModulesHom]
  exact preservesLimitPair_iso_inv_comp_map_comp_left _ _ _ _ _
    (tensorSectionPairing_comp_map_left (B := F) ((pullbackPushforwardModuleNatIso hi).hom.app J))

end Deformation.ToposThickening

end
