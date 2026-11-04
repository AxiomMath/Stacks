module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainValue
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesComp
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The mate of a transformation of direct images, on the unit of Stacks 03CZ

Let `f, g : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be two morphisms of ringed topoi with the same source and
target, in the sense of `Stacks.Sheaves.RingedToposModules.RingedToposHom`. A transformation
`τ : f_* ⟶ g_*` of the direct images of sheaves of modules has a **mate**
`β : g^* ⟶ f^*` under the two adjunctions of Stacks 03D7, namely
`CategoryTheory.conjugateEquiv` of `τ`, and a transformation `t : f_* ⟶ g_*` of the direct images
of sheaves of *sets* has a mate `b : g⁻¹ ⟶ f⁻¹` under the two adjunctions of Stacks 03D3. This
file identifies the two on the unit of extension of scalars of Stacks 03CZ.

This is the situation of a 2-morphism of morphisms of ringed topoi (Stacks 04IC):
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pushforwardModulesMap` is such a `τ`, its
`AlgebraicGeometry.RingedToposHom.TwoMorphism.t` is such a `t`, and
`AlgebraicGeometry.RingedToposHom.TwoMorphism.pullbackModulesMap` is the mate `β`. Neither `τ`
nor `β` is assumed invertible.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.extendScalarsUnitSheafHom`: the unit of extension of scalars
  of Stacks 03CZ at `f⁻¹M`, read on underlying sheaves of sets, with target the underlying sheaf of
  sets of the pullback `f^*M`.
* `Stacks.SheafOfModules.mateTensorHom`: the mate applied to the two tensor factors of the target
  of the chain of Stacks 03EL.
* `Stacks.SheafOfModules.mateTensorSheafHom`: the same morphism on underlying sheaves of sets, with
  both endpoints the restrictions of scalars of the tensor products of the two pullbacks.

## Main results

In the namespace `Stacks.Sheaves.RingedToposModules`:

* `moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app`: the unit of Stacks 03D7 on
  underlying sheaves of sets is the unit of `f⁻¹ ⊣ f_*` followed by the direct image of the unit
  of extension of scalars.
* `extendScalarsUnitSheafHom_comp_mate`: the mate of a transformation of direct images of sheaves
  of modules commutes with the unit of extension of scalars and the mate of the underlying
  transformation of direct images of sheaves of sets: `η_g ≫ β_M = b_M ≫ η_f` on underlying
  sheaves of sets, where `η` is the unit of Stacks 03CZ.

Elsewhere:

* `Stacks.SheafOfModules.mateTensorHom_val_app_unit_tmul`: the value of
  `Stacks.SheafOfModules.mateTensorHom` on a pure tensor.
* `CategoryTheory.Limits.prodComparison_naturality`: the product comparison of a functor is natural
  in the functor.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Definition 18.2.2 (Tag 04IC)](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe v u w v' u' w' t

namespace CategoryTheory.Limits

variable {D : Type*} [Category D] {E : Type*} [Category E] [HasBinaryProducts D]
  [HasBinaryProducts E]

/-- The product comparison of a functor is natural in the functor: for a transformation
`α : Φ ⟶ Ψ`, the product comparison of `Φ` followed by `α` on the two factors is `α` on the
product followed by the product comparison of `Ψ`. -/
lemma prodComparison_naturality (Φ Ψ : D ⥤ E) (α : Φ ⟶ Ψ) (P Q : D) :
    prodComparison Φ P Q ≫ prod.map (α.app P) (α.app Q) =
      α.app (P ⨯ Q) ≫ prodComparison Ψ P Q := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, prodComparison_fst_assoc, Category.assoc,
      prodComparison_fst, α.naturality]
  · rw [Category.assoc, prod.map_snd, prodComparison_snd_assoc, Category.assoc,
      prodComparison_snd, α.naturality]

variable [HasFiniteProducts D]

/-- A finite-product-preserving functor `P` to types carries the product of two morphisms,
applied to a pair of elements, to the pair of the images of the two elements. -/
lemma map_prodMap_prodObjMk {P : D ⥤ Type t} [PreservesFiniteProducts P] {A A' B B' : D}
    (u : A ⟶ A') (v : B ⟶ B') (a : P.obj A) (b : P.obj B) :
    P.map (prod.map u v) (Functor.prodObjMk (P := P) a b) =
      Functor.prodObjMk (P := P) (P.map u a) (P.map v b) := by
  rw [Functor.map_prodMap_apply, Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]

end CategoryTheory.Limits

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-! ## The unit of Stacks 03D7 on underlying sheaves of sets -/

section Unit

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The unit `f⁻¹M ⟶ (f^*M)|_{f⁻¹O_D}` of extension of scalars of Stacks 03CZ at `f⁻¹M`, on
underlying sheaves of sets: its source is the inverse image of the underlying sheaf of sets of `M`
and its target is the underlying sheaf of sets of the pullback `f^*M` of Stacks 03D6 part (2). -/
def extendScalarsUnitSheafHom (f : RingedToposHom X Y)
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    f.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M) ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((f.pullbackModules).obj M) :=
  (Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
    ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))

/-- The unit of the adjunction of Stacks 03D7, on underlying sheaves of sets, is the unit of
`f⁻¹ ⊣ f_*` followed by the direct image of the unit of extension of scalars of Stacks 03CZ. -/
lemma moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app (f : RingedToposHom X Y)
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).unit.app M) =
      f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M) ≫
        f.toToposHom.pushforward.map (extendScalarsUnitSheafHom f M) := by
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (pullbackAdjPushforwardModules_unit_app f M)) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((extendRestrictScalarsAdjunction X.J (fSharpCommRing f)
            (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M))))
    (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_unit_app' f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M)) ?_
  exact congrArg
    (fun z ↦ f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M) ≫ z)
    (moduleSheafFunctor_map_directImageModules_map f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _)

end Unit

/-! ## The mate against the unit of extension of scalars -/

section Mate

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f g : RingedToposHom X Y) (tt : f.toToposHom.pushforward ⟶ g.toToposHom.pushforward)
  (τ : pushforwardModules f ⟶ pushforwardModules g)

/-- Let `τ : f_* ⟶ g_*` be a transformation of the direct images of sheaves of modules of
Stacks 03D6 part (1), let `t : f_* ⟶ g_*` be a transformation of the direct images of sheaves of
sets which is `τ` on underlying sheaves of sets, and let `β : g^* ⟶ f^*` and `b : g⁻¹ ⟶ f⁻¹` be
their mates under the adjunctions of Stacks 03D7 and of Stacks 03D3. Then on underlying sheaves of
sets

`η^g_M ≫ β_M = b_M ≫ η^f_M`,

where `η` is the unit of extension of scalars of Stacks 03CZ. -/
lemma extendScalarsUnitSheafHom_comp_mate
    (hτ : ∀ N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (τ.app N) =
        tt.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    extendScalarsUnitSheafHom g M ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
          (((conjugateEquiv (pullbackAdjPushforwardModules f)
            (pullbackAdjPushforwardModules g)).symm τ).app M) =
      ((conjugateEquiv f.toToposHom.adj g.toToposHom.adj).symm tt).app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M) ≫
        extendScalarsUnitSheafHom f M := by
  refine (g.toToposHom.adj.homEquiv
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M)
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((f.pullbackModules).obj M))).injective ?_
  refine Eq.trans (Adjunction.homEquiv_unit _ _ _ _)
    (Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm)
  refine Eq.trans (whisker_eq _ (g.toToposHom.pushforward.map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app g M).symm _) ?_
  refine Eq.trans (whisker_eq _ (moduleSheafFunctor_map_pushforwardModules_map g
    (((conjugateEquiv (pullbackAdjPushforwardModules f)
      (pullbackAdjPushforwardModules g)).symm τ).app M)).symm) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _).symm ?_
  refine Eq.trans
    (congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
      (unit_conjugateEquiv_symm (pullbackAdjPushforwardModules f)
        (pullbackAdjPushforwardModules g) τ M).symm) ?_
  refine Eq.trans
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_comp _ _) ?_
  refine Eq.trans (eq_whisker
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_unit_app f M) _) ?_
  refine Eq.trans (whisker_eq _ (hτ ((f.pullbackModules).obj M))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (tt.naturality (extendScalarsUnitSheafHom f M))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (unit_conjugateEquiv_symm f.toToposHom.adj g.toToposHom.adj tt
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) M)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (g.toToposHom.pushforward.map_comp _ _).symm

/-- On a local section, `Stacks.Sheaves.RingedToposModules.extendScalarsUnitSheafHom` is the unit
of extension of scalars applied to that section. -/
lemma sectionsFunctor_map_extendScalarsUnitSheafHom (h : RingedToposHom X Y)
    (M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (V : X.Cᵒᵖ)
    (x : ((inverseImageModules h.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M).val.obj V) :
    (Sheaf.sectionsFunctor X.J V).map (extendScalarsUnitSheafHom h M) x =
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing h)
          (inverseImageRingSheaf h.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
        ((inverseImageModules h.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)).val.app V x :=
  rfl

section Sections

variable {C₀ : Type u} [Category.{v} C₀] {J₀ : GrothendieckTopology C₀}
  [J₀.HasSheafCompose (forget RingCat.{t})] [J₀.HasSheafCompose (forget AddCommGrpCat.{t})]

omit [J₀.HasSheafCompose (forget RingCat.{t})] in
/-- A morphism of sheaves of modules, read on local sections of the underlying sheaves of sets,
is the morphism on local sections of the modules. -/
lemma sectionsFunctor_map_moduleSheafFunctor_map' (R : Sheaf J₀ RingCat.{t})
    {M N : SheafOfModules.{t} R} (φ : M ⟶ N) (V : C₀ᵒᵖ)
    (y : (Sheaf.sectionsFunctor J₀ V).obj (Sheaf.moduleSheaf R M)) :
    (Sheaf.sectionsFunctor J₀ V).map ((Sheaf.moduleSheafFunctor R).map φ) y =
      φ.val.app V y :=
  rfl

end Sections

end Mate

end Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

/-! ## The mate on the tensor product of the two pullbacks -/

section MatePairing

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (τ : pushforwardModules f ⟶ pushforwardModules g)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The mate of a transformation of direct images, applied to the two tensor factors of the target
of the chain of Stacks 03EL: the tensor, in the bifunctor of Stacks 0GMW, of the two components of
the mate. -/
def mateTensorHom :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((g.pullbackModules).obj F, (g.pullbackModules).obj G) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
    ((((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app F,
      ((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app G) :
      ((g.pullbackModules).obj F, (g.pullbackModules).obj G) ⟶
        ((f.pullbackModules).obj F, (f.pullbackModules).obj G))

/-- The mate on the tensor product of the two pullbacks carries the sheafification-unit image of
`y ⊗ₜ z` to the unit image of the pure tensor of the two values of the mate. -/
lemma mateTensorHom_val_app_unit_tmul (V : X.Cᵒᵖ)
    (y : ((g.pullbackModules).obj F).val.obj V)
    (z : ((g.pullbackModules).obj G).val.obj V) :
    (mateTensorHom f g τ F G).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
            (𝟙 _)).unit.app
            (((g.pullbackModules).obj F).val ⊗ ((g.pullbackModules).obj G).val)).app V
          (y ⊗ₜ[(ringPresheaf X.O.obj).obj V] z)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf X.J X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
          (𝟙 _)).unit.app
          (((f.pullbackModules).obj F).val ⊗ ((f.pullbackModules).obj G).val)).app V
        ((((conjugateEquiv (pullbackAdjPushforwardModules f)
                (pullbackAdjPushforwardModules g)).symm τ).app F).val.app V y
          ⊗ₜ[(ringPresheaf X.O.obj).obj V]
          (((conjugateEquiv (pullbackAdjPushforwardModules f)
                (pullbackAdjPushforwardModules g)).symm τ).app G).val.app V z) := by
  unfold mateTensorHom
  rw [Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
  exact TensorSheafification.sheafification_map_val_app_unit X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (PresheafOfModules.tensorHom (O := X.O.obj) (SheafOfModules.Hom.val
        (((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app F))
      (SheafOfModules.Hom.val
        (((conjugateEquiv (pullbackAdjPushforwardModules f)
          (pullbackAdjPushforwardModules g)).symm τ).app G))) V
    (y ⊗ₜ[(ringPresheaf X.O.obj).obj V] z)

/-- The mate on the tensor product of the two pullbacks, on underlying sheaves of sets, from the
restriction of scalars to `g⁻¹O_D` of the tensor product of the two `g`-pullbacks to the
restriction of scalars to `f⁻¹O_D` of the tensor product of the two `f`-pullbacks. -/
def mateTensorSheafHom :
    Sheaf.moduleSheaf
        (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((SheafOfModules.restrictScalars g.fSharpInverseImage).obj
          (pullbackTensorTarget g F G)) ⟶
      Sheaf.moduleSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
          (pullbackTensorTarget f F G)) :=
  (Sheaf.moduleSheafFunctor
      (inverseImageRingSheaf g.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
    ((SheafOfModules.restrictScalars g.fSharpInverseImage).map (mateTensorHom f g τ F G))

end MatePairing

end Stacks.SheafOfModules

end
