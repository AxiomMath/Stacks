module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible sheaves of modules are closed under tensor product

Let `O` be a sheaf of commutative rings on a site `(C, J)`. A sheaf `L` of `O`-modules is
*invertible* when tensoring on the left by `L` is an equivalence of the category of sheaves of
`O`-modules. This file shows that the tensor product of two invertible sheaves of modules is
again invertible.

The tensor product of sheaves of modules is the sheafification of the tensor product of the
underlying presheaves of modules, so tensoring on the left by `L` is the composite
`SheafOfModules.forget ⋙ (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj L.val ⋙
sheafify`. The proof is the chain of natural isomorphisms
`tensorLeftFunctor (L ⊗ N) ≅ tensorLeftSheafifyFunctor (L.val ⊗ N.val)
  ≅ tensorLeftFunctor N ⋙ tensorLeftFunctor L`,
whose outer two steps erase a sheafification that has been applied one step too early. Both
rest on the fact that the morphisms inverted by sheafification are stable under tensoring,
which is Tag 05NA (`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight` and
`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft`); the middle step is
  the associator.

## Main definitions

* `Stacks.SheafOfModules.TensorLeftUniversal`: the universal property pinning down a tensor
  functor, namely that its values receive the pointwise presheaf tensor products universally.
* `Stacks.SheafOfModules.IsInvertible`: a sheaf of modules is invertible when a functor with
  that universal property is an equivalence.
* `PresheafOfModules.tensorBifunctor` supplies the tensor functors of presheaves, and
  `Stacks.SheafOfModules.Tensor.sheafTensor` supplies the tensor functors of sheaves. Fixed
  factors are expressed directly through these bifunctors rather than separate view definitions.
* `Stacks.SheafOfModules.tensorLeftSheafifyFunctorMap` and
  `Stacks.SheafOfModules.tensorLeftFunctorMap`: the natural transformation of those tensor
  functors induced by a morphism of the left factor, with its identity and composition laws. The
  left factor is not assumed invertible and the morphism is not assumed an isomorphism.

## Main results

* `Stacks.SheafOfModules.tensorProduct_isInvertible` is Tag 01CT (1), equivalently Tag 040A (1):
  the tensor product of two invertible sheaves of modules is invertible. The statement is proved
  for an arbitrary site, so the ringed-space and the ringed-site forms coincide here.
* `Stacks.SheafOfModules.tensorLeftFunctorObjIso`: tensoring by `L ⊗ N` is the composite of
  tensoring by `N` and tensoring by `L`.
* `Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence`: the
  universal-property form of invertibility agrees with the sheafified tensor functor being an
  equivalence, once the site has sheafification.
* `Stacks.SheafOfModules.TensorLeftUniversal.uniqueIso`: a tensor functor is unique up to a
  canonical natural isomorphism.

## Implementation notes

`IsInvertible` is stated through the universal property `TensorLeftUniversal` rather than
through the sheafified tensor functor, so that it makes sense on an arbitrary site, with no
sheafification instances. The sheafification hypotheses
`[J.WEqualsLocallyBijective AddCommGrpCat]` and `[HasWeakSheafify J AddCommGrpCat]` are
therefore assumed only from `tensorLeftSheafifyFunctor` onwards — but they *are* needed for
Tag 01CT itself, because its statement names the tensor product sheaf `L ⊗ N`, which is a
sheafification.

There is, in the pinned Mathlib, no monoidal structure on `SheafOfModules R`: the monoidal
structure lives on `PresheafOfModules` over a `CommRingCat`-valued presheaf
(`PresheafOfModules.monoidalCategory`), and the sheaf-level tensor product has to be assembled
from it by sheafification. `IsInvertible` below is the "tensoring is an equivalence" form
(Tag 0FFM (1)), not the "two-sided inverse" form (Tag 0FFN); the three-step chain of natural
isomorphisms described above is what this file uses, with the associator step carrying the
content of the general monoidal argument.

The general monoidal argument is nevertheless available. `CategoryTheory.MonoidalCategory
.IsInvertible` does not come from Mathlib; it is defined in
`StacksFrontier/CategoryTheory/Monoidal/InvertibleObject.lean`, which also already proves
`@[stacks 0FFM] invertible_tfae` and `HasInverse.tensorLeftEquivalence` for an arbitrary
monoidal category. And `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean` does supply
the monoidal structure, so the general fact *is* applicable — the comparison is
`Stacks.SheafOfModules.tensorLeftFunctorIsoTensorLeft` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleEquivalence.lean`, already proved and
tagged two directories away.

The site object and morphism universes `u`, `v` are independent of the section universe `w`.
The ring and module sections share the universe `w`, as Mathlib's monoidal structure on
presheaves of modules requires; nothing relates `w` to the size of the site.

## References

* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 040A](https://stacks.math.columbia.edu/tag/040A)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))

attribute [local instance] monoidalCategoryPresheafOfModules
attribute [local implicit_reducible] TensorSheafification.structureSheaf

/-- A tensor functor is characterized by the universal maps from the pointwise presheaf tensor
products to its values: its values are precisely the associated sheaves of the presheaf tensor
products, and this is expressed without requiring that every presheaf be sheafifiable. -/
structure TensorLeftUniversal
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) where
  /-- The natural maps from the presheaf tensor products. -/
  ι : SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
    (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj L.val ⟶
    F ⋙ SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)
  /-- Every map from the presheaf tensor product to a sheaf factors uniquely through `ι`. -/
  bijective (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
    hO)) :
    Function.Bijective (fun f : F.obj M ⟶ N =>
      ι.app M ≫ (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO)).map f)

/-- **Stacks Project, Tag 01CS**, equivalently **Tag 0409 (2)**. A sheaf of `O`-modules is
*invertible* when its tensor functor is an equivalence. The universal property specifies that
tensor functor independently of any chosen construction of sheafification, hence on every
site; so the ringed-space form of the definition and the ringed-site form coincide here. -/
@[stacks 01CS "invertible", stacks 0409 "invertible"]
class IsInvertible
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) : Prop
      where
  /-- Tensoring by `L` is represented by an equivalence. -/
  exists_tensorFunctor : ∃ F : SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    F.IsEquivalence ∧ Nonempty (TensorLeftUniversal O hO L F)

namespace TensorLeftUniversal

variable {O hO}
  {L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
  {F G : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}

/-- The unique extension of a map out of a presheaf tensor product. The source of `f` is
spelled as the value of the functor
`SheafOfModules.forget ⋙ (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj L.val`, which is
the presheaf tensor product `L.val ⊗ M.val`, so that `ι_lift` applies to the components of a
natural transformation without unfolding. -/
noncomputable def lift (a : TensorLeftUniversal O hO L F)
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (f : (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj L.val).obj M ⟶
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).obj
        N) : F.obj M ⟶ N :=
  (a.bijective M N).surjective f |>.choose

@[reassoc (attr := simp)]
theorem ι_lift (a : TensorLeftUniversal O hO L F)
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    (f : (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj L.val).obj M ⟶
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).obj
        N) :
    a.ι.app M ≫ (SheafOfModules.forget _).map (a.lift M N f) = f :=
  (a.bijective M N).surjective f |>.choose_spec

/-- The comparison morphism between two functors satisfying the tensor universal property. -/
noncomputable def comparison (a : TensorLeftUniversal O hO L F)
    (b : TensorLeftUniversal O hO L G) : F ⟶ G where
  app M := a.lift M (G.obj M) (b.ι.app M)
  naturality {M N} f := by
    apply (a.bijective M (G.obj N)).injective
    change a.ι.app M ≫ (SheafOfModules.forget _).map
        (F.map f ≫ a.lift N (G.obj N) (b.ι.app N)) =
      a.ι.app M ≫ (SheafOfModules.forget _).map
        (a.lift M (G.obj M) (b.ι.app M) ≫ G.map f)
    simp only [Functor.map_comp, ← Category.assoc]
    have ha := a.ι.naturality f
    dsimp only [Functor.comp_map] at ha
    rw [← ha]
    simp only [Category.assoc, ι_lift]
    exact b.ι.naturality f

/-- A tensor functor is unique up to its canonical natural isomorphism. -/
noncomputable def uniqueIso (a : TensorLeftUniversal O hO L F)
    (b : TensorLeftUniversal O hO L G) : F ≅ G where
  hom := a.comparison b
  inv := b.comparison a
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply (a.bijective M (F.obj M)).injective
    let forward := a.lift M (G.obj M) (b.ι.app M)
    let backward := b.lift M (F.obj M) (a.ι.app M)
    have forwardUnit : a.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map forward =
          b.ι.app M := a.ι_lift M (G.obj M) (b.ι.app M)
    have backwardUnit : b.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward =
          a.ι.app M := b.ι_lift M (F.obj M) (a.ι.app M)
    change a.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map
          (forward ≫ backward) =
      a.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map (𝟙 (F.obj M))
    calc
      _ = a.ι.app M ≫
          ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map forward ≫
            (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward) :=
        congrArg (fun morphism => a.ι.app M ≫ morphism)
          ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map_comp
            forward backward)
      _ = (a.ι.app M ≫
          (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map forward) ≫
            (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward :=
        (Category.assoc _ _ _).symm
      _ = b.ι.app M ≫
          (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward :=
        congrArg (fun morphism => morphism ≫
          (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward)
          forwardUnit
      _ = a.ι.app M := backwardUnit
      _ = _ := (Category.comp_id (a.ι.app M)).symm.trans
        (congrArg (fun morphism => a.ι.app M ≫ morphism)
          ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map_id
            (F.obj M)).symm)
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply (b.bijective M (G.obj M)).injective
    let forward := b.lift M (F.obj M) (a.ι.app M)
    let backward := a.lift M (G.obj M) (b.ι.app M)
    have forwardUnit : b.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map forward =
          a.ι.app M := b.ι_lift M (F.obj M) (a.ι.app M)
    have backwardUnit : a.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward =
          b.ι.app M := a.ι_lift M (G.obj M) (b.ι.app M)
    change b.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map
          (forward ≫ backward) =
      b.ι.app M ≫
        (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map (𝟙 (G.obj M))
    calc
      _ = b.ι.app M ≫
          ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map forward ≫
            (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward) :=
        congrArg (fun morphism => b.ι.app M ≫ morphism)
          ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map_comp
            forward backward)
      _ = (b.ι.app M ≫
          (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map forward) ≫
            (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward :=
        (Category.assoc _ _ _).symm
      _ = a.ι.app M ≫
          (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward :=
        congrArg (fun morphism => morphism ≫
          (SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map backward)
          forwardUnit
      _ = b.ι.app M := backwardUnit
      _ = _ := (Category.comp_id (b.ι.app M)).symm.trans
        (congrArg (fun morphism => b.ι.app M ≫ morphism)
          ((SheafOfModules.forget (TensorSheafification.structureSheaf O hO)).map_id
            (G.obj M)).symm)

end TensorLeftUniversal

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Tensoring on the left is functorial in the left factor**: a morphism `A ⟶ B` of presheaves
of modules induces a natural transformation `(A ⊗ -)^# ⟶ (B ⊗ -)^#` of the sheafified tensor
functors, by tensoring on the right with each sheaf and then sheafifying.

Nothing here is invertible: `Stacks.SheafOfModules.tensorLeftSheafifyFunctorMapIso` is this very
transformation at a morphism that sheafification inverts, and is built from it. -/
noncomputable def tensorLeftSheafifyFunctorMap
    {A B : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj} (f : A ⟶ B) :
    (SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj A ⋙
      TensorSheafification.sheafify O hO) ⟶
    (SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj B ⋙
      TensorSheafification.sheafify O hO) :=
  Functor.whiskerRight
    (Functor.whiskerLeft
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).map f))
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO)

@[simp]
theorem tensorLeftSheafifyFunctorMap_id
    (A : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :
    tensorLeftSheafifyFunctorMap O hO (𝟙 A) = 𝟙 _ := by
  simp only [tensorLeftSheafifyFunctorMap, CategoryTheory.Functor.map_id,
    Functor.whiskerLeft_id', Functor.whiskerRight_id']
  rfl

@[simp]
theorem tensorLeftSheafifyFunctorMap_comp
    {A B D : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj}
    (f : A ⟶ B) (g : B ⟶ D) :
    tensorLeftSheafifyFunctorMap O hO (f ≫ g) =
      tensorLeftSheafifyFunctorMap O hO f ≫ tensorLeftSheafifyFunctorMap O hO g := by
  simp only [tensorLeftSheafifyFunctorMap, CategoryTheory.Functor.map_comp,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp]

/-- **Tensoring on the left by a sheaf of modules is functorial in that sheaf**: a morphism
`L ⟶ N` of sheaves of `O`-modules induces `(L ⊗ -) ⟶ (N ⊗ -)`. -/
noncomputable def tensorLeftFunctorMap
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (f : L ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L) ⟶
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N) :=
  tensorLeftSheafifyFunctorMap O hO
    ((SheafOfModules.forget
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)).map f)

@[simp]
theorem tensorLeftFunctorMap_id
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorLeftFunctorMap O hO (𝟙 L) = 𝟙 _ :=
  tensorLeftSheafifyFunctorMap_id O hO _

@[simp]
theorem tensorLeftFunctorMap_comp
    {L N P : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (f : L ⟶ N) (g : N ⟶ P) :
    tensorLeftFunctorMap O hO (f ≫ g) =
      tensorLeftFunctorMap O hO f ≫ tensorLeftFunctorMap O hO g :=
  tensorLeftSheafifyFunctorMap_comp O hO _ _

/-- The sheafified tensor functor has the tensor universal property. -/
noncomputable def tensorLeftFunctorUniversal
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    TensorLeftUniversal O hO L (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L)) where
  ι := Functor.whiskerLeft
    (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj L.val)
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit
  bijective M N :=
    ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).homEquiv
      (PresheafOfModules.tensorObj (O := O) L.val M.val)
      N).bijective

/-- The universal-property definition of invertibility agrees with the constructed tensor
functor being an equivalence. -/
theorem isInvertible_iff_tensorLeftFunctor_isEquivalence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    IsInvertible O hO L ↔ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
        (forget₂ CommRingCat RingCat) hO⟩).obj L)).IsEquivalence := by
  constructor
  · rintro ⟨F, hF, ⟨a⟩⟩
    let := hF
    exact @Functor.isEquivalence_of_iso _ _ _ _ _ _
      (a.uniqueIso (tensorLeftFunctorUniversal O hO L)) hF
  · intro h
    exact ⟨_, h, ⟨tensorLeftFunctorUniversal O hO L⟩⟩

/-- The existing tensor-functor API applies to any invertible sheaf of modules. -/
instance tensorLeftFunctor_isEquivalence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [h : IsInvertible O hO L] : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O
        (forget₂ CommRingCat RingCat) hO⟩).obj L)).IsEquivalence :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L).mp h

/-- Sheafifying a presheaf of modules before tensoring does not change the sheafified tensor
functor: the comparison map is the sheafification unit whiskered on the right, which
sheafification inverts by Tag 05NA. -/
noncomputable def tensorLeftSheafifyFunctorIsoSheafify
    (A : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)
      :
    (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj A ⋙
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO) ≅
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj
        (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A).val) ⋙
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO) :=
  let β := Functor.whiskerRight
    (Functor.whiskerLeft (SheafOfModules.forget
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).map
        (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A)))
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO)
  have h : ∀ F, IsIso (β.app F) := fun F =>
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A) F.val
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO A)
  NatIso.ofComponents (fun F => @asIso _ _ _ _ (β.app F) (h F)) fun f => β.naturality f

/-- Tensoring by a presheaf tensor product `A ⊗ B` is the composite of tensoring by `B` and
tensoring by `A`. The intermediate sheafification is erased by Tag 05NA; the remaining content
is the associator. -/
noncomputable def tensorLeftSheafifyFunctorTensorIso
    (A B : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO).obj) :
    (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj (A ⊗ B) ⋙
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO) ≅
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj B ⋙
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO) ⋙
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj A ⋙
      Stacks.SheafOfModules.TensorSheafification.sheafify O hO) :=
  let β := Functor.whiskerRight
    (Functor.whiskerLeft
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj B)
      (Functor.whiskerRight (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O
        hO).unit ((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj A)))
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO)
  have h : ∀ F, IsIso (β.app F) := fun F =>
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft O hO A
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO (B ⊗ F.val))
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO (B ⊗ F.val))
  NatIso.ofComponents
      (F := SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj
          (PresheafOfModules.tensorObj A B) ⋙ TensorSheafification.sheafify O hO)
      (G := SheafOfModules.forget (TensorSheafification.structureSheaf O hO) ⋙
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj B ⋙
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O).obj A ⋙
        TensorSheafification.sheafify O hO)
      (fun M => (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso
        (α_ A B M.val))
      (fun {M N} morphism => by
        change
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
              (PresheafOfModules.tensorHom (𝟙 (PresheafOfModules.tensorObj A B)) morphism.val) ≫
            (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
              (α_ A B N.val).hom =
          (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
              (α_ A B M.val).hom ≫
            (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
              (PresheafOfModules.tensorHom (𝟙 A)
                (PresheafOfModules.tensorHom (𝟙 B) morphism.val))
        refine ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map_comp _ _).symm.trans
          ?_
        refine (congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map ?_).trans
          ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map_comp _ _)
        apply PresheafOfModules.hom_ext
        intro openSet
        apply ModuleCat.hom_ext
        apply TensorProduct.ext_threefold
        intro leftSection middleSection rightSection
        rfl) ≪≫
    NatIso.ofComponents (fun F => @asIso _ _ _ _ (β.app F) (h F)) fun f => β.naturality f

/-- Tensoring by the tensor product sheaf `L ⊗ N` is the composite of tensoring by `N` and
tensoring by `L`. -/
noncomputable def tensorLeftFunctorObjIso
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L)).obj N)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N) ⋙
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L) :=
  (tensorLeftSheafifyFunctorIsoSheafify O hO (L.val ⊗ N.val)).symm ≪≫
    tensorLeftSheafifyFunctorTensorIso O hO L.val N.val

/-- **Stacks Project, Tag 01CT (1), Tag 040A (1).** The tensor product of two invertible sheaves
of modules is invertible. -/
@[stacks 01CT "tensor_invertible", stacks 040A "part (1)", instance]
theorem tensorProduct_isInvertible
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] [IsInvertible O hO N] :
    IsInvertible O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj L)).obj N) :=
  (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO _).mpr
    (Functor.isEquivalence_of_iso (tensorLeftFunctorObjIso O hO L N).symm)

end Sheafification

end Stacks.SheafOfModules
