module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat

/-!
# Tensoring a sheaf of modules with the associated sheaf of a presheaf of modules

Let `O` be a presheaf of commutative rings on a site, let `O♯` be an associated sheaf of
commutative rings and let `a : O ⟶ O♯` be the comparison morphism. Tag 0GMW
(`PresheafOfModules.sheafificationTensorIso`) compares the tensor product of two *associated
sheaves* with the associated sheaf of the objectwise tensor product of the two *presheaves*.
Consumers almost always have one factor which is already a sheaf — a coefficient module — and
one which is only a presheaf, for instance the presheaf of relative differentials. This file
specialises Tag 0GMW to that situation:

`F ⊗_{O♯} G♯ ≅ (F|_O ⊗_O G)♯`

for `F` a sheaf of `O♯`-modules and `G` a presheaf of `O`-modules, together with its
naturality in `F`, and the variant with both factors sheaves,

`F ⊗_{O♯} G ≅ (F|_O ⊗_O G|_O)♯`.

The second one says that the base-change morphism from the tensor product over `O` to the
tensor product over `O♯` becomes invertible after sheafification, which is what lets a
computation performed with the tensor product over `O` — where the sections of a presheaf of
`O`-modules are available — be read off the tensor product sheaf.

## Main definitions

* `PresheafOfModules.restrictSheafFunctor`: a sheaf of `O♯`-modules read as a presheaf of
  `O`-modules, as a functor. Its action on objects is `PresheafOfModules.restrictSheaf`.
* `PresheafOfModules.sheafifyRestrictSheafIso`: the associated sheaf of the restriction of a
  sheaf of modules is that sheaf. This is the counit of the sheafification adjunction, which
  Mathlib already knows to be invertible.
* `PresheafOfModules.tensorSheafifyMixedIso`: the comparison above, for one sheaf and one
  presheaf.
* `PresheafOfModules.tensorSheafifyRestrictIso`: the comparison above, for two sheaves.

## Main results

* `PresheafOfModules.tensorSheafifyMixedIso_inv_naturality` and
  `PresheafOfModules.tensorSheafifyMixedIso_hom_naturality`: naturality in the sheaf factor,
  for each direction of the comparison. This is what transports a morphism of functors on
  sheaves of modules — such as the inclusion of the sequence of principal parts — across the
  comparison.
* `PresheafOfModules.tensorSheafifyRestrictIso_inv_naturality`: the same for two sheaves,
  natural in the first factor with the second one fixed.
* `Stacks.TensorSheafifyMixed.tensorObj_eq` and
  `Stacks.TensorSheafifyMixed.sheafTensorRight_obj_eq`: the objectwise tensor product and the
  tensor product sheaf of `StacksFrontier.CategoryTheory.Sites.Modules.Flat` are the ones used
  here, each by `rfl`. So the flatness vocabulary and this comparison are about one tensor
  product and nothing has to be transported between them.

## Implementation notes

The module universes of the two factors and the universe of the ring are independent, and that
is inherited from Tag 0GMW rather than arranged here: `PresheafOfModules.tensorObj` does not go
through Mathlib's monoidal structure on presheaves of modules, whose instance forces the module
universe to equal the ring universe.

Everything is stated objectwise, with naturality as a separate equation, rather than as an
isomorphism of functors. The functor-level statement is the natural one, and it does not
elaborate: whiskering Tag 0GMW's isomorphism of bifunctors against
`CategoryTheory.Functor.prod` makes the unifier unfold the sheafification functor and exhausts
the heartbeat budget, which is the same failure
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor` records for the `tensorHom`
spelling of `tensorSheafBifunctor_map`. For the same reason the naturality proofs are routed
through `PresheafOfModules.tensorSheafifyComparison_naturality`, whose two sides are already in
the shape the unifier can see, rather than through the naturality of the bifunctor isomorphism.

A universe annotation on `PresheafOfModules.sheafificationAdjunction` is needed in
`sheafifyRestrictSheafIso`: the component of the counit at a sheaf does not determine the module
universe before the `HasWeakSheafify` instance is resolved, and with instances present at three
universes the elaborator picks the wrong one.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

open scoped TensorProduct

universe v u w z z₁

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]

/-- Sheaves of `O♯`-modules read as presheaves of `O`-modules, as a functor. On objects this
is `PresheafOfModules.restrictSheaf`. -/
noncomputable abbrev restrictSheafFunctor :
    SheafOfModules.{z} (toRingCat J Osharp) ⥤
      PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat) :=
  SheafOfModules.forget (toRingCat J Osharp) ⋙ restrictScalars (toRingCatMap J a)

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]

/-- The associated sheaf of the restriction of a sheaf of `O♯`-modules is that sheaf: the
counit of the sheafification adjunction, which Mathlib knows to be invertible. -/
noncomputable def sheafifyRestrictSheafIso (F : SheafOfModules.{z} (toRingCat J Osharp)) :
    (moduleSheafification.{v, u, w, z} J a).obj
        ((restrictSheafFunctor.{v, u, w, z} J a).obj F) ≅ F :=
  asIso ((PresheafOfModules.sheafificationAdjunction.{z, v, w, u} (toRingCatMap J a)).counit.app F)

/-- Naturality of `PresheafOfModules.sheafifyRestrictSheafIso`. -/
lemma sheafifyRestrictSheafIso_naturality {F F' : SheafOfModules.{z} (toRingCat J Osharp)}
    (f : F ⟶ F') :
    (moduleSheafification.{v, u, w, z} J a).map ((restrictSheafFunctor.{v, u, w, z} J a).map f) ≫
        (sheafifyRestrictSheafIso.{v, u, w, z} J a F').hom =
      (sheafifyRestrictSheafIso.{v, u, w, z} J a F).hom ≫ f :=
  (PresheafOfModules.sheafificationAdjunction.{z, v, w, u} (toRingCatMap J a)).counit.naturality f

/-- The sheafification unit of the restriction of a sheaf of modules, followed by the restriction
of `PresheafOfModules.sheafifyRestrictSheafIso`, is the identity. -/
lemma sheafifyRestrictSheafIso_unit_apply (F : SheafOfModules.{z} (toRingCat J Osharp))
    (X : Cᵒᵖ) (x : F.val.obj X) :
    Hom.app (sheafifyRestrictSheafIso.{v, u, w, z} J a F).hom.val X
        (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a
          ((restrictSheafFunctor.{v, u, w, z} J a).obj F)) X x) = x :=
  hom_congr_apply ((PresheafOfModules.sheafificationAdjunction.{z, v, w, u}
    (toRingCatMap J a)).right_triangle_components F) X x

end

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z₁}] [HasWeakSheafify J AddCommGrpCat.{z₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z z₁}]
  [HasWeakSheafify J AddCommGrpCat.{max z z₁}]

section Mixed

variable (F : SheafOfModules.{z} (toRingCat J Osharp))
  (G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The tensor product of a sheaf of modules with the associated sheaf of a presheaf of
modules.** For `F` a sheaf of `O♯`-modules and `G` a presheaf of `O`-modules,
`F ⊗_{O♯} G♯ ≅ (F|_O ⊗_O G)♯`. This is Tag 0GMW with the first factor already a sheaf, and the
module universes of the two factors are independent of each other and of the universe of the
ring. -/
noncomputable def tensorSheafifyMixedIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj F).obj
        ((moduleSheafification.{v, u, w, z₁} J a).obj G) ≅
      (moduleSheafification.{v, u, w, max z z₁} J a).obj
        (tensorObj ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).mapIso
      ((sheafifyRestrictSheafIso.{v, u, w, z} J a F).symm)).app ((moduleSheafification.{v, u, w, z₁}
      J a).obj G) ≪≫
    (sheafificationTensorIso.{v, u, w, z, z₁} J a).app
      ((restrictSheafFunctor.{v, u, w, z} J a).obj F, G)

/-- The forward map of `tensorSheafifyMixedIso` is the tensor product with `G♯` of the inverse of
the counit isomorphism `(F|_O)♯ ≅ F`, followed by `tensorSheafifyDesc`. -/
lemma tensorSheafifyMixedIso_hom :
    (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F G).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map
          ((sheafifyRestrictSheafIso.{v, u, w, z} J a F).inv)).app ((moduleSheafification.{v, u, w,
          z₁} J a).obj G) ≫
        tensorSheafifyDesc.{v, u, w, z, z₁} J a
          ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G :=
  rfl

/-- The inverse of `tensorSheafifyMixedIso` is `tensorSheafifyComparison` followed by the tensor
product with `G♯` of the counit isomorphism `(F|_O)♯ ≅ F`. -/
lemma tensorSheafifyMixedIso_inv :
    (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F G).inv =
      tensorSheafifyComparison.{v, u, w, z, z₁} J a
            ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map
            ((sheafifyRestrictSheafIso.{v, u, w, z} J a F).hom)).app ((moduleSheafification.{v, u,
            w, z₁} J a).obj G) :=
  rfl

/-- The comparison carries the sheafification-unit image of a pure tensor of sections to the
pure tensor of the section of `F` with the sheafification-unit image of the section of `G`.
This pins the comparison down, since those elements generate. -/
lemma tensorSheafifyMixedIso_inv_unit_tmul (X : Cᵒᵖ) (x : F.val.obj X) (y : G.obj X) :
    Hom.app (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F G).inv.val X
        (Hom.app (moduleSheafificationUnit.{v, u, w, max z z₁} J a
            (tensorObj ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G)) X (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val ((moduleSheafification.{v, u, w, z₁} J a).obj G).val)) X
        (x ⊗ₜ Hom.app (moduleSheafificationUnit.{v, u, w, z₁} J a G) X y) := by
  set φ : tensorObj ((moduleSheafification.{v, u, w, z} J a).obj
          ((restrictSheafFunctor.{v, u, w, z} J a).obj F)).val
        ((moduleSheafification.{v, u, w, z₁} J a).obj G).val ⟶
      tensorObj F.val ((moduleSheafification.{v, u, w, z₁} J a).obj G).val :=
    tensorHom (sheafifyRestrictSheafIso.{v, u, w, z} J a F).hom.val
      (𝟙 ((moduleSheafification.{v, u, w, z₁} J a).obj G).val) with hφ
  refine Eq.trans (congrArg (fun t ↦ Hom.app ((sheafification
      (𝟙 (toRingCat J Osharp).obj)).map φ).val X t)
    (tensorSheafifyComparison_unit_tmul J a
      ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G X x y)) ?_
  refine Eq.trans (unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj) φ X
    (Hom.app (moduleSheafificationUnit.{v, u, w, z} J a
        ((restrictSheafFunctor.{v, u, w, z} J a).obj F)) X x ⊗ₜ
      Hom.app (moduleSheafificationUnit.{v, u, w, z₁} J a G) X y)) ?_
  refine congrArg (fun t ↦ Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
      Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val ((moduleSheafification.{v, u, w, z₁} J a).obj G).val)) X t)
          ?_
  rw [hφ]
  refine Eq.trans (tensorHom_tmul _ _ X _ _) ?_
  exact congrArg₂ (fun p q ↦ p ⊗ₜ[(Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj X] q)
    (sheafifyRestrictSheafIso_unit_apply J a F X x) rfl

end Mixed

section MixedNaturality

variable {F F' : SheafOfModules.{z} (toRingCat J Osharp)} (f : F ⟶ F')
  (G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat))

/-- `PresheafOfModules.tensorSheafifyMixedIso` is natural in the sheaf factor. -/
lemma tensorSheafifyMixedIso_inv_naturality :
    (moduleSheafification.{v, u, w, max z z₁} J a).map
          (tensorHom ((restrictSheafFunctor.{v, u, w, z} J a).map f) (𝟙 G)) ≫
        (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F' G).inv =
      (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F G).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map f).app
            ((moduleSheafification.{v, u, w, z₁} J a).obj G) := by
  rw [tensorSheafifyMixedIso_inv, tensorSheafifyMixedIso_inv]
  have mapComp : ∀ {A B D : SheafOfModules.{z} (toRingCat J Osharp)} (g : A ⟶ B) (h : B ⟶ D),
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map (g ≫ h)).app
          ((moduleSheafification.{v, u, w, z₁} J a).obj G) =
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map g).app
            ((moduleSheafification.{v, u, w, z₁} J a).obj G) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map h).app
            ((moduleSheafification.{v, u, w, z₁} J a).obj G) := fun g h ↦
    congrArg (fun α ↦ NatTrans.app α ((moduleSheafification.{v, u, w, z₁} J a).obj G))
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map_comp g h)
  have unitId : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj
        ((moduleSheafification.{v, u, w, z} J a).obj
          ((restrictSheafFunctor.{v, u, w, z} J a).obj F'))).map
        ((moduleSheafification.{v, u, w, z₁} J a).map (𝟙 G)) = 𝟙 _ :=
    (congrArg (fun m ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj
        ((moduleSheafification.{v, u, w, z} J a).obj
          ((restrictSheafFunctor.{v, u, w, z} J a).obj F'))).map m)
      ((moduleSheafification.{v, u, w, z₁} J a).map_id G)).trans
      (CategoryTheory.Functor.map_id _ _)
  have pairMap : (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp)).map
        (sheafifyPairMap J a ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G
          ((restrictSheafFunctor.{v, u, w, z} J a).map f) (𝟙 G)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map
          ((moduleSheafification.{v, u, w, z} J a).map
            ((restrictSheafFunctor.{v, u, w, z} J a).map f))).app
        ((moduleSheafification.{v, u, w, z₁} J a).obj G) :=
    (congrArg (fun m ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map
        ((moduleSheafification.{v, u, w, z} J a).map
          ((restrictSheafFunctor.{v, u, w, z} J a).map f))).app
            ((moduleSheafification.{v, u, w, z₁} J a).obj G) ≫ m) unitId).trans
      (Category.comp_id _)
  have key := (congrArg (fun m ↦ m ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map
        (sheafifyRestrictSheafIso.{v, u, w, z} J a F').hom).app
          ((moduleSheafification.{v, u, w, z₁} J a).obj G)) pairMap).trans
    (((mapComp ((moduleSheafification.{v, u, w, z} J a).map
          ((restrictSheafFunctor.{v, u, w, z} J a).map f))
        (sheafifyRestrictSheafIso.{v, u, w, z} J a F').hom).symm.trans
      (congrArg (fun m ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁}
          Osharp).map m).app ((moduleSheafification.{v, u, w, z₁} J a).obj G))
        (sheafifyRestrictSheafIso_naturality J a f))).trans
      (mapComp (sheafifyRestrictSheafIso.{v, u, w, z} J a F).hom f))
  exact (Category.assoc _ _ _).symm.trans
    (((congrArg (fun m ↦ m ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map
          (sheafifyRestrictSheafIso.{v, u, w, z} J a F').hom).app
            ((moduleSheafification.{v, u, w, z₁} J a).obj G))
      (tensorSheafifyComparison_naturality.{v, u, w, z, z₁} J a
        ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G
        ((restrictSheafFunctor.{v, u, w, z} J a).map f) (𝟙 G))).trans
      (Category.assoc _ _ _)).trans
      ((congrArg (fun m ↦ tensorSheafifyComparison.{v, u, w, z, z₁} J a
          ((restrictSheafFunctor.{v, u, w, z} J a).obj F) G ≫ m) key).trans
        (Category.assoc _ _ _).symm))

/-- `PresheafOfModules.tensorSheafifyMixedIso` is natural in the sheaf factor. -/
lemma tensorSheafifyMixedIso_hom_naturality :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map f).app
        ((moduleSheafification.{v, u, w, z₁} J a).obj G) ≫
        (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F' G).hom =
      (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F G).hom ≫
        (moduleSheafification.{v, u, w, max z z₁} J a).map
          (tensorHom ((restrictSheafFunctor.{v, u, w, z} J a).map f) (𝟙 G)) :=
  ((Iso.eq_inv_comp _).mp
    (((Iso.comp_inv_eq _).mp
        (tensorSheafifyMixedIso_inv_naturality.{v, u, w, z, z₁} J a f G)).trans
      (Category.assoc _ _ _))).symm

end MixedNaturality

section BothSheaves

/-- **The tensor product sheaf of two sheaves of modules, as the associated sheaf of their
objectwise tensor product over `O`.** The base-change morphism from the tensor product over `O`
to the tensor product over `O♯` becomes invertible after sheafification. -/
noncomputable def tensorSheafifyRestrictIso
    (F : SheafOfModules.{z} (toRingCat J Osharp))
    (G : SheafOfModules.{z₁} (toRingCat J Osharp)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj F).obj G ≅
      (moduleSheafification.{v, u, w, max z z₁} J a).obj
        (tensorObj ((restrictSheafFunctor.{v, u, w, z} J a).obj F)
          ((restrictSheafFunctor.{v, u, w, z₁} J a).obj G)) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj F).mapIso
      ((sheafifyRestrictSheafIso.{v, u, w, z₁} J a G).symm) ≪≫
    tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F
      ((restrictSheafFunctor.{v, u, w, z₁} J a).obj G)

/-- The inverse of `tensorSheafifyRestrictIso` is the inverse of `tensorSheafifyMixedIso` applied
to `G|_O`, followed by the tensor product of `F` with the counit isomorphism `(G|_O)♯ ≅ G`. -/
lemma tensorSheafifyRestrictIso_inv (F : SheafOfModules.{z} (toRingCat J Osharp))
    (G : SheafOfModules.{z₁} (toRingCat J Osharp)) :
    (tensorSheafifyRestrictIso.{v, u, w, z, z₁} J a F G).inv =
      (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F
            ((restrictSheafFunctor.{v, u, w, z₁} J a).obj G)).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj F).map
            ((sheafifyRestrictSheafIso.{v, u, w, z₁} J a G).hom) :=
  rfl

/-- `PresheafOfModules.tensorSheafifyRestrictIso` is natural in the first factor. -/
lemma tensorSheafifyRestrictIso_inv_naturality
    {F F' : SheafOfModules.{z} (toRingCat J Osharp)} (f : F ⟶ F')
    (G : SheafOfModules.{z₁} (toRingCat J Osharp)) :
    (moduleSheafification.{v, u, w, max z z₁} J a).map
          (tensorHom ((restrictSheafFunctor.{v, u, w, z} J a).map f)
            (𝟙 ((restrictSheafFunctor.{v, u, w, z₁} J a).obj G))) ≫
        (tensorSheafifyRestrictIso.{v, u, w, z, z₁} J a F' G).inv =
      (tensorSheafifyRestrictIso.{v, u, w, z, z₁} J a F G).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map f).app G := by
  rw [tensorSheafifyRestrictIso_inv, tensorSheafifyRestrictIso_inv]
  exact (Category.assoc _ _ _).symm.trans
    (((congrArg (fun m ↦ m ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).obj F').map
          (sheafifyRestrictSheafIso.{v, u, w, z₁} J a G).hom)
      (tensorSheafifyMixedIso_inv_naturality.{v, u, w, z, z₁} J a f
        ((restrictSheafFunctor.{v, u, w, z₁} J a).obj G))).trans
      (Category.assoc _ _ _)).trans
      ((congrArg (fun m ↦ (tensorSheafifyMixedIso.{v, u, w, z, z₁} J a F
            ((restrictSheafFunctor.{v, u, w, z₁} J a).obj G)).inv ≫ m)
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z₁} Osharp).map f).naturality
            (sheafifyRestrictSheafIso.{v, u, w, z₁} J a G).hom).symm)).trans
        (Category.assoc _ _ _).symm))

end BothSheaves

end PresheafOfModules

namespace Stacks.TensorSheafifyMixed

open PresheafOfModules AlgebraicGeometry

variable {C : Type u} [Category.{v} C]

/-- The objectwise tensor product of presheaves of modules used by the flatness vocabulary of
`StacksFrontier.CategoryTheory.Sites.Modules.Flat` is `PresheafOfModules.tensorObj`. -/
lemma tensorObj_eq {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat))
    (G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)) :
    SheafOfModules.PresheafOfModules.tensorObj (O := O) F G = tensorObj F G :=
  rfl

/-- The tensor product sheaf used by the flatness vocabulary of
`StacksFrontier.CategoryTheory.Sites.Modules.Flat` is
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
lemma sheafTensorRight_obj_eq {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
    (Osharp : Sheaf J CommRingCat.{w}) (F G : SheafOfModules.{z} (toRingCat J Osharp)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).flip.obj F).obj G =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp).obj G).obj F :=
  rfl

end Stacks.TensorSheafifyMixed
