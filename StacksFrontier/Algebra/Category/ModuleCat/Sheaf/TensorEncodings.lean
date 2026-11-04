module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact

/-!
# Compatibility and transport for the canonical sheaf tensor

This file retains the ring and presheaf tensor comparisons used by the flatness and colimit
APIs, and transports preservation of colimits and presentation exactness to the native curried
`Stacks.SheafOfModules.Tensor.sheafTensor`. The module and coefficient universes remain
independent in the fixed-factor comparisons.

Reflexive comparisons between former names for the same canonical bifunctor have been removed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w z a

namespace Stacks.SheafOfModules.TensorEncodings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section RingSheaf

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The sheaf condition on the presheaf of rings underlying a sheaf of commutative rings, in the
form `Stacks.SheafOfModules.TensorSheafification.structureSheaf` takes it. -/
theorem isSheaf_structureRingPresheaf (O : Sheaf J CommRingCat.{w}) :
    Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O.obj) :=
  GrothendieckTopology.HasSheafCompose.isSheaf O.obj O.property

/-- `Stacks.SheafOfModules.Tensor.ringSheaf` and
`CategoryTheory.Sheaf.toRingCat` are the same sheaf of rings. -/
theorem ringSheaf_eq_toRingCat (O : Sheaf J CommRingCat.{w}) :
    Stacks.SheafOfModules.Tensor.ringSheaf O = Sheaf.toRingCat J O :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Stacks.SheafOfModules.Tensor.ringSheaf` and
`Stacks.SheafOfModules.TensorColimits.underlyingRingSheaf` are the same sheaf of rings. -/
theorem ringSheaf_eq_underlyingRingSheaf (O : Sheaf J CommRingCat.{w}) :
    Stacks.SheafOfModules.Tensor.ringSheaf O =
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O :=
  rfl

/-- `Stacks.SheafOfModules.Tensor.ringSheaf` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` are the same sheaf of rings: the sheaf
  condition is a proposition,
so pairing the composite presheaf with it gives the same structure as composing in `Sheaf`. -/
theorem ringSheaf_eq_structureSheaf (O : Sheaf J CommRingCat.{w}) :
    Stacks.SheafOfModules.Tensor.ringSheaf O =
      Stacks.SheafOfModules.TensorSheafification.structureSheaf O.obj (isSheaf_structureRingPresheaf
        O) :=
  rfl

end RingSheaf

section PresheafTensor

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The two universe-polymorphic objectwise tensor products of presheaves of modules —
`PresheafOfModules.tensorObj` and
`AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj` — are the same presheaf of
modules. -/
theorem tensorObj_eq_tensorObj (F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat))
    (G : PresheafOfModules.{a} (O ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.tensorObj F G =
      AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj F G :=
  rfl

/-- At a single module universe, the universe-polymorphic objectwise tensor product of
presheaves of modules is Mathlib's monoidal product. -/
theorem tensorObj_eq_tensor (F G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.tensorObj F G = F ⊗ G :=
  rfl

end PresheafTensor

section Bifunctor

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (J) (O : Sheaf J CommRingCat.{w})

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The functor `F ⊗ -` of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorProductRightExact.lean` is the
`tensorLeft` of Stacks 05NB. -/
theorem tensorSheafRight_eq_tensorLeft
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight J O F =
      (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj F :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The functor `- ⊗ G` of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorProductRightExact.lean` is the
`sheafTensorRight` whose exactness defines flatness in
`StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean`. -/
theorem tensorSheafLeft_eq_sheafTensorRight
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft J O G =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G) :=
  rfl

end Bifunctor

section IndependentUniverses

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}] [HasWeakSheafify J AddCommGrpCat.{z}]
  (J) (O : Sheaf J CommRingCat.{w})

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The comparison that carries weight.** Stacks 05NB's `tensorLeft` is the
native tensor bifunctor with its left factor fixed, at a module universe `z` independent of
the universe `w` of the ring. -/
theorem tensorLeft_eq_tensorSheafBifunctor
    (F : SheafOfModules.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj F =
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).obj F :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Tensoring on the right with `F`, applied to an object, is the sheafification of the
objectwise tensor product.** This is the shape in which
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso` states its source
and target. -/
theorem sheafTensorRight_obj_eq_sheafification
    (F G : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj F).obj G =
      (_root_.PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (J := J) O) (𝟙 _)).obj
        (_root_.Stacks.tensorObj G.val F.val) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `AlgebraicGeometry.SheafOfModules.sheafTensorRight` — the endofunctor whose exactness
*defines* flatness of a sheaf of modules in `StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean`
(Stacks 03ER(3)) — is the universe-polymorphic 0GMW tensor bifunctor with its *right* factor
fixed, again at independent module and ring universes. -/
theorem sheafTensorRight_eq_tensorSheafBifunctor
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj F) =
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).flip.obj F :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Stacks 05NB for the 0GMW tensor bifunctor, at independent universes.** Tensoring with a
fixed sheaf of modules preserves all colimits, with the module universe `z` of the sheaves
independent of the universe `w` of the ring and the index category of arbitrary hom universe. -/
theorem preservesColimitsOfSize_tensorSheafBifunctor_left
    (F : SheafOfModules.{z} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)) :
    PreservesColimitsOfSize.{a, z}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} O).obj F) :=
  Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits J O F

end IndependentUniverses

section Transport

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (J) (O : Sheaf J CommRingCat.{w})

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Stacks 05NB for the single-universe 0GMW tensor bifunctor.** The index category may have
its homs in an arbitrary universe `a`; the instance in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorProductRightExact.lean` gives only `a = w`. -/
theorem preservesColimitsOfSize_tensorSheafRight
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesColimitsOfSize.{a, w}
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight J O F) :=
  Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits J O F

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The presentation exactness of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPresentations.lean`, read as a statement
about the 0GMW tensor bifunctor. -/
theorem exact_tensorSheafBifunctor_presentations
    {F₂ F₁ F G₂ G₁ G : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (f₂ : F₂ ⟶ F₁) (f₁ : F₁ ⟶ F) (g₂ : G₂ ⟶ G₁) (g₁ : G₁ ⟶ G)
    (hf : (ComposableArrows.mk₂ f₂ f₁).Exact) (hg : (ComposableArrows.mk₂ g₂ g₁).Exact)
    [Epi f₁] [Epi g₁] :
    (ComposableArrows.mk₂
      (biprod.desc
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map f₂).app G₁)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj F₁).map g₂))
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map f₁).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj _).map g₁))).Exact :=
  Stacks.SheafOfModules.TensorPresentations.exact_tensorSheaf_presentations_on_site O.obj
    (isSheaf_structureRingPresheaf O) f₂ f₁ g₂ g₁ hf hg
    (leftEpi := ‹Epi f₁›) (rightEpi := ‹Epi g₁›)

/-- The 0GMW tensor bifunctor carries a pair of epimorphisms to an epimorphism. -/
theorem epi_tensorSheafBifunctor_map
    {F₁ F G₁ G : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (f : F₁ ⟶ F) (g : G₁ ⟶ G) [Epi f] [Epi g] :
    Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map f).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj _).map g)) :=
  Stacks.SheafOfModules.TensorPresentations.tensorSheafMapOnSite_epi O.obj
    (isSheaf_structureRingPresheaf O) f g (leftEpi := ‹Epi f›) (rightEpi := ‹Epi g›)

end Transport

end Stacks.SheafOfModules.TensorEncodings

end
