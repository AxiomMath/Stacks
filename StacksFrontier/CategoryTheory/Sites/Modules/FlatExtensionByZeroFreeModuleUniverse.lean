module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceCoproductTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorFreeModuleUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorBifunctorial
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18b.FlatRestrictionFreeModuleUniverse
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0E8I in the module on the big site, at a free module universe

Let `(C, O)` be a ringed site whose objects lie in `Type u`, whose morphisms lie in `v` and
whose structure sheaf has sections in `w`, and let `U` be an object of `C`.
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.restrictionTensorIso` is Stacks 0E8I at a free
module universe,

`j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`,

as an isomorphism of functors in the sheaf `G` of `O|_U`-modules. **This file supplies the
*other* naturality**, in the sheaf `F` of `O`-modules: the presheaf-level comparison it is built
from is natural in `F`, and so is each of the four steps the sheaf-level comparison decomposes
into.

That second naturality is what a proof that `j_{U!}` *preserves flatness* needs. Flatness of
`j_{U!}G` is exactness of `F ↦ F ⊗_O j_{U!}G`, a functor of the module on the big site; 0E8I
identifies its value with `j_{U!}(G ⊗_{O|_U} F|_U)`, which is the composite of three exact
functors — restriction to the slice (Stacks 04IX), tensoring with the flat `G`, and extension by
zero (Stacks 03DJ at a free module universe,
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.extensionByZero_exact`) — but only
*pointwise*, and exactness of a functor cannot be read off a pointwise identification. With
`restrictionTensorIso_naturality_right` below the identification is natural, so the two
functors are isomorphic and the exactness transports.

## Main results

* `Stacks.Sites.OverModules.extensionTensorObjIso_naturality_right`: **the presheaf-level
  comparison behind Stacks 0E8I is natural in the presheaf of modules on `C`**, for the
  *coproduct* model of `j_{U!}`, with the module universe a bare parameter. This is the one
  genuinely new piece of mathematics here; it is checked on each summand of the extension
  formula, which `Stacks.Sites.OverModules.extensionTensor_hom_ext` is enough for.
* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.tensorSheafificationIso_naturality`:
  **Stacks 05NB is natural in the fixed tensor factor** at a free module universe, together with
  the five squares it is pasted from.
* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.restrictionTensorIso_hom_app`: the four steps
  `restrictionTensorIso` is assembled from, at an object.
* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.presheafExtensionTensorIso_naturality_right`
  and `sheafificationCompPullback_inv_naturality_right`: the third and fourth of those four
  steps are natural in the module on the big site. The first two are
  `sheafTensorRightMap_naturality` and `tensorSheafificationIso_naturality` above.
* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.restrictionTensorIso_naturality_right`:
  **Stacks 0E8I is natural in the sheaf of modules on the big site** at a free module universe,
  the paste of those four squares. With `restrictionTensorIso`, which is the naturality in the
  module on the slice, this makes the comparison bifunctorial at
  `RingedSite.{u, v, w}` with the modules in a free `a` — the free-universe counterpart of
  `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso_naturality_right`.

## The two spellings of the slice tensor product, and what they cost

The four squares paste to the naturality of `restrictionTensorIso` in the module on the big
site, which is `restrictionTensorIso_naturality_right`. The paste is delicate, and the whole of
what makes it so is an identification of two spellings of the slice tensor product. The
restriction of `F` to `C/U` appears as
`PresheafOfModules.pushforward₀ (Over.forget U)` in
`Stacks.Sites.OverModules.extensionTensorPullback`, which is the spelling the coproduct model's
comparison carries, and as `SheafOfModules.overFunctor` — that is, as
`PresheafOfModules.pushforward` of an identity, one `ModuleCat.restrictScalars` more — in the
fourth step of `restrictionTensorIso`, which is the spelling `sliceTensorObj` carries.

Which identifications between the two fit in the elaboration budget is not what the shape of the
terms suggests.

* **Objects are cheap.** `extensionTensorPullback X.O.obj U A.val H = sliceTensorObj X U A H`
  is `rfl` inside the budget, and stays so under `Stacks.Sites.OverModules.extensionFunctor`
  with that functor left *reducible*, under `presheafExtendByZero`, and under both of those
  followed by `sheafifyModules`. No `local irreducible` is needed for any of them, and the
  attribute on `extensionFunctor` below is therefore not what pays for the comparison.
* **Morphisms under sheafification are not.** `(sheafifyModules X.J X.O).map` applied to the two
  typings of one morphism of slice tensor products exhausts the budget. Every junction of the
  paste that crosses a `Functor.map` is therefore written in one spelling on both sides; that is
  what `presheafExtensionTensorIso_naturality_slice` is for, and it is why all three shared
  edges of the paste are supplied to `comp_eq_comp_of_four_squares` rather than solved from the
  squares.
* **A single component read at the other spelling is affordable exactly when the natural
  transformation is opaque.** `η.app Z` for `η` the inverse of `presheafPullbackIsoExtension` or
  of `SheafOfModules.sheafificationCompPullback`, read at the two spellings of `Z`, is over
  budget with those isomorphisms transparent and cheap with them `local irreducible`: opaque,
  the comparison is of the two arguments, which is the first bullet; transparent, the unifier
  unfolds a uniqueness isomorphism of left adjoints instead. This is the one device the paste
  needs, and the `Pasting` section below is where it is applied.
* **Inside one whole-composite `rfl` a single retyping is affordable.**
  `restrictionTensorIso_hom_app` holds with both occurrences of the slice tensor product written
  as `sliceTensorObj`, which is the spelling `restrictionTensorIso` is built in, and it holds
  with the first of them written as `extensionTensorPullback` as well. With *both* written as
  `extensionTensorPullback` it does not.

Raising the heartbeat budget is not an option in this development, and none of the above does.

## Universes

The objects of `C` lie in `Type u`, its morphisms in `v`, the structure sheaf in `w` and the
modules in a free parameter `a` with `UnivLE.{v, a}` — the shape of
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroTensorFreeModuleUniverse.lean`, and one
that the constant coefficient ringed site of the small étale site, an
`AlgebraicGeometry.RingedSite.{u + 1, u, max (u + 1) r}` with modules in `max (u + 1) r`, is an
instance of. The `OfEssentiallySmall` statements of
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroTensorBifunctorial.lean` are at
`RingedSite.{c, u, u}` with modules in `u` and cannot be instantiated there, which is why the
sheaf-level naturality layer is restated here rather than reused. Those statements are not
replaced and their consumers are untouched.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

/-! ### The objectwise tensor product in its second variable -/

namespace Stacks.Sites.OverModules

universe a w v u

open AlgebraicGeometry.SheafOfModules.PresheafOfModules (sectionTensorRight tensorRight)

section TensorRightMap

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (A : PresheafOfModules.{a, v, u, w} (ringPresheaf O))
  {F F' : PresheafOfModules.{a, v, u, w} (ringPresheaf O)} (β : F ⟶ F')

/-- The morphism `A ⊗ F ⟶ A ⊗ F'` induced in the *second* tensor slot by `β : F ⟶ F'`, with its
source and target spelled as the values of
`AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorRight`. It is `Stacks.tensorMapRight`,
whose source and target are `Stacks.tensorObj`; the two objectwise tensor products are the same
structure declared in two namespaces, and naming the morphism with this result type discharges
that identification once.

`Stacks.Sites.OverModules.FormulaExtension.tensorRightMap` is the same morphism with the module
universe pinned to the compound form `max v m`, which is the universe the `DirectSum` model of
`j_{U!}` forces; this one keeps it a bare atom, as the coproduct model does. -/
noncomputable def tensorRightMap :
    (tensorRight (O := O) F).obj A ⟶ (tensorRight (O := O) F').obj A :=
  Stacks.tensorMapRight A β

/-- **Tensoring in the first and in the second variable commute**, for the objectwise tensor
product of presheaves of modules: both composites send a pure tensor `x ⊗ y` to `φ x ⊗ β y`. -/
lemma tensorRightMap_naturality {B : PresheafOfModules.{a, v, u, w} (ringPresheaf O)}
    (φ : A ⟶ B) :
    (tensorRight (O := O) F).map φ ≫ tensorRightMap O B β =
      tensorRightMap O A β ≫ (tensorRight (O := O) F').map φ := by
  refine PresheafOfModules.hom_ext fun Y => ?_
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

end TensorRightMap

/-! ### Stacks 0E8I is natural in the module on the big site, at a free module universe -/

section Extension

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C) [UnivLE.{v, a}]
  {F F' : PresheafOfModules.{a, v, u, w} (ringPresheaf O)} (β : F ⟶ F')
  (M : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf (ringPresheaf O) U))

/-- The map `M ⊗ j_U^*F ⟶ M ⊗ j_U^*F'` induced by `β : F ⟶ F'`, with its source and target
spelled as values of `extensionTensorPullback`. -/
noncomputable def extensionTensorPullbackMapRight :
    extensionTensorPullback O U F M ⟶ extensionTensorPullback O U F' M :=
  tensorRightMap ((Over.forget U).op ⋙ O) M ((restrictionFunctor (ringPresheaf O) U).map β)

/-- The map `j_{U!}M ⊗ F ⟶ j_{U!}M ⊗ F'` induced by `β` on sections over `X`, with its source
and target spelled through the coproducts of the extension formula. Naming it performs that
identification once: the two spellings are definitionally equal but not equal at the
transparency a `rw` builds its motive at. -/
noncomputable def extensionTensorMapRightApp (X : Cᵒᵖ) :
    (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (∐ extensionSummands (ringPresheaf O) U M X) ⟶
      (sectionTensorRight ((ringPresheaf O).obj X) (F'.obj X)).obj
        (∐ extensionSummands (ringPresheaf O) U M X) :=
  (tensorRightMap O ((extensionFunctor (ringPresheaf O) U).obj M) β).app X

/-- The map `M ⊗ j_U^*F ⟶ M ⊗ j_U^*F'` induced by `β` on the summand indexed by `p`, with its
source and target spelled as tensor products at `X`. -/
noncomputable def extensionTensorPullbackMapRightApp (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    (sectionTensorRight ((ringPresheaf O).obj X) (F.obj X)).obj
        (extensionSummands (ringPresheaf O) U M X p) ⟶
      (sectionTensorRight ((ringPresheaf O).obj X) (F'.obj X)).obj
        (extensionSummands (ringPresheaf O) U M X p) :=
  (extensionTensorPullbackMapRight O U β M).app (op (Over.mk p))

/-- The map `j_{U!}(M ⊗ j_U^*F) ⟶ j_{U!}(M ⊗ j_U^*F')` induced by `β`, on sections over `X`. -/
noncomputable def extensionTensorExtensionMapRight (X : Cᵒᵖ) :
    (∐ extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) ⟶
      (∐ extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F' M) X) :=
  ((extensionFunctor (ringPresheaf O) U).map (extensionTensorPullbackMapRight O U β M)).app X

/-- The map induced by `β` in the second tensor slot, restricted to the summand indexed by
`p`, is the map induced by `β` on that summand followed by the summand inclusion. -/
@[reassoc]
lemma extensionTensorι_comp_extensionTensorMapRightApp (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    extensionTensorι O U F M X p ≫ extensionTensorMapRightApp O U β M X =
      extensionTensorPullbackMapRightApp O U β M X p ≫ extensionTensorι O U F' M X p := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

/-- `extensionTensorExtensionMapRight` on the summand indexed by `p` is
`extensionTensorPullbackMapRightApp`, followed by the inclusion of that summand. -/
@[reassoc]
lemma ι_comp_extensionTensorExtensionMapRight (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    Sigma.ι (extensionSummands (ringPresheaf O) U (extensionTensorPullback O U F M) X) p ≫
        extensionTensorExtensionMapRight O U β M X =
      extensionTensorPullbackMapRightApp O U β M X p ≫
        Sigma.ι (extensionSummands (ringPresheaf O) U
          (extensionTensorPullback O U F' M) X) p :=
  ι_comp_extensionFunctor_map_app (ringPresheaf O) U _ X p

/-- **`extensionTensorObjIso` is natural in the presheaf of modules on `C`**, for the
coproduct model of `j_{U!}`. Together with `extensionTensorIso`, which is its naturality in the
module on the slice, this makes the presheaf-level comparison behind Stacks 0E8I bifunctorial
at a free module universe.

`Stacks.Sites.OverModules.FormulaExtension.extensionTensorObjIso_naturality_right` is the same
statement for the `DirectSum` model of `j_{U!}`, whose module universe is pinned to the compound
form `max v m`; it is not reused because a consumer that needs the module universe to stay a
bare atom has to use the coproduct model, which is exactly the situation
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroTensorFreeModuleUniverse.lean` records
for the comparison itself. -/
lemma extensionTensorObjIso_naturality_right :
    tensorRightMap O ((extensionFunctor (ringPresheaf O) U).obj M) β ≫
        (extensionTensorObjIso O U F' M).hom =
      (extensionTensorObjIso O U F M).hom ≫
        (extensionFunctor (ringPresheaf O) U).map
          (extensionTensorPullbackMapRight O U β M) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  show extensionTensorMapRightApp O U β M X ≫ (extensionTensorFiberIso O U F' M X).hom =
    (extensionTensorFiberIso O U F M X).hom ≫ extensionTensorExtensionMapRight O U β M X
  refine extensionTensor_hom_ext O U F M _ _ fun p => ?_
  rw [extensionTensorι_comp_extensionTensorMapRightApp_assoc,
    extensionTensorι_comp_extensionTensorFiberIso_hom,
    extensionTensorι_comp_extensionTensorFiberIso_hom_assoc]
  exact (ι_comp_extensionTensorExtensionMapRight O U β M X p).symm

end Extension

end Stacks.Sites.OverModules

/-! ### Stacks 05NB is natural in the fixed tensor factor, at a free module universe -/

namespace Stacks.Sites.ExtensionByZero.FreeModuleUniverse

universe a w v u

open Stacks.Sites.OverModules
open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open AlgebraicGeometry.SheafOfModules.PresheafOfModules (tensorRight)
open Stacks.SheafOfModules.TensorColimits (tensorCommIso
  tensorSheafificationIsoGeneral)
open AlgebraicGeometry.SheafOfModules (presheafTensorLeft)
open Stacks.Sites.ExtensionByZero.OfEssentiallySmall (natIso_inv_square
  comp_eq_comp_of_three_squares comp_eq_comp_of_four_squares map_comp_eq_map_comp_of_eq)

section SheafLevel

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify J AddCommGrpCat.{a}]
  (O : Sheaf J CommRingCat.{w})
  {F F' : SheafOfModules.{a} (ringSheaf O)} (α : F ⟶ F')

/-- The morphism `A ⊗ F ⟶ A ⊗ F'` of sheaves of modules induced in the second tensor slot by
`α : F ⟶ F'`: the sheafification of the presheaf-level `tensorRightMap`. -/
noncomputable def sheafTensorRightMap (A : SheafOfModules.{a} (ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).flip.obj F).obj A ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).flip.obj F').obj A :=
  (sheafifyModules J O).map (tensorRightMap O.obj A.val α.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The same morphism, read as the action of `α` on the functor of tensoring on the left with
`A`. Tensoring on the left with `A` and tensoring on the right with `F` have the *same* value
at the remaining variable, and the same action on `α`. -/
lemma tensorLeft_map_eq_sheafTensorRightMap
    (A : SheafOfModules.{a} (ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).obj A).map α =
      sheafTensorRightMap J O α A :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Tensoring in the first and in the second variable commute**, for sheaves of modules. -/
lemma sheafTensorRightMap_naturality
    {A B : SheafOfModules.{a} (ringSheaf O)} (h : A ⟶ B) :
    sheafTensorRightMap J O α A ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).flip.obj F').map h =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).flip.obj F).map h ≫
        sheafTensorRightMap J O α B := by
  exact (map_comp_eq_map_comp_of_eq (sheafifyModules J O)
    (tensorRightMap_naturality O.obj A.val α.val h.val)).symm

/-- The morphism `F ⊗ A ⟶ F' ⊗ A` induced in the *first* tensor slot by `α : F ⟶ F'`, read as
the action of `α` on the functor of tensoring on the left. It is the component at `A` of the
natural transformation `(sheafTensor O).obj F ⟶ (sheafTensor O).obj F'` that `α` induces. -/
noncomputable def tensorLeftMapApp (A : SheafOfModules.{a} (ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).obj F).obj A ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).obj F').obj A :=
  (sheafifyModules J O).map ((tensorRight (O := O.obj) A.val).map α.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **Tensoring in the first and in the second variable commute**, with the first variable read
through `AlgebraicGeometry.SheafOfModules.presheafTensorLeft`. -/
lemma presheafTensorLeft_naturality
    {G G' : PresheafOfModules.{a} (ringSheaf O).obj} (γ : G ⟶ G')
    {A B : PresheafOfModules.{a} (ringSheaf O).obj} (φ : A ⟶ B) :
    (presheafTensorLeft J O G).map φ ≫ (tensorRight (O := O.obj) B).map γ =
      (tensorRight (O := O.obj) A).map γ ≫ (presheafTensorLeft J O G').map φ := by
  refine PresheafOfModules.hom_ext fun Y => ?_
  refine ModuleCat.hom_ext <| LinearMap.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul x y => rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **The braiding of the objectwise tensor product is natural in the fixed factor.** -/
lemma tensorCommIso_naturality
    {G G' : PresheafOfModules.{a} (ringSheaf O).obj} (γ : G ⟶ G')
    (A : PresheafOfModules.{a} (ringSheaf O).obj) :
    (tensorRight (O := O.obj) A).map γ ≫ (tensorCommIso J O G').hom.app A =
      (tensorCommIso J O G).hom.app A ≫ tensorRightMap O.obj A γ := by
  refine PresheafOfModules.hom_ext fun Y => ?_
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The passage from tensoring on the left to tensoring on the right is natural in the fixed
factor.** -/
lemma tensorLeftIsoSheafTensorRight_naturality
    (A : SheafOfModules.{a} (ringSheaf O)) :
    tensorLeftMapApp J O α A ≫ (tensorLeftIsoSheafTensorRight J O F').hom.app A =
      (tensorLeftIsoSheafTensorRight J O F).hom.app A ≫ sheafTensorRightMap J O α A := by
  exact map_comp_eq_map_comp_of_eq (sheafifyModules J O)
    (tensorCommIso_naturality J O α.val A.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The passage from tensoring on the left to tensoring on the right is natural in the fixed
factor**, read in the inverse direction. -/
lemma tensorLeftIsoSheafTensorRight_inv_naturality
    (A : SheafOfModules.{a} (ringSheaf O)) :
    sheafTensorRightMap J O α A ≫ (tensorLeftIsoSheafTensorRight J O F').inv.app A =
      (tensorLeftIsoSheafTensorRight J O F).inv.app A ≫ tensorLeftMapApp J O α A :=
  natIso_inv_square (tensorLeftIsoSheafTensorRight J O F) A
    (tensorLeftIsoSheafTensorRight J O F') A
    (tensorLeftIsoSheafTensorRight_naturality J O α A)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Stacks 05NB is natural in the fixed tensor factor.** Both sides are sheafifications of
presheaf-level morphisms, and the presheaf-level square is the bifunctoriality of the objectwise
tensor product at the unit of sheafification. -/
lemma tensorSheafificationIsoGeneral_naturality
    (P : PresheafOfModules.{a} (ringSheaf O).obj) :
    (sheafifyModules J O).map ((tensorRight (O := O.obj) P).map α.val) ≫
        (tensorSheafificationIsoGeneral J O F').hom.app P =
      (tensorSheafificationIsoGeneral J O F).hom.app P ≫
        tensorLeftMapApp J O α ((sheafifyModules J O).obj P) :=
  map_comp_eq_map_comp_of_eq (sheafifyModules J O)
    (presheafTensorLeft_naturality J O α.val
      ((PresheafOfModules.sheafificationAdjunction.{a}
        (𝟙 (ringSheaf O).obj)).unit.app P)).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Stacks 05NB is natural in the fixed tensor factor**, read in the inverse direction. -/
lemma tensorSheafificationIsoGeneral_inv_naturality
    (P : PresheafOfModules.{a} (ringSheaf O).obj) :
    tensorLeftMapApp J O α ((sheafifyModules J O).obj P) ≫
        (tensorSheafificationIsoGeneral J O F').inv.app P =
      (tensorSheafificationIsoGeneral J O F).inv.app P ≫
        (sheafifyModules J O).map ((tensorRight (O := O.obj) P).map α.val) :=
  natIso_inv_square (tensorSheafificationIsoGeneral J O F) P
    (tensorSheafificationIsoGeneral J O F') P
    (tensorSheafificationIsoGeneral_naturality J O α P)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The three steps `tensorSheafificationIso` is assembled from, at an object. -/
lemma tensorSheafificationIso_hom_app
    (G : SheafOfModules.{a} (ringSheaf O))
    (Y : PresheafOfModules.{a} (ringSheaf O).obj) :
    (tensorSheafificationIso J O G).hom.app Y =
      (tensorLeftIsoSheafTensorRight J O G).inv.app ((sheafifyModules J O).obj Y) ≫
        (tensorSheafificationIsoGeneral J O G).inv.app Y ≫
        (sheafifyModules J O).map ((tensorCommIso J O G.val).hom.app Y) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The exchange of sheafification with the tensor product is natural in the fixed tensor
factor.** -/
lemma tensorSheafificationIso_naturality
    (Y : PresheafOfModules.{a} (ringSheaf O).obj) :
    sheafTensorRightMap J O α ((sheafifyModules J O).obj Y) ≫
        (tensorSheafificationIso J O F').hom.app Y =
      (tensorSheafificationIso J O F).hom.app Y ≫
        (sheafifyModules J O).map (tensorRightMap O.obj Y α.val) := by
  rw [tensorSheafificationIso_hom_app, tensorSheafificationIso_hom_app]
  exact comp_eq_comp_of_three_squares
    (tensorLeftIsoSheafTensorRight_inv_naturality J O α ((sheafifyModules J O).obj Y))
    (tensorSheafificationIsoGeneral_inv_naturality J O α Y)
    (map_comp_eq_map_comp_of_eq (sheafifyModules J O) (tensorCommIso_naturality J O α.val Y))

end SheafLevel

/-! ### Stacks 0E8I is natural in the module on the big site -/

section Sheaf

variable (X : RingedSite.{u, v, w}) (U : X.C) [UnivLE.{v, a}]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify X.J AddCommGrpCat.{a}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{a}]

/-- The objectwise tensor product on the slice, `H ⊗_{O|_U} A|_U`, with its presheaf of rings
pinned to `((ringSheaf X.O).over U).obj`: the spelling the fourth step of
`restrictionTensorIso` carries, in which the restriction of `A` to the slice is
`SheafOfModules.overFunctor`. `Stacks.Sites.OverModules.extensionTensorPullback` is the other
spelling, in which it is `PresheafOfModules.pushforward₀ (Over.forget U)`; the two are
definitionally equal, and each statement below is written in whichever of them makes its
junction with the next one syntactic. -/
noncomputable abbrev sliceTensorObj (A : SheafOfModules.{a} (ringSheaf X.O))
    (H : PresheafOfModules.{a} ((ringSheaf X.O).over U).obj) :
    PresheafOfModules.{a} ((ringSheaf X.O).over U).obj :=
  (tensorRight (O := (X.O.over U).obj) (A.over U).val).obj H

/-- Sheafification of presheaves of modules on the slice, with the ring sheaf pinned to the
spelling `(ringSheaf X.O).over U` in which the fourth step of
`restrictionTensorIso` is given. The other spelling,
`ringSheaf (X.O.over U)`, is the one `sheafifyModules (X.J.over U) (X.O.over U)`
carries; the two differ by the order of restriction to the slice and of forgetting
commutativity, and pinning one of them here is what keeps that identification out of the proofs
below. -/
noncomputable abbrev sliceSheafifyModules :
    PresheafOfModules.{a} ((ringSheaf X.O).over U).obj ⥤
      SheafOfModules.{a} ((ringSheaf X.O).over U) :=
  PresheafOfModules.sheafification.{a} (R := (ringSheaf X.O).over U)
    (𝟙 ((ringSheaf X.O).over U).obj)

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The four steps `restrictionTensorIso` is assembled from, at an object: the comparison of the
two models of sheaf-level extension by zero, the exchange of sheafification with the tensor
product, the presheaf-level comparison of the extension formula, and the exchange of
sheafification with extension by zero.

Both occurrences of the slice tensor product are written as `sliceTensorObj`. -/
lemma restrictionTensorIso_hom_app
    (F : SheafOfModules.{a} (ringSheaf X.O))
    (G : SheafOfModules.{a} ((ringSheaf X.O).over U)) :
    (restrictionTensorIso.{a} X U F).hom.app G =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map
          ((SheafOfModules.pullbackIso
            (𝟙 ((ringSheaf X.O).over U))).hom.app G) ≫
        (tensorSheafificationIso.{a} X.J X.O F).hom.app
          ((presheafExtendByZero.{a} X U).obj G.val) ≫
        (sheafifyModules.{a} X.J X.O).map
          ((tensorRight (O := X.O.obj) F.val).map
              ((presheafPullbackIsoExtension.{a, w, v, u}
                (ringSheaf X.O).obj U).hom.app G.val) ≫
            (extensionTensorObjIso X.O.obj U F.val G.val).hom ≫
            (presheafPullbackIsoExtension.{a, w, v, u}
              (ringSheaf X.O).obj U).inv.app
              (sliceTensorObj X U F G.val)) ≫
        (SheafOfModules.sheafificationCompPullback
            (𝟙 ((ringSheaf X.O).over U))).inv.app
          (sliceTensorObj X U F G.val) :=
  rfl

variable {F F' : SheafOfModules.{a} (ringSheaf X.O)} (α : F ⟶ F')

/- `Stacks.Sites.OverModules.extensionFunctor` is made opaque from here on.

It unfolds to the objectwise coproduct of the extension formula, so without this the unifier
descends into that coproduct instead of comparing the arguments it is applied to, and the checks
below do not fit in the elaboration budget. This is the same device, and for the same reason, as
the one recorded at
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.presheafExtensionTensorIso_naturality_whiskered`
for the `DirectSum` model. -/
attribute [local irreducible] Stacks.Sites.OverModules.extensionFunctor

/-- The morphism of sheaves of modules on the slice induced by `α : F ⟶ F'`: the sheafification
of `Stacks.Sites.OverModules.extensionTensorPullbackMapRight`, with its source and target in the
`sliceTensorObj` spelling. This is the morphism the target of `restrictionTensorIso` is natural
along. -/
noncomputable def slicePresheafTensorMapRight
    (H : PresheafOfModules.{a} ((ringSheaf X.O).over U).obj) :
    sliceTensorObj X U F H ⟶ sliceTensorObj X U F' H :=
  extensionTensorPullbackMapRight X.O.obj U α.val H

/-- The morphism of sheaves of modules on the slice induced by `α : F ⟶ F'`: the sheafification
of `slicePresheafTensorMapRight`. This is the morphism the target of `restrictionTensorIso` is
natural along. -/
noncomputable def sliceTensorRightMap
    (G : SheafOfModules.{a} ((ringSheaf X.O).over U)) :
    (sliceSheafifyModules X U).obj (sliceTensorObj X U F G.val) ⟶
      (sliceSheafifyModules X U).obj (sliceTensorObj X U F' G.val) :=
  (sliceSheafifyModules X U).map (slicePresheafTensorMapRight X U α G.val)

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat] in
/-- **The presheaf-level step of `restrictionTensorIso` is natural in the sheaf of modules on
`X`.** That step is the comparison `extensionTensorObjIso` of the coproduct model of the
extension formula, read through the identification `presheafPullbackIsoExtension` of Mathlib's
model of extension by zero with it; so its three sub-squares are the bifunctoriality of the
objectwise tensor product, `extensionTensorObjIso_naturality_right`, and the naturality of that
identification. -/
lemma presheafExtensionTensorIso_naturality_right
    (H : PresheafOfModules.{a} ((ringSheaf X.O).over U).obj) :
    tensorRightMap X.O.obj ((presheafExtendByZero.{a} X U).obj H) α.val ≫
        ((tensorRight (O := X.O.obj) F'.val).map
            ((presheafPullbackIsoExtension.{a, w, v, u}
              (ringSheaf X.O).obj U).hom.app H) ≫
          (extensionTensorObjIso X.O.obj U F'.val H).hom ≫
          (presheafPullbackIsoExtension.{a, w, v, u}
            (ringSheaf X.O).obj U).inv.app
            (extensionTensorPullback X.O.obj U F'.val H)) =
      ((tensorRight (O := X.O.obj) F.val).map
          ((presheafPullbackIsoExtension.{a, w, v, u}
            (ringSheaf X.O).obj U).hom.app H) ≫
        (extensionTensorObjIso X.O.obj U F.val H).hom ≫
        (presheafPullbackIsoExtension.{a, w, v, u}
          (ringSheaf X.O).obj U).inv.app
          (extensionTensorPullback X.O.obj U F.val H)) ≫
        (presheafExtendByZero.{a} X U).map (slicePresheafTensorMapRight X U α H) :=
  comp_eq_comp_of_three_squares
    (tensorRightMap_naturality X.O.obj ((presheafExtendByZero.{a} X U).obj H) α.val
      ((presheafPullbackIsoExtension.{a, w, v, u}
        (ringSheaf X.O).obj U).hom.app H)).symm
    (extensionTensorObjIso_naturality_right X.O.obj U α.val H)
    ((presheafPullbackIsoExtension.{a, w, v, u}
      (ringSheaf X.O).obj U).inv.naturality
      (extensionTensorPullbackMapRight X.O.obj U α.val H))

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The fourth step of `restrictionTensorIso` is natural in the sheaf of modules on `X`**:
it is the naturality of the exchange of sheafification with extension by zero.

Its left-hand vertical is written in the `extensionTensorPullback` spelling, matching the
right-hand vertical of `presheafExtensionTensorIso_naturality_right`, and its two horizontals in
the `sliceTensorObj` spelling, matching the fourth step of `restrictionTensorIso_hom_app`. The
identification of the two spellings is paid here, and nowhere else. -/
lemma sheafificationCompPullback_inv_naturality_right
    (G : SheafOfModules.{a} ((ringSheaf X.O).over U)) :
    (sheafifyModules.{a} X.J X.O).map
          ((presheafExtendByZero.{a} X U).map
            (slicePresheafTensorMapRight X U α G.val)) ≫
        (SheafOfModules.sheafificationCompPullback
            (𝟙 ((ringSheaf X.O).over U))).inv.app
          (sliceTensorObj X U F' G.val) =
      (SheafOfModules.sheafificationCompPullback
          (𝟙 ((ringSheaf X.O).over U))).inv.app
        (sliceTensorObj X U F G.val) ≫
        (extendByZero.{a} X U).map (sliceTensorRightMap X U α G) :=
  (SheafOfModules.sheafificationCompPullback
    (𝟙 ((ringSheaf X.O).over U))).inv.naturality
    (slicePresheafTensorMapRight X U α G.val)

/-! ### Stacks 0E8I is natural in the module on the big site, at a free module universe -/

section Pasting

/- `presheafPullbackIsoExtension` and `SheafOfModules.sheafificationCompPullback` are made
opaque for the paste.

The two statements below each read a component `η.app Z` of one of these isomorphisms at the
*other* of the two spellings of the slice tensor product — see the module docstring. Left
transparent, the unifier unfolds `η`, which is the uniqueness isomorphism of two left adjoints
in the first case and the exchange of sheafification with extension by zero in the second,
instead of comparing the two arguments it is applied to, and neither comparison then fits in the
elaboration budget. Made opaque, each is the comparison of two objects of a category of
presheaves of modules, which is cheap. Nothing here needs either isomorphism unfolded:
`restrictionTensorIso_hom_app`, which is the one statement that does, is above. -/
attribute [local irreducible] presheafPullbackIsoExtension
  SheafOfModules.sheafificationCompPullback

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)]
  [X.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify X.J AddCommGrpCat]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat] in
/-- **The presheaf-level step of `restrictionTensorIso` is natural in the sheaf of modules on
`X`**, with the slice tensor product spelled as `sliceTensorObj` throughout, so that the square
matches both `restrictionTensorIso_hom_app` and
`sheafificationCompPullback_inv_naturality_right` without any retyping left for the paste.

This is `presheafExtensionTensorIso_naturality_right` read at the other spelling of the two
components of `presheafPullbackIsoExtension` it contains; the opacity above is what makes that
reading affordable. -/
lemma presheafExtensionTensorIso_naturality_slice
    (H : PresheafOfModules.{a} ((ringSheaf X.O).over U).obj) :
    tensorRightMap X.O.obj ((presheafExtendByZero.{a} X U).obj H) α.val ≫
        ((tensorRight (O := X.O.obj) F'.val).map
            ((presheafPullbackIsoExtension.{a, w, v, u}
              (ringSheaf X.O).obj U).hom.app H) ≫
          (extensionTensorObjIso X.O.obj U F'.val H).hom ≫
          (presheafPullbackIsoExtension.{a, w, v, u}
            (ringSheaf X.O).obj U).inv.app (sliceTensorObj X U F' H)) =
      ((tensorRight (O := X.O.obj) F.val).map
          ((presheafPullbackIsoExtension.{a, w, v, u}
            (ringSheaf X.O).obj U).hom.app H) ≫
        (extensionTensorObjIso X.O.obj U F.val H).hom ≫
        (presheafPullbackIsoExtension.{a, w, v, u}
          (ringSheaf X.O).obj U).inv.app (sliceTensorObj X U F H)) ≫
        (presheafExtendByZero.{a} X U).map (slicePresheafTensorMapRight X U α H) :=
  presheafExtensionTensorIso_naturality_right X U α H

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Stacks 0E8I is natural in the sheaf of modules on `X` as well**, at a free module
universe. Together with `restrictionTensorIso`, which is its naturality in the sheaf of modules
on the slice, this makes the comparison

`j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`

bifunctorial at `RingedSite.{u, v, w}` with the modules in a free `a`.

The proof is the paste of the four naturality squares of the four steps
`restrictionTensorIso_hom_app` decomposes the comparison into: the naturality of the comparison
of the two models of sheaf-level extension by zero, `tensorSheafificationIso_naturality`,
`presheafExtensionTensorIso_naturality_slice`, and
`sheafificationCompPullback_inv_naturality_right`. The three shared edges of the paste are
supplied rather than left to the unifier: each is a value of a sheafification on a composite of
four endpoints, and solving them from the four squares instead puts the elaborator in front of
exactly the comparison the module docstring records as unaffordable.

`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso_naturality_right` is the
same statement at `RingedSite.{c, u, u}` for an essentially `u`-small site, with the modules in
the universe of the morphisms; it is not replaced and its consumers are untouched. This is its
free-module-universe counterpart, in the same relation as
`Stacks.SheafOfModules.FlatRestriction.FreeModuleUniverse.isFlat_over` stands to
`Stacks.SheafOfModules.FlatRestriction.isFlat_over`. -/
lemma restrictionTensorIso_naturality_right
    (G : SheafOfModules.{a} ((ringSheaf X.O).over U)) :
    sheafTensorRightMap X.J X.O α ((extendByZero.{a} X U).obj G) ≫
        (restrictionTensorIso.{a} X U F').hom.app G =
      (restrictionTensorIso.{a} X U F).hom.app G ≫
        (extendByZero.{a} X U).map (sliceTensorRightMap X U α G) := by
  have key := comp_eq_comp_of_four_squares
    (b₁ := sheafTensorRightMap X.J X.O α
      ((sheafifyModules.{a} X.J X.O).obj ((presheafExtendByZero.{a} X U).obj G.val)))
    (b₂ := (sheafifyModules.{a} X.J X.O).map
      (tensorRightMap X.O.obj ((presheafExtendByZero.{a} X U).obj G.val) α.val))
    (b₃ := (sheafifyModules.{a} X.J X.O).map
      ((presheafExtendByZero.{a} X U).map (slicePresheafTensorMapRight X U α G.val)))
    (sheafTensorRightMap_naturality X.J X.O α
      ((SheafOfModules.pullbackIso
        (𝟙 ((ringSheaf X.O).over U))).hom.app G))
    (tensorSheafificationIso_naturality X.J X.O α ((presheafExtendByZero.{a} X U).obj G.val))
    (map_comp_eq_map_comp_of_eq (sheafifyModules.{a} X.J X.O)
      (presheafExtensionTensorIso_naturality_slice X U α G.val))
    (sheafificationCompPullback_inv_naturality_right X U α G)
  rw [restrictionTensorIso_hom_app, restrictionTensorIso_hom_app]
  exact key

end Pasting

end Sheaf

end Stacks.Sites.ExtensionByZero.FreeModuleUniverse

end
