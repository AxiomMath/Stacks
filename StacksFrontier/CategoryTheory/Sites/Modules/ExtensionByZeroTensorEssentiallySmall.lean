module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceExtensionTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactnessEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and the tensor product over a site with large objects

Let `(C, O)` be a ringed site whose objects form a type in an arbitrary universe `c` while its
morphisms, the sections of `O` and the sections of its modules all lie in one universe `u`, let
`C` be essentially `u`-small, and let `U` be an object of `C`. This file carries Stacks 0E8I to
that configuration: extension by zero `j_{U!}` from the localized site `C/U` commutes with
tensoring by a sheaf of `O`-modules `F`,

`j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`,

naturally in the sheaf of `O|_U`-modules `G`.

## Main results

* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso`: **Stacks 0E8I** at
  this universe shape, as an isomorphism of functors in the module on the slice site.

Alongside it the file states, at independent universes for the site, the three steps the
comparison is assembled from, which
`StacksFrontier/CategoryTheory/Sites/Modules/Gate18b/FlatRestriction.lean` carried as private
declarations pinned to one universe:

* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.sheafifyModules`,
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.tensorLeftIsoSheafTensorRight`,
* `Stacks.Sites.ExtensionByZero.OfEssentiallySmall.tensorSheafificationIso`.

## Implementation notes

The proof is the presheaf-level one: the comparison is assembled from three isomorphisms, in
each of which the identification is made once, at the place where the object is named, rather
than rewritten through at every use.

* On presheaves of modules, extension from `C/U` commutes with the objectwise tensor product,
  because the sections of an extension over `V` are the direct sum over the arrows `V ⟶ U` of
  the extension formula of Stacks 03EJ and tensoring distributes over a direct sum. This is
  `Stacks.Sites.OverModules.FormulaExtension.extensionTensorIso`, built on the concrete
  direct-sum model `FormulaExtension.extensionFunctor` of extension; both are stated at
  independent universes, which is what lets them be used here.
* Tensoring commutes with sheafification, which is
  `Stacks.SheafOfModules.TensorColimits.tensorSheafificationIsoGeneral` of Stacks 05NB,
  transported from tensoring on the left to tensoring on the right by `tensorCommIso`. That
  statement is already universe-independent.
* Sheafification commutes with the sheaf-level extension by zero, which is Mathlib's
  `SheafOfModules.sheafificationCompPullback`, also universe-independent.

Extension from `C/U` appears in two models: Mathlib's `PresheafOfModules.pullback`, which is
where the adjunction and the sheaf-level comparison live, and the concrete direct sum of the
extension formula, which is where the tensor comparison can be computed. They are identified by
the uniqueness of left adjoints, in `presheafExtendByZeroIsoExtension`; the left adjoint of
restriction exists here because `Over U` is essentially `u`-small, which is
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.presheafRestrictionSheafIsRightAdjoint`.

The configuration is the one of the small étale ringed site of an algebraic space, an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, whose objects sit one universe above its
morphisms; the single-universe statement
`Stacks.SheafOfModules.ExtensionByZero.extensionByZeroTensorIso` cannot be instantiated at it.
That statement is proved by uniqueness of left adjoints out of Stacks 0E8H, and that route is
*not* available here: the internal Hom of two sheaves of modules has its sections over `V`
given by the morphisms of modules on the slice over `V`, so it exists only at a module universe
containing the universe of the objects of the site.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace Stacks.Sites.ExtensionByZero.OfEssentiallySmall

universe u c

open Stacks.Sites.OverModules
open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open AlgebraicGeometry.SheafOfModules.PresheafOfModules (tensorRight)
open Stacks.SheafOfModules.TensorColimits (tensorCommIso tensorSheafificationIsoGeneral)

attribute [local instance] Classical.decEq

/-! ### Tensoring and sheafification, at independent universes for the site -/

section SheafLevel

variable {C : Type c} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Sheafification of presheaves of modules over the ring presheaf underlying `O`.  Naming it
pins the source presheaf of rings to the spelling `(ringSheaf O).obj`, which is
what lets the two sides of `tensorSheafificationIso` elaborate. -/
noncomputable abbrev sheafifyModules (O : Sheaf J CommRingCat.{u}) :
    PresheafOfModules.{u} (ringSheaf O).obj ⥤
      SheafOfModules.{u} (ringSheaf O) :=
  PresheafOfModules.sheafification.{u} (R := ringSheaf O)
    (𝟙 (ringSheaf O).obj)

/-- Tensoring on the left by `F` and tensoring on the right by `F` agree, as endofunctors of
sheaves of modules. -/
noncomputable def tensorLeftIsoSheafTensorRight (O : Sheaf J CommRingCat.{u})
    (F : SheafOfModules.{u} (ringSheaf O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} O).obj F ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F :=
  NatIso.ofComponents
    (fun A => (sheafifyModules J O).mapIso ((tensorCommIso J O F.val).app A.val)) (by
      intro A B morphism
      exact (((sheafifyModules J O).map_comp _ _).symm.trans
        (congrArg (sheafifyModules J O).map
          ((tensorCommIso J O F.val).hom.naturality morphism.val))).trans
        ((sheafifyModules J O).map_comp _ _))

/-- Tensoring on the right with `F` commutes with sheafification. -/
noncomputable def tensorSheafificationIso (O : Sheaf J CommRingCat.{u})
    (F : SheafOfModules.{u} (ringSheaf O)) :
    sheafifyModules J O ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F ≅
      tensorRight (O := O.obj) F.val ⋙ sheafifyModules J O :=
  Functor.isoWhiskerLeft _ (tensorLeftIsoSheafTensorRight J O F).symm ≪≫
    (tensorSheafificationIsoGeneral J O F).symm ≪≫
    Functor.isoWhiskerRight (tensorCommIso J O F.val) _

end SheafLevel

/-! ### Extension by zero commutes with tensoring -/

section Tensor

variable {C : Type c} [Category.{u} C] [EssentiallySmall.{u} C]

/-- Mathlib's presheaf-level extension by zero, the left adjoint of restriction to the slice
over `U`, written with the morphism of presheaves of rings spelled as the identity of
`R.over U`. -/
noncomputable abbrev presheafExtendByZero (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
    (U : C) :
    PresheafOfModules.{u} (R.over U).obj ⥤ PresheafOfModules.{u} R.obj :=
  haveI := presheafRestrictionSheafIsRightAdjoint J R U
  PresheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (R.over U) : R.over U ⟶ R.over U).hom

/-- The presheaf-level extension by zero agrees with the direct-sum extension of the extension
formula: both are left adjoint to restriction. -/
noncomputable def presheafExtendByZeroIsoExtension (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u}) (U : C) :
    presheafExtendByZero J R U ≅ FormulaExtension.extensionFunctor R.obj U :=
  haveI := presheafRestrictionSheafIsRightAdjoint J R U
  Adjunction.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction _)
    (FormulaExtension.extensionAdjunction R.obj U)

end Tensor

section Sheaf

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C] (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]

/-- Tensoring on the right with a sheaf of modules on the localized site, with its source and
target spelled at the ring sheaf `(ringSheaf X.O).over U` and at the module
universe `u`.  Both are needed in the result type: the slice site has its objects in
`max c u`, so left to itself unification solves the two module universes of
`Stacks.SheafOfModules.Tensor.sheafTensor` — which are free and independent — as `max c u`
rather than as `u`, and the comparison below is then not type-correct. -/
noncomputable abbrev sliceSheafTensorRight
    (G : SheafOfModules.{u} ((ringSheaf X.O).over U)) :
    SheafOfModules.{u} ((ringSheaf X.O).over U) ⥤
      SheafOfModules.{u} ((ringSheaf X.O).over U) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (X.O.over U)).flip.obj G

/-- Extension by zero of sheaves of modules from the site localized at `U`.  Naming it pins the
ring sheaf to the spelling `(ringSheaf X.O).over U`, so that the two sides of
`restrictionTensorIso` elaborate. -/
@[sga "4 XVII 5.1.1" "partial"]
noncomputable abbrev extendByZero :
    SheafOfModules.{u} ((ringSheaf X.O).over U) ⥤
      SheafOfModules.{u} (ringSheaf X.O) :=
  haveI := sheafRestrictionIsRightAdjoint X.J (ringSheaf X.O) U
  SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 ((ringSheaf X.O).over U))

/-- **Stacks 0E8I over a site with large objects.** For a sheaf of modules `F` on `X`, the
extension by zero of `G ⊗ F|_U` is the extension by zero of `G`, tensored with `F`, naturally
in `G`.

The attribute records the shape at which this holds: the objects of `C` form a type in an
arbitrary universe `c`, but the morphisms, the structure sheaf and the modules all lie in one
universe `u`, and `C` is required to be essentially `u`-small. The tag is carried in full by
`Stacks.SheafOfModules.ExtensionByZero.extensionByZeroTensorIso`, where objects, morphisms,
ring and modules lie in a single universe — the faithful reading of the tag's ringed site, which
this statement specializes to at `c := u`; that registration stands and this one does not
replace it. -/
@[stacks 0E8I "for a site essentially u-small, objects in Type c, morphisms and modules in u"]
noncomputable def restrictionTensorIso
    (F : SheafOfModules.{u} (ringSheaf X.O)) :
    extendByZero X U ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F ≅
      sliceSheafTensorRight X U (F.over U) ⋙ extendByZero X U := by
  haveI := sheafRestrictionIsRightAdjoint X.J (ringSheaf X.O) U
  haveI := presheafRestrictionSheafIsRightAdjoint X.J (ringSheaf X.O) U
  let R := ringSheaf X.O
  let I := SheafOfModules.forget.{u} (R.over U)
  let P := presheafExtendByZero X.J R U
  let S := sheafifyModules X.J X.O
  let S' := sheafifyModules (X.J.over U) (X.O.over U)
  let T := tensorRight (O := X.O.obj) F.val
  let T' := tensorRight (O := (X.O.over U).obj) (F.over U).val
  let β : P ≅ FormulaExtension.extensionFunctor R.obj U :=
    presheafExtendByZeroIsoExtension X.J R U
  let γ : P ⋙ T ≅ T' ⋙ P :=
    Functor.isoWhiskerRight β T ≪≫ FormulaExtension.extensionTensorIso X.O.obj U F.val ≪≫
      Functor.isoWhiskerLeft T' β.symm
  let δ : S ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F ≅ T ⋙ S :=
    tensorSheafificationIso X.J X.O F
  let ε : S' ⋙ extendByZero X U ≅ P ⋙ S :=
    SheafOfModules.sheafificationCompPullback (𝟙 ((ringSheaf X.O).over U))
  exact Functor.isoWhiskerRight
      (SheafOfModules.pullbackIso (𝟙 ((ringSheaf X.O).over U)))
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft P δ) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight γ S) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft T' ε.symm)

end Sheaf

end Stacks.Sites.ExtensionByZero.OfEssentiallySmall

end
