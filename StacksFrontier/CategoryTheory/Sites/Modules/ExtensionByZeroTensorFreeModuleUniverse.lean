module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceCoproductTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactnessFreeModuleUniverse
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero and the tensor product at a free module universe

Let `(C, O)` be a ringed site whose objects lie in `Type u`, whose morphisms lie in `v` and
whose structure sheaf has sections in `w`, and let `U` be an object of `C`. This file carries
Stacks 0E8I to a **free module universe `a`**: extension by zero `j_{U!}` from the localized
site `C/U` commutes with tensoring by a sheaf of `O`-modules `F`,

`j_{U!}G ⊗_O F ≅ j_{U!}(G ⊗_{O|_U} F|_U)`,

naturally in the sheaf of `O|_U`-modules `G`.

## Main results

* `Stacks.Sites.ExtensionByZero.FreeModuleUniverse.restrictionTensorIso`: **Stacks 0E8I** with
  the module universe a free parameter, as an isomorphism of functors in the module on the
  slice site.

## Universes

The module universe is a bare variable `a`, subject only to `UnivLE.{v, a}`. That is the
difference from
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroTensorEssentiallySmall.lean`, which
states the same comparison at `RingedSite.{c, u, u}` for an essentially `u`-small site — every
universe there but the one of the objects is collapsed to `u`.

Two things had to be true for the module universe to be free, and both now are.

* The left adjoint `j_{U!}` of restriction has to exist at a free module universe. It does, with
  no smallness assumption on `C`, because the coproduct formula of Stacks 03EJ is indexed by the
  hom-set `V ⟶ U : Type v`; this is
  `SheafOfModules.sheafOverRestriction_of_univLE`.
* The presheaf-level comparison — extension from `C/U` commutes with the objectwise tensor
  product — has to exist at a free module universe. Until
  `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/SliceCoproductTensor.lean` it did not: the
  only comparison available was
  `Stacks.Sites.OverModules.FormulaExtension.extensionTensorIso`, built on the `DirectSum`
  model of `j_{U!}`, whose sections over `V` are a `DFinsupp` over that hom-set and so lie in
  `max v m` rather than in a free universe. `Stacks.Sites.OverModules.extensionTensorIso` is the
  same comparison for the coproduct model, which carries the free parameter.

The two models of `j_{U!}` are identified, as always, by the uniqueness of left adjoints:
`Stacks.Sites.ExtensionByZero.FreeModuleUniverse.presheafPullbackIsoExtension`.

The earlier statement is not replaced. Its consumers are untouched, and they go on using it;
this one exists for a consumer that needs the module universe to stay a bare variable.

## References

* [Stacks Project, Tag 0E8I](https://stacks.math.columbia.edu/tag/0E8I)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.ExtensionByZero.FreeModuleUniverse

universe a w v u

open Stacks.Sites.OverModules
open AlgebraicGeometry (RingedSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open AlgebraicGeometry.SheafOfModules.PresheafOfModules (tensorRight)
open Stacks.SheafOfModules.TensorColimits (tensorCommIso
  tensorSheafificationIsoGeneral)

/-! ### Tensoring and sheafification, at a free module universe -/

section SheafLevel

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify J AddCommGrpCat.{a}]

/-- Sheafification of presheaves of modules over the ring presheaf underlying `O`, at the free
module universe.  Naming it pins the source presheaf of rings to the spelling
`(ringSheaf O).obj`, which is what lets the two sides of
`tensorSheafificationIso` elaborate. -/
noncomputable abbrev sheafifyModules (O : Sheaf J CommRingCat.{w}) :
    PresheafOfModules.{a} (ringSheaf O).obj ⥤
      SheafOfModules.{a} (ringSheaf O) :=
  PresheafOfModules.sheafification.{a} (R := ringSheaf O)
    (𝟙 (ringSheaf O).obj)

/-- Tensoring on the left by `F` and tensoring on the right by `F` agree, as endofunctors of
sheaves of modules, at the free module universe. -/
noncomputable def tensorLeftIsoSheafTensorRight (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{a} (ringSheaf O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, a, a} O).obj F ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F :=
  NatIso.ofComponents
    (fun A => (sheafifyModules J O).mapIso ((tensorCommIso J O F.val).app A.val)) (by
      intro A B morphism
      exact (((sheafifyModules J O).map_comp _ _).symm.trans
        (congrArg (sheafifyModules J O).map
          ((tensorCommIso J O F.val).hom.naturality morphism.val))).trans
        ((sheafifyModules J O).map_comp _ _))

/-- Tensoring on the right with `F` commutes with sheafification, at the free module
universe. -/
noncomputable def tensorSheafificationIso (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{a} (ringSheaf O)) :
    sheafifyModules J O ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F ≅
      tensorRight (O := O.obj) F.val ⋙ sheafifyModules J O :=
  Functor.isoWhiskerLeft _ (tensorLeftIsoSheafTensorRight J O F).symm ≪≫
    (tensorSheafificationIsoGeneral J O F).symm ≪≫
    Functor.isoWhiskerRight (tensorCommIso J O F.val) _

end SheafLevel

/-! ### Extension by zero commutes with tensoring -/

section Sheaf

variable (X : RingedSite.{u, v, w}) (U : X.C) [UnivLE.{v, a}]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify X.J AddCommGrpCat.{a}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{a}]

/-- Mathlib's presheaf-level extension by zero at the free module universe, written with the
morphism of presheaves of rings spelled as the identity of `R.over U`. -/
noncomputable abbrev presheafExtendByZero :
    PresheafOfModules.{a} ((ringSheaf X.O).over U).obj ⥤
      PresheafOfModules.{a} (ringSheaf X.O).obj :=
  haveI := SheafOfModules.presheafOverRestriction_of_univLE.{a, w, v, u}
    (ringSheaf X.O) U
  PresheafOfModules.pullback.{a} (F := Over.forget U)
    (𝟙 ((ringSheaf X.O).over U) :
      (ringSheaf X.O).over U ⟶ (ringSheaf X.O).over U).hom

/-- Tensoring on the right with a sheaf of modules on the localized site, with its source and
target spelled at the ring sheaf `(ringSheaf X.O).over U` and at the module
universe `a`.  Both are needed in the result type: the slice site has its objects in
`max u v`, so left to itself unification solves the two module universes of
`Stacks.SheafOfModules.Tensor.sheafTensor` — which are free and independent — as `max u v`
rather than as `a`, and the comparison below is then not type-correct. -/
noncomputable abbrev sliceSheafTensorRight
    (G : SheafOfModules.{a} ((ringSheaf X.O).over U)) :
    SheafOfModules.{a} ((ringSheaf X.O).over U) ⥤
      SheafOfModules.{a} ((ringSheaf X.O).over U) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor (X.O.over U)).flip.obj G

/-- Extension by zero of sheaves of modules from the site localized at `U`, at the free module
universe.  Naming it pins the ring sheaf to the spelling
`(ringSheaf X.O).over U`, so that the two sides of `restrictionTensorIso`
elaborate. -/
@[sga "4 XVII 5.1.1" "partial"]
noncomputable abbrev extendByZero :
    SheafOfModules.{a} ((ringSheaf X.O).over U) ⥤
      SheafOfModules.{a} (ringSheaf X.O) :=
  haveI := SheafOfModules.sheafOverRestriction_of_univLE.{a, w, v, u}
    (ringSheaf X.O) U
  SheafOfModules.pullback.{a} (F := Over.forget U)
    (𝟙 ((ringSheaf X.O).over U))

/-- **Stacks 0E8I at a free module universe.** For a sheaf of modules `F` on `X`, the extension
by zero of `G ⊗ F|_U` is the extension by zero of `G`, tensored with `F`, naturally in `G`.

The attribute records the shape at which this holds: the objects of `C` in `Type u`, its
morphisms in `v`, the structure sheaf in `w` and the modules in a free `a` with `UnivLE.{v, a}`,
and no smallness assumption on `C`. The tag is carried in full by
`Stacks.SheafOfModules.ExtensionByZero.extensionByZeroTensorIso`, where objects, morphisms,
ring and modules lie in a single universe; that registration stands and this one does not
replace it, nor does it replace
`Stacks.Sites.ExtensionByZero.OfEssentiallySmall.restrictionTensorIso`. -/
@[stacks 0E8I "objects in Type u, morphisms in v, ring sections in w, modules in a free a \
with UnivLE v a, and no smallness assumption on the site"]
noncomputable def restrictionTensorIso
    (F : SheafOfModules.{a} (ringSheaf X.O)) :
    extendByZero.{a} X U ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F ≅
      sliceSheafTensorRight.{a} X U (F.over U) ⋙ extendByZero.{a} X U := by
  haveI := SheafOfModules.sheafOverRestriction_of_univLE.{a, w, v, u}
    (ringSheaf X.O) U
  haveI := SheafOfModules.presheafOverRestriction_of_univLE.{a, w, v, u}
    (ringSheaf X.O) U
  let R := ringSheaf X.O
  let I := SheafOfModules.forget.{a} (R.over U)
  let P := presheafExtendByZero.{a} X U
  let S := sheafifyModules.{a} X.J X.O
  let S' := sheafifyModules.{a} (X.J.over U) (X.O.over U)
  let T := tensorRight (O := X.O.obj) F.val
  let T' := tensorRight (O := (X.O.over U).obj) (F.over U).val
  let β : P ≅ extensionFunctor.{v, u, w, a} R.obj U :=
    presheafPullbackIsoExtension.{a, w, v, u} R.obj U
  let γ : P ⋙ T ≅ T' ⋙ P :=
    Functor.isoWhiskerRight β T ≪≫ extensionTensorIso X.O.obj U F.val ≪≫
      Functor.isoWhiskerLeft T' β.symm
  let δ : S ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F ≅ T ⋙ S :=
    tensorSheafificationIso.{a} X.J X.O F
  let ε : S' ⋙ extendByZero.{a} X U ≅ P ⋙ S :=
    SheafOfModules.sheafificationCompPullback (𝟙 ((ringSheaf X.O).over U))
  exact Functor.isoWhiskerRight
      (SheafOfModules.pullbackIso (𝟙 ((ringSheaf X.O).over U)))
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft P δ) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight γ S) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerLeft T' ε.symm)

end Sheaf

end Stacks.Sites.ExtensionByZero.FreeModuleUniverse

end
