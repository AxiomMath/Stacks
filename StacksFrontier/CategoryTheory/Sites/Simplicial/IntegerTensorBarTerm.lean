module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafifyMixed
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerTensorSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplexCoefficientCopower
import StacksFrontier.CategoryTheory.CommutingSquares
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf-level projection formula of Stacks 0D9E

Let `S` be a simplicial-site situation and `n` a simplicial degree. The degree-`n` term
`bar_n(F)` of the simplex-coefficient resolution of an abelian sheaf `F` on the total site is the
tensor product `g_{n!}ℤ ⊗_ℤ F` of `F` with the lower shriek image of the constant integer sheaf
of the degree-`n` component.

The identification is assembled as follows. Abelian sheaves on the total site are the sheaves
of modules over the constant sheaf of rings `ℤ`, and under that equivalence `g_{n!}ℤ` is the
sheafification of the free presheaf of modules on the presheaf of `n`-simplices (Stacks 09WI).
The tensor product of two sheaves of modules is the sheafification of the objectwise tensor
product of the underlying presheaves of modules (Stacks 0GMW); the tensor product of a free
presheaf of modules with a presheaf of modules is a copower; and the copower of an abelian
presheaf by the presheaf of `n`-simplices is the degree-`n` term of its simplex-coefficient
presheaf, whose sheafification is `bar_n(F)`.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main definitions

* `barTermIsoIntegerTensorApp`: **the projection formula at a single abelian sheaf**,
  `bar_n(F) ≅ g_{n!}ℤ ⊗_ℤ F`.
* `barTermIsoIntegerTensor`: the same as an isomorphism of endofunctors of abelian sheaves on the
  total site.

## Main results

* `barTermIsoIntegerTensorApp_naturality`: the identification is natural in the abelian sheaf
  being resolved.

## Implementation notes

The comparison is stated objectwise, with naturality as a separate equation, rather than as an
isomorphism of functors directly. The functor-level statement is the natural one and it does not
elaborate: whiskering the bifunctor isomorphism of Stacks 0GMW against
`CategoryTheory.Functor.prod` makes the unifier unfold the sheafification functor and exhausts
the heartbeat budget, which is the failure
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafifyMixed` records as well.

`PresheafOfModules.tensorSheafifyMixedIso` compares the tensor product of a sheaf of modules with
the associated sheaf of a presheaf of modules, with the *sheaf* in the first tensor slot. Here the
sheaf being resolved sits in the second slot, so the mirror comparison is built here, and its
naturality in the sheaf factor is proved by the same route, through
`PresheafOfModules.tensorSheafifyComparison_naturality`, whose two sides are already in the shape
the unifier can see.

The comparison of scalars is spelled `CategoryTheory.Sheaf.toRingCatMap` of the sheafification
unit of the constant presheaf of commutative rings `ℤ`, which is the spelling the comparisons of
Stacks 0GMW take. It is definitionally
`Stacks.DerivedTensor.AbelianSheaves.intRingSheafScalars`, but only up to unfolding a definition,
which instance search does not do; so the local injectivity and surjectivity instances are
restated at this spelling. For the same reason the sheaves of modules are named through
`CategoryTheory.SimplicialSiteSituation.barRings` rather than through
`Stacks.DerivedTensor.AbelianSheaves.intRings`: the two spellings of the sheaf of rings carry
two category instances on the sheaves of modules over it, and a `simp` lemma about composition
matches neither term built from the other.

## References

* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

universe v₀ u₀ w₀ z₀ z₁ u

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves Stacks.SheafOfModules.Tensor PresheafOfModules

/-! ### Tensoring the associated sheaf of a presheaf of modules with a sheaf of modules -/

section Mirror

variable {C : Type u₀} [Category.{v₀} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w₀}} {Osharp : Sheaf J CommRingCat.{w₀}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (Sheaf.toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (Sheaf.toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z₀}] [HasWeakSheafify J AddCommGrpCat.{z₀}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z₁}] [HasWeakSheafify J AddCommGrpCat.{z₁}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max z₀ z₁}]
  [HasWeakSheafify J AddCommGrpCat.{max z₀ z₁}]
  (F : PresheafOfModules.{z₀} (O ⋙ forget₂ CommRingCat RingCat))

/-- The tensor product of the associated sheaf of a presheaf of `O`-modules with a sheaf of
`O♯`-modules: `F♯ ⊗_{O♯} G ≅ (F ⊗_O G|_O)♯`. This is
`PresheafOfModules.tensorSheafifyMixedIso` with the two tensor slots interchanged. -/
def tensorSheafifySecondIso (G : SheafOfModules.{z₁} (Sheaf.toRingCat J Osharp)) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, z₀, z₁} Osharp))).obj
        ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F, G) ≅
      (moduleSheafification.{v₀, u₀, w₀, max z₀ z₁} J a).obj
        (tensorObj F ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).obj G)) :=
  ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, z₀, z₁} Osharp))).mapIso
      (Iso.prod (Iso.refl ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F))
        (sheafifyRestrictSheafIso.{v₀, u₀, w₀, z₁} J a G).symm) ≪≫
    (sheafificationTensorIso.{v₀, u₀, w₀, z₀, z₁} J a).app
      (F, (restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).obj G)

/-- The mirror comparison, written out. -/
lemma tensorSheafifySecondIso_hom (G : SheafOfModules.{z₁} (Sheaf.toRingCat J Osharp)) :
    (tensorSheafifySecondIso.{v₀, u₀, w₀, z₀, z₁} J a F G).hom =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, z₀, z₁} Osharp))).map
          (CategoryTheory.Prod.mkHom
            (𝟙 ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F))
            (sheafifyRestrictSheafIso.{v₀, u₀, w₀, z₁} J a G).inv) ≫
        tensorSheafifyDesc.{v₀, u₀, w₀, z₀, z₁} J a F
          ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).obj G) :=
  rfl

/-- The inverse of the mirror comparison, written out. -/
lemma tensorSheafifySecondIso_inv (G : SheafOfModules.{z₁} (Sheaf.toRingCat J Osharp)) :
    (tensorSheafifySecondIso.{v₀, u₀, w₀, z₀, z₁} J a F G).inv =
      tensorSheafifyComparison.{v₀, u₀, w₀, z₀, z₁} J a F
            ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).obj G) ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, z₀, z₁} Osharp))).map
          (CategoryTheory.Prod.mkHom
            (𝟙 ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F))
            (sheafifyRestrictSheafIso.{v₀, u₀, w₀, z₁} J a G).hom) :=
  rfl

/-- The mirror comparison is natural in the sheaf factor. -/
lemma tensorSheafifySecondIso_inv_naturality
    {G G' : SheafOfModules.{z₁} (Sheaf.toRingCat J Osharp)} (g : G ⟶ G') :
    (moduleSheafification.{v₀, u₀, w₀, max z₀ z₁} J a).map
          (tensorHom (𝟙 F) ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).map g)) ≫
        (tensorSheafifySecondIso.{v₀, u₀, w₀, z₀, z₁} J a F G').inv =
      (tensorSheafifySecondIso.{v₀, u₀, w₀, z₀, z₁} J a F G).inv ≫
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, z₀, z₁} Osharp))).map
          (CategoryTheory.Prod.mkHom
            (𝟙 ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F)) g) := by
  have hp : CategoryTheory.Prod.mkHom
        ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).map (𝟙 F))
        ((moduleSheafification.{v₀, u₀, w₀, z₁} J a).map
          ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).map g)) ≫
      CategoryTheory.Prod.mkHom (𝟙 ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F))
        (sheafifyRestrictSheafIso.{v₀, u₀, w₀, z₁} J a G').hom =
    CategoryTheory.Prod.mkHom (𝟙 ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F))
        (sheafifyRestrictSheafIso.{v₀, u₀, w₀, z₁} J a G).hom ≫
      CategoryTheory.Prod.mkHom (𝟙 ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F)) g :=
    CategoryTheory.Prod.hom_ext (by simp) (sheafifyRestrictSheafIso_naturality J a g)
  have hn := tensorSheafifyComparison_naturality J a F
      ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).obj G) (𝟙 F)
      ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).map g)
  rw [tensorSheafifySecondIso_inv, tensorSheafifySecondIso_inv]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (Functor.map _) hp).trans (Functor.map_comp _ _ _)))).trans
        (Category.assoc _ _ _).symm)))

/-- The mirror comparison is natural in the sheaf factor. -/
lemma tensorSheafifySecondIso_hom_naturality
    {G G' : SheafOfModules.{z₁} (Sheaf.toRingCat J Osharp)} (g : G ⟶ G') :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u₀, v₀, w₀, z₀, z₁} Osharp))).map
          (CategoryTheory.Prod.mkHom
            (𝟙 ((moduleSheafification.{v₀, u₀, w₀, z₀} J a).obj F)) g) ≫
        (tensorSheafifySecondIso.{v₀, u₀, w₀, z₀, z₁} J a F G').hom =
      (tensorSheafifySecondIso.{v₀, u₀, w₀, z₀, z₁} J a F G).hom ≫
        (moduleSheafification.{v₀, u₀, w₀, max z₀ z₁} J a).map
          (tensorHom (𝟙 F) ((restrictSheafFunctor.{v₀, u₀, w₀, z₁} J a).map g)) := by
  exact square_of_inv _ _ _ _ (tensorSheafifySecondIso_inv_naturality J a F g).symm

end Mirror

/-! ### The copower identifications are natural -/

section Copower

variable {C : Type u₀} [Category.{v₀} C] (E : Cᵒᵖ ⥤ Type u₀) (R : Cᵒᵖ ⥤ CommRingCat.{u₀})

/-- The identification of `R[E] ⊗_R N` with the copower of `N` by `E` is natural in `N`. -/
lemma freeTensorCopowerIso_naturality
    {N N' : PresheafOfModules.{u₀} (R ⋙ forget₂ CommRingCat RingCat)} (h : N ⟶ N') :
    (toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (tensorHom (𝟙 (freeObj E)) h) ≫
        (freeTensorCopowerIso E R N').hom =
      (freeTensorCopowerIso E R N).hom ≫
        (copowerPresheaf E).map
          ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map h) := by
  refine square_of_inv _ _ _ _ ?_
  apply NatTrans.ext
  funext X
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro e m
  have h1 : AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N X).inv
      (Finsupp.single e m) = _ :=
    freeTensorCopowerIsoApp_inv_single E R N X e m
  have h2 : Hom.app (tensorHom (𝟙 (freeObj E)) h) X
      (ModuleCat.freeMk (R := (R.obj X : Type u₀)) e ⊗ₜ[(R.obj X : Type u₀)] m) = _ :=
    tensorHom_tmul (𝟙 (freeObj E)) h X _ m
  have h3 : AddCommGrpCat.Hom.hom
      ((copowerPresheafMap E
        ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map h)).app X)
      (Finsupp.single e m) = _ :=
    copowerPresheafMap_app_single E _ X e m
  have h4 : AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N' X).inv
      (Finsupp.single e (Hom.app h X m)) = _ :=
    freeTensorCopowerIsoApp_inv_single E R N' X e (Hom.app h X m)
  show AddCommGrpCat.Hom.hom
      (((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map
        (tensorHom (𝟙 (freeObj E)) h)).app X)
      (AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N X).inv (Finsupp.single e m)) =
    AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N' X).inv
      (AddCommGrpCat.Hom.hom
        ((copowerPresheafMap E
          ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map h)).app X)
        (Finsupp.single e m))
  exact ((congrArg (AddCommGrpCat.Hom.hom
      (((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map
        (tensorHom (𝟙 (freeObj E)) h)).app X)) h1).trans h2).trans
    ((congrArg (AddCommGrpCat.Hom.hom (freeTensorCopowerIsoApp E R N' X).inv) h3).trans h4).symm

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- The identification of the copower by the presheaf of `n`-simplices with the degree-`n` term
of the simplex-coefficient presheaf is natural in the abelian presheaf. -/
lemma copowerStdSimplexIso_naturality
    {G H : S.totalCategoryᵒᵖ ⥤ AddCommGrpCat.{u}} (β : G ⟶ H) :
    (copowerPresheaf (stdSimplexPresheaf' S n)).map β ≫ (copowerStdSimplexIso S n H).hom =
      (copowerStdSimplexIso S n G).hom ≫
        ((simplexCoefficientDiagram' (totalSimplexDegree S).leftOp).map β).app
          (Opposite.op n) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply Finsupp.addHom_ext
  intro x m
  have h1 : AddCommGrpCat.Hom.hom
      ((copowerPresheafMap (stdSimplexPresheaf' S n) β).app U) (Finsupp.single x m) = _ :=
    copowerPresheafMap_app_single (stdSimplexPresheaf' S n) β U x m
  have h2 : AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S n H).hom.app U)
      (Finsupp.single x (AddCommGrpCat.Hom.hom (β.app U) m)) = _ :=
    copowerStdSimplexIso_hom_app_single S n H U x (AddCommGrpCat.Hom.hom (β.app U) m)
  have h3 : AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S n G).hom.app U)
      (Finsupp.single x m) = _ :=
    copowerStdSimplexIso_hom_app_single S n G U x m
  have h4 := ι_copowerMap (C := AddCommGrpCat.{u})
    (id : (n ⟶ (totalSimplexDegree S).leftOp.obj U) →
      (n ⟶ (totalSimplexDegree S).leftOp.obj U)) (β.app U)
    (stdSimplexPresheafObjEquiv S n U x)
  show AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S n H).hom.app U)
      (AddCommGrpCat.Hom.hom ((copowerPresheafMap (stdSimplexPresheaf' S n) β).app U)
        (Finsupp.single x m)) =
    AddCommGrpCat.Hom.hom (copowerMap id (β.app U))
      (AddCommGrpCat.Hom.hom ((copowerStdSimplexIso S n G).hom.app U) (Finsupp.single x m))
  refine ((congrArg (AddCommGrpCat.Hom.hom
    ((copowerStdSimplexIso S n H).hom.app U)) h1).trans h2).trans ?_
  refine Eq.trans ?_ (congrArg (AddCommGrpCat.Hom.hom (copowerMap id (β.app U))) h3).symm
  exact (congrArg (fun k => AddCommGrpCat.Hom.hom k m) h4).symm

end Copower

/-! ### The projection formula -/

section Formula

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- The constant presheaf of commutative rings `ℤ` on the total site. -/
@[sga "3 I 3.1.3" "special case"]
abbrev intPresheaf : S.totalCategoryᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const S.totalCategoryᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))

/-- The sheafification unit presenting the constant sheaf of commutative rings `ℤ` on the total
site. This is the comparison of scalars that the tensor product comparisons of Stacks 0GMW
take. -/
abbrev intUnit : intPresheaf S ⟶ (intRingSheaf S.totalTopology).obj :=
  toSheafify S.totalTopology (intPresheaf S)

/-- The comparison of scalars `intUnit` is locally injective. -/
instance isLocallyInjective_intUnit :
    Presheaf.IsLocallyInjective S.totalTopology
      (Sheaf.toRingCatMap S.totalTopology (intUnit S)) :=
  isLocallyInjective_intRingSheafScalars S.totalTopology

/-- The comparison of scalars `intUnit` is locally surjective. -/
instance isLocallySurjective_intUnit :
    Presheaf.IsLocallySurjective S.totalTopology
      (Sheaf.toRingCatMap S.totalTopology (intUnit S)) :=
  isLocallySurjective_intRingSheafScalars S.totalTopology

/-- The constant sheaf of (not necessarily commutative) rings `ℤ` on the total site, in the
spelling the comparisons of Stacks 0GMW take. -/
abbrev barRings : Sheaf S.totalTopology RingCat.{u} :=
  Sheaf.toRingCat S.totalTopology (intRingSheaf S.totalTopology)

/-- The free presheaf of modules on the presheaf of `n`-simplices, over the constant presheaf of
commutative rings `ℤ`. -/
abbrev barFree : PresheafOfModules.{u} (intPresheaf S ⋙ forget₂ CommRingCat RingCat) :=
  freeObj (stdSimplexPresheaf' S n)

/-- `g_{n!}ℤ` as a sheaf of modules over `barRings`. -/
abbrev barComponent : SheafOfModules.{u} (barRings S) :=
  componentIntegerModule S n

/-- An abelian sheaf on the total site, read as a sheaf of modules over `barRings`. -/
abbrev barModule (F : Sheaf S.totalTopology Ab.{u}) : SheafOfModules.{u} (barRings S) :=
  (moduleEquivalence S.totalTopology).inverse.obj F

/-- A morphism of abelian sheaves on the total site, read as a morphism of sheaves of modules
over `barRings`. -/
abbrev barModuleMap {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    barModule S F ⟶ barModule S G :=
  (moduleEquivalence S.totalTopology).inverse.map α

/-- An abelian sheaf on the total site, read as a presheaf of modules over the constant presheaf
of commutative rings `ℤ`. -/
abbrev barRestrict (F : Sheaf S.totalTopology Ab.{u}) :
    PresheafOfModules.{u} (intPresheaf S ⋙ forget₂ CommRingCat RingCat) :=
  (restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).obj (barModule S F)

/-- `g_{n!}ℤ`, read as the sheafification of the free presheaf of modules on the presheaf of
`n`-simplices, in the spelling of the comparisons of Stacks 0GMW. -/
def componentIntegerModuleIso :
    barComponent S n ≅
      (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj (barFree S n) :=
  moduleEquivalenceInverseComponentIntegerSheafIso S n

/-- The underlying presheaf of modules of an abelian sheaf is its underlying abelian presheaf. -/
def barCounitIso (F : Sheaf S.totalTopology Ab.{u}) :
    (toPresheaf (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).obj (barRestrict S F) ≅ F.obj :=
  (sheafToPresheaf S.totalTopology Ab.{u}).mapIso
    ((moduleEquivalence S.totalTopology).counitIso.app F)

/-- `barCounitIso` is natural. -/
lemma barCounitIso_naturality {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    (toPresheaf (intPresheaf S ⋙ forget₂ CommRingCat RingCat)).map
          ((restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).map
            (barModuleMap S α)) ≫ (barCounitIso S G).hom =
      (barCounitIso S F).hom ≫ (sheafToPresheaf S.totalTopology Ab.{u}).map α :=
  congrArg (fun k => (sheafToPresheaf S.totalTopology Ab.{u}).map k)
    ((moduleEquivalence S.totalTopology).counitIso.hom.naturality α)

/-- Tensoring with `g_{n!}ℤ` in sheaves of modules, as the sheafification of the objectwise
tensor product of the free presheaf of modules on the `n`-simplices with the sheaf being
resolved. -/
def barTensorIso (F : Sheaf S.totalTopology Ab.{u}) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (intRingSheaf S.totalTopology)))).obj
        (barComponent S n, barModule S F) ≅
      (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj
        (tensorObj (barFree S n) (barRestrict S F)) :=
  ((Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (intRingSheaf S.totalTopology)))).mapIso
      (Iso.prod (componentIntegerModuleIso S n) (Iso.refl (barModule S F))) ≪≫
    tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S) (barFree S n)
      (barModule S F)

/-- `barTensorIso`, written out. -/
lemma barTensorIso_hom (F : Sheaf S.totalTopology Ab.{u}) :
    (barTensorIso S n F).hom =
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (intRingSheaf S.totalTopology)))).map
          (CategoryTheory.Prod.mkHom (componentIntegerModuleIso S n).hom
            (𝟙 (barModule S F))) ≫
        (tensorSheafifySecondIso.{u, u, u, u, u} S.totalTopology (intUnit S) (barFree S n)
          (barModule S F)).hom :=
  rfl

/-- `barTensorIso` is natural in the abelian sheaf being resolved. -/
lemma barTensorIso_naturality {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (intRingSheaf S.totalTopology)))).map
          (CategoryTheory.Prod.mkHom (𝟙 (barComponent S n)) (barModuleMap S α)) ≫
        (barTensorIso S n G).hom =
      (barTensorIso S n F).hom ≫
        (moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).map
          (tensorHom (𝟙 (barFree S n))
            ((restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).map
              (barModuleMap S α))) := by
  have hp : CategoryTheory.Prod.mkHom (𝟙 (barComponent S n)) (barModuleMap S α) ≫
      CategoryTheory.Prod.mkHom (componentIntegerModuleIso S n).hom (𝟙 (barModule S G)) =
    CategoryTheory.Prod.mkHom (componentIntegerModuleIso S n).hom (𝟙 (barModule S F)) ≫
      CategoryTheory.Prod.mkHom
        (𝟙 ((moduleSheafification.{u, u, u, u} S.totalTopology (intUnit S)).obj (barFree S n)))
        (barModuleMap S α) :=
    CategoryTheory.Prod.hom_ext (by simp) (by simp)
  rw [barTensorIso_hom, barTensorIso_hom]
  refine square_comp ?_
    (tensorSheafifySecondIso_hom_naturality.{u, u, u, u, u} S.totalTopology (intUnit S)
      (barFree S n) (barModuleMap S α))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ hp

/-- Tensoring with `g_{n!}ℤ` as the tensor bifunctor of Stacks 0GMW with its left factor
fixed. -/
lemma integerTensorAb_map_eq {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    (integerTensorAb S n).map α =
      (moduleEquivalence S.totalTopology).functor.map
        (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (intRingSheaf S.totalTopology)))).map
          (CategoryTheory.Prod.mkHom (𝟙 (barComponent S n)) (barModuleMap S α))) := by
  refine congrArg (moduleEquivalence S.totalTopology).functor.map ?_
  exact ((congrArg (· ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (intRingSheaf S.totalTopology)).obj (barComponent S n)).map (barModuleMap S α))
    (congrArg (fun t => NatTrans.app t _) ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (intRingSheaf S.totalTopology)).map_id (barComponent S n)))).trans
    (Category.id_comp _)).symm

/-- The projection formula, read from the tensor product towards the resolution. -/
def barTermIsoAux (F : Sheaf S.totalTopology Ab.{u}) :
    (integerTensorAb S n).obj F ≅ (barTerm S n).obj F :=
  (moduleEquivalence S.totalTopology).functor.mapIso (barTensorIso S n F) ≪≫
    (sheafificationCompToSheaf (Sheaf.toRingCatMap S.totalTopology (intUnit S))).app
        (tensorObj (barFree S n) (barRestrict S F)) ≪≫
      (presheafToSheaf S.totalTopology Ab.{u}).mapIso
          (freeTensorCopowerIso (stdSimplexPresheaf' S n) (intPresheaf S) (barRestrict S F)) ≪≫
        (presheafToSheaf S.totalTopology Ab.{u}).mapIso
            ((copowerPresheaf (stdSimplexPresheaf' S n)).mapIso (barCounitIso S F)) ≪≫
          (presheafToSheaf S.totalTopology Ab.{u}).mapIso (copowerStdSimplexIso S n F.obj)

/-- `barTermIsoAux`, written out. -/
lemma barTermIsoAux_hom (F : Sheaf S.totalTopology Ab.{u}) :
    (barTermIsoAux S n F).hom =
      ((moduleEquivalence S.totalTopology).functor.mapIso (barTensorIso S n F)).hom ≫
        ((sheafificationCompToSheaf (Sheaf.toRingCatMap S.totalTopology (intUnit S))).app
            (tensorObj (barFree S n) (barRestrict S F))).hom ≫
          ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
              (freeTensorCopowerIso (stdSimplexPresheaf' S n) (intPresheaf S)
                (barRestrict S F))).hom ≫
            ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
                ((copowerPresheaf (stdSimplexPresheaf' S n)).mapIso (barCounitIso S F))).hom ≫
              ((presheafToSheaf S.totalTopology Ab.{u}).mapIso
                (copowerStdSimplexIso S n F.obj)).hom :=
  rfl

/-- `barTermIsoAux` is natural in the abelian sheaf being resolved. -/
lemma barTermIsoAux_naturality {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    (integerTensorAb S n).map α ≫ (barTermIsoAux S n G).hom =
      (barTermIsoAux S n F).hom ≫ (barTerm S n).map α := by
  rw [barTermIsoAux_hom, barTermIsoAux_hom, integerTensorAb_map_eq]
  refine square_comp
    (square_map (moduleEquivalence S.totalTopology).functor _ _ _ _
      (barTensorIso_naturality S n α))
    (square_comp
      ((sheafificationCompToSheaf
        (Sheaf.toRingCatMap S.totalTopology (intUnit S))).hom.naturality
          (tensorHom (𝟙 (barFree S n))
            ((restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).map
              (barModuleMap S α))))
      (square_comp
        (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
          (freeTensorCopowerIso_naturality (stdSimplexPresheaf' S n) (intPresheaf S)
            ((restrictSheafFunctor.{u, u, u, u} S.totalTopology (intUnit S)).map
              (barModuleMap S α))))
        (square_comp
          (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
            (square_map (copowerPresheaf (stdSimplexPresheaf' S n)) _ _ _ _
              (barCounitIso_naturality S α)))
          (square_map (presheafToSheaf S.totalTopology Ab.{u}) _ _ _ _
            (copowerStdSimplexIso_naturality S n
              ((sheafToPresheaf S.totalTopology Ab.{u}).map α))))))

/-- **The sheaf-level projection formula of Stacks 0D9E (1).** The degree-`n` term of the
simplex-coefficient resolution of an abelian sheaf on the total site is the tensor product of
that sheaf with `g_{n!}ℤ`. -/
def barTermIsoIntegerTensorApp (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    (F : Sheaf S.totalTopology Ab.{u}) :
    (barTerm S n).obj F ≅ (integerTensorAb S n).obj F :=
  (barTermIsoAux S n F).symm

/-- `barTermIsoIntegerTensorApp` is natural in the abelian sheaf being resolved. -/
theorem barTermIsoIntegerTensorApp_naturality (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) {F G : Sheaf S.totalTopology Ab.{u}} (α : F ⟶ G) :
    (barTerm S n).map α ≫ (barTermIsoIntegerTensorApp S n G).hom =
      (barTermIsoIntegerTensorApp S n F).hom ≫ (integerTensorAb S n).map α := by
  show (barTerm S n).map α ≫ (barTermIsoAux S n G).inv =
    (barTermIsoAux S n F).inv ≫ (integerTensorAb S n).map α
  rw [Iso.comp_inv_eq, Category.assoc, barTermIsoAux_naturality S n α,
    Iso.inv_hom_id_assoc]

/-- The same, as an isomorphism of functors. -/
def barTermIsoIntegerTensor (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    barTerm S n ≅ integerTensorAb S n :=
  NatIso.ofComponents (barTermIsoIntegerTensorApp S n)
    (barTermIsoIntegerTensorApp_naturality S n)

end Formula

end CategoryTheory.SimplicialSiteSituation

end
