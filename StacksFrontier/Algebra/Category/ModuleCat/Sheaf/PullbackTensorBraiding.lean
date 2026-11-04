module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections

/-! # The comparison of Stacks 03EL commutes with the braiding

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi — four fields, a
morphism of topoi together with the two forms of the structure map, as in
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, with no presentation of the morphism of topoi
by a functor of the underlying sites. The comparison of **Stacks 03EL**

`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G`

is `Stacks.SheafOfModules.pullbackTensorIso`, and the only things known about it are that the
six-step chain of bijections `Stacks.SheafOfModules.pullbackTensorHomEquiv` carries it to the
identity and that it is natural in the two modules. This file proves that it is **compatible with
the braiding** of the tensor product sheaf: braiding the two factors downstairs, pulling back and
comparing is comparing, pulling back and braiding the two factors upstairs.

Stacks 03EL asserts the comparison and its functoriality in the two modules and nothing else, so
this is not part of the tag; the tag is carried by `Stacks.SheafOfModules.pullbackTensorIso`.
The compatibility is what turns a *right*-unitor coherence of the comparison into a *left*-unitor
one, the braided coherence law `β ≫ ρ = λ` for the tensor product sheaf being
`SheafOfModules.sheafTensorBraiding_comp_tensorSheafUnitRightIso`; before this file the comparison
of Stacks 03EL carried no compatibility with the braiding anywhere in the development, and the two
unitor coherences were unrelated.

## Main results

* `Stacks.SheafOfModules.pullbackTensorBottomPairing_comp_braiding`: **the pairing at the bottom
  of the chain of Stacks 03EL, braided.** This is where the mathematics is: the bottom of the
  chain pairs two local sections by the pure tensor of their images under the unit of extension of
  scalars (`Stacks.SheafOfModules.pairingApp_pullbackTensorBottom`), and the braiding of the
  tensor product sheaf exchanges the two factors of a pure tensor
  (`Stacks.SheafOfModules.tensorSheafBraiding_tensorSectionsAt`), so the two pairings differ by
  the braiding of the binary product and by nothing else.
* `Stacks.SheafOfModules.pullbackTensorIso_hom_app_comp_braiding`: **the comparison of
  Stacks 03EL commutes with the braiding**, for an arbitrary morphism of ringed topoi.

## Implementation notes

**How the coherence is proved.** Both sides are morphisms out of `f^*(F ⊗_{O_D} G)`, so step 1 of
the chain — the adjunction of Stacks 03D7 — is injective on them, and transposing along it moves
the identity to the *target* topos. There the two sides are
`Stacks.SheafOfModules.pullbackTensorTransposedComparison` postcomposed with the direct image of
the braiding, and the braiding precomposed with the transposed comparison of the opposite order,
both out of a tensor product sheaf of two sheaves on `D`; `tensorSheaf_hom_ext` then reduces
everything to the unit image of a pure tensor `a ⊗ₜ r`. On that element both sides are the direct
image of one morphism — `pullbackTensorBraidedBottomHom` — evaluated at the pair `(a, r)` pushed
through the unit of `f⁻¹ ⊣ f_*`: on the left because the braiding of the target meets the pairing
at the bottom of the chain, on the right because the braiding downstairs exchanges the pure tensor
and then the braiding of the binary product is carried across the topos unit by its naturality and
across the product comparison by
`CategoryTheory.Limits.map_braiding_hom_comp_prodComparison`.

The direct image is never described on sections, and for an abstract
`CategoryTheory.Sheaf.MorphismOfTopoi` it has no description: every statement below keeps the
sections of `f_*N` opaque and rewrites only the *morphism* inside. That is why no site
presentation is needed.

**`CategoryTheory.Limits.prod.braiding` rather than a bespoke swap.** The swap of a binary product
used here is Mathlib's, and its compatibility with a product comparison is Mathlib's
`CategoryTheory.Limits.map_braiding_hom_comp_prodComparison`. DEDUP OWED:
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorRightUnitor.lean` carries private
`swapHom` and `prodComparison_swapHom`, which are those two Mathlib declarations restated; they
should be replaced by them.

**Naming the endpoint objects is the only lever on the elaborator's budget**, and it is used
throughout: `pullbackTensorBottomPairing`, `pullbackTensorBraidedBottomHom` and
`pullbackTensorUnitProdSection` exist because the two value formulas below, written with their
expansions inline and assembled as one nested term, exhaust the default heartbeat budget at `whnf`
before the statement has elaborated. Splitting the two sides of the coherence into their own
declarations is what brings the whole file inside the budget; no heartbeat budget is raised
anywhere here.

**Why a pair of local sections is declared with its product object written out.** The two
spellings of the type of a local section of `F` — `F.val.obj U` and the sections over `U` of
`Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F` — are definitionally but not
syntactically equal, and a goal carrying both is not type-correct at `implicit` transparency,
after which a `rw` reports a pattern it cannot find.
`sectionsFunctor_map_prodBraiding_prodObjMk` is therefore stated over
binders of the second type and applied by `exact`, and every `Functor.prodObjMk` below carries its
two object arguments explicitly.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

universe w v u w' v' u'

namespace Stacks.SheafOfModules

section Braiding

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The transpose, across the adjunction of Stacks 03D7, of the comparison of Stacks 03EL:
steps 2, 3 and 4 of the chain applied to the bottom of the chain. -/
def pullbackTensorTransposedComparison :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
      (pushforwardModules f).obj (pullbackTensorTarget f F G) :=
  (pullbackTensorStep2 f F G (pullbackTensorTarget f F G)).symm
    ((pullbackTensorStep3 f F G (pullbackTensorTarget f F G)).symm
      ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
        (pullbackTensorBottomHom f F G)))

/-- Step 1 of the chain of Tag 03EL carries the comparison of Stacks 03EL to
`pullbackTensorTransposedComparison`. -/
lemma pullbackTensorStep1_pullbackTensorIso_hom_app :
    pullbackTensorStep1 f F G (pullbackTensorTarget f F G)
        ((pullbackTensorIso f).hom.app (F, G)) =
      pullbackTensorTransposedComparison f F G :=
  (pullbackTensorStep1 f F G (pullbackTensorTarget f F G)).apply_symm_apply _

/-- **The underlying sheaf of sets of the inverse image of a sheaf of `O_D`-modules**, read at the
`inverseImageModules` spelling of the inverse image and over the inverse-image structure sheaf.
Named once because that is the spelling the universal property of the tensor product over
`f⁻¹O_D` — step 4 of the chain of Tag 03EL — is stated at, and writing it out inline makes every
statement below unreadable. -/
abbrev inverseImageModuleSheaf : Sheaf X.J (Type w) :=
  Sheaf.moduleSheaf
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)

/-- The pairing at the bottom of the chain of Tag 03EL, declared once with its source spelled as
the product of the two module sheaves over the inverse-image structure sheaf — the spelling the
universal property of the tensor product over `f⁻¹O_D` is stated at. -/
def pullbackTensorBottomPairing :
    inverseImageModuleSheaf f F ⨯ inverseImageModuleSheaf f G ⟶
      Sheaf.moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
          (pullbackTensorTarget f F G)) :=
  ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
    (pullbackTensorBottomHom f F G)).1

/-- A functor to types preserving finite products carries the braiding of a binary product to the
swap of a pair. -/
private lemma map_prodBraiding_prodObjMk {D : Type*} [Category D] [HasFiniteProducts D]
    (P : D ⥤ Type*) [PreservesFiniteProducts P] {A B : D} (x : P.obj A) (y : P.obj B) :
    P.map (Limits.prod.braiding A B).hom (Functor.prodObjMk x y) = Functor.prodObjMk y x := by
  rw [Limits.prod.braiding_hom, Functor.map_lift_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] [Y.J.HasSheafCompose (forget RingCat)] in
/-- **The braiding of a binary product on a pair of local sections.** It is stated over binders
typed as sections of the two module sheaves rather than as sections of `F` and `G`: the two types
are definitionally but not syntactically equal, and against the second spelling the rewrites below
report patterns they cannot find. -/
lemma sectionsFunctor_map_prodBraiding_prodObjMk (U : Y.Cᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.J U).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F))
    (y : (Sheaf.sectionsFunctor Y.J U).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)) :
    (Sheaf.sectionsFunctor Y.J U).map
        (Limits.prod.braiding (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).hom
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U) x y) =
      Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U) y x :=
  map_prodBraiding_prodObjMk _ x y

/-- The pair of local sections carried through the unit of `f⁻¹ ⊣ f_*`, declared once. This is
the element every value formula of the chain of Tag 03EL stops at: the inverse image of an
abstract morphism of topoi has no description on sections. -/
def pullbackTensorUnitProdSection (U : Y.Cᵒᵖ) (a : F.val.obj U) (r : G.val.obj U) :
    (Sheaf.sectionsFunctor Y.J U).obj
      (f.toToposHom.pushforward.obj
        (f.toToposHom.inverseImage.obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))) :=
  (Sheaf.sectionsFunctor Y.J U).map
    (f.toToposHom.adj.unit.app
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G))
    (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
      (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
      (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) a r)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- **The pairing at the bottom of the chain of Tag 03EL, braided.** Postcomposing it with the
braiding of the target is precomposing the pairing of the opposite order with the braiding of the
binary product: both carry a pair of local sections to the pure tensor of their images under the
unit of extension of scalars, in the opposite order. -/
lemma pullbackTensorBottomPairing_comp_braiding :
    pullbackTensorBottomPairing f F G ≫
        (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
              ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom) =
      (Limits.prod.braiding (inverseImageModuleSheaf f F) (inverseImageModuleSheaf f G)).hom ≫
        pullbackTensorBottomPairing f G F := by
  refine pairing_ext
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (fun V x s ↦ ?_)
  refine Eq.trans (pairingApp_comp _ _ V x s) ?_
  refine Eq.trans (congrArg ((Sheaf.sectionsFunctor X.J V).map
      ((Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
          (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
            ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom)))
    (pairingApp_pullbackTensorBottom f F G V x s)) ?_
  refine Eq.trans (tensorSheafBraiding_tensorSectionsAt X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property V
    ((f.pullbackModules).obj F) ((f.pullbackModules).obj G) _ _) ?_
  refine Eq.trans ?_ ((Sheaf.sectionsFunctor X.J V).map_comp_apply _ _ _).symm
  refine Eq.trans ?_
    (congrArg ((Sheaf.sectionsFunctor X.J V).map (pullbackTensorBottomPairing f G F))
      (map_prodBraiding_prodObjMk (Sheaf.sectionsFunctor X.J V) x s)).symm
  exact (pairingApp_pullbackTensorBottom f G F V s x).symm

/-- The product comparison of `f⁻¹` commutes with the braiding of a binary product. This is
`CategoryTheory.Limits.map_braiding_hom_comp_prodComparison`, read at the two module sheaves. -/
lemma prodComparison_comp_prodBraiding :
    Limits.prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
        (Limits.prod.braiding (inverseImageModuleSheaf f F)
          (inverseImageModuleSheaf f G)).hom =
      f.toToposHom.inverseImage.map
          (Limits.prod.braiding (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).hom ≫
        Limits.prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) :=
  (Limits.map_braiding_hom_comp_prodComparison f.toToposHom.inverseImage
    (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)
    (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)).symm

/-- **The braided bottom of the chain of Tag 03EL**: the braiding of the binary product followed
by the product comparison and the pairing of the opposite order. Both sides of the braiding
coherence reduce to the direct image of this one morphism, evaluated at
`pullbackTensorUnitProdSection`. -/
def pullbackTensorBraidedBottomHom :
    f.toToposHom.inverseImage.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ⟶
      Sheaf.moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj
          (pullbackTensorTarget f G F)) :=
  f.toToposHom.inverseImage.map
      (Limits.prod.braiding (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).hom ≫
    (Limits.prodComparison f.toToposHom.inverseImage
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ≫
      pullbackTensorBottomPairing f G F)

/-- The bottom of the chain of Tag 03EL followed by the braiding of the target is
`pullbackTensorBraidedBottomHom`. -/
lemma pullbackTensorBottom_comp_braiding :
    (Limits.prodComparison f.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
          pullbackTensorBottomPairing f F G) ≫
        (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
              ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom) =
      pullbackTensorBraidedBottomHom f F G :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ Limits.prodComparison f.toToposHom.inverseImage
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫ z)
        (pullbackTensorBottomPairing_comp_braiding f F G)).trans
      (((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ pullbackTensorBottomPairing f G F)
            (prodComparison_comp_prodBraiding f F G))).trans
        (Category.assoc _ _ _)))

/-- The transpose of the comparison of Stacks 03EL on the unit image of a pure tensor. -/
lemma pullbackTensorTransposedComparison_val_app_unit_tmul (U : Y.Cᵒᵖ)
    (a : F.val.obj U) (r : G.val.obj U) :
    (pullbackTensorTransposedComparison f F G).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf Y.J Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (𝟙 _)).unit.app
            (F.val ⊗ G.val)).app U (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.pushforward.map
          (Limits.prodComparison f.toToposHom.inverseImage
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
            pullbackTensorBottomPairing f F G))
        (pullbackTensorUnitProdSection f F G U a r) :=
  pullbackTensorStep2_symm_step3_symm_val_app_unit_tmul f F G
    (pullbackTensorTarget f F G)
    ((pullbackTensorStep4 f F G (pullbackTensorTarget f F G)).symm
      (pullbackTensorBottomHom f F G)) U a r

/-- The left-hand side of the braiding coherence, transposed and read on a pure tensor. -/
lemma pullbackTensorTransposedComparison_comp_braiding_val_app (U : Y.Cᵒᵖ)
    (a : F.val.obj U) (r : G.val.obj U) :
    (pullbackTensorTransposedComparison f F G ≫
          (pushforwardModules f).map
            (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
              ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf Y.J Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (𝟙 _)).unit.app
            (F.val ⊗ G.val)).app U (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.pushforward.map (pullbackTensorBraidedBottomHom f F G))
        (pullbackTensorUnitProdSection f F G U a r) := by
  refine Eq.trans (congrArg ((Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).map
            (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
              ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom))))
    (pullbackTensorTransposedComparison_val_app_unit_tmul f F G U a r)) ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
      (pullbackTensorUnitProdSection f F G U a r))
    (f.toToposHom.pushforward.map_comp _ _).symm) ?_
  exact congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map m) (pullbackTensorUnitProdSection f F G U a r))
    (pullbackTensorBottom_comp_braiding f F G)

/-- The right-hand side of the braiding coherence, transposed and read on a pure tensor. -/
lemma braiding_comp_pullbackTensorTransposedComparison_val_app (U : Y.Cᵒᵖ)
    (a : F.val.obj U) (r : G.val.obj U) :
    ((tensorSheafBraiding Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property F G).hom ≫
          pullbackTensorTransposedComparison f G F).val.app U
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf Y.J Y.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) (𝟙 _)).unit.app
            (F.val ⊗ G.val)).app U (a ⊗ₜ[(ringPresheaf Y.O.obj).obj U] r)) =
      (Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.pushforward.map (pullbackTensorBraidedBottomHom f F G))
        (pullbackTensorUnitProdSection f F G U a r) := by
  have hunit : (Limits.prod.braiding
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).hom ≫
        f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) =
      f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) ≫
        f.toToposHom.pushforward.map
          (f.toToposHom.inverseImage.map
            (Limits.prod.braiding (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
              (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).hom) :=
    f.toToposHom.adj.unit.naturality
      (Limits.prod.braiding (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)).hom
  refine Eq.trans (congrArg ((pullbackTensorTransposedComparison f G F).val.app U)
    (tensorSheafBraiding_tensorSectionsAt Y.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property U F G a r)) ?_
  refine Eq.trans (pullbackTensorTransposedComparison_val_app_unit_tmul f G F U r a) ?_
  refine Eq.trans (congrArg ((Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map
        (Limits.prodComparison f.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ≫
          pullbackTensorBottomPairing f G F)))
    (congrArg ((Sheaf.sectionsFunctor Y.J U).map
        (f.toToposHom.adj.unit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⨯
            Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)))
      (sectionsFunctor_map_prodBraiding_prodObjMk F G U a r).symm)) ?_
  refine Eq.trans (congrArg ((Sheaf.sectionsFunctor Y.J U).map
      (f.toToposHom.pushforward.map
        (Limits.prodComparison f.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ≫
          pullbackTensorBottomPairing f G F)))
    ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ _).symm) ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
      (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
        (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) a r))
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫
      f.toToposHom.pushforward.map
        (Limits.prodComparison f.toToposHom.inverseImage
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G)
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F) ≫
          pullbackTensorBottomPairing f G F)) hunit))) ?_
  refine Eq.trans (congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
      (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w'} Y.J U)
        (A := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F)
        (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G) a r))
    (Category.assoc _ _ _)) ?_
  refine Eq.trans ((Sheaf.sectionsFunctor Y.J U).map_comp_apply _ _ _) ?_
  exact congrArg (fun m ↦ (Sheaf.sectionsFunctor Y.J U).map m
      (pullbackTensorUnitProdSection f F G U a r))
    (f.toToposHom.pushforward.map_comp _ _).symm

/-- **The comparison of Stacks 03EL commutes with the braiding of the tensor product sheaf.**

For a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` in the four-field sense of
`Stacks.Sheaves.RingedToposModules.RingedToposHom` and sheaves of `O_D`-modules `F` and `G`, the
comparison `f^*(F ⊗_{O_D} G) ⟶ f^*F ⊗_{O_C} f^*G` followed by the braiding upstairs is the
pullback of the braiding downstairs followed by the comparison at `(G, F)`.

No presentation of the morphism of topoi by a functor of sites is used, and no coherence of the
comparison beyond its own universal property: the proof transposes along the adjunction of
Stacks 03D7 and compares the two sides on the unit image of a pure tensor, where both are the
pure tensor of the two pullback images in the opposite order. -/
theorem pullbackTensorIso_hom_app_comp_braiding :
    (pullbackTensorIso f).hom.app (F, G) ≫
        (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom =
      (f.pullbackModules).map
          (tensorSheafBraiding Y.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property F G).hom ≫
        (pullbackTensorIso f).hom.app (G, F) := by
  refine (pullbackTensorStep1 f F G (pullbackTensorTarget f G F)).injective ?_
  refine Eq.trans ((pullbackAdjPushforwardModules f).homEquiv_naturality_right
    ((pullbackTensorIso f).hom.app (F, G))
    (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom) ?_
  refine Eq.trans ?_ ((pullbackAdjPushforwardModules f).homEquiv_naturality_left
    (tensorSheafBraiding Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property F G).hom
    ((pullbackTensorIso f).hom.app (G, F))).symm
  refine Eq.trans (congrArg (fun z ↦ z ≫ (pushforwardModules f).map
      (tensorSheafBraiding X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        ((f.pullbackModules).obj F) ((f.pullbackModules).obj G)).hom)
    (pullbackTensorStep1_pullbackTensorIso_hom_app f F G)) ?_
  refine Eq.trans ?_ (congrArg (fun z ↦
      (tensorSheafBraiding Y.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property F G).hom ≫ z)
    (pullbackTensorStep1_pullbackTensorIso_hom_app f G F).symm)
  exact tensorSheaf_hom_ext (fun U a r ↦
    (pullbackTensorTransposedComparison_comp_braiding_val_app f F G U a r).trans
      (braiding_comp_pullbackTensorTransposedComparison_val_app f F G U a r).symm)

end Braiding

end Stacks.SheafOfModules

end
