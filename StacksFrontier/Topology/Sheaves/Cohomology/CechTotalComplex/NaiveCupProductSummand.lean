module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductOnSectionsAtAPoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProduct

/-!
# The naive cup product on a summand, and the Čech coefficient pairing

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `𝒦^•`, `ℳ^•` be complexes
of `𝒪_X`-modules.  The naive cup product of Stacks Tag 0FP3,

`Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•) ⟶ f_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)`,

is defined as an adjoint transpose, so nothing about it is visible on a summand until the
transpose is undone.  This file undoes it: on the summand indexed by `(a, b)` of total degree
`n` the naive cup product is the *degreewise* naive cup product
`Stacks.RingedSpace.pushforwardTensorMap` of `𝒦^a` and `ℳ^b`, followed by the pushforward of the
inclusion of the `(a, b)` summand of the target.  That is `ι_naiveCupProduct`, and it is what
reduces the complex-level cup product of Tag 0FP3 to the sheaf-level map whose effect on local
sections is known.

Composing it with that effect gives the second result, which is the point of the file: at the
coefficient point `π : S ⟶ ({*}, Γ(S, 𝒪_S))` of Stacks 01BH, the naive cup product of Tag 0FP3
read on global sections at the sheafification-unit image of a pure tensor is the degreewise
pairing `μ` of the Čech coefficient pairing
`Stacks.Cech.SheafTensorPairing.sheafTensorComplexPairing`.  That `μ` is exactly what the signed
Alexander--Whitney formula `Stacks.Cech.LinearCupProduct.cechCupProduct_ι` of Stacks 07MB feeds
on, and `Stacks.Cech.ModuleCupProduct.cechCupProductA_eq` identifies the cup product it computes
with `Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor`, the left-hand column of the
diagram of Stacks Tag 0FKV.  So the two results below are the join between Tag 0FP3 and that
column.

## Main results

* `Stacks.Cohomology.NaiveCupProductSummand.ι_naiveCupProduct` — **the naive cup product of
  Stacks Tag 0FP3 on the summand indexed by `(a, b)`** is the degreewise naive cup product
  there.
* `Stacks.Cohomology.NaiveCupProductSummand.naiveCupProduct_sheafTensorComplexPairing` — **the
  naive cup product at the coefficient point, on global sections, is the degreewise pairing of
  the Čech coefficient pairing of Tag 0FKV.**

## Implementation notes

*Why the abstract paste.*  Both sides of `ι_naiveCupProduct` are morphisms into a pushforward,
so the statement is proved by comparing adjoint transposes; and the transposes are compared by
four identities, each with its own spelling of the structure sheaf.  `transpose_paste` is that
comparison with every category, functor, object and morphism a variable, so the reassociations
inside it are ordinary rewrites; each of the four identities is then supplied as a finished
equation, proved in a declaration of its own.  Written as one tactic proof instead, the
rewrites fail: `rw` re-checks the goal at `implicit` transparency and reports that it did not
find a pattern the goal visibly contains, because `structureSheafRing S` and
`Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf` are the same sheaf of rings only by `rfl`.

*Why the four identities are four declarations.*  Each crosses exactly one spelling boundary:
`counit_square_f` reads the counit square of Tag 0FP3 in a single degree;
`ι_counitPair` is Mathlib's summand description of a map of total complexes, stated at the
spelling in which the instances of the tensor product are found — stated instead with the
functors left to unification, instance search fails to find `Preadditive` for the category of
modules written over `Stacks.RingedSpace.structureRingSheaf`;
`comparisonAppIso_comp_pair` crosses between the product-category and the curried spelling of
the tensor product; and `pullback_pushforwardTensorMap_counit` undoes the transpose defining the
degreewise naive cup product.  Combining any two of them into one declaration is what exhausts
the heartbeat budget in this part of the tree.

*What is not needed.*  No boundedness, flatness or quasi-coherence hypothesis, and no
invertibility of any edge: the counit square of Tag 0FP3 and the summand description of the
Stacks 01CD comparison of total tensor complexes hold in general.

*The tag.*  Neither result is a clause of the statement of Tag 0FKV, whose diagram is a square
in `D(Γ(S, 𝒪_S))`, nor of Tag 0FP3, whose statement is the square of Tag 0FP3 in `D(𝒪_Y)`.
Both are steps of the proof of Tag 0FKV — the identification of the cup product of Tag 0FP3
with the cup product on Čech complexes — so neither carries a tag.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped CategoryTheory.Prod TensorProduct

universe u

namespace Stacks.Cohomology.NaiveCupProductSummand

open _root_.PresheafOfModules CategoryTheory.Sheaf RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf (coefficientPoint)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsFunctor)
open Stacks.Cech.SheafTensorPairing (sheafTensorComplexPairing)
open Stacks.Cohomology.DerivedGlobalCupProduct (toCoeffPoint)
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedSectionsOnAPoint (onePointRingedSpace)
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.PullbackTensorComposition (tensorSheaf_map_pair)
open Stacks.RingedSpace

attribute [local instance] Stacks.RingedSpace.coeffCommRing
  Stacks.Cohomology.DerivedPullbackTensor.modulePullback_preservesAntidiagonalCoproducts

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback StacksDraft.KFlat.modulePushforward

/-! ### The comparison of adjoint transposes, in the abstract -/

/-- **Two morphisms into a pushforward agree when their transposes paste.**  For an adjunction
`P ⊣ Q`, the composite `u ≫ θ` is `p ≫ Q(ι)` as soon as the transpose of `θ` factors as `δ ≫ β`,
the transport of `u` along `δ` factors as `c ≫ ι'`, the transport of `ι'` along `β` factors as
`s ≫ ι`, and `c ≫ s` is the transpose of `p`.

Every category, functor, object and morphism is a variable, which is what makes the four
reassociations below ordinary rewrites; at the application site the only work is matching the
variables, which is a single conversion check. -/
private lemma transpose_paste {C D : Type*} [Category C] [Category D]
    {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q)
    {A A' : C} {B B' E W : D}
    (u : A ⟶ A') (θ : A' ⟶ Q.obj B') (p : A ⟶ Q.obj B) (ι : B ⟶ B')
    (δ : P.obj A' ⟶ E) (β : E ⟶ B') (c : P.obj A ⟶ W) (ι' : W ⟶ E) (s : W ⟶ B)
    (γ : P.obj A ⟶ B)
    (ha : P.map θ ≫ adj.counit.app B' = δ ≫ β)
    (hb : P.map u ≫ δ = c ≫ ι')
    (hc : ι' ≫ β = s ≫ ι)
    (hd : c ≫ s = γ)
    (he : P.map p ≫ adj.counit.app B = γ) :
    u ≫ θ = p ≫ Q.map ι := by
  apply (adj.homEquiv A B').symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, P.map_comp, P.map_comp,
    Category.assoc, Category.assoc, ha, ← Category.assoc, hb, Category.assoc, hc,
    ← Category.assoc, hd, adj.counit_naturality, ← Category.assoc, he]

/-- **The transpose of an adjoint transpose is what it was.**  This is
`CategoryTheory.Adjunction.homEquiv_counit` read through `Equiv.symm_apply_apply`, with every
object a variable. -/
private lemma map_homEquiv_counit {C D : Type*} [Category C] [Category D]
    {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q) {A : C} {B : D} (t : P.obj A ⟶ B) :
    P.map (adj.homEquiv A B t) ≫ adj.counit.app B = t :=
  (Adjunction.eq_unit_comp_map_iff adj t (adj.homEquiv A B t)).mp
    (Adjunction.homEquiv_unit adj A B t)

/-! ### The four identities -/

section Degreewise

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (F G : SheafOfModules.{u} (structureRingSheaf X))

/-- **The adjoint transpose of the degreewise naive cup product** is the comparison of Stacks
01CD followed by the counit in each tensor factor, which is how it was defined. -/
private lemma pullback_pushforwardTensorMap_counit :
    (pullbackFunctor f).map (pushforwardTensorMap f F G) ≫
        (pullbackAdjunction f).counit.app ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj (F, G)) =
      comparison f ((pushforwardFunctor f).obj F) ((pushforwardFunctor f).obj G) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf)).map (counitPair f F G) :=
  map_homEquiv_counit (pullbackAdjunction f)
    (comparison f ((pushforwardFunctor f).obj F) ((pushforwardFunctor f).obj G) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf)).map (counitPair f F G))

/-- **The degreewise comparison of Stacks 01CD followed by the pair of counits**, with the pair
written through the curried tensor product: that is the spelling in which a summand of a total
tensor complex reads, while the transpose of the degreewise naive cup product is written at the
product-category spelling. -/
private lemma comparisonAppIso_comp_pair :
    (comparisonAppIso f ((pushforwardFunctor f).obj F) ((pushforwardFunctor f).obj G)).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
              ((pullbackAdjunction f).counit.app F)).app
            ((pullbackFunctor f).obj ((pushforwardFunctor f).obj G)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj F).map
            ((pullbackAdjunction f).counit.app G)) =
      comparison f ((pushforwardFunctor f).obj F) ((pushforwardFunctor f).obj G) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf)).map (counitPair f F G) :=
  whisker_eq _
    (tensorSheaf_map_pair ((pullbackAdjunction f).counit.app F)
      ((pullbackAdjunction f).counit.app G)).symm

end Degreewise

section Complexes

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)

/-- **The counit square of Stacks Tag 0FP3**, with the two factors of its right-hand side named:
the comparison of total tensor complexes of Stacks 01CD as an isomorphism of complexes, and the
tensor product of the two counits as a map of total complexes.  This is
`Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pullbackComplex_naiveCupProduct_counit` with
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map` applied to its second factor. -/
private lemma counit_square :
    (pullbackComplex f).map (naiveCupProduct f K M) ≫
        (complexAdjunction f).counit.app
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
            (K, M)) =
      (pullbackTensorComplexIsoOfIsIso f ((pushforwardComplex f).obj K)
          ((pushforwardComplex f).obj M)).hom ≫
        HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
          ((complexAdjunction f).counit.app M)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) :=
  (pullbackComplex_naiveCupProduct_counit f K M).trans
    (whisker_eq _
      (totalComplexPair_map (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
        ((complexAdjunction f).counit.app K) ((complexAdjunction f).counit.app M)))

/-- The counit square of Stacks Tag 0FP3 in a single degree. -/
private lemma counit_square_f (n : ℤ) :
    (pullbackFunctor f).map ((naiveCupProduct f K M).f n) ≫
        (pullbackAdjunction f).counit.app
          (((totalComplexPair
              (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).obj
            (K, M)).X n) =
      (pullbackTensorComplexIsoOfIsIso f ((pushforwardComplex f).obj K)
          ((pushforwardComplex f).obj M)).hom.f n ≫
        (HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
          ((complexAdjunction f).counit.app M)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
            (ComplexShape.up ℤ)).f n :=
  HomologicalComplex.congr_hom (counit_square f K M) n

/-- **The tensor product of the two counits on the summand indexed by `(a, b)`**: it is the pair
of counits in degrees `a` and `b`, followed by the inclusion of the `(a, b)` summand of the
target.  This is `HomologicalComplex.ι_mapBifunctorMap`, stated at the spelling of the category
of modules that carries the instances of the tensor product. -/
private lemma ι_counitPair (a b n : ℤ) (h : a + b = n) :
    HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj ((pushforwardComplex f).obj K))
          ((pullbackComplex f).obj ((pushforwardComplex f).obj M))
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
            (ComplexShape.up ℤ) a b n h ≫
        (HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
          ((complexAdjunction f).counit.app M)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
            (ComplexShape.up ℤ)).f n =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
              (((complexAdjunction f).counit.app K).f a)).app
            (((pullbackComplex f).obj ((pushforwardComplex f).obj M)).X b) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (K.X a)).map
            (((complexAdjunction f).counit.app M).f b)) ≫
        HomologicalComplex.ιMapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
            (ComplexShape.up ℤ) a b n h :=
  (HomologicalComplex.ι_mapBifunctorMap _ _ _ _ a b n h).trans (Category.assoc _ _ _).symm

/-! ### The naive cup product on a summand -/

/-- **The naive cup product of Stacks Tag 0FP3 on the summand indexed by `(a, b)`.**  On the
summand `f_*𝒦^a ⊗_{𝒪_Y} f_*ℳ^b` of total degree `n = a + b`, the naive cup product

`Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•) ⟶ f_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)`

is the degreewise naive cup product `f_*𝒦^a ⊗_{𝒪_Y} f_*ℳ^b ⟶ f_*(𝒦^a ⊗_{𝒪_X} ℳ^b)` of
`Stacks.RingedSpace.pushforwardTensorMap`, followed by the pushforward of the inclusion of the
`(a, b)` summand of `Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)`.

This is what makes the complex-level cup product of Tag 0FP3 readable on local sections: the
total-complex form cannot be, since `f_*` does not preserve the coproducts occurring in a total
degree, while the degreewise form is computed on sections by
`Stacks.RingedSpace.pushforwardTensorMap_unit_tmul`.

No boundedness, flatness or quasi-coherence hypothesis is needed, and no edge is required to
be invertible.  This is a step of the proof of Stacks Tag 0FKV, not a clause of its statement, so
it carries no tag. -/
theorem ι_naiveCupProduct (a b n : ℤ) (h : a + b = n) :
    HomologicalComplex.ιMapBifunctor ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
            (ComplexShape.up ℤ) a b n h ≫
        (naiveCupProduct f K M).f n =
      pushforwardTensorMap f (K.X a) (M.X b) ≫
        (StacksDraft.KFlat.modulePushforward f).map
          (HomologicalComplex.ιMapBifunctor K M
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
              (ComplexShape.up ℤ) a b n h) :=
  transpose_paste (pullbackAdjunction f) _ _ _ _
    ((pullbackTensorComplexIsoOfIsIso f ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M)).hom.f n)
    ((HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app K)
      ((complexAdjunction f).counit.app M)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ)).f n)
    ((comparisonAppIso f (((pushforwardComplex f).obj K).X a)
      (((pushforwardComplex f).obj M).X b)).hom)
    (HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj ((pushforwardComplex f).obj K))
      ((pullbackComplex f).obj ((pushforwardComplex f).obj M))
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
        (ComplexShape.up ℤ) a b n h)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
          ((pullbackAdjunction f).counit.app (K.X a))).app
        ((pullbackFunctor f).obj ((pushforwardFunctor f).obj (M.X b))) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (K.X a)).map
        ((pullbackAdjunction f).counit.app (M.X b)))
    (comparison f ((pushforwardFunctor f).obj (K.X a)) ((pushforwardFunctor f).obj (M.X b)) ≫
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf)).map (counitPair f (K.X a) (M.X b)))
    (counit_square_f f K M n)
    (ι_pullbackTensorComplexIsoOfIsIso_hom f ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M) a b n h)
    (ι_counitPair f K M a b n h)
    (comparisonAppIso_comp_pair f (K.X a) (M.X b))
    (pullback_pushforwardTensorMap_counit f (K.X a) (M.X b))

end Complexes

/-! ### The join with the Čech column of Tag 0FKV -/

/-- **The naive cup product of Stacks Tag 0FP3 at the coefficient point, on global sections, is
the Čech coefficient pairing of Stacks Tag 0FKV.**  For `π : S ⟶ ({*}, Γ(S, 𝒪_S))` the morphism
of Stacks 01BH and global sections `x` of `𝒦^a` and `y` of `ℳ^b`, the naive cup product carries
the sheafification-unit image of the pure tensor `x ⊗ y` on the summand indexed by `(a, b)` to
the value at `x ⊗ y` of the degreewise pairing `μ a b n` of
`Stacks.Cech.SheafTensorPairing.sheafTensorComplexPairing`.

That `μ` is what the signed Alexander--Whitney formula of Stacks 07MB,
`Stacks.Cech.LinearCupProduct.cechCupProduct_ι`, evaluates the Čech cup product to on a
homogeneous summand, and by `Stacks.Cech.ModuleCupProduct.cechCupProductA_eq` the Čech cup
product in question is `Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor`, the left-hand
column of the diagram of Tag 0FKV.  So this is the join between Tag 0FP3 and that column.

The two pure tensors are taken over the two different rings `Γ({*}, 𝒪_{\{*\}})` and
`Γ(S, 𝒪_S)`, with no map between them, which is why the statement is an equation between the
two *values* at one pair of global sections rather than between two maps out of one tensor
product; `Stacks.RingedSpace.pushforwardTensorMap_toCoeffPoint_top` is where that asymmetry is
resolved.

This is a step of the proof of Tag 0FKV and not a clause of its statement, so it carries no
tag. -/
theorem naiveCupProduct_sheafTensorComplexPairing (S : RingedSpace.{u, u})
    (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S) ℤ)
    (a b n : ℤ) (h : a + b = n)
    (x : ((pushforwardFunctor (toCoeffPoint S)).obj (K.X a)).val.obj (op ⊤))
    (y : ((pushforwardFunctor (toCoeffPoint S)).obj (M.X b)).val.obj (op ⊤)) :
    Hom.app ((naiveCupProduct (toCoeffPoint S) K M).f n).val (op ⊤)
        (Hom.app (HomologicalComplex.ιMapBifunctor
            ((pushforwardComplex (toCoeffPoint S)).obj K)
            ((pushforwardComplex (toCoeffPoint S)).obj M)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              (onePointRingedSpace ↥(baseRing S)).sheaf)
            (ComplexShape.up ℤ) a b n h).val (op ⊤)
          (Hom.app
            ((PresheafOfModules.sheafificationAdjunction
                  (R := structureRingSheaf (onePointRingedSpace ↥(baseRing S)))
                  (𝟙 (structureRingSheaf
                    (onePointRingedSpace ↥(baseRing S))).obj)).unit.app
              (PresheafOfModules.tensorObj
                (O := (onePointRingedSpace ↥(baseRing S)).presheaf)
                ((pushforwardFunctor (toCoeffPoint S)).obj (K.X a)).val
                ((pushforwardFunctor (toCoeffPoint S)).obj (M.X b)).val))
            (op ⊤) (x ⊗ₜ y))) =
      (((sheafTensorComplexPairing S.sheaf ⊤ K M).μ a b n h).app
        (op (Over.mk (𝟙 (⊤ : Opens S.carrier))))).hom (x ⊗ₜ y) :=
  (hom_congr_apply' (congrArg (fun z ↦ SheafOfModules.Hom.val z)
      (ι_naiveCupProduct (toCoeffPoint S) K M a b n h)) (op ⊤) _).trans
    (congrArg
      (fun z => Hom.app ((pushforwardFunctor (toCoeffPoint S)).map
        (HomologicalComplex.ιMapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ) a b n h)).val (op ⊤) z)
      (pushforwardTensorMap_toCoeffPoint_top S (K.X a) (M.X b) x y))

end Stacks.Cohomology.NaiveCupProductSummand

end
