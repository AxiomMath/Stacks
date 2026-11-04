module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge

/-!
# Pullback in de Rham cohomology is compatible with the cup product

For a commutative square `g' ≫ f = f' ≫ g` of schemes, Section 0FM1 of the Stacks project asserts
that the pullback maps `H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')` are compatible with the cup product. This
file proves it, for the cup product of Section 50.4 on the realization of de Rham cohomology by
derived global sections of modules.

## Main definitions

* `Stacks.DeRhamBaseChange.deRhamComparisonQ`: the canonical map
  `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` in `D(X, f⁻¹𝒪_S)`.
* `Stacks.DeRhamBaseChange.deRhamPullbackSquare`: the pullback of de Rham cohomology along a
  commutative square, on the module realization.

## Main results

* `Stacks.DeRhamBaseChange.deRhamComparisonQ_multiplicative`: the canonical map
  `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` carries the multiplication of `Ω^•_{X/S}` to the relative cup
  product of Tag 0B68 followed by `Rg₀_*` of the multiplication of `Ω^•_{X'/S'}`.
* `Stacks.DeRhamBaseChange.deRhamPullbackSquare_cup`: **`g'^*(ξ ∪ η) = g'^*ξ ∪ g'^*η`.**

## The argument

The pullback is the canonical map followed by the Leray identification `H^m(X, Rg₀_* -) =
H^m(X', -)` (the edge identity of the library). The cup product on `X` is the global cup product
of `(X, f⁻¹𝒪_S)` followed by the canonical map to the total tensor complex and the wedge product.
The relative cup product induces the cup product on cohomology through the Leray identification
(`Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_relativeCupProduct_cupPairing`), and the
canonical map is multiplicative by the complex-level statement of
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupProduct` and Tag 0FP3.

## References

* [Stacks Project, Section 0FM1](https://stacks.math.columbia.edu/tag/0FM1)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage AlgebraicGeometry.ProperSmoothDeRham
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens CategoryTheory.Prod
  Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)
open Stacks.Cohomology.DerivedRelativeCupProduct (relativeCupProduct)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (naiveCupProduct pushforwardComplex)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cupPairing cupProductOnSpace cohomologyModule)
open scoped TensorProduct

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.DeRhamBaseChange

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The canonical map `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}`** in `D(X, f⁻¹𝒪_S)`: the canonical map of de
Rham complexes followed by the comparison `g₀_* ⟶ Rg₀_*`. It induces the pullback on de Rham
cohomology. -/
def deRhamComparisonQ :
    DerivedCategory.Q.obj (deRhamComplexModules f) ⟶
      (derivedPushforward (inverseImageBaseMap g' f' f g w)).obj
        (DerivedCategory.Q.obj (deRhamComplexModules f')) :=
  DerivedCategory.Q.map (deRhamPushforwardModules g' f' f g w) ≫
    pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) (deRhamComplexModules f')

/-- **The canonical map `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` is multiplicative** in the derived
category: it carries the multiplication `Ω^•_{X/S} ⊗^𝐋 Ω^•_{X/S} ⟶ Tot(Ω^• ⊗ Ω^•) --∧--> Ω^•`
to the relative cup product of Tag 0B68 followed by `Rg₀_*` of the multiplication of
`Ω^•_{X'/S'}`. This is the complex-level statement
`Stacks.DeRhamBaseChange.deRhamWedge_comp_deRhamPushforwardInt` combined with Tag 0FP3. -/
theorem deRhamComparisonQ_multiplicative :
    (derivedToTensorNatTrans (inverseImageBase f)).app
          (deRhamComplexModules f, deRhamComplexModules f) ≫
        DerivedCategory.Q.map (deRhamWedge f) ≫ deRhamComparisonQ g' f' f g w =
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          (inverseImageBase f).sheaf)).map
          (deRhamComparisonQ g' f' f g w ×ₘ deRhamComparisonQ g' f' f g w) ≫
        relativeCupProduct (inverseImageBaseMap g' f' f g w)
          (DerivedCategory.Q.obj (deRhamComplexModules f'))
          (DerivedCategory.Q.obj (deRhamComplexModules f')) ≫
        (derivedPushforward (inverseImageBaseMap g' f' f g w)).map
          ((derivedToTensorNatTrans (inverseImageBase f')).app
              (deRhamComplexModules f', deRhamComplexModules f') ≫
            DerivedCategory.Q.map (deRhamWedge f')) := by
  have h0 :=
    Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.naiveCupProduct_relativeCupProduct
      (inverseImageBaseMap g' f' f g w) (deRhamComplexModules f') (deRhamComplexModules f')
  have h1 :=
    Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ_naturality
      (inverseImageBaseMap g' f' f g w) (deRhamWedge f')
  have h2 := (derivedToTensorNatTrans (inverseImageBase f)).naturality
    (deRhamPushforwardModules g' f' f g w ×ₘ deRhamPushforwardModules g' f' f g w)
  have hM := congrArg DerivedCategory.Q.map (deRhamWedge_comp_deRhamPushforwardInt g' f' f g w)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp] at hM
  simp only [Functor.comp_map, Functor.prod_map] at h2
  simp only [deRhamComparisonQ]
  rw [reassoc_of% hM, h1, ← reassoc_of% h2, reassoc_of% h0]
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc]
  rfl

/-- **The cup product on `H^*_{dR}(X/S)`, through the global cup product of `(X, f⁻¹𝒪_S)`**: it is
the cup product of Cohomology, Section 0FKU followed by `RΓ` of the canonical map to the total
tensor complex and of the wedge product. -/
theorem deRhamCohomologyCup_eq_cupPairing (i j : ℤ)
    (ξ : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) i)
    (η : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) j) :
    AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j ξ η =
      ((cupPairing (cupProductOnSpace (inverseImageBase f))
          (DerivedCategory.Q.obj (deRhamComplexModules f))
          (DerivedCategory.Q.obj (deRhamComplexModules f)) i j) ≫
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (inverseImageBase f))) (i + j)).map
          ((baseSections (inverseImageBase f)).map
            ((derivedToTensorNatTrans (inverseImageBase f)).app
              (deRhamComplexModules f, deRhamComplexModules f))) ≫
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (inverseImageBase f))) (i + j)).map
          ((baseSections (inverseImageBase f)).map
            (DerivedCategory.Q.map (deRhamWedge f)))).hom (ξ ⊗ₜ η) := by
  have e := AlgebraicGeometry.SheafOfModules.canonicalPairingModule_eq
    (AlgebraicGeometry.SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))) i j
  have e2 := AlgebraicGeometry.SheafOfModules.dgAction_regular_deRham
    (Scheme.Hom.deRhamAlgebras f)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
  exact congrArg (fun φ => φ.hom (ξ ⊗ₜ η)) (e.trans (congrArg
    (fun m => _ ≫ AlgebraicGeometry.SheafOfModules.cohomologyModuleMap (i + j) m) e2.symm))

/-- **The pullback `H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of a commutative square**
([Stacks, Tag 0FL6]), on the realization of de Rham cohomology by derived global sections of
modules, in which the cup product of Section 50.4 lives: the pullback of the abelian realization
read through the comparison of the two realizations ([Stacks, Tag 01F1]). -/
def deRhamPullbackSquare (m : ℤ) :
    AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m →+
      AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f')) m :=
  ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m).inv ≫
    Scheme.Hom.deRhamCohomologyPullback g' f f' g w m ≫
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f')
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
        m).hom).hom

/-- **The pullback is the canonical map followed by the Leray identification**: on `H^m`, the
canonical map `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` followed by `H^m(X, Rg₀_* -) = H^m(X', -)`. This is
the edge identity of the library. -/
theorem deRhamPullbackSquare_eq_lerayMap (m : ℤ)
    (z : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m) :
    deRhamPullbackSquare g' f' f g w m z =
      Stacks.Cohomology.LerayCupPairing.lerayMap (inverseImageBaseMap g' f' f g w)
        (DerivedCategory.Q.obj (deRhamComplexModules f')) m
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) m).map
          ((baseSections (inverseImageBase f)).map (deRhamComparisonQ g' f' f g w))).hom z) := by
  have h := deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback g' f' f g w m
    ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
        m).inv.hom z)
  rw [Iso.inv_hom_id_apply] at h
  exact h

/-- `H^n(RΓ(-))` of a composite of three morphisms, on an element. -/
theorem homologyMap_baseSections_comp₃_apply (Z : RingedSpace.{u, u}) (n : ℤ)
    {K L M N : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))}
    (a : K ⟶ L) (b : L ⟶ M) (c : M ⟶ N) (t : cohomologyModule K n) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Z)) n).map
        ((baseSections Z).map (a ≫ b ≫ c))).hom t =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Z)) n).map
        ((baseSections Z).map c)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Z)) n).map
          ((baseSections Z).map b)).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Z)) n).map
            ((baseSections Z).map a)).hom t)) := by
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The multiplicativity of the canonical map `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}`, read on
cohomology. -/
theorem homologyMap_deRhamComparisonQ_multiplicative (n : ℤ)
    (t : cohomologyModule (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (inverseImageBase f).sheaf).obj (DerivedCategory.Q.obj (deRhamComplexModules f))).obj
        (DerivedCategory.Q.obj (deRhamComplexModules f))) n) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) n).map
        ((baseSections (inverseImageBase f)).map (deRhamComparisonQ g' f' f g w))).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) n).map
        ((baseSections (inverseImageBase f)).map (DerivedCategory.Q.map (deRhamWedge f)))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) n).map
          ((baseSections (inverseImageBase f)).map
            ((derivedToTensorNatTrans (inverseImageBase f)).app
              (deRhamComplexModules f, deRhamComplexModules f)))).hom t)) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) n).map
        ((baseSections (inverseImageBase f)).map
          ((derivedPushforward (inverseImageBaseMap g' f' f g w)).map
            ((derivedToTensorNatTrans (inverseImageBase f')).app
                (deRhamComplexModules f', deRhamComplexModules f') ≫
              DerivedCategory.Q.map (deRhamWedge f'))))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) n).map
          ((baseSections (inverseImageBase f)).map
            (relativeCupProduct (inverseImageBaseMap g' f' f g w)
              (DerivedCategory.Q.obj (deRhamComplexModules f'))
              (DerivedCategory.Q.obj (deRhamComplexModules f'))))).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) n).map
            ((baseSections (inverseImageBase f)).map
              ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
                (inverseImageBase f).sheaf)).map
                (deRhamComparisonQ g' f' f g w ×ₘ deRhamComparisonQ g' f' f g w)))).hom t)) :=
  (homologyMap_baseSections_comp₃_apply _ n _ _ _ t).symm.trans
    ((congrArg (fun φ => ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (inverseImageBase f))) n).map
        ((baseSections (inverseImageBase f)).map φ)).hom t)
      (deRhamComparisonQ_multiplicative g' f' f g w)).trans
      (homologyMap_baseSections_comp₃_apply _ n _ _ _ t))

/-- The pullback of a cup product, through the canonical map and the relative cup product. -/
theorem deRhamPullbackSquare_cup_eq (i j : ℤ)
    (ξ : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) i)
    (η : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) j) :
    deRhamPullbackSquare g' f' f g w (i + j)
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j ξ η) =
      Stacks.Cohomology.LerayCupPairing.lerayMap (inverseImageBaseMap g' f' f g w)
        (DerivedCategory.Q.obj (deRhamComplexModules f')) (i + j)
        (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (inverseImageBase f))) (i + j)).map
        ((baseSections (inverseImageBase f)).map
          ((derivedPushforward (inverseImageBaseMap g' f' f g w)).map
            ((derivedToTensorNatTrans (inverseImageBase f')).app
                (deRhamComplexModules f', deRhamComplexModules f') ≫
              DerivedCategory.Q.map (deRhamWedge f'))))).hom
        (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (inverseImageBase f))) (i + j)).map
          ((baseSections (inverseImageBase f)).map
            (relativeCupProduct (inverseImageBaseMap g' f' f g w)
              (DerivedCategory.Q.obj (deRhamComplexModules f'))
              (DerivedCategory.Q.obj (deRhamComplexModules f'))))).hom
          ((cupPairing (cupProductOnSpace (inverseImageBase f)) _ _ i j).hom
            (((DerivedCategory.homologyFunctor
                (ModuleCat.{u} (baseRing (inverseImageBase f))) i).map
              ((baseSections (inverseImageBase f)).map (deRhamComparisonQ g' f' f g w))).hom ξ ⊗ₜ
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (inverseImageBase f))) j).map
              ((baseSections (inverseImageBase f)).map
                (deRhamComparisonQ g' f' f g w))).hom η)))) := by
  refine (deRhamPullbackSquare_eq_lerayMap g' f' f g w (i + j) _).trans (congrArg _ ?_)
  refine (congrArg _ (deRhamCohomologyCup_eq_cupPairing f i j ξ η)).trans ?_
  refine (homologyMap_deRhamComparisonQ_multiplicative g' f' f g w (i + j) _).trans (congrArg _ ?_)
  exact congrArg _ (Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_naturality_apply _
      (deRhamComparisonQ g' f' f g w) (deRhamComparisonQ g' f' f g w) i j ξ η).symm

/-- `H^n(RΓ(-))` of a composite of two morphisms, on an element. -/
theorem homologyMap_baseSections_comp_apply (Z : RingedSpace.{u, u}) (n : ℤ)
    {K L M : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Z))}
    (a : K ⟶ L) (b : L ⟶ M) (t : cohomologyModule K n) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Z)) n).map
        ((baseSections Z).map (a ≫ b))).hom t =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Z)) n).map
        ((baseSections Z).map b)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Z)) n).map
          ((baseSections Z).map a)).hom t) := by
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The cup product of two pulled-back classes, through the Leray identification. -/
theorem deRhamCohomologyCup_deRhamPullbackSquare (i j : ℤ)
    (ξ : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) i)
    (η : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) j) :
    AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j
        (deRhamPullbackSquare g' f' f g w i ξ) (deRhamPullbackSquare g' f' f g w j η) =
      ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (inverseImageBase f'))) (i + j)).map
        ((baseSections (inverseImageBase f')).map
          ((derivedToTensorNatTrans (inverseImageBase f')).app
              (deRhamComplexModules f', deRhamComplexModules f') ≫
            DerivedCategory.Q.map (deRhamWedge f')))).hom
        ((cupPairing (cupProductOnSpace (inverseImageBase f')) _ _ i j).hom
          (Stacks.Cohomology.LerayCupPairing.lerayMap (inverseImageBaseMap g' f' f g w)
              (DerivedCategory.Q.obj (deRhamComplexModules f')) i
              (((DerivedCategory.homologyFunctor
                  (ModuleCat.{u} (baseRing (inverseImageBase f))) i).map
                ((baseSections (inverseImageBase f)).map (deRhamComparisonQ g' f' f g w))).hom ξ) ⊗ₜ
            Stacks.Cohomology.LerayCupPairing.lerayMap (inverseImageBaseMap g' f' f g w)
              (DerivedCategory.Q.obj (deRhamComplexModules f')) j
              (((DerivedCategory.homologyFunctor
                  (ModuleCat.{u} (baseRing (inverseImageBase f))) j).map
                ((baseSections (inverseImageBase f)).map
                  (deRhamComparisonQ g' f' f g w))).hom η))) := by
  refine (congrArg₂ (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j)
    (deRhamPullbackSquare_eq_lerayMap g' f' f g w i ξ)
    (deRhamPullbackSquare_eq_lerayMap g' f' f g w j η)).trans ?_
  refine (deRhamCohomologyCup_eq_cupPairing f' i j _ _).trans ?_
  exact (homologyMap_baseSections_comp_apply _ (i + j) _ _ _).symm

/-- **Pullback in de Rham cohomology is compatible with the cup product** (Stacks, Section 0FM1):
for a commutative square `g' ≫ f = f' ≫ g` of schemes, `g'^*(ξ ∪ η) = g'^*ξ ∪ g'^*η` for
`ξ ∈ H^i_{dR}(X/S)` and `η ∈ H^j_{dR}(X/S)`.

The proof is the source's: the canonical map `Ω^•_{X/S} ⟶ Rg₀_*Ω^•_{X'/S'}` is multiplicative
(`Stacks.DeRhamBaseChange.deRhamComparisonQ_multiplicative`, from the multiplicativity of
pullback of differential forms and Tag 0FP3), and the relative cup product induces the cup
product on cohomology through the Leray identification. -/
theorem deRhamPullbackSquare_cup (i j : ℤ)
    (ξ : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) i)
    (η : AlgebraicGeometry.SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) j) :
    deRhamPullbackSquare g' f' f g w (i + j)
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j ξ η) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j
        (deRhamPullbackSquare g' f' f g w i ξ) (deRhamPullbackSquare g' f' f g w j η) := by
  refine (deRhamPullbackSquare_cup_eq g' f' f g w i j ξ η).trans ?_
  refine (Stacks.Cohomology.LerayCupPairing.lerayMap_naturality (inverseImageBaseMap g' f' f g w)
    ((derivedToTensorNatTrans (inverseImageBase f')).app
        (deRhamComplexModules f', deRhamComplexModules f') ≫
      DerivedCategory.Q.map (deRhamWedge f')) (i + j) _).trans ?_
  refine (congrArg _
    (Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_relativeCupProduct_cupPairing
      (inverseImageBaseMap g' f' f g w) (DerivedCategory.Q.obj (deRhamComplexModules f'))
      (DerivedCategory.Q.obj (deRhamComplexModules f')) i j _ _)).trans ?_
  exact (deRhamCohomologyCup_deRhamPullbackSquare g' f' f g w i j ξ η).symm

end Stacks.DeRhamBaseChange
