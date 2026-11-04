module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AugmentationModelBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquare

/-!
# The left-hand column of [Stacks, Tag 0FKV] along the augmentation of [Stacks, Tag 07M9]

Let `(S, 𝒪_S)` be a ringed space, put `A = Γ(S, 𝒪_S)`, let `𝒰 : S = ⋃ U i` be an open covering
and let `𝒦^•`, `ℳ^•` be bounded below complexes of `𝒪_S`-modules.  The left-hand column of the
diagram of [Stacks, Tag 0FKV] is the Čech cup product of [Stacks, Tag 07MB] followed by the
comparison of [Stacks, Tag 08BN] into `RΓ(S, -)`; the final paragraph of the source's proof
precomposes it with the augmentation of [Stacks, Tag 07M9] in both tensor factors and identifies
the result with the corresponding column of the diagram displayed just before the tag, the one
whose top left corner is `Γ(S, 𝒦^•) ⊗^𝐋_A Γ(S, ℳ^•)`.

This file proves that identification from the bottom edge upwards, as far as the Čech cup
product: the comparison of Tag 08BN precomposed with the augmentation is the unit
`Γ(S, 𝒯^•) ⟶ RΓ(S, 𝒯^•)`, and pasting the augmentation square
`Stacks.Cech.LinearCupProduct.naiveCupProduct_cechCupProduct` on top of it turns the Čech cup
product into the naive cup product of the sheaf-tensor pairing.  Its right-hand companion is
`Stacks.Cech.CupProductSquare.sectionsToTotalCechDerived_comp_cechRightLeg`.

## Main definitions

* `Stacks.Cech.CupProductSquare.cechToBaseSectionsA`: **the bottom edge of Tag 0FKV's square
  with its source spelled by `Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA`**, the total
  Čech complex the Čech cup product and the generic augmentation are built on.

## Main results

* `Stacks.Cech.CupProductSquare.sectionsToTotalCech_comp_cechToBaseSectionsA`: the pinning
  `sectionsToTotalCechDerived_comp_cechToBaseSections` at that spelling.
* `Stacks.Cech.CupProductSquare.cechAugmentationTotal_comp_cechToBaseSectionsA`: **the
  comparison of [Stacks, Tag 08BN] precomposed with the generic augmentation of
  [Stacks, Tag 07M9] is the unit `Γ(S, 𝒯^•) ⟶ RΓ(S, 𝒯^•)`**, conjugated by the identification
  `Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso` of the two presentations of
  `Γ(S, -)`.
* `Stacks.Cech.CupProductSquare.naiveCupProduct_comp_cechToBaseSectionsA`: **the Čech cup
  product followed by the comparison of [Stacks, Tag 08BN], precomposed with the augmentation in
  both tensor factors, is the naive cup product followed by the unit** -- the augmentation square
  pasted onto the previous statement.

## Use

These are two edge identifications of the proof of [Stacks, Tag 0FKV]
(`Stacks.Cech.CupProductSquare.cupProductSquareCommutes`).  They hold for an arbitrary bounded
below complex and an arbitrary covering; flasqueness enters only to cancel the augmentation,
which `isIso_sectionsToBaseSections_app_of_isFlasque` licenses.

## Implementation notes

*Where the crossing is paid, and why it has to be there.*  The Čech cup product of
[Stacks, Tag 07MB] and the generic augmentation of [Stacks, Tag 07M9] are built over the
coefficient ring `Stacks.Cech.ModuleCupProduct.CoeffRing 𝒪_S V` with the `CommRing` instance
`Stacks.Cech.ModuleCupProduct.sectionCommRing`; the comparison of [Stacks, Tag 08BN] is built
over `Stacks.Cohomology.CechSheaf.SectionRing (ringSheaf 𝒪_S) V` with the `Ring` instance carried
by `RingCat`.  The two agree by `Stacks.Cech.ModuleCupProduct.sectionCommRing_toRing`, by `rfl`,
and the two total Čech complexes agree by
`Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA_eq`, also by `rfl`.

That crossing is cheap where it is an object-level `isDefEq`: inside `DerivedCategory.Q.obj`,
hence inside a composition, hence in the type ascription of `cechToBaseSectionsA` below.  It is
**not** cheap inside `DerivedCategory.Q.map`, nor inside an equation between two derived-category
morphisms: there the unifier has to reconcile the `Abelian` and `HasDerivedCategory` instance
terms built over the two ring instances, and a bare

`DerivedCategory.Q.map (aug at one spelling) = DerivedCategory.Q.map (aug at the other) := rfl`

is a 200000-heartbeat `whnf` timeout, as are four further phrasings that
carry the crossing into the derived category in some other way.  So `cechToBaseSectionsA` pays it
once, in the one place where it is an object, and every statement after that is in a single
spelling and costs nothing.

*Why `exact` of fully variable lemmas.*  `rw` re-checks the goal at `implicit` transparency, at
which the two ring instances do not agree; the two composites below are therefore assembled by
`exact` of `comp_eq_of_map_eq` and `map_comp_paste`, which have every category, functor, object
and morphism a variable.  For the same reason the augmentation square is applied with its type
**computed by substitution** rather than ascribed: writing that type out means synthesizing the
`HasMapBifunctor` instances of the two total Čech complexes afresh at this base ring, which is
what `Stacks.Cech.ModuleCupProduct` records as having exhausted the heartbeat budget, and it does
so here too.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (coverObject sectionsTerminalFunctorIso)
open Stacks.Cohomology.GlobalKunneth (baseSections)
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor totalCechComplexFunctorA)
open Stacks.Cech.CupProduct (tensorModules)
open Stacks.Cech.LinearCupProduct (cechAugmentationTotal cechCupProduct naiveCupProduct
  cechAugmentationTotal_eq_sectionsToTotalCech naiveCupProduct_cechCupProduct)
open Stacks.Cech.SheafTensorPairing (cechCupProductSheafTensor sheafTensorComplexPairing)

universe u w uC vC

namespace Stacks.Cech.CupProductSquare

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

/-- Rewriting the first leg of a composite whose first factor is the image of a morphism under a
functor, with every category, functor, object and morphism a variable.  It is applied below by
`exact`, which is one `isDefEq`; the same rewriting performed by `rw` in the concrete statement
is rejected, because `rw` re-checks the goal at `implicit` transparency, at which the `CommRing`
instance the Čech cup product is built over and the `Ring` instance the comparison of
[Stacks, Tag 08BN] is built over do not agree. -/
private theorem comp_eq_of_map_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b c : C} {f : a ⟶ c} {p : a ⟶ b} {q : b ⟶ c} (hf : f = p ≫ q)
    {d : D} (g : F.obj c ⟶ d) (r : F.obj b ⟶ d) (hq : F.map q ≫ g = r) :
    F.map f ≫ g = F.map p ≫ r := by
  rw [hf, F.map_comp, Category.assoc, hq]

/-- Pasting a commuting square of `C` onto a factorization of one of its legs in `D`, with every
category, functor, object and morphism a variable; applied below by `exact`, for the same reason
as `comp_eq_of_map_eq`. -/
theorem map_comp_paste {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {a b c e : C} {d : D} {α : a ⟶ b} {β : b ⟶ c} {γ : a ⟶ e} {δ : e ⟶ c}
    (h : α ≫ β = γ ≫ δ) (g : F.obj c ⟶ d) (r : F.obj e ⟶ d) (hq : F.map δ ≫ g = r) :
    F.map α ≫ F.map β ≫ g = F.map γ ≫ r := by
  rw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, hq]

variable (S : RingedSpace.{u, u}) {I : Type u} (Ui : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)
  (T : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- **The bottom edge of [Stacks, Tag 0FKV]'s square, with its source spelled by
`Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA`.**

The morphism is `cechToBaseSections` at `T`, unchanged; only its source is written as `Q` of the
total Čech complex the Čech cup product of [Stacks, Tag 07MB] and the generic augmentation of
[Stacks, Tag 07M9] are built on, which is the same complex by
`Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA_eq`.  This is the one place in the
left-hand column where that crossing is paid; see the implementation notes of this file for why
it has to be paid here and not inside the derived category. -/
def cechToBaseSectionsA :
    DerivedCategory.Q.obj ((totalCechComplexFunctorA S.sheaf ⊤ Ui hU).obj T.1) ⟶
      (baseSections S).obj (DerivedCategory.Q.obj T.1) :=
  (cechToBaseSections S Ui hU).app T

/-- **The pinning of the comparison of [Stacks, Tag 08BN]** at the spelling of
`cechToBaseSectionsA`: after the module-valued augmentation of [Stacks, Tag 07M9] the comparison
is the unit `Γ(S, 𝒯^•) ⟶ RΓ(S, 𝒯^•)`.  This is
`sectionsToTotalCechDerived_comp_cechToBaseSections`, whose augmentation is
`DerivedCategory.Q` of the component of `Stacks.Cech.Linear.sectionsToTotalCech` by `rfl`. -/
theorem sectionsToTotalCech_comp_cechToBaseSectionsA :
    DerivedCategory.Q.map ((Stacks.Cech.Linear.sectionsToTotalCech S.carrier
          (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app T.1) ≫ cechToBaseSectionsA S Ui hU T =
      (sectionsToBaseSections S).app T :=
  sectionsToTotalCechDerived_comp_cechToBaseSections S Ui hU T

/-- **The comparison of [Stacks, Tag 08BN] precomposed with the generic augmentation of
[Stacks, Tag 07M9] is the unit `Γ(S, 𝒯^•) ⟶ RΓ(S, 𝒯^•)`**, conjugated by the identification
`Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso` of the two presentations of `Γ(S, -)`.

The generic augmentation `Stacks.Cech.LinearCupProduct.cechAugmentationTotal` is the one the
augmentation square `Stacks.Cech.LinearCupProduct.naiveCupProduct_cechCupProduct` is stated
with, so this is the form in which the bottom edge of Tag 0FKV's square meets the left-hand
column; the module-valued augmentation of the comparison of Tag 08BN is the same map by
`Stacks.Cech.LinearCupProduct.cechAugmentationTotal_eq_sectionsToTotalCech`, which is where the
conjugating isomorphism comes from and the only content of this proof. -/
theorem cechAugmentationTotal_comp_cechToBaseSectionsA :
    DerivedCategory.Q.map (cechAugmentationTotal (coverObject Ui hU) (CoeffRing.{u} S.sheaf ⊤)
          Over.mkIdTerminal ((sectionsComplexFunctor S.sheaf ⊤).obj T.1)) ≫
        cechToBaseSectionsA S Ui hU T =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (sectionsTerminalFunctorIso.{u, u, u} (R := ringSheaf.{u, u, u} S.sheaf) ⊤)
            (up ℤ)).app T.1).hom ≫
        (sectionsToBaseSections S).app T :=
  comp_eq_of_map_eq DerivedCategory.Q
    (cechAugmentationTotal_eq_sectionsToTotalCech S.sheaf ⊤ Ui hU T.1) _ _
    (sectionsToTotalCech_comp_cechToBaseSectionsA S Ui hU T)

end Stacks.Cech.CupProductSquare

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

/-- **The augmentation square of [Stacks, Tag 07M9] pasted onto any factorization of the
augmentation in the derived category.**

In the derived category of `R`-modules, if the augmentation of the target complex `M` followed by
some map `g` out of `Q(Tot(Č(W,M)))` is `r`, then the Čech cup product of [Stacks, Tag 07MB]
followed by `g`, precomposed with the augmentation in both tensor factors, is the naive cup
product followed by `r`.

This is `naiveCupProduct_cechCupProduct` pushed through `DerivedCategory.Q`, stated with the
target leg `g` and its factorization `hq` as hypotheses so that the *statement* stays generic.
That is deliberate: writing the same identity out at the instantiation of
[Stacks, Tag 0FKV] -- a ringed space, the cover in the slice over the whole space, the
sheaf-tensor pairing -- means synthesizing the `HasMapBifunctor` instances of the two total Čech
complexes afresh at the ring of global sections, and that alone exhausts the heartbeat budget
before the proof is reached, exactly as `Stacks.Cech.ModuleCupProduct` records for the cup
product itself.  Applied to
`Stacks.Cech.CupProductSquare.cechAugmentationTotal_comp_cechToBaseSectionsA` it gives the
left-hand half of the final paragraph of the proof of Tag 0FKV, with the type computed by
substitution.

It holds for every covering, every complex and every `g`. -/
theorem Q_map_cechCupProduct_comp_of_augmentation_comp {C : Type uC} [Category.{vC} C]
    [HasFiniteProducts C] {ι : Type w} [UnivLE.{w, u}] (W : ι → C) (R : Type u) [CommRing R]
    {Z : C} (hZ : IsTerminal Z) {K L M : CochainComplex (PresheafModules.{u} C R) ℤ}
    (D : ComplexPairing.{u} R K L M) {d : DerivedCategory (ModuleCat.{u} R)}
    (g : DerivedCategory.Q.obj ((totalCechComplexFunctor W R).obj M) ⟶ d)
    (r : DerivedCategory.Q.obj ((sectionsAtFunctor R (op Z)).obj M) ⟶ d)
    (hq : DerivedCategory.Q.map (cechAugmentationTotal W R hZ M) ≫ g = r) :
    DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (cechAugmentationTotal W R hZ K)
          (cechAugmentationTotal W R hZ L) (tensorModules R) (up ℤ)) ≫
        DerivedCategory.Q.map (cechCupProduct W R D) ≫ g =
      DerivedCategory.Q.map (naiveCupProduct R D (op Z)) ≫ r :=
  Stacks.Cech.CupProductSquare.map_comp_paste DerivedCategory.Q
    (naiveCupProduct_cechCupProduct W R hZ D) g r hq

end Stacks.Cech.LinearCupProduct

end
