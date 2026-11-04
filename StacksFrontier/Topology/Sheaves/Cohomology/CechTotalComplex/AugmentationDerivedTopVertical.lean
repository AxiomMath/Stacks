module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AugmentationDerivedPinning

/-!
# The top vertical of [Stacks, Tag 0FKV]'s left-hand column

Let `(S, 𝒪_S)` be a ringed space, put `A = Γ(S, 𝒪_S)`, let `𝒰 : S = ⋃ U i` be an open covering
and let `𝒦^•`, `ℳ^•` be bounded below complexes of `𝒪_S`-modules.  The left-hand column of the
diagram of [Stacks, Tag 0FKV] starts with the canonical map

`x ⊗^𝐋_A y ⟶ Tot(x ⊗_A y)`

of [Stacks, Tag 064M] at the pair of total Čech complexes, continues with the Čech cup product of
[Stacks, Tag 07MB] and ends with the comparison of [Stacks, Tag 08BN].  The final paragraph of
the source's proof precomposes that column with the augmentation of [Stacks, Tag 07M9] in both
tensor factors and identifies the result with the column of the diagram displayed just before the
tag, whose top left corner is `Γ(S, 𝒦^•) ⊗^𝐋_A Γ(S, ℳ^•)`.

Below the Čech cup product that identification is
`Stacks.Cech.CupProductSquare.cechAugmentationTotal_comp_cechToBaseSectionsA` and
`Stacks.Cech.LinearCupProduct.Q_map_cechCupProduct_comp_of_augmentation_comp`. The topmost
square is the naturality of `CochainComplex.DerivedTensor.ToTotal.canonicalDerivedToTensorNatTrans`
at the pair of augmentations, and the three squares paste to the whole column. Nothing is required
of the covering or of the coefficient complexes.

## Main results

* `CochainComplex.DerivedTensor.ToTotal.tensorHom_eq_mapBifunctorMap_tensorModules` and
  `CochainComplex.DerivedTensor.ToTotal.totalTensorPair_map_eq_tensorModules`: the total tensor
  product of two cochain maps, as the `HomologicalComplex.mapBifunctorMap` of
  `Stacks.Cech.CupProduct.tensorModules` that the Čech augmentation square is stated with.
* `CochainComplex.DerivedTensor.ToTotal.canonicalDerivedToTensorNatTrans_naturality`: **the top
  vertical.**  The canonical map `x ⊗^𝐋_R y ⟶ Tot(x ⊗_R y)` of [Stacks, Tag 064M] is natural in
  a pair of cochain maps, in the spelling the Čech augmentation square uses on the other side.
* `CochainComplex.DerivedTensor.ToTotal.canonicalDerivedToTensorNatTrans_comp_of_paste`: the
  three-square paste with **every object, morphism and comparison a variable**.
* `LinearCupProduct.Q_map_canonicalDerivedToTensor_comp_cechCupProduct_comp_of_augmentation_comp`:
  **the left-hand column of [Stacks, Tag 0FKV], generically.**  The canonical map followed by the
  Čech cup product of [Stacks, Tag 07MB] and any map `g` out of `Q(Tot(Č(W,M)))`, precomposed
  with the augmentation of [Stacks, Tag 07M9] in both tensor factors, is the canonical map at the
  sections followed by the naive cup product and the factorization of `g` along the augmentation.
* `Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor_eq_cechCupProduct`: the cup product at
  the sheaf-tensor coefficients is the generic one, on the nose.
* `Stacks.Cech.CupProductSquare.augmentation_comp_cechLeftLeg`: **the left-hand leg of
  [Stacks, Tag 0FKV], precomposed with the augmentation in both tensor factors**, is the
  canonical map at the two complexes of sections, the naive cup product and the unit
  `Γ(S, -) ⟶ RΓ(S, -)`.

## Implementation notes

`canonicalDerivedToTensorNatTrans_comp_of_paste` mentions no `HomologicalComplex.mapBifunctor` or
`HomologicalComplex.mapBifunctorMap`: its two intermediate complexes and its two comparison maps
are variables. At the coefficient ring `Stacks.Cech.ModuleCupProduct.CoeffRing 𝒪_S ⊤` of
Tag 0FKV, synthesizing the `HasMapBifunctor` instance of such a term afresh exceeds the
200000-heartbeat budget, so the instantiation supplies those variables by substitution, as the
types of `canonicalDerivedToTensorNatTrans_naturality` and of the augmentation square.

In the `Stacks.Cech.SheafTensorPairing` section `WEqualsLocallyBijective` is an instance
argument, as it is for `Stacks.SheafOfModules.Tensor.sheafTensor`. Synthesized from scratch under
the binder of `∀ F, ((sheafTensor 𝒪_X).obj F).Additive`, it is searched as
`∀ F, (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat`, which exceeds the
20000-heartbeat `synthInstance` budget. It is discharged by synthesis at every instantiation, so
the results of the `Stacks.Cech.CupProductSquare` section, read at `S.sheaf` for a ringed space
`S`, do not carry it.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (coverObject)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.CupProduct (tensorModules)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor totalCechComplexFunctorA)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections tensorBase)
open CochainComplex.DerivedTensor (canonicalDerivedTensorProductFunctor)
open scoped CategoryTheory.Prod

universe u w uC vC

namespace CochainComplex.DerivedTensor.ToTotal

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable (R : Type u) [CommRing R]

/-- **The tensor product of two cochain maps of `R`-modules is their `mapBifunctorMap` at the
tensor bifunctor `Stacks.Cech.CupProduct.tensorModules`** of the Čech cup product of
[Stacks, Tag 07MB]. This holds by definition: `tensorModules R` is
`MonoidalCategory.curriedTensor (ModuleCat R)` and `HomologicalComplex.tensorHom` is
`HomologicalComplex.mapBifunctorMap` at that bifunctor. -/
theorem tensorHom_eq_mapBifunctorMap_tensorModules {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    HomologicalComplex.tensorHom a b =
      HomologicalComplex.mapBifunctorMap a b (tensorModules R) (up ℤ) :=
  rfl

/-- **The total tensor complex of a morphism of pairs `(a, b)` is the `mapBifunctorMap` of `a`
and `b` at `Stacks.Cech.CupProduct.tensorModules`**: tensoring in each variable separately
composes to tensoring in both. -/
theorem totalTensorPair_map_eq_tensorModules
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ} (a : K ⟶ K') (b : L ⟶ L') :
    (totalTensorPair R).map (a ×ₘ b) =
      HomologicalComplex.mapBifunctorMap a b (tensorModules R) (up ℤ) :=
  (totalTensorPair_map a b).trans (tensorHom_eq_mapBifunctorMap_tensorModules R a b)

/-- **The top vertical of [Stacks, Tag 0FKV]'s left-hand column.**

The canonical map `x ⊗^𝐋_R y ⟶ Tot(x ⊗_R y)` of [Stacks, Tag 064M] is natural in a pair of
cochain maps `a`, `b`: pushing `a ⊗^𝐋 b` through it is the same as pushing `Tot(a ⊗ b)` through
it.  At the pair of augmentations of [Stacks, Tag 07M9] this is the top square of the
left-hand column of Tag 0FKV.

The target is written with `HomologicalComplex.mapBifunctorMap` of
`Stacks.Cech.CupProduct.tensorModules`, as in the Čech augmentation square
`Stacks.Cech.LinearCupProduct.naiveCupProduct_cechCupProduct`.  It holds for all complexes,
K-flat or not, bounded or not. -/
theorem canonicalDerivedToTensorNatTrans_naturality
    {K K' L L' : CochainComplex (ModuleCat.{u} R) ℤ} (a : K ⟶ K') (b : L ⟶ L') :
    (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
          (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (canonicalDerivedToTensorNatTrans R).app (K', L') =
      (canonicalDerivedToTensorNatTrans R).app (K, L) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap a b (tensorModules R) (up ℤ)) :=
  ((canonicalDerivedToTensorNatTrans R).naturality (a ×ₘ b)).trans
    (congrArg
      (fun f => (canonicalDerivedToTensorNatTrans R).app (K, L) ≫ DerivedCategory.Q.map f)
      (totalTensorPair_map_eq_tensorModules R a b))

/-- **The three squares of [Stacks, Tag 0FKV]'s left-hand column pasted, with every object,
morphism and comparison a variable.**

Given a naturality square `hnat` for the two comparisons `ntl`, `ntu` along `a`, `b` and `mbm`, a
commuting square `haug` for `mbm`, `cup`, `nv`, `c`, and a factorization `hq` of `c` followed by
`g`, the canonical comparison followed by `cup` and `g`, precomposed with `a ⊗^𝐋 b`, is the
canonical comparison followed by `nv` and `r`. -/
theorem canonicalDerivedToTensorNatTrans_comp_of_paste
    {X X2 Y Y2 Z Z2 T T2 : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : X ⟶ X2) (b : Y ⟶ Y2) (c : Z ⟶ Z2)
    (mbm : T ⟶ T2) (nv : T ⟶ Z) (cup : T2 ⟶ Z2)
    (ntl : (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).obj
        (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ⟶ DerivedCategory.Q.obj T)
    (ntu : (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).obj
        (DerivedCategory.Q.obj X2, DerivedCategory.Q.obj Y2) ⟶ DerivedCategory.Q.obj T2)
    (hnat : (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
          (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫ ntu =
        ntl ≫ DerivedCategory.Q.map mbm)
    (haug : mbm ≫ cup = nv ≫ c)
    {d : DerivedCategory (ModuleCat.{u} R)}
    (g : DerivedCategory.Q.obj Z2 ⟶ d) (r : DerivedCategory.Q.obj Z ⟶ d)
    (hq : DerivedCategory.Q.map c ≫ g = r) :
    (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
          (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        ntu ≫ DerivedCategory.Q.map cup ≫ g =
      ntl ≫ DerivedCategory.Q.map nv ≫ r := by
  rw [← Category.assoc, hnat, Category.assoc,
    Stacks.Cech.CupProductSquare.map_comp_paste DerivedCategory.Q haug g r hq]

/-- **The canonical map followed by a cochain map, precomposed with a pair of cochain maps**:
`canonicalDerivedToTensorComp` at `cup`, followed by `g`, precomposed with `a ⊗^𝐋 b`, is
`canonicalDerivedToTensorComp` at `nv` followed by `r`, as soon as
`Tot(a ⊗ b) ≫ cup = nv ≫ c` and `Q c ≫ g = r`. -/
theorem canonicalDerivedToTensorComp_paste
    {X X2 Y Y2 Z Z2 : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : X ⟶ X2) (b : Y ⟶ Y2) (c : Z ⟶ Z2)
    (nv : HomologicalComplex.mapBifunctor X Y (tensorModules R) (up ℤ) ⟶ Z)
    (cup : HomologicalComplex.mapBifunctor X2 Y2 (tensorModules R) (up ℤ) ⟶ Z2)
    (haug : HomologicalComplex.mapBifunctorMap a b (tensorModules R) (up ℤ) ≫ cup = nv ≫ c)
    {d : DerivedCategory (ModuleCat.{u} R)}
    (g : DerivedCategory.Q.obj Z2 ⟶ d) (r : DerivedCategory.Q.obj Z ⟶ d)
    (hq : DerivedCategory.Q.map c ≫ g = r) :
    (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
          (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        canonicalDerivedToTensorComp R X2 Y2 Z2 cup ≫ g =
      canonicalDerivedToTensorComp R X Y Z nv ≫ r := by
  unfold canonicalDerivedToTensorComp
  simp only [Category.assoc]
  exact canonicalDerivedToTensorNatTrans_comp_of_paste R a b c
    (HomologicalComplex.mapBifunctorMap a b (tensorModules R) (up ℤ)) nv cup
    ((canonicalDerivedToTensorNatTrans R).app (X, Y))
    ((canonicalDerivedToTensorNatTrans R).app (X2, Y2))
    (canonicalDerivedToTensorNatTrans_naturality R a b) haug g r hq

end CochainComplex.DerivedTensor.ToTotal

namespace Stacks.Cech.LinearCupProduct

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorNatTrans
  canonicalDerivedToTensorNatTrans_comp_of_paste canonicalDerivedToTensorNatTrans_naturality)

/-- **The left-hand column of [Stacks, Tag 0FKV], reduced along the augmentation of
[Stacks, Tag 07M9], generically.**

In the derived category of `R`-modules: the canonical map `x ⊗^𝐋_R y ⟶ Tot(x ⊗_R y)` of
[Stacks, Tag 064M] at the two total Čech complexes, followed by the Čech cup product of
[Stacks, Tag 07MB] and by any map `g` out of `Q(Tot(Č(W,M)))`, precomposed with the augmentation
of [Stacks, Tag 07M9] in both tensor factors, is the canonical map at the two complexes of
sections followed by the naive cup product and by the factorization `r` of `g` along the
augmentation.

At the data of Tag 0FKV -- a ringed space, the cover in the slice over the whole space, the
sheaf-tensor pairing -- with `g` the comparison of [Stacks, Tag 08BN] and `hq`
`Stacks.Cech.CupProductSquare.cechAugmentationTotal_comp_cechToBaseSectionsA`, this is
`Stacks.Cech.CupProductSquare.augmentation_comp_cechLeftLeg`.

It holds for every covering, every pair of complexes and every `g`. -/
theorem Q_map_canonicalDerivedToTensor_comp_cechCupProduct_comp_of_augmentation_comp
    {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] {ι : Type w} [UnivLE.{w, u}]
    (W : ι → C) (R : Type u) [CommRing R] {Z : C} (hZ : IsTerminal Z)
    {K L M : CochainComplex (PresheafModules.{u} C R) ℤ} (D : ComplexPairing.{u} R K L M)
    {d : DerivedCategory (ModuleCat.{u} R)}
    (g : DerivedCategory.Q.obj ((totalCechComplexFunctor W R).obj M) ⟶ d)
    (r : DerivedCategory.Q.obj ((sectionsAtFunctor R (op Z)).obj M) ⟶ d)
    (hq : DerivedCategory.Q.map (cechAugmentationTotal W R hZ M) ≫ g = r) :
    (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map
          (DerivedCategory.Q.map (cechAugmentationTotal W R hZ K) ×ₘ
            DerivedCategory.Q.map (cechAugmentationTotal W R hZ L)) ≫
        (canonicalDerivedToTensorNatTrans R).app
            ((totalCechComplexFunctor W R).obj K, (totalCechComplexFunctor W R).obj L) ≫
          DerivedCategory.Q.map (cechCupProduct W R D) ≫ g =
      (canonicalDerivedToTensorNatTrans R).app
          ((sectionsAtFunctor R (op Z)).obj K, (sectionsAtFunctor R (op Z)).obj L) ≫
        DerivedCategory.Q.map (naiveCupProduct R D (op Z)) ≫ r :=
  canonicalDerivedToTensorNatTrans_comp_of_paste R _ _ _ _ _ _ _ _
    (canonicalDerivedToTensorNatTrans_naturality R (cechAugmentationTotal W R hZ K)
      (cechAugmentationTotal W R hZ L))
    (naiveCupProduct_cechCupProduct W R hZ D) g r hq

end Stacks.Cech.LinearCupProduct

namespace Stacks.Cech.SheafTensorPairing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (V : Opens X) (K L : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ)
  {ι : Type u} (U : ι → Opens X) (hU : V = ⨆ i, U i)

/-- **The cup product at the sheaf-tensor coefficients is the generic Čech cup product of
[Stacks, Tag 07MB]**, on the nose, at the cover in the slice over `V` and the base ring
`A = 𝒪_X(V)`. -/
theorem cechCupProductSheafTensor_eq_cechCupProduct :
    cechCupProductSheafTensor O V K L U hU =
      Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) (CoeffRing O V)
        (sheafTensorComplexPairing O V K L) :=
  rfl

/-- Sections over `V` of a complex of `𝒪_X`-modules, read at the terminal object of the slice
over `V`: the source of the Čech augmentation of [Stacks, Tag 07M9] in the spelling of
`Stacks.Cech.LinearCupProduct.cechAugmentationTotal`. -/
abbrev sectionsAtTerminal (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ) :
    CochainComplex (ModuleCat.{u} (CoeffRing O V)) ℤ :=
  (Stacks.Cech.LinearCupProduct.sectionsAtFunctor (CoeffRing O V) (op (Over.mk (𝟙 V)))).obj
    ((sectionsComplexFunctor O V).obj T)

/-- **The augmentation of [Stacks, Tag 07M9]** `Γ(V, 𝒦^•) ⟶ Tot(Č^•(𝒰, 𝒦^•))` of a complex of
`𝒪_X`-modules, with its target written as `Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA`,
the spelling of the cup product `cechCupProductSheafTensor`. -/
abbrev augmentationA (T : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} O)) ℤ) :
    sectionsAtTerminal O V T ⟶ (totalCechComplexFunctorA O V U hU).obj T :=
  Stacks.Cech.LinearCupProduct.cechAugmentationTotal (coverObject U hU) (CoeffRing O V)
    Over.mkIdTerminal ((sectionsComplexFunctor O V).obj T)

/-- **The naive cup product** `Tot(Γ(V, 𝒦^•) ⊗_A Γ(V, ℒ^•)) ⟶ Γ(V, Tot(𝒦^• ⊗_{𝒪_X} ℒ^•))` of
the sheaf-tensor coefficient pairing, `A = 𝒪_X(V)`. -/
abbrev naiveCupProductA :
    HomologicalComplex.mapBifunctor (sectionsAtTerminal O V K) (sectionsAtTerminal O V L)
        (tensorModules (CoeffRing O V)) (up ℤ) ⟶
      sectionsAtTerminal O V (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)) :=
  Stacks.Cech.LinearCupProduct.naiveCupProduct (CoeffRing O V)
    (sheafTensorComplexPairing O V K L) (op (Over.mk (𝟙 V)))

/-- **The augmentation square of [Stacks, Tag 07M9] at the sheaf-tensor coefficients**: under
the augmentation in both tensor factors the Čech cup product `cechCupProductSheafTensor` is the
naive cup product followed by the augmentation of `Tot(𝒦^• ⊗ ℒ^•)`.  This is
`Stacks.Cech.LinearCupProduct.naiveCupProduct_cechCupProduct`, stated at the spelling of
`Stacks.Cech.CupProductSquare.cechLeftLeg`. -/
theorem augmentationA_cechCupProductSheafTensor :
    HomologicalComplex.mapBifunctorMap (augmentationA O V U hU K) (augmentationA O V U hU L)
        (tensorModules (CoeffRing O V)) (up ℤ) ≫ cechCupProductSheafTensor O V K L U hU =
      naiveCupProductA O V K L ≫
        augmentationA O V U hU (HomologicalComplex.mapBifunctor K L (sheafTensor O) (up ℤ)) :=
  Stacks.Cech.LinearCupProduct.naiveCupProduct_cechCupProduct (coverObject U hU)
    (CoeffRing O V) Over.mkIdTerminal (sheafTensorComplexPairing O V K L)

end Stacks.Cech.SheafTensorPairing

namespace Stacks.Cech.CupProductSquare

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorComp
  canonicalDerivedToTensorComp_paste)
open Stacks.Cech.SheafTensorPairing (augmentationA naiveCupProductA
  augmentationA_cechCupProductSheafTensor)

variable (S : RingedSpace.{u, u}) {I : Type u} (Ui : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)
  (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- **The unit `Γ(S, 𝒯^•) ⟶ RΓ(S, 𝒯^•)` with its source written as sections at the terminal
object of the slice over `S`**: the identification
`Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso` of the two presentations of `Γ(S, -)`
followed by `sectionsToBaseSections`. -/
def sectionsAtTerminalToBaseSections
    (T : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    DerivedCategory.Q.obj (Stacks.Cech.SheafTensorPairing.sectionsAtTerminal S.sheaf ⊤ T.1) ⟶
      (baseSections S).obj (DerivedCategory.Q.obj T.1) :=
  DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
      (Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso.{u, u, u}
        (R := ringSheaf.{u, u, u} S.sheaf) ⊤) (up ℤ)).app T.1).hom ≫
    (sectionsToBaseSections S).app T

/-- **The comparison of [Stacks, Tag 08BN] after the augmentation of [Stacks, Tag 07M9] is the
unit**, in the spelling `augmentationA` of the augmentation. -/
theorem augmentationA_comp_cechToBaseSectionsA
    (T : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf))) :
    DerivedCategory.Q.map (augmentationA S.sheaf ⊤ Ui hU T.1) ≫ cechToBaseSectionsA S Ui hU T =
      sectionsAtTerminalToBaseSections S T :=
  cechAugmentationTotal_comp_cechToBaseSectionsA S Ui hU T

/-- **The left-hand column of [Stacks, Tag 0FKV]'s square, precomposed with the augmentation of
[Stacks, Tag 07M9] in both tensor factors, is the left-hand column of the diagram the source
displays just before the tag**: the canonical map at the two complexes of global sections, the
naive cup product of the sheaf-tensor pairing, and the unit `Γ(S, -) ⟶ RΓ(S, -)` at
`Tot(𝒦^• ⊗_{𝒪_S} ℳ^•)`. -/
theorem augmentation_comp_cechLeftLeg :
    (Functor.uncurry.obj (tensorBase S)).map
          (DerivedCategory.Q.map (augmentationA S.sheaf ⊤ Ui hU K.1) ×ₘ
            DerivedCategory.Q.map (augmentationA S.sheaf ⊤ Ui hU M.1)) ≫
        cechLeftLeg S Ui hU K M =
      canonicalDerivedToTensorComp (CoeffRing.{u} S.sheaf ⊤) _ _ _
          (naiveCupProductA S.sheaf ⊤ K.1 M.1) ≫
        sectionsAtTerminalToBaseSections S (tensorPlus S K M) :=
  canonicalDerivedToTensorComp_paste (CoeffRing.{u} S.sheaf ⊤) _ _ _ _ _
    (augmentationA_cechCupProductSheafTensor S.sheaf ⊤ K.1 M.1 Ui hU) _ _
    (augmentationA_comp_cechToBaseSectionsA S Ui hU (tensorPlus S K M))

end Stacks.Cech.CupProductSquare

end
