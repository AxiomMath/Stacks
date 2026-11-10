module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquareCommutes
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechHodgeClass
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.PullbackCup
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductCocycles
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearMapRestrictScalars

/- `CupProductSquareCommutes` must stay the first import: imported after the Hodge files, the
instance environment changes and the comparison of the cup-product terms of
`Stacks.Cech.SheafTensorPairing` with the ones elaborated here exceeds the heartbeat budget. -/

/-!
# The cup product of classes of Čech cocycles

Let `(S, 𝒪_S)` be a ringed space with an open covering `𝒰`. By [Stacks, Tag 0FKV] the global cup
product of Cohomology, Section 0FKU, followed by the canonical map to the total tensor complex,
is computed on the total Čech complexes by the Čech cup product of [Stacks, Tag 07MB]. Read on
cohomology classes: for cocycles `z` of `Tot(Č^•(𝒰, 𝒦^•))` and `w` of `Tot(Č^•(𝒰, ℳ^•))`, the cup
product of their classes in `H^*(S, 𝒦^•)` and `H^*(S, ℳ^•)` is the class of the Čech cup product
of `z ⊗ w`.

For sheaves `ℱ`, `𝒢` placed in degree `0` and a multiplication `μ : ℱ ⊗ 𝒢 ⟶ ℋ`, the Čech cup
product of the cochains attached to two Čech cocycles `c`, `e` is the cochain attached to their
Alexander–Whitney product `(c ∪ e)_{s₀ … s_{q+q'}} = μ(c_{s₀ … s_q}, e_{s_q … s_{q+q'}})`; the
sign `(-1)^{a q'}` of the Čech cup product vanishes, as the coefficient degree `a` is `0`.

Applied to the wedge product of differential forms, for a morphism of schemes `f : X ⟶ S`: the
Hodge cup product of the classes of a Čech `q`-cocycle `c` of `Ω^p_{X/S}` and a Čech `q'`-cocycle
`e` of `Ω^{p'}_{X/S}` is `(-1)^{q p'}` times the class of the wedge product `c ∪ e`, the sign
being the Koszul sign built into the Hodge cup product.

## Main definitions

* `Stacks.HodgeWeil.formsWedgeBilinear`: the wedge product `Ω^p × Ω^{p'} ⟶ Ω^{p + p'}` on
  sections, as a bilinear map over the base ring sheaf.
* `Stacks.HodgeWeil.wedgeCup`: the Alexander–Whitney wedge product of Čech cochains of
  differential forms.
* `Stacks.HodgeWeil.cechCocycleToCycles`: the cycle of the total Čech complex attached to a Čech
  cocycle.

## Main results

* `Stacks.HodgeWeil.totalCupPairing_cechBaseClass`: **[Stacks, Tag 0FKV] on classes**: the cup
  product of the classes `cechBaseClass` of two cocycles of total Čech complexes is the class of
  their Čech cup product.
* `Stacks.HodgeWeil.cechCupProduct_comp_map_singlePlus`: the Čech cup product at the
  sheaf-tensor coefficients followed by a multiplication of sheaves placed in degree `0` is the
  Čech cup product of the bilinear map on sections of the multiplication.
* `Stacks.HodgeWeil.cohomologyMap_totalCupPairing_cechSheafClass`: the cup product of the classes
  of two Čech cocycles of sheaves in degree `0`, followed by a multiplication, is the class of
  their Alexander–Whitney product.
* `Stacks.HodgeWeil.cechD_wedgeCup`: the wedge product of two Čech cocycles is a Čech cocycle.
* `Stacks.HodgeWeil.hodgeComponentCup_cechSheafClass` and
  `Stacks.HodgeWeil.hodgeCohomologyCup_hodgeCechClass`: **the Hodge cup product of the classes of
  two Čech cocycles is `(-1)^{q p'}` times the class of their wedge product.**

## Implementation notes

The tensoring of classes is the one of [Stacks, Tag 068H] used inside the cup pairing, so the
statement on classes is phrased through a cycle `z₀` of the total tensor complex lifting the
tensor product of cycles (`RingTheory.TorProducts.exists_tensorCycles` provides one), as in
`Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_globalCycleClass`.

Several statements below are stated with every object and morphism a variable, or for an
arbitrary multiplication `μ` with a hypothesis on its values: the same complexes are written at
several definitionally equal spellings (over `Γ(S, 𝒪_S)` and over the section ring of the
structure sheaf), and these are compared once, in a lemma of their own.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing tensorBase)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule totalCupPairing)
open RingTheory.TorProducts (cycleClass)
open scoped CategoryTheory.Prod TensorProduct

universe w u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

section Square

/-- Pasting three commutative diagrams, stated with every object and morphism a variable so that
it applies by one unification. -/
theorem paste_comp_eq {C : Type*} [Category* C] {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ : C}
    (l : o₀ ⟶ o₁) (x : o₁ ⟶ o₂) (t : o₂ ⟶ o₃) (m : o₃ ⟶ o₄) (zw : o₁ ⟶ o₅) (z₀ : o₅ ⟶ o₆)
    (c₁ : o₆ ⟶ o₇) (πT : o₇ ⟶ o₈) (bT : o₈ ⟶ o₃) (c₂ : o₇ ⟶ o₉) (πM : o₉ ⟶ o₁₀)
    (bM : o₁₀ ⟶ o₄) (hM : o₈ ⟶ o₁₀)
    (h1 : l ≫ x ≫ t = l ≫ zw ≫ z₀ ≫ c₁ ≫ πT ≫ bT) (h2 : bT ≫ m = hM ≫ bM)
    (h3 : c₂ ≫ πM = πT ≫ hM) :
    l ≫ x ≫ t ≫ m = (l ≫ zw ≫ z₀ ≫ c₁ ≫ c₂) ≫ πM ≫ bM := by
  rw [← Category.assoc x, ← Category.assoc l, h1]
  simp only [Category.assoc, h2, reassoc_of% h3]

open CochainComplex.DerivedTensor (canonicalDerivedTensorProductFunctor)
open CochainComplex.DerivedTensor.ToTotal (canonicalDerivedToTensorComp
  canonicalDerivedToTensorNatTrans)

variable {R : Type u} [CommRing R]

/-- **A commutative square of [Stacks, Tag 0FKV]'s shape, read on classes of cocycles.**  Let
`cup : Tot(X ⊗_R Y) ⟶ Z` be a chain map and suppose that the canonical map
`X ⊗^𝐋_R Y ⟶ Tot(X ⊗_R Y)` followed by `cup` and by `t` equals `f ⊗^𝐋 g` followed by `μ₁` and
`μ₂`.  Then for cocycles `z ∈ Zⁱ(X)` and `w ∈ Zʲ(Y)` the tensoring of the images of their
classes under `f` and `g`, followed by `μ₁` and `μ₂`, is the image under `t` of the class of the
cocycle `cup(z ⊗ w)`. -/
theorem tensor_cycleClass_eq_of_comp_eq {X Y Z : CochainComplex (ModuleCat.{u} R) ℤ}
    (cup : HomologicalComplex.mapBifunctor X Y (Stacks.Cech.CupProduct.tensorModules R)
      (ComplexShape.up ℤ) ⟶ Z)
    {U V E E' : DerivedCategory (ModuleCat.{u} R)} (f : DerivedCategory.Q.obj X ⟶ U)
    (g : DerivedCategory.Q.obj Y ⟶ V)
    (μ₁ : ((canonicalDerivedTensorProductFunctor R).obj U).obj V ⟶ E) (μ₂ : E ⟶ E')
    (t : DerivedCategory.Q.obj Z ⟶ E')
    {i j : ℤ}
    (P : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj U ⊗
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj V ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).obj E)
    (hP : P = (RingTheory.TorProducts.cohomologyTensorProduct U V i j).map ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map μ₁)
    (hsq : canonicalDerivedToTensorComp R X Y Z cup ≫ t =
      (Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map (f ×ₘ g) ≫ μ₁ ≫ μ₂)
    (z : ModuleCat.of R R ⟶ X.cycles i) (w : ModuleCat.of R R ⟶ Y.cycles j)
    (z₀ : X.cycles i ⊗ Y.cycles j ⟶ (X ⊗ Y).cycles (i + j))
    (hz₀ : z₀ ≫ (X ⊗ Y).iCycles (i + j) =
      (X.iCycles i ⊗ₘ Y.iCycles j) ≫ HomologicalComplex.ιTensorObj X Y i j (i + j) rfl) :
    (λ_ (ModuleCat.of R R)).inv ≫
        ((cycleClass z ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map f) ⊗ₘ
          (cycleClass w ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map g)) ≫
        P ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map μ₂ =
      cycleClass ((λ_ (ModuleCat.of R R)).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap cup (i + j)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map t := by
  subst hP
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)
  have h1 := RingTheory.TorProducts.tensor_cycleClass_naturality z w f g
  have hs := congrArg H.map hsq
  simp only [canonicalDerivedToTensorComp, H.map_comp] at hs
  calc _ = ((λ_ (ModuleCat.of R R)).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
          (RingTheory.TorProducts.cohomologyTensorProduct (DerivedCategory.Q.obj X)
            (DerivedCategory.Q.obj Y) i j).map) ≫
          H.map ((Functor.uncurry.obj (canonicalDerivedTensorProductFunctor R)).map (f ×ₘ g)) ≫
            H.map μ₁ ≫ H.map μ₂ := by
        simp only [Category.assoc] at h1 ⊢
        rw [reassoc_of% h1]
        rfl
    _ = ((λ_ (ModuleCat.of R R)).inv ≫ (cycleClass z ⊗ₘ cycleClass w) ≫
          (RingTheory.TorProducts.cohomologyTensorProduct (DerivedCategory.Q.obj X)
            (DerivedCategory.Q.obj Y) i j).map ≫ H.map ((canonicalDerivedToTensorNatTrans R).app
              (X, Y))) ≫ H.map (DerivedCategory.Q.map cup) ≫ H.map t := by
        rw [← hs]
        simp only [Category.assoc]
        rfl
    _ = ((λ_ (ModuleCat.of R R)).inv ≫ (z ⊗ₘ w) ≫ cycleClass z₀) ≫
          H.map (DerivedCategory.Q.map cup) ≫ H.map t :=
        congrArg (fun x => x ≫ H.map (DerivedCategory.Q.map cup) ≫ H.map t)
          (RingTheory.TorProducts.cycleClass_tensor_toTensor z w z₀ hz₀)
    _ = _ := by
        rw [Category.assoc, Category.assoc,
          reassoc_of% RingTheory.TorProducts.cycleClass_comp_map z₀ cup]
        have e := RingTheory.TorProducts.comp_cycleClass ((λ_ (ModuleCat.of R R)).inv ≫ (z ⊗ₘ w))
          (z₀ ≫ HomologicalComplex.cyclesMap cup (i + j))
        simp only [Category.assoc] at e
        exact (reassoc_of% e) (H.map t)

/-- The tensor product of two maps out of `R`, followed by the inclusion of a summand of the
total tensor complex, is their cup product of cochains. -/
@[reassoc]
theorem leftUnitor_inv_tensorHom_ιTensorObj (X Y : CochainComplex (ModuleCat.{u} R) ℤ)
    {p q : ℤ} (α : ModuleCat.of R R ⟶ X.X p) (β : ModuleCat.of R R ⟶ Y.X q) (n : ℤ)
    (hn : p + q = n) :
    (λ_ (ModuleCat.of R R)).inv ≫ (α ⊗ₘ β) ≫ HomologicalComplex.ιMapBifunctor X Y
        (Stacks.Cech.CupProduct.tensorModules R) (ComplexShape.up ℤ) p q n hn =
      Stacks.Cech.Hypercohomology.toMor
          (M := ((Stacks.Cech.CupProduct.tensorModules R).obj (ModuleCat.of R R)).obj
            (ModuleCat.of R R)) ((1 : R) ⊗ₜ[R] (1 : R)) ≫
        Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules R) X Y p q n hn α β := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  change (HomologicalComplex.ιMapBifunctor X Y (Stacks.Cech.CupProduct.tensorModules R)
      (ComplexShape.up ℤ) p q n hn).hom
      ((α ⊗ₘ β).hom ((λ_ (ModuleCat.of R R)).inv.hom (1 : R))) =
    (HomologicalComplex.ιMapBifunctor X Y (Stacks.Cech.CupProduct.tensorModules R)
      (ComplexShape.up ℤ) p q n hn).hom
      ((((Stacks.Cech.CupProduct.tensorModules R).obj (X.X p)).map β).hom
        ((((Stacks.Cech.CupProduct.tensorModules R).map α).app (ModuleCat.of R R)).hom
          ((Stacks.Cech.Hypercohomology.toMor
            (M := ((Stacks.Cech.CupProduct.tensorModules R).obj (ModuleCat.of R R)).obj
              (ModuleCat.of R R)) ((1 : R) ⊗ₜ[R] (1 : R))).hom (1 : R))))
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    Stacks.Cech.Hypercohomology.toMor_apply_one]
  rfl

/-- **The image of a tensor product of two cocycles under two chain maps out of the total tensor
complex, on cycles**: the cup product of the two cochains followed by the two chain maps. -/
theorem cyclesMap_comp_iCycles_of_tensorCycles {X Y Z T : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : HomologicalComplex.mapBifunctor X Y (Stacks.Cech.CupProduct.tensorModules R)
      (ComplexShape.up ℤ) ⟶ Z) (ψ : Z ⟶ T) {i j : ℤ}
    (x : ModuleCat.of R R ⟶ X.X i) (y : ModuleCat.of R R ⟶ Y.X j)
    (z : ModuleCat.of R R ⟶ X.cycles i) (hz : z ≫ X.iCycles i = x)
    (w : ModuleCat.of R R ⟶ Y.cycles j) (hw : w ≫ Y.iCycles j = y)
    (z₀ : X.cycles i ⊗ Y.cycles j ⟶ (HomologicalComplex.mapBifunctor X Y
      (Stacks.Cech.CupProduct.tensorModules R) (ComplexShape.up ℤ)).cycles (i + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor X Y (Stacks.Cech.CupProduct.tensorModules R)
        (ComplexShape.up ℤ)).iCycles (i + j) =
      (X.iCycles i ⊗ₘ Y.iCycles j) ≫ HomologicalComplex.ιMapBifunctor X Y
        (Stacks.Cech.CupProduct.tensorModules R) (ComplexShape.up ℤ) i j (i + j) rfl) :
    ((λ_ (ModuleCat.of R R)).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫ HomologicalComplex.cyclesMap φ (i + j) ≫
        HomologicalComplex.cyclesMap ψ (i + j)) ≫ T.iCycles (i + j) =
      Stacks.Cech.Hypercohomology.toMor
          (M := ((Stacks.Cech.CupProduct.tensorModules R).obj (ModuleCat.of R R)).obj
            (ModuleCat.of R R)) ((1 : R) ⊗ₜ[R] (1 : R)) ≫
        Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules R) X Y i j (i + j) rfl
          x y ≫ φ.f (i + j) ≫ ψ.f (i + j) := by
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i_assoc]
  rw [reassoc_of% hz₀, tensorHom_comp_tensorHom_assoc, hz, hw]
  exact leftUnitor_inv_tensorHom_ιTensorObj_assoc X Y x y _ rfl _

end Square

section General

variable (S : RingedSpace.{u, u}) {I : Type u} (U : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, U i)

/-- The total Čech complex `Tot(Č^•(𝒰, 𝒦^•))` of a bounded below complex, as a complex of
`Γ(S, 𝒪_S)`-modules. -/
abbrev cechTotalA
    (K : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))) :
    CochainComplex (ModuleCat.{u} (baseRing S)) ℤ :=
  (Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA S.sheaf ⊤ U hU).obj K.obj

/-- The class of a cocycle of the total Čech complex, read in `Hⁱ(S, 𝒦^•)` through the
comparison of [Stacks, Tag 08BN], is `cechBaseClass` of its cohomology class. -/
theorem cycleClass_comp_cechToBaseSections
    (K : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))) {i : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU K).cycles i) :
    cycleClass z ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
        ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app K) =
      z ≫ (cechTotalA S U hU K).homologyπ i ≫ cechBaseClass S U hU K i :=
  (Category.assoc _ _ _).trans (congrArg (z ≫ ·) (Category.assoc _ _ _))

/-- [Stacks, Tag 0FKV] (`Stacks.Cech.CupProductSquare.cupProductSquareCommutes`), with its two
legs written out. -/
theorem cupProductSquareCommutes_unfolded
    (K M : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))) :
    CochainComplex.DerivedTensor.ToTotal.canonicalDerivedToTensorComp
        (baseRing S) (cechTotalA S U hU K)
        (cechTotalA S U hU M) (cechTotalA S U hU (Stacks.Cech.CupProductSquare.tensorPlus S K M))
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.obj M.obj U hU) ≫
        (Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app
          (Stacks.Cech.CupProductSquare.tensorPlus S K M) =
      (Functor.uncurry.obj (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
          (baseRing S))).map
          ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app K ×ₘ
            (Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app M) ≫
        (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace S).app
          (DerivedCategory.Q.obj K.obj, DerivedCategory.Q.obj M.obj) ≫
        (baseSections S).map
          ((Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app
            (K.obj, M.obj)) :=
  Stacks.Cech.CupProductSquare.cupProductSquareCommutes S U hU (K := K) (M := M)

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- `totalCupPairing_cechBaseClass` with the classes written through `cycleClass`. -/
theorem totalCupPairing_cycleClass_cechToBaseSections
    (K M : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))) {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU M).cycles j)
    (z₀ : (cechTotalA S U hU K).cycles i ⊗ (cechTotalA S U hU M).cycles j ⟶
      (cechTotalA S U hU K ⊗ cechTotalA S U hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (cechTotalA S U hU K ⊗ cechTotalA S U hU M).iCycles (i + j) =
      ((cechTotalA S U hU K).iCycles i ⊗ₘ (cechTotalA S U hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (cechTotalA S U hU K) (cechTotalA S U hU M) i j (i + j)
          rfl) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((cycleClass z ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
            ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app K)) ⊗ₘ
          (cycleClass w ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) j).map
            ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app M))) ≫
        totalCupPairing K.obj M.obj i j =
      cycleClass ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.obj M.obj U hU)
          (i + j)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app
            (Stacks.Cech.CupProductSquare.tensorPlus S K M)) := by
  have key := tensor_cycleClass_eq_of_comp_eq (R := baseRing S)
    (X := cechTotalA S U hU K) (Y := cechTotalA S U hU M)
    (Z := cechTotalA S U hU (Stacks.Cech.CupProductSquare.tensorPlus S K M))
    (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.obj M.obj U hU)
    ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app K)
    ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app M)
    ((Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace S).app
      (DerivedCategory.Q.obj K.obj, DerivedCategory.Q.obj M.obj))
    ((baseSections S).map
      ((Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app (K.obj, M.obj)))
    ((Stacks.Cech.CupProductSquare.cechToBaseSections S U hU).app
      (Stacks.Cech.CupProductSquare.tensorPlus S K M))
    (Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing
      (Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace S)
      (DerivedCategory.Q.obj K.obj) (DerivedCategory.Q.obj M.obj) i j)
    (Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_eq _ _ _ i j)
    (cupProductSquareCommutes_unfolded S U hU K M) z w z₀ hz₀
  exact key

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- **[Stacks, Tag 0FKV] on cohomology classes.**  Let `z` and `w` be cocycles of the total Čech
complexes `Tot(Č^•(𝒰, 𝒦^•))` and `Tot(Č^•(𝒰, ℳ^•))` of degrees `i` and `j`, and let `z₀` lift the
tensor product of cocycles to the cocycles of `Tot(Tot(Č^•(𝒰, 𝒦^•)) ⊗ Tot(Č^•(𝒰, ℳ^•)))`. Then
the cup product (`totalCupPairing`) of their classes `cechBaseClass` in `Hⁱ(S, 𝒦^•)` and
`Hʲ(S, ℳ^•)` is the class in `Hⁱ⁺ʲ(S, Tot(𝒦^• ⊗ ℳ^•))` of the image of `z ⊗ w` under the Čech cup
product `Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor`. -/
theorem totalCupPairing_cechBaseClass
    (K M : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))) {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU M).cycles j)
    (z₀ : (cechTotalA S U hU K).cycles i ⊗ (cechTotalA S U hU M).cycles j ⟶
      (cechTotalA S U hU K ⊗ cechTotalA S U hU M).cycles (i + j))
    (hz₀ : z₀ ≫ (cechTotalA S U hU K ⊗ cechTotalA S U hU M).iCycles (i + j) =
      ((cechTotalA S U hU K).iCycles i ⊗ₘ (cechTotalA S U hU M).iCycles j) ≫
        HomologicalComplex.ιTensorObj (cechTotalA S U hU K) (cechTotalA S U hU M) i j (i + j)
          rfl) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((z ≫ (cechTotalA S U hU K).homologyπ i ≫ cechBaseClass S U hU K i) ⊗ₘ
          (w ≫ (cechTotalA S U hU M).homologyπ j ≫ cechBaseClass S U hU M j)) ≫
        totalCupPairing K.obj M.obj i j =
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.obj M.obj U hU)
          (i + j) ≫
        (cechTotalA S U hU (Stacks.Cech.CupProductSquare.tensorPlus S K M)).homologyπ (i + j) ≫
        cechBaseClass S U hU (Stacks.Cech.CupProductSquare.tensorPlus S K M) (i + j) := by
  have key := totalCupPairing_cycleClass_cechToBaseSections S U hU K M z w z₀ hz₀
  rw [cycleClass_comp_cechToBaseSections, cycleClass_comp_cechToBaseSections] at key
  refine key.trans ((cycleClass_comp_cechToBaseSections S U hU
    (Stacks.Cech.CupProductSquare.tensorPlus S K M)
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
      HomologicalComplex.cyclesMap
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.obj M.obj U hU)
        (i + j))).trans ?_)
  simp only [Category.assoc]
  exact congrArg (fun x => (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ x)
    (Category.assoc _ _ _)

/-- **The class of a Čech cohomology class is natural in the complex.** -/
theorem cechBaseClass_comp_cohomologyMap
    {T T' : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf))}
    (φ : T.obj ⟶ T'.obj) (n : ℤ) :
    cechBaseClass S U hU T n ≫
        Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := S) φ n =
      HomologicalComplex.homologyMap
          ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA S.sheaf ⊤ U hU).map φ) n ≫
        cechBaseClass S U hU T' n := by
  have hn := Stacks.Cech.CupProductSquare.cechToBaseSections_naturality S U hU
    (ObjectProperty.homMk φ : T ⟶ T')
  have hf := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S)) n).inv.naturality
    ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA S.sheaf ⊤ U hU).map φ)
  have e := congrArg (fun t => (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (baseRing S))
    n).inv.app ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA S.sheaf ⊤ U hU).obj T.obj) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map t) hn
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map_comp _ _).symm).trans
    (e.symm.trans ((congrArg (_ ≫ ·)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map_comp _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hf.symm).trans
        (Category.assoc _ _ _))))))

end General

section CupProductOfPairings

open Stacks.Cech.LinearCupProduct (ComplexPairing cechCupProduct totalCechComplexFunctor
  PresheafModules)

/-- **The Čech cup product of a pairing followed by a map of the target complex is the Čech cup
product of the composite pairing.** -/
theorem cechCupProduct_comp_map_of_pairing {C : Type*} [Category* C] [HasFiniteProducts C]
    {ι : Type w} [UnivLE.{w, u}] (W : ι → C)
    (R : Type u) [CommRing R] {K L M M' : CochainComplex (PresheafModules.{u} C R) ℤ}
    (D : ComplexPairing R K L M) (D' : ComplexPairing R K L M') (h : M ⟶ M')
    (hD : ∀ (a b n : ℤ) (hab : a + b = n), D'.μ a b n hab = D.μ a b n hab ≫ h.f n) :
    cechCupProduct W R D ≫ (totalCechComplexFunctor W R).map h = cechCupProduct W R D' := by
  have hnat := Stacks.Cech.LinearCupProduct.cechCupProduct_natural_of_pairing_hom W R D D'
    (𝟙 K) (𝟙 L) h (fun a b n hab => by
      rw [HomologicalComplex.id_f, HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
        NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
        hD a b n hab])
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    HomologicalComplex.mapBifunctorMap_id, Category.id_comp] at hnat
  exact hnat.symm

/-- `cechCupProduct_comp_map_of_pairing` at `𝒪_X`-module coefficients over the ring of
sections. -/
theorem cechCupProductA_comp_map {T : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (V : Opens T) {ι : Type u}
    (U : ι → Opens T) (hU : V = ⨆ i, U i)
    {K L M M' : CochainComplex (Stacks.Cech.ModuleCupProduct.Modules O) ℤ}
    (D : ComplexPairing (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj K)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj L)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj M))
    (D' : ComplexPairing (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj K)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj L)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj M'))
    (h : M ⟶ M')
    (hD : ∀ (a b n : ℤ) (hab : a + b = n), D'.μ a b n hab =
      D.μ a b n hab ≫ ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).map h).f n) :
    Stacks.Cech.ModuleCupProduct.cechCupProductA O V U hU D ≫
        (Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA O V U hU).map h =
      Stacks.Cech.ModuleCupProduct.cechCupProductA O V U hU D' :=
  cechCupProduct_comp_map_of_pairing (Stacks.Cohomology.CechSheaf.coverObject U hU)
    (Stacks.Cech.ModuleCupProduct.CoeffRing O V) D D'
    ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).map h) hD

/-- The pointwise tensor product of presheaves of modules is zero when, at every object, one of
the factors is. -/
private theorem isZero_tensorPresheafModules {C : Type*} [Category* C] (R : Type u) [CommRing R]
    (P Q : PresheafModules.{u} C R) (h : ∀ Z, IsZero (P.obj Z) ∨ IsZero (Q.obj Z)) :
    IsZero (((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} R).obj P).obj Q) :=
  Functor.isZero _ fun Z => by
    rw [ModuleCat.isZero_iff_subsingleton]
    change Subsingleton (_ ⊗[R] _)
    obtain h | h := h Z <;> rw [ModuleCat.isZero_iff_subsingleton] at h <;> infer_instance

/-- The pointwise tensor product of presheaves of modules with a zero presheaf on the left is
zero. -/
theorem isZero_tensorPresheafModules_left {C : Type*} [Category* C] (R : Type u) [CommRing R]
    {P : PresheafModules.{u} C R} (hP : IsZero P) (Q : PresheafModules.{u} C R) :
    IsZero (((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} R).obj P).obj Q) :=
  isZero_tensorPresheafModules R P Q fun Z =>
    .inl (((evaluation _ _).obj Z).map_isZero hP)

/-- The pointwise tensor product of presheaves of modules with a zero presheaf on the right is
zero. -/
theorem isZero_tensorPresheafModules_right {C : Type*} [Category* C] (R : Type u) [CommRing R]
    (P : PresheafModules.{u} C R) {Q : PresheafModules.{u} C R} (hQ : IsZero Q) :
    IsZero (((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} R).obj P).obj Q) :=
  isZero_tensorPresheafModules R P Q fun Z =>
    .inr (((evaluation _ _).obj Z).map_isZero hQ)

/-- `Stacks.Cech.LinearCupProduct.cupPair_ιTotalCechTo_cechCupProduct` for a first factor in
coefficient degree `0`, where the sign is `1`. -/
theorem cupPair_ιTotalCechTo_cechCupProduct_zero {C : Type*} [Category* C] [HasFiniteProducts C]
    {ι : Type w} [UnivLE.{w, u}] (W : ι → C) (R : Type u) [CommRing R]
    {K L M : CochainComplex (PresheafModules.{u} C R) ℤ} (D : ComplexPairing R K L M)
    {P Q : ModuleCat.{u} R} {r s : ℕ} {b : ℤ}
    (z : P ⟶ Stacks.Cech.LinearCupProduct.cechCochains W R (K.X 0) r)
    (w : Q ⟶ Stacks.Cech.LinearCupProduct.cechCochains W R (L.X b) s) (p q n : ℤ)
    (hp : (r : ℤ) + 0 = p) (hq : (s : ℤ) + b = q) (hn : p + q = n) :
    Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules R)
        ((totalCechComplexFunctor W R).obj K) ((totalCechComplexFunctor W R).obj L) p q n hn
        (z ≫ Stacks.Cech.LinearCupProduct.ιTotalCechTo W R K r 0 p hp)
        (w ≫ Stacks.Cech.LinearCupProduct.ιTotalCechTo W R L s b q hq) ≫
        (cechCupProduct W R D).f n =
      Stacks.Cech.CupProduct.tensorModulesMap R z w ≫
        Stacks.Cech.LinearCupProduct.cechAlexanderWhitney W R (D.μ 0 b (0 + b) rfl) r s ≫
        Stacks.Cech.LinearCupProduct.ιTotalCechTo W R M (r + s) (0 + b) n
          (by push_cast; omega) := by
  rw [Stacks.Cech.LinearCupProduct.cupPair_ιTotalCechTo_cechCupProduct W R D z w p q n hp hq hn,
    zero_mul, Int.negOnePow_zero, Units.val_one, one_smul]

/-- `cupPair_ιTotalCechTo_cechCupProduct_zero` at `𝒪_X`-module coefficients over the ring of
sections. -/
theorem cupPair_ιTotalCechTo_cechCupProductA_zero {T : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) (V : Opens T) {ι : Type u}
    (U : ι → Opens T) (hU : V = ⨆ i, U i)
    {K L M : CochainComplex (Stacks.Cech.ModuleCupProduct.Modules O) ℤ}
    (D : ComplexPairing (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj K)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj L)
      ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj M))
    {P Q : ModuleCat.{u} (Stacks.Cech.ModuleCupProduct.CoeffRing O V)} {r s : ℕ} {b : ℤ}
    (z : P ⟶ Stacks.Cech.LinearCupProduct.cechCochains
      (Stacks.Cohomology.CechSheaf.coverObject U hU)
      (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
      (((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj K).X 0) r)
    (w : Q ⟶ Stacks.Cech.LinearCupProduct.cechCochains
      (Stacks.Cohomology.CechSheaf.coverObject U hU)
      (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
      (((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj L).X b) s) (p q n : ℤ)
    (hp : (r : ℤ) + 0 = p) (hq : (s : ℤ) + b = q) (hn : p + q = n) :
    Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules
          (Stacks.Cech.ModuleCupProduct.CoeffRing O V))
        ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA O V U hU).obj K)
        ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA O V U hU).obj L) p q n hn
        (z ≫ Stacks.Cech.LinearCupProduct.ιTotalCechTo
          (Stacks.Cohomology.CechSheaf.coverObject U hU)
          (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
          ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj K) r 0 p hp)
        (w ≫ Stacks.Cech.LinearCupProduct.ιTotalCechTo
          (Stacks.Cohomology.CechSheaf.coverObject U hU)
          (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
          ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj L) s b q hq) ≫
        (Stacks.Cech.ModuleCupProduct.cechCupProductA O V U hU D).f n =
      Stacks.Cech.CupProduct.tensorModulesMap (Stacks.Cech.ModuleCupProduct.CoeffRing O V) z w ≫
        Stacks.Cech.LinearCupProduct.cechAlexanderWhitney
          (Stacks.Cohomology.CechSheaf.coverObject U hU)
          (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
          (D.μ 0 b (0 + b) rfl) r s ≫
        Stacks.Cech.LinearCupProduct.ιTotalCechTo (Stacks.Cohomology.CechSheaf.coverObject U hU)
          (Stacks.Cech.ModuleCupProduct.CoeffRing O V)
          ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O V).obj M) (r + s) (0 + b) n
          (by push_cast; omega) :=
  cupPair_ιTotalCechTo_cechCupProduct_zero (Stacks.Cohomology.CechSheaf.coverObject U hU)
    (Stacks.Cech.ModuleCupProduct.CoeffRing O V) D z w p q n hp hq hn

end CupProductOfPairings

section Pairing

open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor totalCechComplexFunctorA)
open Stacks.Cohomology.CechSheaf (coverObject)

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- **The Čech cup product at the sheaf-tensor coefficients followed by a multiplication of
sheaves placed in degree `0` is the Čech cup product of the bilinear map on sections** of that
multiplication. -/
theorem cechCupProduct_comp_map_singlePlus
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj (sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus A H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hμ : ∀ (V : (Opens X.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj (sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
          (𝟙 (ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj ((Stacks.Cech.Hypercohomology.singlePlus A F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus A G 0).obj.X 0).val)).app V
            (x ⊗ₜ[A.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {I : Type u} (U : I → Opens X.carrier) (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) :
    Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor A ⊤
        (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj
        (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj U hU ≫
        (totalCechComplexFunctorA A ⊤ U hU).map μ =
      Stacks.Cech.ModuleCupProduct.cechCupProductA A ⊤ U hU
        (Stacks.Cech.Hypercohomology.singlePairingAt 0 0
          (Stacks.Cech.Hypercohomology.bilinearPairing (O := A) β)) := by
  refine cechCupProductA_comp_map A ⊤ U hU
    (Stacks.Cech.SheafTensorPairing.sheafTensorComplexPairing A ⊤
        (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj
        (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj)
    (Stacks.Cech.Hypercohomology.singlePairingAt 0 0
      (Stacks.Cech.Hypercohomology.bilinearPairing (O := A) β)) μ ?_
  intro a b n hab
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    subst hab
    rw [Stacks.Cech.Hypercohomology.singlePairingAt_μ]
    refine NatTrans.ext (funext fun Z => ModuleCat.hom_ext (TensorProduct.ext' fun x y => ?_))
    exact (hμ (op Z.unop.left) x y).symm
  · rw [Stacks.Cech.Hypercohomology.singlePairingAt_μ_of_ne 0 0 _ a b n hab h0]
    have hzT : IsZero (((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u}
        (CoeffRing A ⊤)).obj (((sectionsComplexFunctor A ⊤).obj
          (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj).X a)).obj
        (((sectionsComplexFunctor A ⊤).obj
          (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj).X b)) := by
      by_cases ha : a = 0
      · exact isZero_tensorPresheafModules_right _ _
          ((Stacks.Cech.ModuleCupProduct.sectionsFunctor A ⊤).map_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G b
              fun hb => h0 ⟨ha, hb⟩))
      · exact isZero_tensorPresheafModules_left _
          ((Stacks.Cech.ModuleCupProduct.sectionsFunctor A ⊤).map_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F a ha)) _
    exact hzT.eq_of_src _ _

open Stacks.Cohomology.CechSheaf (abSections) in
/-- The cochain attached to a Čech cochain, as the inclusion of a homogeneous summand. -/
theorem cochainOfAt_eq_comp_ιTotalCechTo
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    {I : Type u} (U : I → Opens X.carrier) (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p) :
    Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c =
      (Stacks.Cech.Hypercohomology.sliceMor U hU F c ≫
        Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing A ⊤)
          (Stacks.Cech.Hypercohomology.singleXIsoAt A F 0 0 rfl).inv p) ≫
        Stacks.Cech.LinearCupProduct.ιTotalCechTo (coverObject U hU) (CoeffRing A ⊤)
          ((sectionsComplexFunctor A ⊤).obj (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj)
          p 0 ((p : ℤ) + 0) rfl :=
  (Category.assoc _ _ _).symm

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- **The cup product of two homogeneous cochains of total Čech complexes in coefficient
degree `0`, followed by a multiplication**, is the Alexander–Whitney product of the two
Čech cochains along the bilinear map of the multiplication. -/
theorem unitTensor_cupPair_cechCupProductSheafTensor_comp_map
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj (sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus A H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hμ : ∀ (V : (Opens X.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj (sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
          (𝟙 (ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj ((Stacks.Cech.Hypercohomology.singlePlus A F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus A G 0).obj.X 0).val)).app V
            (x ⊗ₜ[A.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {I : Type u} (U : I → Opens X.carrier) (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) {r s : ℕ}
    {p q : ℤ} (hp : (r : ℤ) + 0 = p) (hq : (s : ℤ) + 0 = q) (n : ℤ) (hn : p + q = n)
    (x : Stacks.Cech.Hypercohomology.unitModule (CoeffRing A ⊤) ⟶
      ((totalCechComplexFunctorA A ⊤ U hU).obj
        (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj).X p)
    (y : Stacks.Cech.Hypercohomology.unitModule (CoeffRing A ⊤) ⟶
      ((totalCechComplexFunctorA A ⊤ U hU).obj
        (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj).X q)
    (z : Stacks.Cech.Hypercohomology.unitModule (CoeffRing A ⊤) ⟶
      Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU) (CoeffRing A ⊤)
        (((sectionsComplexFunctor A ⊤).obj
          (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj).X 0) r)
    (w : Stacks.Cech.Hypercohomology.unitModule (CoeffRing A ⊤) ⟶
      Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU) (CoeffRing A ⊤)
        (((sectionsComplexFunctor A ⊤).obj
          (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj).X 0) s)
    (hx : x = z ≫ Stacks.Cech.LinearCupProduct.ιTotalCechTo (coverObject U hU) (CoeffRing A ⊤)
      ((sectionsComplexFunctor A ⊤).obj (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj)
      r 0 p hp)
    (hy : y = w ≫ Stacks.Cech.LinearCupProduct.ιTotalCechTo (coverObject U hU) (CoeffRing A ⊤)
      ((sectionsComplexFunctor A ⊤).obj (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj)
      s 0 q hq)
    (t : Stacks.Cech.Hypercohomology.unitModule (CoeffRing A ⊤) ⟶
      Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU) (CoeffRing A ⊤)
        (((sectionsComplexFunctor A ⊤).obj
          (Stacks.Cech.Hypercohomology.singlePlus A H (0 + 0)).obj).X (0 + 0)) (r + s))
    (ht : Stacks.Cech.Hypercohomology.unitTensor A ≫
      Stacks.Cech.CupProduct.tensorModulesMap (CoeffRing A ⊤) z w ≫
      Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU) (CoeffRing A ⊤)
        ((Stacks.Cech.Hypercohomology.singlePairingAt 0 0
          (Stacks.Cech.Hypercohomology.bilinearPairing (O := A) β)).μ 0 0 (0 + 0) rfl) r s = t) :
    Stacks.Cech.Hypercohomology.unitTensor A ≫ Stacks.CupProduct.cupPair
        (Stacks.Cech.CupProduct.tensorModules (CoeffRing A ⊤))
        ((totalCechComplexFunctorA A ⊤ U hU).obj (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj)
        ((totalCechComplexFunctorA A ⊤ U hU).obj (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj)
        p q n hn x y ≫
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor A ⊤
          (Stacks.Cech.Hypercohomology.singlePlus A F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus A G 0).obj U hU).f n ≫
        ((totalCechComplexFunctorA A ⊤ U hU).map μ).f n =
      t ≫ Stacks.Cech.LinearCupProduct.ιTotalCechTo (coverObject U hU) (CoeffRing A ⊤)
        ((sectionsComplexFunctor A ⊤).obj (Stacks.Cech.Hypercohomology.singlePlus A H (0 + 0)).obj)
        (r + s) (0 + 0) n (by push_cast; omega) := by
  subst hx hy ht
  rw [← HomologicalComplex.comp_f, cechCupProduct_comp_map_singlePlus μ β hμ U hU,
    cupPair_ιTotalCechTo_cechCupProductA_zero A ⊤ U hU]
  simp only [Category.assoc]

open Stacks.Cohomology.CechSheaf (abSections) in
/-- The cochain attached to a Čech cochain in an arbitrary total degree, as the inclusion of a
homogeneous summand, with the sheaf placed in degree `0 + 0`. -/
theorem cochainOfAtTo_eq_comp_ιTotalCechTo
    {H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    {I : Type u} (U : I → Opens X.carrier) (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) {p : ℕ}
    (c : CechCochains.Cochain U (abSections H) p) (n : ℤ) (h : (p : ℤ) + (0 + 0) = n) :
    Stacks.Cech.Hypercohomology.cochainOfAtTo U hU H 0 c n h =
      (Stacks.Cech.Hypercohomology.sliceMor U hU H c ≫
        Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing A ⊤)
          (Stacks.Cech.Hypercohomology.singleXIsoAt A H (0 + 0) (0 + 0) rfl).inv p) ≫
        Stacks.Cech.LinearCupProduct.ιTotalCechTo (coverObject U hU) (CoeffRing A ⊤)
          ((sectionsComplexFunctor A ⊤).obj
            (Stacks.Cech.Hypercohomology.singlePlus A H (0 + 0)).obj) p (0 + 0) n h :=
  (Category.assoc _ _ _).symm

open Stacks.Cohomology.CechSheaf (abSections) in
/-- `Stacks.Cech.Hypercohomology.unitTensor_cechAlexanderWhitney_singlePairingAt` in degree `0`,
over the coefficient ring of `Stacks.Cech.ModuleCupProduct`. -/
theorem unitTensor_cechAlexanderWhitney_sliceMor
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (β : Stacks.BilinearMap F.val G.val H.val)
    {I : Type u} (U : I → Opens X.carrier) (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) {r s : ℕ}
    (c : CechCochains.Cochain U (abSections F) r) (e : CechCochains.Cochain U (abSections G) s) :
    Stacks.Cech.Hypercohomology.unitTensor A ≫
      Stacks.Cech.CupProduct.tensorModulesMap (CoeffRing A ⊤)
        (Stacks.Cech.Hypercohomology.sliceMor U hU F c ≫
          Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing A ⊤)
            (Stacks.Cech.Hypercohomology.singleXIsoAt A F 0 0 rfl).inv r)
        (Stacks.Cech.Hypercohomology.sliceMor U hU G e ≫
          Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing A ⊤)
            (Stacks.Cech.Hypercohomology.singleXIsoAt A G 0 0 rfl).inv s) ≫
      Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU) (CoeffRing A ⊤)
        ((Stacks.Cech.Hypercohomology.singlePairingAt 0 0
          (Stacks.Cech.Hypercohomology.bilinearPairing (O := A) β)).μ 0 0 (0 + 0) rfl) r s =
      Stacks.Cech.Hypercohomology.sliceMor U hU H
          (Stacks.Cech.Hypercohomology.cechAWCochain U β c e) ≫
        Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing A ⊤)
          (Stacks.Cech.Hypercohomology.singleXIsoAt A H (0 + 0) (0 + 0) rfl).inv (r + s) :=
  Stacks.Cech.Hypercohomology.unitTensor_cechAlexanderWhitney_singlePairingAt U hU 0 0 β c e

end Pairing


section Cocycles

open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor totalCechComplexFunctorA)
open Stacks.Cohomology.CechSheaf (coverObject abSections)

variable (S : RingedSpace.{u, u}) {I : Type u} (U : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, U i)

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- **The cup product of the cochains attached to two Čech cocycles in degree `0`, followed by a
multiplication**, over `Γ(S, 𝒪_S)`: the cochain attached to their Alexander–Whitney product. -/
theorem cupPair_cochainOfAt_cechCupProductSheafTensor_comp_map
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
        (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hμ : ∀ (V : (Opens S.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
          (sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf S.sheaf)
          (𝟙 (ringSheaf S.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj.X 0).val)).app V
            (x ⊗ₜ[S.sheaf.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (e : CechCochains.Cochain U (abSections G) s)
    :
    Stacks.Cech.Hypercohomology.toMor
          (M := ((Stacks.Cech.CupProduct.tensorModules (baseRing S)).obj
            (ModuleCat.of (baseRing S) (baseRing S))).obj (ModuleCat.of (baseRing S) (baseRing S)))
          ((1 : baseRing S) ⊗ₜ[baseRing S] (1 : baseRing S)) ≫
        Stacks.CupProduct.cupPair (Stacks.Cech.CupProduct.tensorModules (baseRing S))
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0))
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0))
          ((r : ℤ) + 0) ((s : ℤ) + 0) (((r : ℤ) + 0) + ((s : ℤ) + 0)) rfl
          (Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c)
          (Stacks.Cech.Hypercohomology.cochainOfAt U hU G 0 e) ≫
        (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj U hU).f
            (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        ((totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ).f (((r : ℤ) + 0) + ((s : ℤ) + 0)) =
      Stacks.Cech.Hypercohomology.cochainOfAtTo U hU H 0
        (Stacks.Cech.Hypercohomology.cechAWCochain U β c e) (((r : ℤ) + 0) + ((s : ℤ) + 0))
        (by push_cast; ring) := by
  have key := unitTensor_cupPair_cechCupProductSheafTensor_comp_map (X := S) (A := S.sheaf) μ β hμ
    U hU rfl rfl (((r : ℤ) + 0) + ((s : ℤ) + 0)) rfl
    (Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c)
    (Stacks.Cech.Hypercohomology.cochainOfAt U hU G 0 e)
    (Stacks.Cech.Hypercohomology.sliceMor U hU F c ≫
      Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing S.sheaf ⊤)
        (Stacks.Cech.Hypercohomology.singleXIsoAt S.sheaf F 0 0 rfl).inv r)
    (Stacks.Cech.Hypercohomology.sliceMor U hU G e ≫
      Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing S.sheaf ⊤)
        (Stacks.Cech.Hypercohomology.singleXIsoAt S.sheaf G 0 0 rfl).inv s)
    (cochainOfAt_eq_comp_ιTotalCechTo U hU c) (cochainOfAt_eq_comp_ιTotalCechTo U hU e)
    (Stacks.Cech.Hypercohomology.sliceMor U hU H
          (Stacks.Cech.Hypercohomology.cechAWCochain U β c e) ≫
        Stacks.Cech.LinearCupProduct.cechCochainsMap (coverObject U hU) (CoeffRing S.sheaf ⊤)
          (Stacks.Cech.Hypercohomology.singleXIsoAt S.sheaf H (0 + 0) (0 + 0) rfl).inv (r + s))
    (unitTensor_cechAlexanderWhitney_sliceMor β U hU c e)
  exact key.trans (cochainOfAtTo_eq_comp_ιTotalCechTo U hU _ _ _).symm

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- **The Čech cup product of two Čech cocycles in degree `0`, followed by a multiplication, on
cycles**: the cocycle of the total Čech complex of the target attached to their
Alexander–Whitney product. -/
theorem cyclesMap_cechCupProductSheafTensor_comp_iCycles
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
        (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hμ : ∀ (V : (Opens S.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
          (sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf S.sheaf)
          (𝟙 (ringSheaf S.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj.X 0).val)).app V
            (x ⊗ₜ[S.sheaf.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (e : CechCochains.Cochain U (abSections G) s)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).cycles ((r : ℤ) + 0))
    (hz : z ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).iCycles
      ((r : ℤ) + 0) = Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles ((s : ℤ) + 0))
    (hw : w ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
      ((s : ℤ) + 0) = Stacks.Cech.Hypercohomology.cochainOfAt U hU G 0 e)
    (z₀ : (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).cycles
          ((r : ℤ) + 0) ⊗
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          ((s : ℤ) + 0) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)))
    (hz₀ : z₀ ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) =
      ((cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).iCycles
          ((r : ℤ) + 0) ⊗ₘ
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          ((s : ℤ) + 0)) ≫
        HomologicalComplex.ιTensorObj
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0))
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0))
          ((r : ℤ) + 0) ((s : ℤ) + 0) (((r : ℤ) + 0) + ((s : ℤ) + 0)) rfl) :
    ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj U hU)
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        HomologicalComplex.cyclesMap ((totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ)
          (((r : ℤ) + 0) + ((s : ℤ) + 0))) ≫
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0)).iCycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) =
      Stacks.Cech.Hypercohomology.cochainOfAtTo U hU H 0
        (Stacks.Cech.Hypercohomology.cechAWCochain U β c e) (((r : ℤ) + 0) + ((s : ℤ) + 0))
        (by push_cast; ring) :=
  (cyclesMap_comp_iCycles_of_tensorCycles (R := baseRing S)
    (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj U hU)
    ((totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ)
    (Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c)
    (Stacks.Cech.Hypercohomology.cochainOfAt U hU G 0 e) z hz w hw z₀ hz₀).trans
    (cupPair_cochainOfAt_cechCupProductSheafTensor_comp_map S U hU μ β hμ c e)

/-- **A cycle of the total Čech complex lifting the cochain attached to a Čech cocycle has the
class of that Čech cocycle**, read in any equal degree. -/
theorem cechBaseClass_eq_cohomologyCast_cechSheafClass
    {H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)} {p : ℕ}
    (c : CechCochains.Cochain U (abSections H) p)
    (hc : CechCochains.cechD U (abSections H) p c = 0) (n : ℤ) (h : (p : ℤ) + 0 = n)
    (ζ : Stacks.Cech.Hypercohomology.unitModule
        (Stacks.Cohomology.CechSheaf.SectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤) ⟶
      ((Stacks.Cech.Linear.totalCechComplexFunctor S.carrier
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf) ⊤ U
        hU).obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj).cycles n)
    (hζ : ζ ≫ ((Stacks.Cech.Linear.totalCechComplexFunctor S.carrier
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)
        ⊤ U hU).obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj).iCycles n =
      Stacks.Cech.Hypercohomology.cochainOfAtTo U hU H 0 c n h) :
    (ζ ≫ ((Stacks.Cech.Linear.totalCechComplexFunctor S.carrier
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)
        ⊤ U hU).obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj).homologyπ n ≫
        cechBaseClass S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0) n).hom 1 =
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast
        (DerivedCategory.Q.obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj) h).hom
        (cechSheafClass S U hU H c hc) := by
  subst h
  have hζ' := (cancel_mono (HomologicalComplex.iCycles _ _)).1 (hζ.trans
    (HomologicalComplex.liftCycles_i _ (Stacks.Cech.Hypercohomology.cochainOfAt U hU H 0 c)
      ((p : ℤ) + 0 + 1) (CochainComplex.next ℤ _)
      (Stacks.Cech.Hypercohomology.cochainOfAt_d_eq_zero U hU H 0 c hc)).symm)
  subst hζ'
  rw [Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast_rfl]
  rfl

/-- `totalCupPairing_cechBaseClass` followed by a map of complexes. -/
theorem totalCupPairing_cechBaseClass_comp_cohomologyMap
    (K L M : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)))
    (μ : (Stacks.Cech.CupProductSquare.tensorPlus S K L).obj ⟶ M.obj) {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU L).cycles j)
    (z₀ : (cechTotalA S U hU K).cycles i ⊗ (cechTotalA S U hU L).cycles j ⟶
      (cechTotalA S U hU K ⊗ cechTotalA S U hU L).cycles (i + j))
    (hz₀ : z₀ ≫ (cechTotalA S U hU K ⊗ cechTotalA S U hU L).iCycles (i + j) =
      ((cechTotalA S U hU K).iCycles i ⊗ₘ (cechTotalA S U hU L).iCycles j) ≫
        HomologicalComplex.ιTensorObj (cechTotalA S U hU K) (cechTotalA S U hU L) i j (i + j)
          rfl) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫
        ((z ≫ (cechTotalA S U hU K).homologyπ i ≫ cechBaseClass S U hU K i) ⊗ₘ
          (w ≫ (cechTotalA S U hU L).homologyπ j ≫ cechBaseClass S U hU L j)) ≫
        totalCupPairing K.obj L.obj i j ≫
        Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := S) μ (i + j) =
      ((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.obj L.obj U hU)
          (i + j) ≫
        HomologicalComplex.cyclesMap
          ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ) (i + j)) ≫
        (cechTotalA S U hU M).homologyπ (i + j) ≫ cechBaseClass S U hU M (i + j) := by
  have h1 := totalCupPairing_cechBaseClass S U hU K L z w z₀ hz₀
  have h2 := cechBaseClass_comp_cohomologyMap S U hU μ (i + j)
  have h3 := HomologicalComplex.homologyπ_naturality
    ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ) (i + j)
  exact paste_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3.symm

/-- `totalCupPairing_cechBaseClass_comp_cohomologyMap` on elements. -/
theorem totalCupPairing_cechBaseClass_comp_cohomologyMap_apply
    (K L M : CochainComplex.Plus
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)))
    (μ : (Stacks.Cech.CupProductSquare.tensorPlus S K L).obj ⟶ M.obj) {i j : ℤ}
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU K).cycles i)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶ (cechTotalA S U hU L).cycles j)
    (z₀ : (cechTotalA S U hU K).cycles i ⊗ (cechTotalA S U hU L).cycles j ⟶
      (cechTotalA S U hU K ⊗ cechTotalA S U hU L).cycles (i + j))
    (hz₀ : z₀ ≫ (cechTotalA S U hU K ⊗ cechTotalA S U hU L).iCycles (i + j) =
      ((cechTotalA S U hU K).iCycles i ⊗ₘ (cechTotalA S U hU L).iCycles j) ≫
        HomologicalComplex.ιTensorObj (cechTotalA S U hU K) (cechTotalA S U hU L) i j (i + j)
          rfl) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := S) μ (i + j)).hom
      ((totalCupPairing K.obj L.obj i j).hom
        ((z ≫ (cechTotalA S U hU K).homologyπ i ≫ cechBaseClass S U hU K i).hom 1 ⊗ₜ
          (w ≫ (cechTotalA S U hU L).homologyπ j ≫ cechBaseClass S U hU L j).hom 1)) =
      (((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤ K.obj L.obj U hU)
          (i + j) ≫
        HomologicalComplex.cyclesMap
          ((Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ) (i + j)) ≫
        (cechTotalA S U hU M).homologyπ (i + j) ≫ cechBaseClass S U hU M (i + j)).hom 1 := by
  have h := congrArg (fun φ => φ.hom (1 : baseRing S))
    (totalCupPairing_cechBaseClass_comp_cohomologyMap S U hU K L M μ z w z₀ hz₀)
  exact Eq.trans rfl h

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- **The class of the product cycle is the class of the Alexander–Whitney product of the two
Čech cocycles.** -/
theorem cechBaseClass_cyclesMap_cechCupProductSheafTensor_apply
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
        (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hμ : ∀ (V : (Opens S.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
          (sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf S.sheaf)
          (𝟙 (ringSheaf S.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj.X 0).val)).app V
            (x ⊗ₜ[S.sheaf.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (hc : CechCochains.cechD U (abSections F) r c = 0)
    (e : CechCochains.Cochain U (abSections G) s)
    (he : CechCochains.cechD U (abSections G) s e = 0)
    (z : ModuleCat.of (baseRing S) (baseRing S) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).cycles ((r : ℤ) + 0))
    (hz : z ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).iCycles
      ((r : ℤ) + 0) = Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c)
    (w : ModuleCat.of (baseRing S) (baseRing S) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles ((s : ℤ) + 0))
    (hw : w ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
      ((s : ℤ) + 0) = Stacks.Cech.Hypercohomology.cochainOfAt U hU G 0 e)
    (z₀ : (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).cycles
          ((r : ℤ) + 0) ⊗
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          ((s : ℤ) + 0) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)))
    (hz₀ : z₀ ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) =
      ((cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).iCycles
          ((r : ℤ) + 0) ⊗ₘ
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          ((s : ℤ) + 0)) ≫
        HomologicalComplex.ιTensorObj
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0))
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0))
          ((r : ℤ) + 0) ((s : ℤ) + 0) (((r : ℤ) + 0) + ((s : ℤ) + 0)) rfl) :
    (((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (z ⊗ₘ w) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj U hU)
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        HomologicalComplex.cyclesMap ((totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ)
          (((r : ℤ) + 0) + ((s : ℤ) + 0))) ≫
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0)).homologyπ
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        cechBaseClass S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0)
          (((r : ℤ) + 0) + ((s : ℤ) + 0))).hom 1 =
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast
        (DerivedCategory.Q.obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
          (by push_cast; ring)).hom
        (cechSheafClass S U hU H (Stacks.Cech.Hypercohomology.cechAWCochain U β c e)
          (Stacks.Cech.Hypercohomology.cechD_cechAWCochain U hU β c e hc he)) :=
  cechBaseClass_eq_cohomologyCast_cechSheafClass S U hU
    (Stacks.Cech.Hypercohomology.cechAWCochain U β c e)
    (Stacks.Cech.Hypercohomology.cechD_cechAWCochain U hU β c e hc he) _ _ _
    (cyclesMap_cechCupProductSheafTensor_comp_iCycles S U hU μ β hμ c e z hz w hw z₀ hz₀)

/-- **The cycle of the total Čech complex of `ℱ[0]` attached to a Čech cocycle** of `ℱ`, as a
cycle of the total Čech complex over `Γ(S, 𝒪_S)`. -/
def cechCocycleToCycles
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)} {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    ModuleCat.of (baseRing S) (baseRing S) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).cycles
        ((p : ℤ) + 0) :=
  (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).liftCycles
    (Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c) ((p : ℤ) + 0 + 1)
    (CochainComplex.next ℤ _) (Stacks.Cech.Hypercohomology.cochainOfAt_d_eq_zero U hU F 0 c hc)

/-- The cycle attached to a Čech cocycle lifts the cochain attached to it. -/
@[reassoc]
theorem cechCocycleToCycles_iCycles
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)}
    {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cechCocycleToCycles S U hU c hc ≫
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).iCycles
          ((p : ℤ) + 0) =
      Stacks.Cech.Hypercohomology.cochainOfAt U hU F 0 c :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The class of a Čech cocycle is the class of its attached cycle. -/
theorem cechSheafClass_eq_cechCocycleToCycles
    {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)} {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cechSheafClass S U hU F c hc =
      (cechCocycleToCycles S U hU c hc ≫
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).homologyπ
          ((p : ℤ) + 0) ≫
        cechBaseClass S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)
          ((p : ℤ) + 0)).hom 1 :=
  rfl

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- The cup product of the classes of two Čech cocycles, followed by a multiplication, through
the cycles of the total Čech complexes. -/
theorem cohomologyMap_totalCupPairing_cechSheafClass_eq_cycles
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
        (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (_hμ : ∀ (V : (Opens S.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
          (sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf S.sheaf)
          (𝟙 (ringSheaf S.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj.X 0).val)).app V
            (x ⊗ₜ[S.sheaf.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (hc : CechCochains.cechD U (abSections F) r c = 0)
    (e : CechCochains.Cochain U (abSections G) s)
    (he : CechCochains.cechD U (abSections G) s e = 0)
    (z₀ : (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).cycles
          ((r : ℤ) + 0) ⊗
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          ((s : ℤ) + 0) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)))
    (hz₀ : z₀ ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) =
      ((cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).iCycles
          ((r : ℤ) + 0) ⊗ₘ
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          ((s : ℤ) + 0)) ≫
        HomologicalComplex.ιTensorObj
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0))
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0))
          ((r : ℤ) + 0) ((s : ℤ) + 0) (((r : ℤ) + 0) + ((s : ℤ) + 0)) rfl) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := S) μ
        (((r : ℤ) + 0) + ((s : ℤ) + 0))).hom
      ((totalCupPairing (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
        (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj ((r : ℤ) + 0) ((s : ℤ) + 0)).hom
        (cechSheafClass S U hU F c hc ⊗ₜ cechSheafClass S U hU G e he)) =
      (((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((cechCocycleToCycles S U hU c hc) ⊗ₘ
        (cechCocycleToCycles S U hU e he)) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj U hU)
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        HomologicalComplex.cyclesMap ((totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ)
          (((r : ℤ) + 0) + ((s : ℤ) + 0))) ≫
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0)).homologyπ
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        cechBaseClass S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0)
          (((r : ℤ) + 0) + ((s : ℤ) + 0))).hom 1 :=
  (congrArg (fun t => (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := S) μ
      (((r : ℤ) + 0) + ((s : ℤ) + 0))).hom
      ((totalCupPairing (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
        (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj ((r : ℤ) + 0)
          ((s : ℤ) + 0)).hom t))
    (congrArg₂ (· ⊗ₜ ·) (cechSheafClass_eq_cechCocycleToCycles S U hU c hc)
      (cechSheafClass_eq_cechCocycleToCycles S U hU e he))).trans
  (totalCupPairing_cechBaseClass_comp_cohomologyMap_apply S U hU
    (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)
    (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)
    (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0) μ (cechCocycleToCycles S U hU c hc)
    (cechCocycleToCycles S U hU e he) z₀ hz₀)

set_option maxHeartbeats 1000000 in
-- the large composites of total Čech complexes and cup products in this statement are slow to
-- elaborate and unify
/-- The class of the product cycle of two Čech cocycles is the class of their Alexander–Whitney
product. -/
theorem cycles_class_eq_cechSheafClass_cechAWCochain
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
        (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hμ : ∀ (V : (Opens S.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
          (sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf S.sheaf)
          (𝟙 (ringSheaf S.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj.X 0).val)).app V
            (x ⊗ₜ[S.sheaf.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (hc : CechCochains.cechD U (abSections F) r c = 0)
    (e : CechCochains.Cochain U (abSections G) s)
    (he : CechCochains.cechD U (abSections G) s e = 0)
    (z₀ : (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).cycles
          ((r : ℤ) + 0) ⊗
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          ((s : ℤ) + 0) ⟶
      (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).cycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)))
    (hz₀ : z₀ ≫ (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0) ⊗
        cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) =
      ((cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0)).iCycles
          ((r : ℤ) + 0) ⊗ₘ
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)).iCycles
          ((s : ℤ) + 0)) ≫
        HomologicalComplex.ιTensorObj
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0))
          (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0))
          ((r : ℤ) + 0) ((s : ℤ) + 0) (((r : ℤ) + 0) + ((s : ℤ) + 0)) rfl) :
    (((λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ ((cechCocycleToCycles S U hU c hc) ⊗ₘ
        (cechCocycleToCycles S U hU e he)) ≫ z₀ ≫
        HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.cechCupProductSheafTensor S.sheaf ⊤
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
            (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj U hU)
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        HomologicalComplex.cyclesMap ((totalCechComplexFunctorA S.sheaf ⊤ U hU).map μ)
          (((r : ℤ) + 0) + ((s : ℤ) + 0))) ≫
        (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0)).homologyπ
          (((r : ℤ) + 0) + ((s : ℤ) + 0)) ≫
        cechBaseClass S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0)
          (((r : ℤ) + 0) + ((s : ℤ) + 0))).hom 1 =
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast
        (DerivedCategory.Q.obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
          (by push_cast; ring)).hom
        (cechSheafClass S U hU H (Stacks.Cech.Hypercohomology.cechAWCochain U β c e)
          (Stacks.Cech.Hypercohomology.cechD_cechAWCochain U hU β c e hc he)) :=
  cechBaseClass_cyclesMap_cechCupProductSheafTensor_apply S U hU μ β hμ c hc e he _
    (cechCocycleToCycles_iCycles S U hU c hc) _ (cechCocycleToCycles_iCycles S U hU e he) z₀ hz₀

/-- **The cup product of the classes of two Čech cocycles in degree `0`, followed by a
multiplication, is the class of their Alexander–Whitney product**, in the unbounded model of
derived global sections. -/
theorem cohomologyMap_totalCupPairing_cechSheafClass
    {F G H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)}
    (μ : HomologicalComplex.mapBifunctor
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
      (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
        (sheafTensor.{u, u, u, u, u} S.sheaf)
        (ComplexShape.up ℤ) ⟶ (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
    (β : Stacks.BilinearMap F.val G.val H.val)
    (hμ : ∀ (V : (Opens S.carrier)ᵒᵖ) (x : F.val.obj V) (y : G.val.obj V),
      (HomologicalComplex.ιMapBifunctor (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
          (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj
          (sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫ μ.f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf S.sheaf)
          (𝟙 (ringSheaf S.sheaf).obj)).unit.app
          (PresheafOfModules.tensorObj
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj.X 0).val)).app V
            (x ⊗ₜ[S.sheaf.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 H).inv.val.app V
        (β.app V ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom.val.app V y)))
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (hc : CechCochains.cechD U (abSections F) r c = 0)
    (e : CechCochains.Cochain U (abSections G) s)
    (he : CechCochains.cechD U (abSections G) s e = 0) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap (S := S) μ
        (((r : ℤ) + 0) + ((s : ℤ) + 0))).hom
      ((totalCupPairing (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0).obj
        (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0).obj ((r : ℤ) + 0) ((s : ℤ) + 0)).hom
        (cechSheafClass S U hU F c hc ⊗ₜ cechSheafClass S U hU G e he)) =
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast
        (DerivedCategory.Q.obj (Stacks.Cech.Hypercohomology.singlePlus S.sheaf H 0).obj)
          (by push_cast; ring)).hom
        (cechSheafClass S U hU H (Stacks.Cech.Hypercohomology.cechAWCochain U β c e)
          (Stacks.Cech.Hypercohomology.cechD_cechAWCochain U hU β c e hc he)) := by
  obtain ⟨z₀, hz₀⟩ := RingTheory.TorProducts.exists_tensorCycles
    (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf F 0))
    (cechTotalA S U hU (Stacks.Cech.Hypercohomology.singlePlus S.sheaf G 0)) ((r : ℤ) + 0)
    ((s : ℤ) + 0)
  exact (cohomologyMap_totalCupPairing_cechSheafClass_eq_cycles S U hU μ β hμ c hc e he z₀
    hz₀).trans
    (cycles_class_eq_cechSheafClass_cechAWCochain S U hU μ β hμ c hc e he z₀ hz₀)

end Cocycles

section Hodge

open AlgebraicGeometry.SheafOfModules (deRhamTerm moduleOfDifferentials formProduct
  exteriorProductComponent hodgeCohomologyComponent hodgeComponentCup baseRingedSpace)
open Stacks.Cohomology.CechSheaf (abSections)

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- **The wedge product `Ω^p × Ω^{p'} ⟶ Ω^{p + p'}` on sections**, as a bilinear map of
presheaves of modules over the base ring sheaf. -/
def formsWedgeBilinear (p p' : ℕ) :
    Stacks.BilinearMap (deRhamTerm B p).val (deRhamTerm B p').val (deRhamTerm B (p + p')).val :=
  Stacks.BilinearMap.restrictScalars
    (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ := φ)).hom
    (B.exterior.mul (p : ℤ) (p' : ℤ))

/-- The wedge bilinear map is the wedge product of forms. -/
@[simp]
theorem formsWedgeBilinear_app (p p' : ℕ) (V : (Opens X.carrier)ᵒᵖ)
    (x : (deRhamTerm B p).val.obj V) (y : (deRhamTerm B p').val.obj V) :
    (formsWedgeBilinear B p p').app V x y = formProduct B p p' V x y :=
  rfl

variable {I : Type u} (U : I → Opens X.carrier)

/-- **The Alexander–Whitney wedge product of Čech cochains of differential forms**:
`(c ∪ e)_{s₀ … s_{q+q'}} = c_{s₀ … s_q} ∧ e_{s_q … s_{q+q'}}`, the two factors restricted to
`U_{s₀} ∩ ⋯ ∩ U_{s_{q+q'}}`. -/
def wedgeCup {p p' q q' : ℕ} (c : CechCochains.Cochain U (abSections (deRhamTerm B p)) q)
    (e : CechCochains.Cochain U (abSections (deRhamTerm B p')) q') :
    CechCochains.Cochain U (abSections (deRhamTerm B (p + p'))) (q + q') :=
  Stacks.Cech.Hypercohomology.cechAWCochain U (formsWedgeBilinear B p p') c e

/-- The value of the wedge product of Čech cochains on a tuple of indices: the wedge product of
the value of the first cochain on the front face and of the second on the back face, both
restricted to the intersection. -/
theorem wedgeCup_apply {p p' q q' : ℕ} (c : CechCochains.Cochain U (abSections (deRhamTerm B p)) q)
    (e : CechCochains.Cochain U (abSections (deRhamTerm B p')) q') (t : Fin (q + q' + 1) → I) :
    wedgeCup B U c e t = formProduct B p p' (op (⨅ j, U (t j)))
      (Stacks.Cohomology.Basis.res (abSections (deRhamTerm B p))
        (Stacks.Cech.Hypercohomology.cechInter_le_reindex U t _)
        (c (t ∘ Stacks.Cech.LinearCupProduct.frontIdx q (q + q') (by omega))))
      (Stacks.Cohomology.Basis.res (abSections (deRhamTerm B p'))
        (Stacks.Cech.Hypercohomology.cechInter_le_reindex U t _)
        (e (t ∘ Stacks.Cech.LinearCupProduct.backIdx q q' (q + q') le_rfl))) :=
  rfl

/-- **The wedge product of two Čech cocycles is a Čech cocycle.** -/
theorem cechD_wedgeCup (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) {p p' q q' : ℕ}
    {c : CechCochains.Cochain U (abSections (deRhamTerm B p)) q}
    {e : CechCochains.Cochain U (abSections (deRhamTerm B p')) q'}
    (hc : CechCochains.cechD U (abSections (deRhamTerm B p)) q c = 0)
    (he : CechCochains.cechD U (abSections (deRhamTerm B p')) q' e = 0) :
    CechCochains.cechD U (abSections (deRhamTerm B (p + p'))) (q + q') (wedgeCup B U c e) = 0 :=
  Stacks.Cech.Hypercohomology.cechD_cechAWCochain U hU _ c e hc he

/-- On a local pure tensor in degree `0`, the wedge product of complexes concentrated in degree
`0` is the wedge bilinear map. -/
theorem singleIntMultiplication_exteriorProductComponent_val_app (p p' : ℕ)
    (V : (Opens X.carrier)ᵒᵖ)
    (x : (deRhamTerm B p).val.obj V) (y : (deRhamTerm B p').val.obj V) :
    (HomologicalComplex.ιMapBifunctor
        (Stacks.Cech.Hypercohomology.singlePlus A (deRhamTerm B p) 0).obj
        (Stacks.Cech.Hypercohomology.singlePlus A (deRhamTerm B p') 0).obj
        (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ) 0 0 0 (add_zero 0) ≫
        (singleIntMultiplication (exteriorProductComponent B p p')).f 0).val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
          (𝟙 (ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj
            ((Stacks.Cech.Hypercohomology.singlePlus A (deRhamTerm B p) 0).obj.X 0).val
            ((Stacks.Cech.Hypercohomology.singlePlus A (deRhamTerm B p') 0).obj.X 0).val)).app V
            (x ⊗ₜ[A.obj.obj V] y)) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (deRhamTerm B (p + p'))).inv.val.app V
        ((formsWedgeBilinear B p p').app V
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (deRhamTerm B p)).hom.val.app V x)
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (deRhamTerm B p')).hom.val.app V y)) :=
  (singleIntMultiplication_val_app _ V x y).trans (congrArg _
    (AlgebraicGeometry.SheafOfModules.exteriorProductComponent_unit_apply B p p' V _ _))

/-- Reindexing the degree of a Hodge cohomology class is the identification of the two
cohomology modules. -/
theorem reindexHodgeDeg_eq_cohomologyCast {p : ℕ} {a b : ℤ} (h : a = b)
    (x : hodgeCohomologyComponent B p a) :
    AlgebraicGeometry.SheafOfModules.reindexHodgeDeg B h x =
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast (S := baseRingedSpace A)
        (DerivedCategory.Q.obj
          (Stacks.Cech.Hypercohomology.singlePlus A (deRhamTerm (X := X) B p) 0).obj)
          h).hom x := by
  subst h
  rfl

/-- **The cup product of Section 0FKU of the classes of two Čech cocycles of differential forms,
along the wedge product, is the class of their Alexander–Whitney wedge product.** -/
theorem hodgeComponentCup_cechSheafClass (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) (p p' : ℕ)
    {q q' : ℕ} (c : CechCochains.Cochain U (abSections (deRhamTerm B p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm B p)) q c = 0)
    (e : CechCochains.Cochain U (abSections (deRhamTerm B p')) q')
    (he : CechCochains.cechD U (abSections (deRhamTerm B p')) q' e = 0) :
    hodgeComponentCup B (exteriorProductComponent B p p') (q : ℤ) (q' : ℤ)
        (cechSheafClass (baseRingedSpace A) U hU (deRhamTerm (X := X) B p) c hc)
        (cechSheafClass (baseRingedSpace A) U hU (deRhamTerm (X := X) B p') e he) =
      AlgebraicGeometry.SheafOfModules.reindexHodgeDeg B (Nat.cast_add q q')
        (cechSheafClass (baseRingedSpace A) U hU (deRhamTerm (X := X) B (p + p')) (wedgeCup B U c e)
          (cechD_wedgeCup B U hU hc he)) := by
  refine (hodgeComponentCup_eq_totalCupPairing B _ _ _ _ _).trans
    (Eq.trans ?_ (reindexHodgeDeg_eq_cohomologyCast B _ _).symm)
  exact cohomologyMap_totalCupPairing_cechSheafClass (baseRingedSpace A) U hU
    (singleIntMultiplication (exteriorProductComponent B p p')) (formsWedgeBilinear B p p')
    (singleIntMultiplication_exteriorProductComponent_val_app B p p') c hc e he

end Hodge

section Scheme

open AlgebraicGeometry.SheafOfModules (deRhamTerm hodgeCohomologyCup reindexHodgeDeg)
open Stacks.Cohomology.CechSheaf (abSections)

variable {X S : Scheme.{u}} (f : X ⟶ S) {I : Type u} (U : I → X.Opens)
  (hU : (⊤ : X.Opens) = ⨆ i, U i)

/-- **The Hodge cup product of the classes of two Čech cocycles is, up to the Koszul sign
`(-1)^{q p'}`, the class of their Alexander–Whitney wedge product.**  For a Čech `q`-cocycle `c`
of `Ω^p_{X/S}` and a Čech `q'`-cocycle `e` of `Ω^{p'}_{X/S}` on an open covering `𝒰` of `X`,

`[c] ∪ [e] = (-1)^{q p'} [c ∪ e] ∈ H^{q + q'}(X, Ω^{p + p'}_{X/S})`,

where `(c ∪ e)_{s₀ … s_{q+q'}} = c_{s₀ … s_q} ∧ e_{s_q … s_{q+q'}}` (`wedgeCup`).  The sign is the
Koszul sign built into the Hodge cup product `hodgeCohomologyCup`; the Čech cup product of two
cocycles of sheaves placed in degree `0` carries no sign. -/
theorem hodgeCohomologyCup_hodgeCechClass (p p' : ℕ) {q q' : ℕ}
    (c : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p)) q)
    (hc : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p)) q c = 0)
    (e : CechCochains.Cochain U (abSections (deRhamTerm (formsAlgebras f) p')) q')
    (he : CechCochains.cechD U (abSections (deRhamTerm (formsAlgebras f) p')) q' e = 0) :
    hodgeCohomologyCup (formsAlgebras f) p p' q q' (hodgeCechClass f U hU p c hc)
        (hodgeCechClass f U hU p' e he) =
      (((q : ℤ) * p').negOnePow : ℤ) • reindexHodgeDeg (formsAlgebras f) (Nat.cast_add q q')
        (hodgeCechClass f U hU (p + p') (wedgeCup (formsAlgebras f) U c e)
          (cechD_wedgeCup (formsAlgebras f) U hU hc he)) :=
  congrArg ((((q : ℤ) * p').negOnePow : ℤ) • ·)
    (hodgeComponentCup_cechSheafClass (formsAlgebras f) U hU p p' c hc e he)

end Scheme

end Stacks.HodgeWeil

end
