module

public import StacksFrontier.Topology.Sheaves.Cohomology.KunnethOnSections.RelativeNaive
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapAlongCrossing

/-!
# The crossing Künneth map on degreewise direct images

In `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMapAlongCrossing` the
relative Künneth map of a square of ringed spaces is compared with that of a second square along
morphisms `τ_X : X ⟶ X'`, `τ_Y : Y ⟶ Y'`, `τ_W : W ⟶ W'`; the comparison is the abstract
Künneth map of `Lτ_W^* ⊣ Rτ_{W,*}` with the *crossing legs*
`Lτ_W^*Lp'^*Rτ_{X,*} ≅ L(p ≫ τ_X)^*Rτ_{X,*} ⟶ Lp^*`.  This file computes that map on
degreewise direct images, as
`StacksFrontier.Topology.Sheaves.Cohomology.KunnethOnSections.RelativeNaive`
does for the relative Künneth map: restricted along `τ_{X,*} ⟶ Rτ_{X,*}` and
`τ_{Y,*} ⟶ Rτ_{Y,*}` and followed by the comparisons `Lp^* ⟶ p^*`, `Lq^* ⟶ q^*` and `⊗^𝐋 ⟶ ⊗`, it
is the comparisons `Lp'^* ⟶ p'^*`, `Lq'^* ⟶ q'^*` and `⊗^𝐋 ⟶ ⊗` followed by the *naive* crossing
map `Tot(p'^*τ_{X,*}𝒦 ⊗ q'^*τ_{Y,*}ℳ) ⟶ τ_{W,*}Tot(p^*𝒦 ⊗ q^*ℳ)` and by `τ_{W,*} ⟶ Rτ_{W,*}`.

## Main results

* `Stacks.Cohomology.KunnethNaive.homEquiv_bitensor_hexagon`: the abstract hexagon, with the
  legs given at a single pair of objects.
* `Stacks.Cohomology.KunnethNaive.crossingKunneth_naive`: the statement above.

## References

* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
* [Stacks Project, Tag 0FP0](https://stacks.math.columbia.edu/tag/0FP0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.DerivedKunneth
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.Tensor
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.KunnethNaive

section Abstract

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
  (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The abstract hexagon at a single pair of objects.**  The transpose under `L ⊣ R` of
`α ≫ B(bX, bY)` at `(x₀, y₀)`, restricted along `ηa`, `ηb` and followed by `R(B(xa, xb) ≫ tX)`,
is the route `tY ≫ ν ≫ ηT`, as soon as the transposed diagram commutes. -/
theorem homEquiv_bitensor_hexagon {x₀ y₀ : C} {X₁ Y₁ : D} (bX : L.obj x₀ ⟶ X₁)
    (bY : L.obj y₀ ⟶ Y₁) {a b S S' : C} {T Ga Gb Pa Pb PS PT N : D}
    (ηa : a ⟶ x₀) (ηb : b ⟶ y₀) (tY : A.obj (a, b) ⟶ S) (ν : S ⟶ S') (ηT : S' ⟶ R.obj T)
    (xa : X₁ ⟶ Ga) (xb : Y₁ ⟶ Gb) (tX : B.obj (Ga, Gb) ⟶ T)
    (ca : L.obj a ⟶ Pa) (qa : Pa ⟶ Ga) (cb : L.obj b ⟶ Pb) (qb : Pb ⟶ Gb)
    (cS : L.obj S ⟶ PS) (cT : L.obj S' ⟶ PT) (qT : PT ⟶ T) (nT : PS ⟶ PT)
    (w : PS ⟶ N) (m : N ⟶ T) (tXp : B.obj (Pa, Pb) ⟶ N)
    (hga : L.map ηa ≫ bX ≫ xa = ca ≫ qa) (hgb : L.map ηb ≫ bY ≫ xb = cb ≫ qb)
    (hgT : L.map ηT ≫ adj.counit.app T = cT ≫ qT)
    (hν : L.map ν ≫ cT = cS ≫ nT) (hn : nT ≫ qT = w ≫ m)
    (h0 : L.map tY ≫ cS ≫ w = α.app (a, b) ≫ B.map (ca ×ₘ cb) ≫ tXp)
    (ht : tXp ≫ m = B.map (qa ×ₘ qb) ≫ tX) :
    tY ≫ ν ≫ ηT =
      A.map (ηa ×ₘ ηb) ≫ adj.homEquiv _ _ (α.app (x₀, y₀) ≫ B.map (bX ×ₘ bY)) ≫
        R.map (B.map (xa ×ₘ xb) ≫ tX) := by
  have hB : B.map ((L.map ηa ≫ bX) ×ₘ (L.map ηb ≫ bY)) ≫ B.map (xa ×ₘ xb) =
      B.map (ca ×ₘ cb) ≫ B.map (qa ×ₘ qb) := by
    rw [← B.map_comp, ← B.map_comp, prod_comp, prod_comp, Category.assoc, Category.assoc, hga,
      hgb]
  have hα := α.naturality (ηa ×ₘ ηb)
  change L.map (A.map (ηa ×ₘ ηb)) ≫ α.app (x₀, y₀) =
    α.app (a, b) ≫ B.map (L.map ηa ×ₘ L.map ηb) at hα
  refine (adj.homEquiv _ _).symm.injective ?_
  have hR : (adj.homEquiv _ _).symm (A.map (ηa ×ₘ ηb) ≫
        adj.homEquiv _ _ (α.app (x₀, y₀) ≫ B.map (bX ×ₘ bY)) ≫
        R.map (B.map (xa ×ₘ xb) ≫ tX)) =
      α.app (a, b) ≫ B.map ((L.map ηa ≫ bX) ×ₘ (L.map ηb ≫ bY)) ≫
        B.map (xa ×ₘ xb) ≫ tX := by
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
    simp only [Category.assoc]
    rw [reassoc_of% hα, ← B.map_comp_assoc, prod_comp]
  rw [hR, reassoc_of% hB, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit, hgT, reassoc_of% hν, hn,
    reassoc_of% h0, ht]

end Abstract

/-! ### The geometric statement -/

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

section Crossing

variable {X X' Y Y' W W' : RingedSpace.{u, u}} (τX : X ⟶ X') (τY : Y ⟶ Y') (τW : W ⟶ W')
  (p : W ⟶ X) (q : W ⟶ Y) (p' : W' ⟶ X') (q' : W' ⟶ Y')
  (hpsq : τW ≫ p' = p ≫ τX) (hqsq : τW ≫ q' = q ≫ τY)
  (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
  (M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)

/-- **The degreewise crossing leg** `τ_W^*p'^*τ_{X,*}𝒦 ⟶ p^*𝒦`: the composition isomorphism of
degreewise pullbacks for `(τ_W, p')` followed by the degreewise counit leg of `τ_X` at the
factorization `p ≫ τ_X = τ_W ≫ p'`. -/
def naiveCrossingLeg :
    (pullbackComplex τW).obj ((pullbackComplex p').obj ((pushforwardComplex τX).obj K)) ⟶
      (pullbackComplex p).obj K :=
  (Stacks.PullbackTensorComposition.pullbackComplexCompIso τW p').hom.app
      ((pushforwardComplex τX).obj K) ≫
    naiveCounitLeg τX p (τW ≫ p') hpsq.symm K

/-- The chase behind `crossingLeg_naive`, every object and morphism a variable. -/
private theorem chase_crossingLeg {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ : C}
    {lφ : A₀ ⟶ A₁} {cB : A₁ ⟶ A₂} {leg : A₂ ⟶ A₃} {d : A₃ ⟶ A₄} {cA : A₀ ⟶ A₅}
    {Lφ : A₅ ⟶ A₂} {dc : A₅ ⟶ A₆} {nl : A₆ ⟶ A₄} {d₁ : A₀ ⟶ A₇} {d₂ : A₇ ⟶ A₈}
    {pc : A₈ ⟶ A₆} {qa : A₈ ⟶ A₄}
    (n1 : lφ ≫ cB = cA ≫ Lφ) (n2 : Lφ ≫ leg ≫ d = dc ≫ nl) (n3 : cA ≫ dc = d₁ ≫ d₂ ≫ pc)
    (n4 : qa = pc ≫ nl) :
    lφ ≫ (cB ≫ leg) ≫ d = (d₁ ≫ d₂) ≫ qa := by
  rw [n4, Category.assoc, Category.assoc, reassoc_of% n1, n2, reassoc_of% n3]

/-- **The derived crossing leg against the degreewise one**: `Lτ_W^*Lp'^*` of
`τ_{X,*} ⟶ Rτ_{X,*}`, followed by the crossing leg and `Lp^* ⟶ p^*`, is `Lτ_W^*` of
`Lp'^* ⟶ p'^*` and `Lτ_W^* ⟶ τ_W^*` followed by the degreewise crossing leg. -/
theorem crossingLeg_naive :
    (derivedPullback τW).map ((derivedPullback p').map (pushforwardComparisonQ τX K)) ≫
        ((derivedPullbackCompIsoCanonical τW p').hom.app
            ((derivedPushforward τX).obj (DerivedCategory.Q.obj K)) ≫
          (pullbackCounitLeg τX p (τW ≫ p') hpsq.symm).app (DerivedCategory.Q.obj K)) ≫
        (derivedPullbackNatTrans p).app K =
      ((derivedPullback τW).map
          ((derivedPullbackNatTrans p').app ((pushforwardComplex τX).obj K)) ≫
        (derivedPullbackNatTrans τW).app
          ((pullbackComplex p').obj ((pushforwardComplex τX).obj K))) ≫
        DerivedCategory.Q.map (naiveCrossingLeg τX τW p p' hpsq K) :=
  chase_crossingLeg
    ((derivedPullbackCompIsoCanonical τW p').hom.naturality (pushforwardComparisonQ τX K))
    (counitLeg_naive τX p (τW ≫ p') hpsq.symm K)
    (derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans τW p'
      ((pushforwardComplex τX).obj K))
    (DerivedCategory.Q.map_comp _ _)

variable [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The naive crossing map** `Tot(p'^*τ_{X,*}𝒦 ⊗ q'^*τ_{Y,*}ℳ) ⟶ τ_{W,*}Tot(p^*𝒦 ⊗ q^*ℳ)`,
the adjoint transpose under `τ_W^* ⊣ τ_{W,*}` of the comparison of total tensor complexes of
[Stacks, Tag 01CD] followed by the two degreewise crossing legs. -/
def naiveCrossing :
    (totalComplexPair (sheafTensor W'.sheaf)).obj
        ((pullbackComplex p').obj ((pushforwardComplex τX).obj K),
          (pullbackComplex q').obj ((pushforwardComplex τY).obj M)) ⟶
      (pushforwardComplex τW).obj ((totalComplexPair (sheafTensor W.sheaf)).obj
        ((pullbackComplex p).obj K, (pullbackComplex q).obj M)) :=
  (complexAdjunction τW).homEquiv _ _
    ((pullbackTensorComplexNatIso τW).hom.app
        ((pullbackComplex p').obj ((pushforwardComplex τX).obj K),
          (pullbackComplex q').obj ((pushforwardComplex τY).obj M)) ≫
      (totalComplexPair (sheafTensor W.sheaf)).map
        (naiveCrossingLeg τX τW p p' hpsq K ×ₘ naiveCrossingLeg τY τW q q' hqsq M))

/-- `τ_W^*` of the naive crossing map followed by the counit is its transpose, read in the
derived category. -/
theorem naiveCrossing_counit_square_Q :
    DerivedCategory.Q.map ((pullbackComplex τW).map
        (naiveCrossing τX τY τW p q p' q' hpsq hqsq K M)) ≫
        DerivedCategory.Q.map ((complexAdjunction τW).counit.app
          ((totalComplexPair (sheafTensor W.sheaf)).obj
            ((pullbackComplex p).obj K, (pullbackComplex q).obj M))) =
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso τW).hom.app
          ((pullbackComplex p').obj ((pushforwardComplex τX).obj K),
            (pullbackComplex q').obj ((pushforwardComplex τY).obj M))) ≫
        DerivedCategory.Q.map ((totalComplexPair (sheafTensor W.sheaf)).map
          (naiveCrossingLeg τX τW p p' hpsq K ×ₘ naiveCrossingLeg τY τW q q' hqsq M)) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.Q.map ·)
      (Equiv.symm_apply_apply ((complexAdjunction τW).homEquiv _ _) _)).trans
      (DerivedCategory.Q.map_comp _ _))

/-- A functor out of a product category carries a componentwise composite to the composite. -/
private theorem map_prod_comp {C D : Type*} [Category C] [Category D] (F : C × C ⥤ D)
    {a a' a'' b b' b'' : C} (f : a ⟶ a') (f' : a' ⟶ a'') (g : b ⟶ b') (g' : b' ⟶ b'') :
    F.map ((f ≫ f') ×ₘ (g ≫ g')) = F.map (f ×ₘ g) ≫ F.map (f' ×ₘ g') := by
  rw [← F.map_comp, prod_comp]

/-- The chase behind `crossing_toTensor_square`, every object and morphism a variable. -/
private theorem chase_toTensor {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ : C}
    (LX : A₀ ⟶ A₁) (LY : A₁ ⟶ A₂) (z : A₂ ⟶ A₃) (w : A₃ ⟶ A₄) (LXY : A₀ ⟶ A₂)
    (hLXY : LXY = LX ≫ LY) (μ₀ : A₁ ⟶ B₁) (bd : B₁ ⟶ B₂) (tt : B₂ ⟶ A₄) (μ : A₀ ⟶ B₀)
    (bL : B₀ ⟶ B₁) (bc : B₀ ⟶ B₂) (h0 : LY ≫ z ≫ w = μ₀ ≫ bd ≫ tt)
    (hn : LX ≫ μ₀ = μ ≫ bL) (hc : bc = bL ≫ bd) :
    LXY ≫ z ≫ w = μ ≫ bc ≫ tt := by
  rw [hLXY, hc, Category.assoc, h0, reassoc_of% hn, Category.assoc]

/-- [Stacks, Tag 0FP0] at the pair of degreewise inverse images, with the comparisons
`Lp'^* ⟶ p'^*` and `Lq'^* ⟶ q'^*` in front. -/
theorem crossing_toTensor_square :
    (derivedPullback τW).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf)).map
            ((derivedPullbackNatTrans p').app ((pushforwardComplex τX).obj K) ×ₘ
              (derivedPullbackNatTrans q').app ((pushforwardComplex τY).obj M)) ≫
          (derivedToTensorNatTrans W').app
            ((pullbackComplex p').obj ((pushforwardComplex τX).obj K),
              (pullbackComplex q').obj ((pushforwardComplex τY).obj M))) ≫
        (derivedPullbackNatTrans τW).app ((totalComplexPair (sheafTensor W'.sheaf)).obj
          ((pullbackComplex p').obj ((pushforwardComplex τX).obj K),
            (pullbackComplex q').obj ((pushforwardComplex τY).obj M))) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso τW).hom.app
            ((pullbackComplex p').obj ((pushforwardComplex τX).obj K),
              (pullbackComplex q').obj ((pushforwardComplex τY).obj M))) =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison τW).app
          ((derivedPullback p').obj (DerivedCategory.Q.obj ((pushforwardComplex τX).obj K)),
            (derivedPullback q').obj (DerivedCategory.Q.obj ((pushforwardComplex τY).obj M))) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            (((derivedPullback τW).map
                ((derivedPullbackNatTrans p').app ((pushforwardComplex τX).obj K)) ≫
              (derivedPullbackNatTrans τW).app
                ((pullbackComplex p').obj ((pushforwardComplex τX).obj K))) ×ₘ
            ((derivedPullback τW).map
                ((derivedPullbackNatTrans q').app ((pushforwardComplex τY).obj M)) ≫
              (derivedPullbackNatTrans τW).app
                ((pullbackComplex q').obj ((pushforwardComplex τY).obj M)))) ≫
          (derivedToTensorNatTrans W).app
            ((pullbackComplex τW).obj ((pullbackComplex p').obj ((pushforwardComplex τX).obj K)),
              (pullbackComplex τW).obj
                ((pullbackComplex q').obj ((pushforwardComplex τY).obj M))) :=
  chase_toTensor _ _ _ _ _ (Functor.map_comp _ _ _) _ _ _ _ _ _
    (derivedPullbackTensorIso_toTensor_comm τW
      ((pullbackComplex p').obj ((pushforwardComplex τX).obj K))
      ((pullbackComplex q').obj ((pushforwardComplex τY).obj M))).symm
    ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison τW).naturality
      ((derivedPullbackNatTrans p').app ((pushforwardComplex τX).obj K) ×ₘ
        (derivedPullbackNatTrans q').app ((pushforwardComplex τY).obj M)))
    (map_prod_comp _ _ _ _ _)

omit [HasSheafify (Opens.grothendieckTopology W'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The canonical map `⊗^𝐋 ⟶ ⊗` is natural along the two degreewise crossing legs. -/
theorem derivedToTensor_naturality_crossingLegs :
    (derivedToTensorNatTrans W).app
          ((pullbackComplex τW).obj ((pullbackComplex p').obj ((pushforwardComplex τX).obj K)),
            (pullbackComplex τW).obj ((pullbackComplex q').obj ((pushforwardComplex τY).obj M))) ≫
        DerivedCategory.Q.map ((totalComplexPair (sheafTensor W.sheaf)).map
          (naiveCrossingLeg τX τW p p' hpsq K ×ₘ naiveCrossingLeg τY τW q q' hqsq M)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
          (DerivedCategory.Q.map (naiveCrossingLeg τX τW p p' hpsq K) ×ₘ
            DerivedCategory.Q.map (naiveCrossingLeg τY τW q q' hqsq M)) ≫
        (derivedToTensorNatTrans W).app ((pullbackComplex p).obj K, (pullbackComplex q).obj M) :=
  ((derivedToTensorNatTrans W).naturality
    (naiveCrossingLeg τX τW p p' hpsq K ×ₘ naiveCrossingLeg τY τW q q' hqsq M)).symm

/-- **The crossing Künneth map on degreewise direct images.**  The comparisons
`τ_{X,*} ⟶ Rτ_{X,*}` and `τ_{Y,*} ⟶ Rτ_{Y,*}` followed by the abstract Künneth map of
`Lτ_W^* ⊣ Rτ_{W,*}` with the crossing legs and by `Rτ_{W,*}` of the comparisons `Lp^* ⟶ p^*`,
`Lq^* ⟶ q^*` and `⊗^𝐋 ⟶ ⊗`, is the comparisons `Lp'^* ⟶ p'^*`, `Lq'^* ⟶ q'^*` and `⊗^𝐋 ⟶ ⊗`
followed by the naive crossing map and the comparison `τ_{W,*} ⟶ Rτ_{W,*}`. -/
theorem crossingKunneth_naive :
    ((Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf)).map
          ((derivedPullbackNatTrans p').app ((pushforwardComplex τX).obj K) ×ₘ
            (derivedPullbackNatTrans q').app ((pushforwardComplex τY).obj M)) ≫
        (derivedToTensorNatTrans W').app
          ((pullbackComplex p').obj ((pushforwardComplex τX).obj K),
            (pullbackComplex q').obj ((pushforwardComplex τY).obj M))) ≫
      DerivedCategory.Q.map (naiveCrossing τX τY τW p q p' q' hpsq hqsq K M) ≫
      pushforwardComparisonQ τW ((totalComplexPair (sheafTensor W.sheaf)).obj
        ((pullbackComplex p).obj K, (pullbackComplex q).obj M)) =
    (Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf)).map
        ((derivedPullback p').map (pushforwardComparisonQ τX K) ×ₘ
          (derivedPullback q').map (pushforwardComparisonQ τY M)) ≫
      (derivedAdjunction τW).homEquiv _ _
        ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison τW).app
            ((derivedPullback p').obj ((derivedPushforward τX).obj (DerivedCategory.Q.obj K)),
              (derivedPullback q').obj ((derivedPushforward τY).obj (DerivedCategory.Q.obj M))) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            (((derivedPullbackCompIsoCanonical τW p').hom.app
                ((derivedPushforward τX).obj (DerivedCategory.Q.obj K)) ≫
              (pullbackCounitLeg τX p (τW ≫ p') hpsq.symm).app (DerivedCategory.Q.obj K)) ×ₘ
            ((derivedPullbackCompIsoCanonical τW q').hom.app
                ((derivedPushforward τY).obj (DerivedCategory.Q.obj M)) ≫
              (pullbackCounitLeg τY q (τW ≫ q') hqsq.symm).app (DerivedCategory.Q.obj M)))) ≫
      (derivedPushforward τW).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((derivedPullbackNatTrans p).app K ×ₘ (derivedPullbackNatTrans q).app M) ≫
          (derivedToTensorNatTrans W).app ((pullbackComplex p).obj K, (pullbackComplex q).obj M)) :=
  homEquiv_bitensor_hexagon (derivedAdjunction τW)
    (Functor.uncurry.obj (derivedTensorProductFunctor W'.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison τW)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (crossingLeg_naive τX τW p p' hpsq K) (crossingLeg_naive τY τW q q' hqsq M)
    (derivedCounit_pushforwardComparisonQ τW _)
    ((derivedPullbackNatTrans τW).naturality _)
    (naiveCrossing_counit_square_Q τX τY τW p q p' q' hpsq hqsq K M)
    (crossing_toTensor_square τX τY τW p' q' K M)
    (derivedToTensor_naturality_crossingLegs τX τY τW p q p' q' hpsq hqsq K M)

end Crossing

end Stacks.Cohomology.KunnethNaive

end
