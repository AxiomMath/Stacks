module

public import
    StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMap
public import
    StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackNatTransAlongAComposite

/-!
# The relative Künneth map on degreewise direct images

Let `a : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, `b : (Y, 𝒪_Y) ⟶ (S, 𝒪_S)`, `p : W ⟶ X` and `q : W ⟶ Y` be
morphisms of ringed spaces with `p ≫ a = f = q ≫ b`, and let `𝒦^•`, `ℳ^•` be complexes of
`𝒪_X`- and `𝒪_Y`-modules.  The relative Künneth map of [Stacks, Tag 0FLP],

`Ra_*𝒦^• ⊗^𝐋_{𝒪_S} Rb_*ℳ^• ⟶ Rf_*(Lp^*𝒦^• ⊗^𝐋_{𝒪_W} Lq^*ℳ^•)`,

restricted along the comparisons `a_* ⟶ Ra_*` and `b_* ⟶ Rb_*` and followed by the comparisons
`Lp^* ⟶ p^*`, `Lq^* ⟶ q^*` and `⊗^𝐋 ⟶ ⊗`, is the *naive* Künneth map

`Tot(a_*𝒦^• ⊗_{𝒪_S} b_*ℳ^•) ⟶ f_*Tot(p^*𝒦^• ⊗_{𝒪_W} q^*ℳ^•)`

of degreewise pullbacks and pushforwards followed by `f_* ⟶ Rf_*`.  This is the analogue for the
Künneth map of [Stacks, Tag 0FP3], which is the case `p = q = 𝟙` of the relative cup product.

## Main definitions

* `Stacks.Cohomology.KunnethNaive.naiveCounitLeg`: the degreewise leg `f^*a_* ⟶ p^*`, the
  composition isomorphism of degreewise pullbacks followed by `p^*` of the counit of `a^* ⊣ a_*`.
* `Stacks.Cohomology.KunnethNaive.naiveKunneth`: the naive Künneth map, adjoint to the
  comparison of total tensor complexes of [Stacks, Tag 01CD] followed by the two legs.

## Main results

* `Stacks.Cohomology.KunnethNaive.adjunctionBitensorMap_hexagon_legs`: the abstract hexagon for
  the abstract Künneth map with arbitrary legs.
* `Stacks.Cohomology.KunnethNaive.counitLeg_naive`: the derived counit leg against the
  degreewise one, [Stacks, Tag 0FP1] along a composite.
* `Stacks.Cohomology.KunnethNaive.kunnethMap_naive`: **the relative Künneth map on degreewise
  direct images.**

## References

* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
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
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.KunnethNaive

/-! ### The abstract hexagon with arbitrary legs -/

section Abstract

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C₁ : Type u₃} [Category.{v₃} C₁] {C₂ : Type u₄} [Category.{v₄} C₂]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
  (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {R₁ : C₁ ⥤ C} {P₁ : C₁ ⥤ D} (β : R₁ ⋙ L ⟶ P₁)
  {R₂ : C₂ ⥤ C} {P₂ : C₂ ⥤ D} (γ : R₂ ⋙ L ⟶ P₂)

/-- **The abstract hexagon for the abstract Künneth map.**  For an adjunction `L ⊣ R`, bifunctors
`A` and `B`, a comparison `α : A ⋙ L ⟶ (L × L) ⋙ B` and two legs `β`, `γ`, the route
`A(a, b) ⟶ S ⟶ S' ⟶ R T` agrees with the route through `ηa`, `ηb`, the abstract Künneth map and
`R` of `B(xa, xb) ≫ tX`, as soon as the transposed diagram commutes. -/
lemma adjunctionBitensorMap_hexagon_legs {K : C₁} {M : C₂}
    {a b S S' : C} {T Ga Gb Pa Pb PS PT N : D}
    (ηa : a ⟶ R₁.obj K) (ηb : b ⟶ R₂.obj M)
    (tY : A.obj (a, b) ⟶ S) (ν : S ⟶ S') (ηT : S' ⟶ R.obj T)
    (xa : P₁.obj K ⟶ Ga) (xb : P₂.obj M ⟶ Gb) (tX : B.obj (Ga, Gb) ⟶ T)
    (ca : L.obj a ⟶ Pa) (qa : Pa ⟶ Ga) (cb : L.obj b ⟶ Pb) (qb : Pb ⟶ Gb)
    (cS : L.obj S ⟶ PS) (cT : L.obj S' ⟶ PT) (qT : PT ⟶ T) (nT : PS ⟶ PT)
    (w : PS ⟶ N) (m : N ⟶ T) (tXp : B.obj (Pa, Pb) ⟶ N)
    (hga : L.map ηa ≫ β.app K ≫ xa = ca ≫ qa)
    (hgb : L.map ηb ≫ γ.app M ≫ xb = cb ≫ qb)
    (hgT : L.map ηT ≫ adj.counit.app T = cT ≫ qT)
    (hν : L.map ν ≫ cT = cS ≫ nT) (hn : nT ≫ qT = w ≫ m)
    (h0 : L.map tY ≫ cS ≫ w = α.app (a, b) ≫ B.map (ca ×ₘ cb) ≫ tXp)
    (ht : tXp ≫ m = B.map (qa ×ₘ qb) ≫ tX) :
    tY ≫ ν ≫ ηT =
      A.map (ηa ×ₘ ηb) ≫ adjunctionBitensorMap adj A B α β γ K M ≫
        R.map (B.map (xa ×ₘ xb) ≫ tX) := by
  have hB : B.map ((L.map ηa ≫ β.app K) ×ₘ (L.map ηb ≫ γ.app M)) ≫ B.map (xa ×ₘ xb) =
      B.map (ca ×ₘ cb) ≫ B.map (qa ×ₘ qb) := by
    rw [← B.map_comp, ← B.map_comp, prod_comp, prod_comp, Category.assoc, Category.assoc, hga,
      hgb]
  refine (adj.homEquiv _ _).symm.injective ?_
  have hR : (adj.homEquiv _ _).symm (A.map (ηa ×ₘ ηb) ≫ adjunctionBitensorMap adj A B α β γ K M ≫
        R.map (B.map (xa ×ₘ xb) ≫ tX)) =
      α.app (a, b) ≫ B.map ((L.map ηa ≫ β.app K) ×ₘ (L.map ηb ≫ γ.app M)) ≫
        B.map (xa ×ₘ xb) ≫ tX := by
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
      homEquiv_symm_adjunctionBitensorMap]
    simp only [Category.assoc]
  rw [hR, reassoc_of% hB, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit]
  rw [hgT, reassoc_of% hν, hn, reassoc_of% h0, ht]

end Abstract

/-! ### The geometric hexagon -/

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

section Leg

variable {S X W : RingedSpace.{u, u}}

/-- **The degreewise counit leg** `f^*a_*𝒦^• ⟶ p^*𝒦^•` attached to a factorization
`p ≫ a = f`: the composition isomorphism `f^* = (p ≫ a)^* ≅ p^*a^*` of degreewise pullbacks,
followed by `p^*` of the counit `a^*a_* ⟶ id` of Stacks 0096. -/
def naiveCounitLeg (a : X ⟶ S) (p : W ⟶ X) (f : W ⟶ S) (hp : p ≫ a = f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (pullbackComplex f).obj ((pushforwardComplex a).obj K) ⟶ (pullbackComplex p).obj K :=
  eqToHom (congrArg (fun g => (pullbackComplex g).obj ((pushforwardComplex a).obj K)) hp.symm) ≫
    (Stacks.PullbackTensorComposition.pullbackComplexCompIso p a).inv.app
      ((pushforwardComplex a).obj K) ≫
    (pullbackComplex p).map ((complexAdjunction a).counit.app K)

/-- The degreewise counit leg at the literal composite. -/
theorem naiveCounitLeg_comp (a : X ⟶ S) (p : W ⟶ X)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    naiveCounitLeg a p (p ≫ a) rfl K =
      (Stacks.PullbackTensorComposition.pullbackComplexCompIso p a).inv.app
          ((pushforwardComplex a).obj K) ≫
        (pullbackComplex p).map ((complexAdjunction a).counit.app K) := by
  simp only [naiveCounitLeg, eqToHom_refl, Category.id_comp]

/-- The derived counit leg at the literal composite, written out. -/
theorem pullbackCounitLeg_comp_app (a : X ⟶ S) (p : W ⟶ X)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (pullbackCounitLeg a p (p ≫ a) rfl).app E =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).inv.app
          ((derivedPushforward a).obj E) ≫
        (derivedPullback p).map ((derivedAdjunction a).counit.app E) := by
  simp only [pullbackCounitLeg, pullbackCounitLegComp, eqToHom_refl, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.id_comp]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- The composition law for the comparison `Lf^* ⟶ f^*`, read with the inverse of the
composition isomorphism. -/
theorem compIso_inv_comp_derivedPullbackNatTrans (a : X ⟶ S) (p : W ⟶ X)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S) ℤ) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).inv.app
          (DerivedCategory.Q.obj K) ≫
        (derivedPullback p).map ((derivedPullbackNatTrans a).app K) ≫
          (derivedPullbackNatTrans p).app ((pullbackComplex a).obj K) =
      (derivedPullbackNatTrans (p ≫ a)).app K ≫
        DerivedCategory.Q.map ((Stacks.PullbackTensorComposition.pullbackComplexCompIso p a).inv.app
          K) := by
  have h4 := derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans p a K
  refine (Iso.inv_comp_eq
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).app
      (DerivedCategory.Q.obj K))).2 ?_
  rw [← Category.assoc]
  refine (Iso.eq_comp_inv (DerivedCategory.Q.mapIso
    ((Stacks.PullbackTensorComposition.pullbackComplexCompIso p a).app K))).2 ?_
  rw [Category.assoc]
  exact h4.symm

/-- [Stacks, Tag 0FP1] pushed along `Lp^*`. -/
theorem derivedPullback_map_derivedCounit_pushforwardComparisonQ (a : X ⟶ S) (p : W ⟶ X)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (derivedPullback p).map ((derivedPullback a).map (pushforwardComparisonQ a K)) ≫
        (derivedPullback p).map ((derivedAdjunction a).counit.app (DerivedCategory.Q.obj K)) =
      (derivedPullback p).map ((derivedPullbackNatTrans a).app ((pushforwardComplex a).obj K)) ≫
        (derivedPullback p).map (DerivedCategory.Q.map ((complexAdjunction a).counit.app K)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, derivedCounit_pushforwardComparisonQ]

/-- The diagram chase behind `counitLeg_naive_comp`, with every object and morphism a
variable, so that it is applied by `exact` at the concrete spelling. -/
private theorem chase_counitLeg {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : C}
    {x : A₀ ⟶ A₁} {i : A₁ ⟶ A₂} {i' : A₀ ⟶ A₃} {y : A₃ ⟶ A₂} {c : A₂ ⟶ A₄} {d : A₃ ⟶ A₅}
    {e : A₅ ⟶ A₄} {n : A₄ ⟶ A₆} {n' : A₅ ⟶ A₇} {g : A₇ ⟶ A₆} {A₈ : C} {t : A₀ ⟶ A₈}
    {k : A₈ ⟶ A₇}
    {β : A₁ ⟶ A₄} {κ : A₈ ⟶ A₆}
    (h1 : x ≫ i = i' ≫ y) (h2 : y ≫ c = d ≫ e) (h3 : e ≫ n = n' ≫ g)
    (h4 : i' ≫ d ≫ n' = t ≫ k) (hβ : β = i ≫ c) (hκ : κ = k ≫ g) :
    x ≫ β ≫ n = t ≫ κ := by
  rw [hβ, hκ, Category.assoc, reassoc_of% h1, reassoc_of% h2, h3, reassoc_of% h4]

/-- The derived counit leg against the degreewise one, at the literal composite. -/
theorem counitLeg_naive_comp (a : X ⟶ S) (p : W ⟶ X)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (derivedPullback (p ≫ a)).map (pushforwardComparisonQ a K) ≫
        (pullbackCounitLeg a p (p ≫ a) rfl).app (DerivedCategory.Q.obj K) ≫
          (derivedPullbackNatTrans p).app K =
      (derivedPullbackNatTrans (p ≫ a)).app ((pushforwardComplex a).obj K) ≫
        DerivedCategory.Q.map (naiveCounitLeg a p (p ≫ a) rfl K) := by
  have h1 : (derivedPullback (p ≫ a)).map (pushforwardComparisonQ a K) ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).inv.app
          ((derivedPushforward a).obj (DerivedCategory.Q.obj K)) =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).inv.app
          (DerivedCategory.Q.obj ((pushforwardComplex a).obj K)) ≫
        (derivedPullback p).map ((derivedPullback a).map (pushforwardComparisonQ a K)) :=
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).inv.naturality _
  have h3 : (derivedPullback p).map (DerivedCategory.Q.map ((complexAdjunction a).counit.app K)) ≫
        (derivedPullbackNatTrans p).app K =
      (derivedPullbackNatTrans p).app ((pullbackComplex a).obj ((pushforwardComplex a).obj K)) ≫
        DerivedCategory.Q.map ((pullbackComplex p).map ((complexAdjunction a).counit.app K)) :=
    (derivedPullbackNatTrans p).naturality _
  exact chase_counitLeg h1 (derivedPullback_map_derivedCounit_pushforwardComparisonQ a p K) h3
    (compIso_inv_comp_derivedPullbackNatTrans a p ((pushforwardComplex a).obj K))
    (pullbackCounitLeg_comp_app a p (DerivedCategory.Q.obj K))
    (by rw [naiveCounitLeg_comp, DerivedCategory.Q.map_comp])

/-- **The derived counit leg against the degreewise one.**  `Lf^*` of the comparison
`a_* ⟶ Ra_*`, followed by the counit leg `Lf^*Ra_* ⟶ Lp^*` of the relative Künneth map and the
comparison `Lp^* ⟶ p^*`, is the comparison `Lf^* ⟶ f^*` followed by the degreewise counit leg.
This is [Stacks, Tag 0FP1] for `a`, carried along the composition law of the comparison
`Lf^* ⟶ f^*` for `f = p ≫ a`. -/
theorem counitLeg_naive (a : X ⟶ S) (p : W ⟶ X) (f : W ⟶ S) (hp : p ≫ a = f)
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (derivedPullback f).map (pushforwardComparisonQ a K) ≫
        (pullbackCounitLeg a p f hp).app (DerivedCategory.Q.obj K) ≫
          (derivedPullbackNatTrans p).app K =
      (derivedPullbackNatTrans f).app ((pushforwardComplex a).obj K) ≫
        DerivedCategory.Q.map (naiveCounitLeg a p f hp K) := by
  subst hp
  exact counitLeg_naive_comp a p K

end Leg

section Kunneth

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
  (M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)

/-- The transpose of the naive Künneth map: the comparison of total tensor complexes of
[Stacks, Tag 01CD] for `f`, followed by the two degreewise counit legs. -/
def naiveKunnethTranspose :
    (pullbackComplex f).obj ((totalComplexPair (sheafTensor S.sheaf)).obj
        ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)) ⟶
      (totalComplexPair (sheafTensor W.sheaf)).obj
        ((pullbackComplex p).obj K, (pullbackComplex q).obj M) :=
  (pullbackTensorComplexNatIso f).hom.app
      ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M) ≫
    (totalComplexPair (sheafTensor W.sheaf)).map
      (naiveCounitLeg a p f hp K ×ₘ naiveCounitLeg b q f hq M)

/-- **The naive Künneth map** `Tot(a_*𝒦^• ⊗_{𝒪_S} b_*ℳ^•) ⟶ f_*Tot(p^*𝒦^• ⊗_{𝒪_W} q^*ℳ^•)`,
the adjoint transpose under `f^* ⊣ f_*` of `naiveKunnethTranspose`. -/
def naiveKunneth :
    (totalComplexPair (sheafTensor S.sheaf)).obj
        ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M) ⟶
      (pushforwardComplex f).obj ((totalComplexPair (sheafTensor W.sheaf)).obj
        ((pullbackComplex p).obj K, (pullbackComplex q).obj M)) :=
  (complexAdjunction f).homEquiv _ _ (naiveKunnethTranspose a b p q f hp hq K M)

/-- `f^*` of the naive Künneth map followed by the counit is its transpose. -/
theorem pullbackComplex_naiveKunneth_counit :
    (pullbackComplex f).map (naiveKunneth a b p q f hp hq K M) ≫
        (complexAdjunction f).counit.app ((totalComplexPair (sheafTensor W.sheaf)).obj
          ((pullbackComplex p).obj K, (pullbackComplex q).obj M)) =
      naiveKunnethTranspose a b p q f hp hq K M :=
  Equiv.symm_apply_apply ((complexAdjunction f).homEquiv _ _) _

/-- The comparison `Lf^* ⟶ f^*` is natural along the naive Künneth map. -/
theorem derivedPullbackNatTrans_naturality_naiveKunneth :
    (derivedPullback f).map (DerivedCategory.Q.map (naiveKunneth a b p q f hp hq K M)) ≫
        (derivedPullbackNatTrans f).app ((pushforwardComplex f).obj
          ((totalComplexPair (sheafTensor W.sheaf)).obj
            ((pullbackComplex p).obj K, (pullbackComplex q).obj M))) =
      (derivedPullbackNatTrans f).app ((totalComplexPair (sheafTensor S.sheaf)).obj
          ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)) ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (naiveKunneth a b p q f hp hq K M)) :=
  (derivedPullbackNatTrans f).naturality _

/-- The square identifying the naive Künneth map, read in the derived category. -/
theorem naiveKunneth_counit_square_Q :
    DerivedCategory.Q.map ((pullbackComplex f).map (naiveKunneth a b p q f hp hq K M)) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app
          ((totalComplexPair (sheafTensor W.sheaf)).obj
            ((pullbackComplex p).obj K, (pullbackComplex q).obj M))) =
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app
          ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)) ≫
        DerivedCategory.Q.map ((totalComplexPair (sheafTensor W.sheaf)).map
          (naiveCounitLeg a p f hp K ×ₘ naiveCounitLeg b q f hq M)) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.Q.map ·) (pullbackComplex_naiveKunneth_counit a b p q f hp hq K
        M)).trans
      (DerivedCategory.Q.map_comp _ _))

/-- [Stacks, Tag 0FP0] at the pair of degreewise direct images, in the direction the hexagon
consumes. -/
theorem derivedPullbackTensorIso_toTensor_square_directImages :
    (derivedPullback f).map ((derivedToTensorNatTrans S).app
          ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)) ≫
        (derivedPullbackNatTrans f).app ((totalComplexPair (sheafTensor S.sheaf)).obj
          ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app
            ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)) =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app
          (DerivedCategory.Q.obj ((pushforwardComplex a).obj K),
            DerivedCategory.Q.obj ((pushforwardComplex b).obj M)) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((derivedPullbackNatTrans f).app ((pushforwardComplex a).obj K) ×ₘ
              (derivedPullbackNatTrans f).app ((pushforwardComplex b).obj M)) ≫
          (derivedToTensorNatTrans W).app
            ((pullbackComplex f).obj ((pushforwardComplex a).obj K),
              (pullbackComplex f).obj ((pushforwardComplex b).obj M)) :=
  (derivedPullbackTensorIso_toTensor_comm f ((pushforwardComplex a).obj K)
    ((pushforwardComplex b).obj M)).symm

omit [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The canonical map `⊗^𝐋 ⟶ ⊗` is natural along the two degreewise counit legs. -/
theorem derivedToTensor_naturality_counitLegs :
    (derivedToTensorNatTrans W).app
          ((pullbackComplex f).obj ((pushforwardComplex a).obj K),
            (pullbackComplex f).obj ((pushforwardComplex b).obj M)) ≫
        DerivedCategory.Q.map ((totalComplexPair (sheafTensor W.sheaf)).map
          (naiveCounitLeg a p f hp K ×ₘ naiveCounitLeg b q f hq M)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
          (DerivedCategory.Q.map (naiveCounitLeg a p f hp K) ×ₘ
            DerivedCategory.Q.map (naiveCounitLeg b q f hq M)) ≫
        (derivedToTensorNatTrans W).app ((pullbackComplex p).obj K, (pullbackComplex q).obj M) :=
  ((derivedToTensorNatTrans W).naturality
    (naiveCounitLeg a p f hp K ×ₘ naiveCounitLeg b q f hq M)).symm

/-- **The relative Künneth map on degreewise direct images.**  The comparisons `a_* ⟶ Ra_*`
and `b_* ⟶ Rb_*` followed by the relative Künneth map of [Stacks, Tag 0FLP] and `Rf_*` of the
comparisons `Lp^* ⟶ p^*`, `Lq^* ⟶ q^*` and `⊗^𝐋 ⟶ ⊗`, is the canonical map
`a_*𝒦^• ⊗^𝐋 b_*ℳ^• ⟶ Tot(a_*𝒦^• ⊗ b_*ℳ^•)` followed by the naive Künneth map and the comparison
`f_* ⟶ Rf_*`. -/
theorem kunnethMap_naive :
    (derivedToTensorNatTrans S).app
          ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M) ≫
        DerivedCategory.Q.map (naiveKunneth a b p q f hp hq K M) ≫
        pushforwardComparisonQ f ((totalComplexPair (sheafTensor W.sheaf)).obj
          ((pullbackComplex p).obj K, (pullbackComplex q).obj M)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map
          (pushforwardComparisonQ a K ×ₘ pushforwardComparisonQ b M) ≫
        kunnethMap a b p q f hp hq (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≫
        (derivedPushforward f).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
              ((derivedPullbackNatTrans p).app K ×ₘ (derivedPullbackNatTrans q).app M) ≫
            (derivedToTensorNatTrans W).app
              ((pullbackComplex p).obj K, (pullbackComplex q).obj M)) :=
  adjunctionBitensorMap_hexagon_legs (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (pullbackCounitLeg a p f hp) (pullbackCounitLeg b q f hq)
    (pushforwardComparisonQ a K) (pushforwardComparisonQ b M)
    ((derivedToTensorNatTrans S).app
      ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M))
    (DerivedCategory.Q.map (naiveKunneth a b p q f hp hq K M))
    (pushforwardComparisonQ f ((totalComplexPair (sheafTensor W.sheaf)).obj
      ((pullbackComplex p).obj K, (pullbackComplex q).obj M)))
    ((derivedPullbackNatTrans p).app K) ((derivedPullbackNatTrans q).app M)
    ((derivedToTensorNatTrans W).app ((pullbackComplex p).obj K, (pullbackComplex q).obj M))
    ((derivedPullbackNatTrans f).app ((pushforwardComplex a).obj K))
    (DerivedCategory.Q.map (naiveCounitLeg a p f hp K))
    ((derivedPullbackNatTrans f).app ((pushforwardComplex b).obj M))
    (DerivedCategory.Q.map (naiveCounitLeg b q f hq M))
    ((derivedPullbackNatTrans f).app ((totalComplexPair (sheafTensor S.sheaf)).obj
      ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)))
    ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj
      ((totalComplexPair (sheafTensor W.sheaf)).obj
        ((pullbackComplex p).obj K, (pullbackComplex q).obj M))))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app
      ((totalComplexPair (sheafTensor W.sheaf)).obj
        ((pullbackComplex p).obj K, (pullbackComplex q).obj M))))
    (DerivedCategory.Q.map ((pullbackComplex f).map (naiveKunneth a b p q f hp hq K M)))
    (DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app
      ((pushforwardComplex a).obj K, (pushforwardComplex b).obj M)))
    (DerivedCategory.Q.map ((totalComplexPair (sheafTensor W.sheaf)).map
      (naiveCounitLeg a p f hp K ×ₘ naiveCounitLeg b q f hq M)))
    ((derivedToTensorNatTrans W).app
      ((pullbackComplex f).obj ((pushforwardComplex a).obj K),
        (pullbackComplex f).obj ((pushforwardComplex b).obj M)))
    (counitLeg_naive a p f hp K) (counitLeg_naive b q f hq M)
    (derivedCounit_pushforwardComparisonQ f _)
    (derivedPullbackNatTrans_naturality_naiveKunneth a b p q f hp hq K M)
    (naiveKunneth_counit_square_Q a b p q f hp hq K M)
    (derivedPullbackTensorIso_toTensor_square_directImages a b f K M)
    (derivedToTensor_naturality_counitLegs a b p q f hp hq K M)

end Kunneth

end Stacks.Cohomology.KunnethNaive

end
