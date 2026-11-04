module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.LeftComparisonAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TensorPullCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.NaiveCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The naive cup product and the relative cup product on a ringed space

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `𝒦^•` and `ℳ^•` be
complexes of `𝒪_X`-modules.  **Stacks 0FP3** asserts that the diagram

```
f_*𝒦^• ⊗^L_{𝒪_Y} f_*ℳ^• ─────→ Rf_*𝒦^• ⊗^L_{𝒪_Y} Rf_*ℳ^•
          │                                │
          ↓                                ↓
Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•)        Rf_*(𝒦^• ⊗^L_{𝒪_X} ℳ^•)
          │                                │
          ↓                                ↓
f_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•) ─────→ Rf_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)
```

commutes in `D(𝒪_Y)`.  Its two horizontal edges and its top right edge are the comparison
`f_* ⟶ Rf_*` of degreewise pushforward with the derived pushforward; the top left and bottom
right edges are the canonical map from the derived tensor product to the ordinary total tensor
complex of Stacks 06YU; the middle left edge is the naive cup product and the middle right edge
is the relative cup product of Stacks 0B68.

## Main definitions

* `Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ`: the
  comparison `Q(f_*𝒦^•) ⟶ Rf_*(Q𝒦^•)` of degreewise pushforward with the derived pushforward,
  read between the images of the localization functor `Q`.

## Main results

* `derivedCounit_pushforwardComparisonQ`, in this namespace: **Stacks 0FP1** read at `Q`, which
  is the form the proof consumes.
* `naiveCupProduct_relativeCupProduct`, in this namespace: **Stacks 0FP3**.

## The argument

The proof is the source's.  Both composites are maps into `Rf_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)`, so they
are compared through their adjoint transposes along `Lf^*` for the adjunction of Stacks 079W.
Transposing replaces the two bottom edges by the counit `Lf^*Rf_* ⟶ id`, and Stacks 0FP1
rewrites each occurrence of `Lf^*f_* ⟶ Lf^*Rf_* ⟶ id` as `Lf^*f_* ⟶ f^*f_* ⟶ id`.  The
anticlockwise composite then becomes the naive cup product read through the square that
identifies it, by naturality of the comparison `Lf^* ⟶ f^*`; the clockwise one becomes the
comparison of Stacks 079U, moved past the comparison `f_* ⟶ Rf_*` by its own naturality,
followed by the counit in each tensor factor.  What remains between the two is Stacks 0FP0 at
the pair `(f_*𝒦^•, f_*ℳ^•)`, together with the naturality of the canonical map to the ordinary
total tensor complex.

## Implementation notes

*The abstract layer is the uncurried one.*  The two arrow-algebra lemmas below —
`counit_comp_of_counit_fac` and `adjunctionBitensorMap_hexagon` — are the counterparts, for
bifunctors written on a product category `C × C ⥤ C` and morphisms paired with `×ₘ`, of
`Stacks.Cohomology.CupProductAndDerivedPushforward.counit_comp_of_counit_fac` and
`hexagon_of_transposes`, which are stated for curried bifunctors `𝒟 ⥤ 𝒟 ⥤ 𝒟`.  The uncurried
form is the one this tree's relative cup product is phrased in — `adjunctionBitensorMap` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct`, and likewise
the abstract sections of the associativity, commutativity and composition files — so the
hexagon is stated over `adjunctionBitensorMap` itself and its comparison is a genuine morphism
of bifunctors, whose naturality the proof uses rather than carrying it as a hypothesis.

*The diagram is stated at complexes, not at objects of the derived category.*  Three of its six
vertices — the two total tensor complexes and the degreewise pushforward — are complexes, and
the two horizontal edges exist only for a complex, so the statement quantifies over complexes
`𝒦^•`, `ℳ^•` of `𝒪_X`-modules and reads the derived tensor products at their images under `Q`,
which is what the source does.

*No hypothesis beyond the source's data.*  No boundedness, flatness or quasi-coherence
hypothesis enters, and the four sheafification binders are the ones the derived tensor product
of Stacks 06YU is stated under; both are `Prop`s inhabited for every ringed space, as recorded
in the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct`.

## References

* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0FP0](https://stacks.math.columbia.edu/tag/0FP0)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.Tensor
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces

/-! ## Diagram bookkeeping

Both proofs below are instances of two statements about an adjunction and two bifunctors on
product categories, proved here once in abstract categories.  Stating them abstractly is what
lets the existing inputs be supplied up to definitional equality: this development spells the
category of modules on a ringed space both as
`SheafOfModules (structureSheafRing X)` and as
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`, and a rewrite cannot cross
between the two. -/

section Bookkeeping

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C}

/-- Two commuting squares sharing a middle column compose to a commuting square for the
composites of their horizontal edges. -/
lemma comp_naturality {A A' B B' Z Z' : C} {u : A ⟶ A'} {v : B ⟶ B'} {w : Z ⟶ Z'}
    {x : A ⟶ B} {x' : A' ⟶ B'} {y : B ⟶ Z} {y' : B' ⟶ Z'}
    (hx : u ≫ x' = x ≫ v) (hy : v ≫ y' = y ≫ w) :
    u ≫ x' ≫ y' = (x ≫ y) ≫ w := by
  rw [← Category.assoc, hx, Category.assoc, hy, Category.assoc]

/-- A comparison `η : b ⟶ R W` whose transpose factors as `p ≫ q`, composed with a map `R c₂`
on the right, transposes to `p ≫ e` followed by `r`, provided `q ≫ c₂ = e ≫ r`. -/
lemma counit_comp_of_counit_fac (adj : L ⊣ R) {a b : C} {W Z P E : D}
    (c₁ : a ⟶ b) (η : b ⟶ R.obj W) (c₂ : W ⟶ Z) (p : L.obj b ⟶ P) (q : P ⟶ W)
    (e : P ⟶ E) (r : E ⟶ Z)
    (h : L.map η ≫ adj.counit.app W = p ≫ q) (k : q ≫ c₂ = e ≫ r) :
    L.map (c₁ ≫ η ≫ R.map c₂) ≫ adj.counit.app Z = (L.map c₁ ≫ p ≫ e) ≫ r := by
  have hc : L.map (R.map c₂) ≫ adj.counit.app Z = adj.counit.app W ≫ c₂ :=
    adj.counit.naturality c₂
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hc,
    ← Category.assoc (L.map η), h, Category.assoc, Category.assoc, k]
  simp only [Category.assoc]

variable (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The abstract hexagon.**  For an adjunction `L ⊣ R`, a bifunctor `A` on the source of `L`,
a bifunctor `B` on its target and a morphism of bifunctors `α : A ⋙ L ⟶ (L × L) ⋙ B`, the two
routes from `A(a, b)` to `R T` — along `A(a, b) ⟶ S ⟶ S' ⟶ R T`, and along the comparisons
`ηa`, `ηb` into `R` followed by `adjunctionBitensorMap` and `R tX` — agree as soon as the
transposed diagram does. -/
lemma adjunctionBitensorMap_hexagon
    {a b S S' : C} {G G' T Pa Pb PS PT N : D}
    (ηa : a ⟶ R.obj G) (ηb : b ⟶ R.obj G')
    (tY : A.obj (a, b) ⟶ S) (ν : S ⟶ S') (ηT : S' ⟶ R.obj T) (tX : B.obj (G, G') ⟶ T)
    (ca : L.obj a ⟶ Pa) (qa : Pa ⟶ G) (cb : L.obj b ⟶ Pb) (qb : Pb ⟶ G')
    (cS : L.obj S ⟶ PS) (cT : L.obj S' ⟶ PT) (qT : PT ⟶ T) (nT : PS ⟶ PT)
    (w : PS ⟶ N) (m : N ⟶ T) (tXp : B.obj (Pa, Pb) ⟶ N)
    (hga : L.map ηa ≫ adj.counit.app G = ca ≫ qa)
    (hgb : L.map ηb ≫ adj.counit.app G' = cb ≫ qb)
    (hgT : L.map ηT ≫ adj.counit.app T = cT ≫ qT)
    (hν : L.map ν ≫ cT = cS ≫ nT) (hn : nT ≫ qT = w ≫ m)
    (h0 : L.map tY ≫ cS ≫ w = α.app (a, b) ≫ B.map (ca ×ₘ cb) ≫ tXp)
    (ht : tXp ≫ m = B.map (qa ×ₘ qb) ≫ tX) :
    tY ≫ ν ≫ ηT =
      A.map (ηa ×ₘ ηb) ≫ adjunctionBitensorMap adj A B α G G' ≫ R.map tX := by
  have hcup : (adj.homEquiv _ _).symm (adjunctionBitensorMap adj A B α G G') =
      α.app (R.obj G, R.obj G') ≫
        B.map (adj.counit.app G ×ₘ adj.counit.app G') :=
    Equiv.symm_apply_apply _ _
  have hα : L.map (A.map (ηa ×ₘ ηb)) ≫ α.app (R.obj G, R.obj G') =
      α.app (a, b) ≫ B.map (L.map ηa ×ₘ L.map ηb) := α.naturality (ηa ×ₘ ηb)
  have hB {a₁ a₂ b₁ b₂ c₁ c₂ : D} (u₁ : a₁ ⟶ b₁) (u₂ : a₂ ⟶ b₂) (v₁ : b₁ ⟶ c₁)
      (v₂ : b₂ ⟶ c₂) :
      B.map (u₁ ×ₘ u₂) ≫ B.map (v₁ ×ₘ v₂) = B.map ((u₁ ≫ v₁) ×ₘ (u₂ ≫ v₂)) :=
    (B.map_comp _ _).symm
  refine (adj.homEquiv _ _).symm.injective ?_
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, hcup]
  simp only [Category.assoc]
  rw [hgT, reassoc_of% hν, hn, reassoc_of% h0, ht, reassoc_of% hB ca cb qa qb, ← hga, ← hgb,
    ← hB, reassoc_of% hα]
  simp only [Category.assoc]

end Bookkeeping

/-! ## The comparison `f_* ⟶ Rf_*` at the localization functor -/

universe u

attribute [local instance] HasDerivedCategory.standard

-- The two spellings of the category of `𝒪_X`-modules used below —
-- `SheafOfModules (structureSheafRing X)` and
-- `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X`, which is
-- `SheafOfModules (Tensor.ringSheaf X.sheaf)` — have to be definitionally equal at the
-- `implicit` transparency level, which is what `simp` and `dsimp` type-check their rewrites
-- at.  `structureSheafRing` is `@[instance_reducible]`, so it unfolds there already, and its
-- reduct is `⟨X.presheaf ⋙ forget₂ CommRingCat RingCat, _⟩`; the canonical
-- `Stacks.SheafOfModules.Tensor.ringSheaf` is a plain `def`, so it has to be opened by hand
-- before `AlgebraicGeometry.SheafedSpace.sheaf` and `TopCat.Sheaf` can carry its first
-- component to the same `X.presheaf ⋙ forget₂ CommRingCat RingCat`.  Its second component is
-- a `Presheaf.IsSheaf` proof, so `sheafCompose` is listed only for the ringed-space
-- identifications the file makes elsewhere.
attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison `Q(f_*𝒦^•) ⟶ Rf_*(Q𝒦^•)`** of degreewise pushforward with the derived
pushforward, from the image in `D(𝒪_Y)` of the degreewise pushforward of a complex of
`𝒪_X`-modules to the derived pushforward of its image in `D(𝒪_X)`.  It is the canonical
comparison of the derived functor with the two identifications between `Q` and `Qh ∘ quotient`
inserted at either end. -/
def pushforwardComparisonQ
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    DerivedCategory.Q.obj ((pushforwardComplex f).obj K) ⟶
      (derivedPushforward f).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)).inv.app
        ((pushforwardComplex f).obj K) ≫
    ((derivedPushforwardUnit f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      (derivedPushforward f).map ((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom.app K))

/-- **The comparison `f_* ⟶ Rf_*` is natural in the complex.** -/
lemma pushforwardComparisonQ_naturality
    {K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ}
    (a : K ⟶ L) :
    DerivedCategory.Q.map ((pushforwardComplex f).map a) ≫ pushforwardComparisonQ f L =
      pushforwardComparisonQ f K ≫ (derivedPushforward f).map (DerivedCategory.Q.map a) := by
  have h₁ := DerivedCategory.quotientCompQhIso_inv_naturality
    (C := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)
    ((pushforwardComplex f).map a)
  have h₂ := (derivedPushforwardUnit f).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have h₃ := congrArg ((derivedPushforward f).map ·)
    (DerivedCategory.quotientCompQhIso_hom_naturality
      (C := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) a)
  simp only [Functor.map_comp] at h₃
  exact comp_naturality h₁ (comp_naturality h₂ h₃)

/-! ## Stacks 0FP1 at the localization functor -/

/-- The counit of `f^* ⊣ f_*` on the homotopy categories is the class of the counit on
complexes. -/
lemma homotopyCounit_app_quotient
    (N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (homotopyPullbackPushforwardAdjunction f).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((complexAdjunction f).counit.app N) := rfl

/-- **Stacks 0FP1 read at the localization functor `Q`.**  For a complex `N` of `𝒪_X`-modules
the square whose upper edge is `Lf^*` of the comparison `f_* ⟶ Rf_*`, whose lower edge is the
counit of `Lf^* ⊣ Rf_*`, whose left edge is the comparison `Lf^* ⟶ f^*` and whose right edge
is the ordinary counit `f^*f_* ⟶ id` commutes in `D(𝒪_X)`. -/
theorem derivedCounit_pushforwardComparisonQ
    (N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (derivedPullback f).map (pushforwardComparisonQ f N) ≫
        (derivedAdjunction f).counit.app (DerivedCategory.Q.obj N) =
      (derivedPullbackNatTrans f).app ((pushforwardComplex f).obj N) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app N) := by
  have key := counit_comp_of_counit_fac (derivedAdjunction f)
    ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing Y))).inv.app
      ((pushforwardComplex f).obj N))
    ((derivedPushforwardUnit f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    ((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom.app N)
    ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((pushforwardComplex f).obj N)))
    (DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).counit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)))
    ((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom.app
      ((pullbackComplex f).obj ((pushforwardComplex f).obj N)))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app N))
    (derivedAdjunction_counit_fac f _)
    (DerivedCategory.quotientCompQhIso_hom_naturality ((complexAdjunction f).counit.app N))
  have hnat : (derivedPullbackNatTrans f).app ((pushforwardComplex f).obj N) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (structureSheafRing Y))).inv.app
        ((pushforwardComplex f).obj N)) ≫
        (derivedPullbackComparison f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((pushforwardComplex f).obj N)) ≫
          (DerivedCategory.quotientCompQhIso
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom.app
              ((pullbackComplex f).obj ((pushforwardComplex f).obj N)) := by
    have hid : DerivedCategory.Qh.map
            (((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app ((pushforwardComplex f).obj N)) ≫
          (DerivedCategory.quotientCompQhIso
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom.app
              ((pullbackComplex f).obj ((pushforwardComplex f).obj N)) =
        (DerivedCategory.quotientCompQhIso
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom.app
            ((pullbackComplex f).obj ((pushforwardComplex f).obj N)) := by
      have h : DerivedCategory.Qh.map
          (((RingedSpaceModuleAdjunction.modulePullback f).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).hom.app ((pushforwardComplex f).obj N)) = 𝟙 _ :=
        DerivedCategory.Qh.map_id _
      rw [h]
      exact Category.id_comp _
    dsimp only [derivedPullbackNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [hid]
  refine key.trans ?_
  rw [hnat]

/-! ## Stacks 0FP3 -/

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)

/-- **The comparison `Lf^*(QN) ⟶ Q(f^*N)` is natural along the naive cup product.**  This is the
`naturality` field of `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` at the
naive cup product, with the two functor compositions reduced.  It is recorded as a lemma because
Stacks 0FP3 below consumes it as a hypothesis, and a hypothesis read off the environment costs
only its instantiation, whereas the same term written inline has to be elaborated from syntax. -/
theorem derivedPullbackNatTrans_naturality_naiveCupProduct :
    (derivedPullback f).map (DerivedCategory.Q.map (naiveCupProduct f K M)) ≫
        (derivedPullbackNatTrans f).app
          ((pushforwardComplex f).obj ((totalComplexPair (sheafTensor X.sheaf)).obj (K, M))) =
      (derivedPullbackNatTrans f).app
          (
              (totalComplexPair (sheafTensor Y.sheaf)).obj
                ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) ≫
        DerivedCategory.Q.map ((pullbackComplex f).map (naiveCupProduct f K M)) :=
  (derivedPullbackNatTrans f).naturality _

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The square identifying the naive cup product, read in the derived category.**  This is
`Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pullbackComplex_naiveCupProduct_counit` carried
along the localization functor `Q`, with the two composites split.  It is named for the same
reason as the previous lemma. -/
theorem naiveCupProduct_counit_square_Q :
    DerivedCategory.Q.map ((pullbackComplex f).map (naiveCupProduct f K M)) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app (
            (totalComplexPair (sheafTensor X.sheaf)).obj (K, M))) =
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app
          ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) ≫
        DerivedCategory.Q.map ((totalComplexPair (sheafTensor X.sheaf)).map
          ((complexAdjunction f).counit.app K ×ₘ (complexAdjunction f).counit.app M)) :=
  (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.Q.map ·)
      (pullbackComplex_naiveCupProduct_counit f K M)).trans
        (DerivedCategory.Q.map_comp _ _))

/-- **Stacks 0FP0 at the pair of degreewise pushforwards**, read in the direction Stacks 0FP3
consumes.  This is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_toTensor_comm` at
`(f_*𝒦^•, f_*ℳ^•)`, reversed; it is named for the same reason as the two lemmas above. -/
theorem derivedPullbackTensorIso_toTensor_square_pushforward :
    (derivedPullback f).map ((derivedToTensorNatTrans Y).app
          ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) ≫
        (derivedPullbackNatTrans f).app
            (
                (totalComplexPair (sheafTensor Y.sheaf)).obj
                  ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app
            ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app
          (DerivedCategory.Q.obj ((pushforwardComplex f).obj K),
            DerivedCategory.Q.obj ((pushforwardComplex f).obj M)) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj K) ×ₘ
              (derivedPullbackNatTrans f).app ((pushforwardComplex f).obj M)) ≫
          (derivedToTensorNatTrans X).app
            ((pullbackComplex f).obj ((pushforwardComplex f).obj K),
              (pullbackComplex f).obj ((pushforwardComplex f).obj M)) :=
  (derivedPullbackTensorIso_toTensor_comm f ((pushforwardComplex f).obj K)
    ((pushforwardComplex f).obj M)).symm

/-- **Stacks 0FP3.**  For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and complexes
`𝒦^•`, `ℳ^•` of `𝒪_X`-modules, the hexagon

```
f_*𝒦^• ⊗^L_{𝒪_Y} f_*ℳ^• ─────→ Rf_*𝒦^• ⊗^L_{𝒪_Y} Rf_*ℳ^•
          │                                │
          ↓                                ↓
Tot(f_*𝒦^• ⊗_{𝒪_Y} f_*ℳ^•)        Rf_*(𝒦^• ⊗^L_{𝒪_X} ℳ^•)
          │                                │
          ↓                                ↓
f_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•) ─────→ Rf_*Tot(𝒦^• ⊗_{𝒪_X} ℳ^•)
```

commutes in `D(𝒪_Y)`.  Its horizontal edges and its top right edge are the comparison
`f_* ⟶ Rf_*`; the top left and bottom right edges are the canonical map from the derived
tensor product to the ordinary total tensor complex of Stacks 06YU; the middle left edge is
the naive cup product and the middle right edge is the relative cup product of Stacks 0B68. -/
@[stacks 0FP3]
theorem naiveCupProduct_relativeCupProduct :
    (derivedToTensorNatTrans Y).app
          ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M) ≫
        DerivedCategory.Q.map (naiveCupProduct f K M) ≫
        pushforwardComparisonQ f ((totalComplexPair (sheafTensor X.sheaf)).obj (K, M)) =
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
          (pushforwardComparisonQ f K ×ₘ pushforwardComparisonQ f M) ≫
        relativeCupProduct f (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≫
        (derivedPushforward f).map ((derivedToTensorNatTrans X).app (K, M)) :=
  adjunctionBitensorMap_hexagon (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (pushforwardComparisonQ f K) (pushforwardComparisonQ f M)
    ((derivedToTensorNatTrans Y).app
      ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M))
    (DerivedCategory.Q.map (naiveCupProduct f K M))
    (pushforwardComparisonQ f ((totalComplexPair (sheafTensor X.sheaf)).obj (K, M)))
    ((derivedToTensorNatTrans X).app (K, M))
    ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj K) :
      (derivedPullback f).obj (DerivedCategory.Q.obj ((pushforwardComplex f).obj K)) ⟶
        DerivedCategory.Q.obj ((pullbackComplex f).obj ((pushforwardComplex f).obj K)))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app K))
    ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj M) :
      (derivedPullback f).obj (DerivedCategory.Q.obj ((pushforwardComplex f).obj M)) ⟶
        DerivedCategory.Q.obj ((pullbackComplex f).obj ((pushforwardComplex f).obj M)))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app M))
    ((derivedPullbackNatTrans f).app
        (
            (totalComplexPair (sheafTensor Y.sheaf)).obj
              ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) :
      (derivedPullback f).obj (DerivedCategory.Q.obj
          (
              (totalComplexPair (sheafTensor Y.sheaf)).obj
                ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M))) ⟶
        DerivedCategory.Q.obj ((pullbackComplex f).obj
          (
              (totalComplexPair (sheafTensor Y.sheaf)).obj
                ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M))))
    ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj (
        (totalComplexPair (sheafTensor X.sheaf)).obj (K, M))) :
      (derivedPullback f).obj
          (DerivedCategory.Q.obj ((pushforwardComplex f).obj (
              (totalComplexPair (sheafTensor X.sheaf)).obj (K, M)))) ⟶
        DerivedCategory.Q.obj
          ((pullbackComplex f).obj ((pushforwardComplex f).obj (
              (totalComplexPair (sheafTensor X.sheaf)).obj (K, M)))))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app (
        (totalComplexPair (sheafTensor X.sheaf)).obj (K, M))))
    (DerivedCategory.Q.map ((pullbackComplex f).map (naiveCupProduct f K M)))
    (DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app
        ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M)) :
      DerivedCategory.Q.obj ((pullbackComplex f).obj
          (
              (totalComplexPair (sheafTensor Y.sheaf)).obj
                ((pushforwardComplex f).obj K, (pushforwardComplex f).obj M))) ⟶
        DerivedCategory.Q.obj ((totalComplexPair (sheafTensor X.sheaf)).obj
          ((pullbackComplex f).obj ((pushforwardComplex f).obj K),
            (pullbackComplex f).obj ((pushforwardComplex f).obj M))))
    (DerivedCategory.Q.map ((totalComplexPair (sheafTensor X.sheaf)).map
      ((complexAdjunction f).counit.app K ×ₘ (complexAdjunction f).counit.app M)))
    ((derivedToTensorNatTrans X).app
        ((pullbackComplex f).obj ((pushforwardComplex f).obj K),
          (pullbackComplex f).obj ((pushforwardComplex f).obj M)) :
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
          (DerivedCategory.Q.obj ((pullbackComplex f).obj ((pushforwardComplex f).obj K)),
            DerivedCategory.Q.obj ((pullbackComplex f).obj ((pushforwardComplex f).obj M))) ⟶
        DerivedCategory.Q.obj ((totalComplexPair (sheafTensor X.sheaf)).obj
          ((pullbackComplex f).obj ((pushforwardComplex f).obj K),
            (pullbackComplex f).obj ((pushforwardComplex f).obj M))))
    (derivedCounit_pushforwardComparisonQ f K)
    (derivedCounit_pushforwardComparisonQ f M)
    (derivedCounit_pushforwardComparisonQ f ((totalComplexPair (sheafTensor X.sheaf)).obj (K, M)))
    (derivedPullbackNatTrans_naturality_naiveCupProduct f K M)
    (naiveCupProduct_counit_square_Q f K M)
    (derivedPullbackTensorIso_toTensor_square_pushforward f K M)
    (derivedToTensorNatTrans_naturality_prod X ((complexAdjunction f).counit.app K)
      ((complexAdjunction f).counit.app M)).symm

end Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces

end
