module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.NaiveCupProduct
import StacksCore.Tactic.StacksAttribute

/-! # The naive cup product and the relative cup product

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `K`, `M` be
unbounded cochain complexes of `O_C`-modules.  **Stacks 0FPK** asserts that the diagram

```
f_*K ⊗^L_{O_D} f_*M ───────────→ Rf_*K ⊗^L_{O_D} Rf_*M
        │                                 │
        ↓                                 ↓
Tot(f_*K ⊗_{O_D} f_*M)            Rf_*(K ⊗^L_{O_C} M)
        │                                 │
        ↓                                 ↓
f_*Tot(K ⊗_{O_C} M) ───────────→ Rf_*Tot(K ⊗_{O_C} M)
```

commutes in `D(O_D)`.  The two horizontal maps and the top right vertical one are the comparison
`f_* ⟶ Rf_*` of the derived pushforward with degreewise pushforward; the right-hand column is the
relative cup product of **Stacks 0B6C** followed by `Rf_*` of the canonical map from the derived
tensor product to the ordinary total tensor complex (**Stacks 06YU**); the left-hand column is
that same canonical map followed by the naive cup product.

## Main definitions

* `Stacks.Cohomology.CupProductAndDerivedPushforward.pushforwardComparisonQ`: the comparison
  `Q(f_*K) ⟶ Rf_*(QK)` of the derived pushforward with degreewise pushforward, read between the
  images of the localization functor `Q`.

## Main results

* `Stacks.Cohomology.CupProductAndDerivedPushforward.derivedCounit_pushforwardComparisonQ`:
  **Stacks 0FPI** read at `Q`, which is the form the proof consumes.
* `Stacks.Cohomology.CupProductAndDerivedPushforward.naiveCupProduct_relativeCupProduct`:
  **Stacks 0FPK** for a morphism of ringed topoi presented by a morphism of the underlying
  sites, registered as a variant.  The full statement, for an arbitrary morphism of ringed
  topoi, is `naiveCupProduct_relativeCupProduct` in
  `Stacks.Cohomology.CupProductAndDerivedPushforwardOfToposHom`.

## Implementation notes

The proof is the source's.  Both composites are maps into `Rf_*Tot(K ⊗_{O_C} M)`, so they are
compared through their adjoints along `Lf^*` for the adjunction of **Stacks 07A6**.  Transposing
replaces the two bottom edges by the counit `Lf^*Rf_* ⟶ id`, and **Stacks 0FPI** rewrites each
occurrence of `Lf^*f_* ⟶ Lf^*Rf_* ⟶ id` as `Lf^*f_* ⟶ f^*f_* ⟶ id`.  The anticlockwise composite
then becomes the naive cup product read through its identifying square, by naturality of the
comparison `Lf^* ⟶ f^*`; the clockwise one becomes the comparison of **Stacks 07A4**, moved past
the comparison `f_* ⟶ Rf_*` by its own naturality, followed by the counit in each tensor factor.
What remains between the two is **Stacks 0FPH** at the pair `(f_*K, f_*M)`, together with the
naturality of the canonical map to the ordinary total tensor complex.

No boundedness hypothesis is imposed on `K` or `M`: the source imposes none, and neither the
naive cup product nor any step of the argument needs one.  The only binders beyond the source's
data are `hmos`, the assertion that `f` is a morphism of ringed topoi in the source's sense,
which `AlgebraicGeometry.RingedToposSiteHom` does not record as a field, and `Prop`-class
existence instances for the derived functors; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/OrdinaryAndDerivedCounit.lean`.

## References

* [Stacks Project, Tag 0FPK](https://stacks.math.columbia.edu/tag/0FPK)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.NaiveCupProduct
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Cohomology.CupProductAndDerivedPushforward

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ## Diagram bookkeeping

Both proofs below are instances of two statements about an adjunction and two bifunctors, proved
here once in abstract categories.  Stating them abstractly is what lets the existing inputs be
supplied up to definitional equality: the development spells the category of modules on a ringed
topos both as `SheafOfModules X.ringSheaf` and as
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)`, and a rewrite cannot cross between
the two. -/

section Bookkeeping

variable {𝒞 : Type*} {𝒟 : Type*} [Category 𝒞] [Category 𝒟] {L : 𝒟 ⥤ 𝒞} {R : 𝒞 ⥤ 𝒟}

/-- A comparison `η : B ⟶ R(W)` whose transpose factors as `p ≫ q`, composed with a map
`R(c₂)` on the right, transposes to `p ≫ e` followed by `r`, provided `q ≫ c₂ = e ≫ r`. -/
lemma counit_comp_of_counit_fac (adj : L ⊣ R) {A B : 𝒟} {W Z P E : 𝒞}
    (c₁ : A ⟶ B) (η : B ⟶ R.obj W) (c₂ : W ⟶ Z) (p : L.obj B ⟶ P) (q : P ⟶ W)
    (e : P ⟶ E) (r : E ⟶ Z)
    (h : L.map η ≫ adj.counit.app W = p ≫ q) (k : q ≫ c₂ = e ≫ r) :
    L.map (c₁ ≫ η ≫ R.map c₂) ≫ adj.counit.app Z = (L.map c₁ ≫ p ≫ e) ≫ r := by
  have hc : L.map (R.map c₂) ≫ adj.counit.app Z = adj.counit.app W ≫ c₂ :=
    adj.counit.naturality c₂
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hc,
    ← Category.assoc (L.map η), h, Category.assoc, Category.assoc, k]
  simp only [Category.assoc]

/-- **The abstract hexagon.**  For an adjunction `L ⊣ R`, bifunctors `TY` on the base of `R` and
`TX` on its target, comparisons `ηa`, `ηb` into `R`, and a map `cup` whose transpose is a
comparison followed by the counit in both factors, the two routes from `TY(a, b)` to `R(T)` agree
as soon as the transposed diagram does. -/
lemma hexagon_of_transposes (adj : L ⊣ R) (TY : 𝒟 ⥤ 𝒟 ⥤ 𝒟) (TX : 𝒞 ⥤ 𝒞 ⥤ 𝒞)
    {a b S S' : 𝒟} {A B T Pa Pb PS PT G : 𝒞}
    (ηa : a ⟶ R.obj A) (ηb : b ⟶ R.obj B)
    (tY : (TY.obj a).obj b ⟶ S) (ν : S ⟶ S') (ηT : S' ⟶ R.obj T)
    (cup : (TY.obj (R.obj A)).obj (R.obj B) ⟶ R.obj ((TX.obj A).obj B))
    (tX : (TX.obj A).obj B ⟶ T)
    (α : L.obj ((TY.obj a).obj b) ⟶ (TX.obj (L.obj a)).obj (L.obj b))
    (αR : L.obj ((TY.obj (R.obj A)).obj (R.obj B)) ⟶
      (TX.obj (L.obj (R.obj A))).obj (L.obj (R.obj B)))
    (ca : L.obj a ⟶ Pa) (qa : Pa ⟶ A) (cb : L.obj b ⟶ Pb) (qb : Pb ⟶ B)
    (cS : L.obj S ⟶ PS) (cT : L.obj S' ⟶ PT) (qT : PT ⟶ T) (nT : PS ⟶ PT)
    (w : PS ⟶ G) (m : G ⟶ T) (tXp : (TX.obj Pa).obj Pb ⟶ G)
    (hcup : (adj.homEquiv _ _).symm cup =
      αR ≫ bifunctorMap TX (adj.counit.app A) (adj.counit.app B))
    (hα : L.map (bifunctorMap TY ηa ηb) ≫ αR = α ≫ bifunctorMap TX (L.map ηa) (L.map ηb))
    (hga : L.map ηa ≫ adj.counit.app A = ca ≫ qa)
    (hgb : L.map ηb ≫ adj.counit.app B = cb ≫ qb)
    (hgT : L.map ηT ≫ adj.counit.app T = cT ≫ qT)
    (hν : L.map ν ≫ cT = cS ≫ nT) (hn : nT ≫ qT = w ≫ m)
    (h0 : L.map tY ≫ cS ≫ w = α ≫ bifunctorMap TX ca cb ≫ tXp)
    (ht : tXp ≫ m = bifunctorMap TX qa qb ≫ tX) :
    tY ≫ ν ≫ ηT = bifunctorMap TY ηa ηb ≫ cup ≫ R.map tX := by
  refine (adj.homEquiv _ _).symm.injective ?_
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, hcup]
  simp only [Category.assoc]
  rw [hgT, reassoc_of% hν, hn, reassoc_of% h0, ht,
    reassoc_of% (bifunctorMap_comp TX ca qa cb qb), ← hga, ← hgb,
    ← bifunctorMap_comp TX (L.map ηa) (adj.counit.app A) (L.map ηb) (adj.counit.app B),
    reassoc_of% hα]
  simp only [Category.assoc]

end Bookkeeping

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/-! ## The comparison `f_* ⟶ Rf_*` at the localization functor -/

/-- **The comparison `Q(f_*K) ⟶ Rf_*(QK)`** of degreewise pushforward with the derived
pushforward, from the image in `D(O_D)` of the degreewise pushforward of a complex of
`O_C`-modules to the derived pushforward of its image in `D(O_C)`.  It is the canonical
comparison of the derived functor with the two identifications between `Q` and `Qh ∘ quotient`
inserted at either end. -/
def pushforwardComparisonQ
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj ((pushforwardComplex f).obj K) ⟶
      (derivedPushforward f).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app
        ((pushforwardComplex f).obj K) ≫
    ((derivedPushforwardUnit f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      (derivedPushforward f).map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app K))

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The comparison `f_* ⟶ Rf_*` is natural in the complex.** -/
lemma pushforwardComparisonQ_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (a : K ⟶ L) :
    DerivedCategory.Q.map ((pushforwardComplex f).map a) ≫ pushforwardComparisonQ f L =
      pushforwardComparisonQ f K ≫ (derivedPushforward f).map (DerivedCategory.Q.map a) := by
  have h₁ := DerivedCategory.quotientCompQhIso_inv_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((pushforwardComplex f).map a)
  have h₂ := (derivedPushforwardUnit f).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have h₃ : (derivedPushforward f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) ≫
        (derivedPushforward f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app L) =
      (derivedPushforward f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app K) ≫
        (derivedPushforward f).map (DerivedCategory.Q.map a) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      DerivedCategory.quotientCompQhIso_hom_naturality]
  exact comp_naturality h₁ (comp_naturality h₂ h₃)

/-! ## Stacks 0FPI at the localization functor -/

section Counit

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
/-- The counit of `f^* ⊣ f_*` on the homotopy categories is the class of the counit on
complexes. -/
lemma homotopyCounit_app_quotient
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (homotopyPullbackPushforwardAdjunction f).counit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((complexAdjunction f).counit.app N) := rfl

include hmos in
/-- **Stacks 0FPI read at the localization functor `Q`.**  For a complex `N` of `O_C`-modules the
square whose upper edge is `Lf^*` of the comparison `f_* ⟶ Rf_*`, whose lower edge is the counit
of `Lf^* ⊣ Rf_*`, whose left edge is the comparison `Lf^* ⟶ f^*` and whose right edge is the
ordinary counit `f^*f_* ⟶ id` commutes in `D(O_C)`. -/
theorem derivedCounit_pushforwardComparisonQ
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedPullback f).map (pushforwardComparisonQ f N) ≫
        (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).counit.app
          (DerivedCategory.Q.obj N) =
      pullbackComparisonQ f ((pushforwardComplex f).obj N) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app N) :=
  counit_comp_of_counit_fac (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app
      ((pushforwardComplex f).obj N))
    ((derivedPushforwardUnit f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app N)
    ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((pushforwardComplex f).obj N)))
    (DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).counit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)))
    ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
      ((pullbackComplex f).obj ((pushforwardComplex f).obj N)))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app N))
    (DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac f hmos _)
    (DerivedCategory.quotientCompQhIso_hom_naturality ((complexAdjunction f).counit.app N))

end Counit

/-! ## Stacks 0FPK -/

section Square

variable [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

include hmos in
/-- **Stacks 0FPK, site-presented.**  For a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` presented by a morphism of sites and
unbounded cochain complexes `K`, `M` of `O_C`-modules, the hexagon

```
f_*K ⊗^L_{O_D} f_*M ───────────→ Rf_*K ⊗^L_{O_D} Rf_*M
        │                                 │
        ↓                                 ↓
Tot(f_*K ⊗_{O_D} f_*M)            Rf_*(K ⊗^L_{O_C} M)
        │                                 │
        ↓                                 ↓
f_*Tot(K ⊗_{O_C} M) ───────────→ Rf_*Tot(K ⊗_{O_C} M)
```

commutes in `D(O_D)`.  Its horizontal edges and its top right edge are the comparison
`f_* ⟶ Rf_*`; the top left and bottom right edges are the canonical map from the derived tensor
product to the ordinary total tensor complex of Stacks 06YU; the middle left edge is the naive
cup product and the middle right edge is the relative cup product of Stacks 0B6C. -/
@[stacks 0FPK "variant: the special case of a morphism of ringed topoi presented by a morphism of
sites; the tag for an arbitrary morphism of ringed topoi is
Stacks.Cohomology.CupProductAndDerivedPushforwardOfToposHom.naiveCupProduct_relativeCupProduct"]
theorem naiveCupProduct_relativeCupProduct
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (canonicalDerivedTensorProduct Y.O).toTensor ((pushforwardComplex f).obj K)
          ((pushforwardComplex f).obj M) ≫
        DerivedCategory.Q.map (naiveCupProduct f hmos K M) ≫
        pushforwardComparisonQ f (HomologicalComplex.mapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) =
      bifunctorMap (derivedTensorProductFunctor Y.O) (pushforwardComparisonQ f K)
            (pushforwardComparisonQ f M) ≫
        relativeCupProduct f hmos (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≫
        (derivedPushforward f).map ((canonicalDerivedTensorProduct X.O).toTensor K M) := by
  have hcomparison := (derivedPullbackTensorIso f hmos).hom.naturality
    ((pushforwardComparisonQ f K, pushforwardComparisonQ f M) :
      ((DerivedCategory.Q.obj ((pushforwardComplex f).obj K),
        DerivedCategory.Q.obj ((pushforwardComplex f).obj M)) : _ × _) ⟶
      ((derivedPushforward f).obj (DerivedCategory.Q.obj K),
        (derivedPushforward f).obj (DerivedCategory.Q.obj M)))
  exact hexagon_of_transposes (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (derivedTensorProductFunctor Y.O) (derivedTensorProductFunctor X.O)
    (pushforwardComparisonQ f K) (pushforwardComparisonQ f M)
    ((canonicalDerivedTensorProduct Y.O).toTensor ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M))
    (DerivedCategory.Q.map (naiveCupProduct f hmos K M))
    (pushforwardComparisonQ f (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)))
    (relativeCupProduct f hmos (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M))
    ((canonicalDerivedTensorProduct X.O).toTensor K M)
    (derivedPullbackTensorComparison f hmos
      (DerivedCategory.Q.obj ((pushforwardComplex f).obj K))
      (DerivedCategory.Q.obj ((pushforwardComplex f).obj M)))
    (derivedPullbackTensorComparison f hmos
      ((derivedPushforward f).obj (DerivedCategory.Q.obj K))
      ((derivedPushforward f).obj (DerivedCategory.Q.obj M)))
    (pullbackComparisonQ f ((pushforwardComplex f).obj K))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app K))
    (pullbackComparisonQ f ((pushforwardComplex f).obj M))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app M))
    (pullbackComparisonQ f (HomologicalComplex.mapBifunctor ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M) (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)))
    (pullbackComparisonQ f ((pushforwardComplex f).obj (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))))
    (DerivedCategory.Q.map ((pullbackComplex f).map (naiveCupProduct f hmos K M)))
    (DerivedCategory.Q.map (pullbackToposTensorTotalIso f hmos ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M)).hom)
    (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      ((complexAdjunction f).counit.app K) ((complexAdjunction f).counit.app M)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)))
    ((canonicalDerivedTensorProduct X.O).toTensor
      ((pullbackComplex f).obj ((pushforwardComplex f).obj K))
      ((pullbackComplex f).obj ((pushforwardComplex f).obj M)))
    (Equiv.symm_apply_apply _ _) hcomparison
    (derivedCounit_pushforwardComparisonQ f hmos K)
    (derivedCounit_pushforwardComparisonQ f hmos M)
    (derivedCounit_pushforwardComparisonQ f hmos (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)))
    (pullbackComparisonQ_naturality f (naiveCupProduct f hmos K M))
    (by rw [← Functor.map_comp, ← Functor.map_comp, pullbackComplex_naiveCupProduct_counit])
    (derivedPullback_toTensor_square f hmos ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M))
    (((canonicalDerivedTensorProduct X.O).toTensor_naturality _ _).symm.trans
      (Category.assoc _ _ _).symm)

end Square

end Stacks.Cohomology.CupProductAndDerivedPushforward

end
