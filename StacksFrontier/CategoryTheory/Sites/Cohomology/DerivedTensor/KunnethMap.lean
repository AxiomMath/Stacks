module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth map for a square of morphisms of ringed topoi

Let
```
W --q--> Y
|        |
p        g
↓        ↓
X --f--> S
```
be morphisms of ringed topoi and let `c : W ⟶ S` be a morphism with `c = f ∘ p = g ∘ q`.  For
`E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)` there is a canonical map

`Rf_*E ⊗^L_{𝒪_S} Rg_*K ⟶ Rc_*(Lp^*E ⊗^L_{𝒪_W} Lq^*K)`,

the Künneth map of [Stacks, Tag 0F1E].  It has two descriptions, which agree.

The first is the canonical maps `Rf_*E ⟶ Rc_*Lp^*E` and `Rg_*K ⟶ Rc_*Lq^*K` in the two tensor
factors, followed by the relative cup product `Rc_*A ⊗^L Rc_*B ⟶ Rc_*(A ⊗^L B)` of
[Stacks, Tag 0B6C].  The second is the adjoint, for `Lc^* ⊣ Rc_*`, of

`Lc^*(Rf_*E ⊗^L Rg_*K) ≅ Lc^*Rf_*E ⊗^L Lc^*Rg_*K ⟶ Lp^*E ⊗^L Lq^*K`,

whose first step is the compatibility of derived pullback with the derived tensor product
([Stacks, Tag 07A4]) and whose second is, in each factor, the map `Lc^*Rf_*E ⟶ Lp^*E` got from
`Lc^* ≅ Lf^* ⋙ Lp^*` ([Stacks, Tag 0D6D]) and the counit `Lf^*Rf_* ⟶ id`.

## Main definitions

* `Stacks.Cohomology.KunnethMapOnRingedTopoi.adjunctionCupProductOfMaps`: for an adjunction
  `L ⊣ R` and maps `L M ⟶ G`, `L N ⟶ H`, the map `A(M, N) ⟶ R (B(G, H))`.
* `Stacks.Cohomology.KunnethMapOnRingedTopoi.pullbackDirectImageCounit`: the map
  `Lc^*Rf_*E ⟶ Lp^*E`.
* `Stacks.Cohomology.KunnethMapOnRingedTopoi.directImageMap`: the canonical map
  `Rf_*E ⟶ Rc_*Lp^*E`.
* `Stacks.Cohomology.KunnethMapOnRingedTopoi.kunnethMapOfCupProduct`: the Künneth map, by the
  first description.
* `Stacks.Cohomology.KunnethMapOnRingedTopoi.kunnethMapOfAdjoint`: the Künneth map, by the second
  description.

## Main results

* `Stacks.Cohomology.KunnethMapOnRingedTopoi.map_homEquiv_comp_adjunctionCupProduct`:
  precomposing `adjunctionCupProduct` with the adjoint transposes of `u` and `v` gives
  `adjunctionCupProductOfMaps u v`.
* `Stacks.Cohomology.KunnethMapOnRingedTopoi.kunnethMapOfCupProduct_eq_kunnethMapOfAdjoint`: the
  two descriptions of the Künneth map agree.

## References

* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.KunnethMapOnRingedTopoi

/-! ### The cup product of an abstract adjunction, out of an arbitrary pair of objects -/

section Abstract

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The canonical map `A(M, N) ⟶ R (B(G, H))` attached to maps `u : L M ⟶ G` and `v : L N ⟶ H`:
the adjoint transpose of the comparison `α` followed by `u` and `v` in the two factors.

At `M = R G`, `N = R H` and the counits this is
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct`. -/
def adjunctionCupProductOfMaps {M N : C} {G H : D} (u : L.obj M ⟶ G) (v : L.obj N ⟶ H) :
    A.obj (M, N) ⟶ R.obj (B.obj (G, H)) :=
  adj.homEquiv _ _ (α.app (M, N) ≫ B.map (u ×ₘ v))

/-- The map of `adjunctionCupProductOfMaps`, written through the unit of the adjunction. -/
lemma adjunctionCupProductOfMaps_eq_unit_comp {M N : C} {G H : D} (u : L.obj M ⟶ G)
    (v : L.obj N ⟶ H) :
    adjunctionCupProductOfMaps adj A B α u v =
      adj.unit.app (A.obj (M, N)) ≫ R.map (α.app (M, N) ≫ B.map (u ×ₘ v)) :=
  Adjunction.homEquiv_unit adj _ _ _

/-- The cup product of `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct`
is the case of `adjunctionCupProductOfMaps` in which the two maps are the counits. -/
lemma adjunctionCupProduct_eq_adjunctionCupProductOfMaps (G H : D) :
    RelativeCupProductOnRingedTopoi.adjunctionCupProduct adj A B α G H =
      adjunctionCupProductOfMaps adj A B α (adj.counit.app G) (adj.counit.app H) :=
  rfl

/-- **The two constructions agree, abstractly.**  Precomposing the cup product of
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct` with `A` applied to the
adjoint transposes of `u` and `v` returns `adjunctionCupProductOfMaps u v`. -/
lemma map_homEquiv_comp_adjunctionCupProduct {M N : C} {G H : D} (u : L.obj M ⟶ G)
    (v : L.obj N ⟶ H) :
    A.map (adj.homEquiv M G u ×ₘ adj.homEquiv N H v) ≫
        RelativeCupProductOnRingedTopoi.adjunctionCupProduct adj A B α G H =
      adjunctionCupProductOfMaps adj A B α u v := by
  apply (adj.homEquiv _ _).symm.injective
  unfold RelativeCupProductOnRingedTopoi.adjunctionCupProduct adjunctionCupProductOfMaps
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  have ha := α.naturality (adj.homEquiv M G u ×ₘ adj.homEquiv N H v)
  change L.map (A.map (adj.homEquiv M G u ×ₘ adj.homEquiv N H v)) ≫
      α.app (R.obj G, R.obj H) =
    α.app (M, N) ≫ B.map (L.map (adj.homEquiv M G u) ×ₘ L.map (adj.homEquiv N H v)) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  congr 2
  exact Prod.ext ((adj.homEquiv_counit M G _).symm.trans ((adj.homEquiv M G).symm_apply_apply u))
    ((adj.homEquiv_counit N H _).symm.trans ((adj.homEquiv N H).symm_apply_apply v))

end Abstract

/-! ### The Künneth map -/

attribute [local instance] HasDerivedCategory.standard

universe u

variable {W X Y S : RingedTopos.{u, u, u}}
  [W.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify W.J AddCommGrpCat.{u}] [W.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify S.J AddCommGrpCat.{u}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (p : RingedToposSiteHom W X) (f : RingedToposSiteHom X S)
  (c : RingedToposSiteHom W S)
  [(pullbackOnHomotopy p).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy c).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      (ComplexShape.up ℤ))]
  (hmosp : p.u.IsMorphismOfSites X.J W.J) (hmosf : f.u.IsMorphismOfSites S.J X.J)
  (hmosc : c.u.IsMorphismOfSites S.J W.J)

/-- The map `Lc^*Rf_*E ⟶ Lp^*E` for a factorization `c = f ∘ p`: the isomorphism
`Lc^* ≅ Lf^* ⋙ Lp^*` of [Stacks, Tag 0D6D], followed by `Lp^*` of the counit of
`Lf^* ⊣ Rf_*`. -/
def pullbackDirectImageCounit (hp : f.comp p = c)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPullback c).obj ((derivedPushforward f).obj E) ⟶ (derivedPullback p).obj E :=
  letI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (f.comp p) (RingedToposSiteHom.isMorphismOfSites_comp_u p f hmosp hmosf)
  (DerivedBaseChangeOnTopoi.derivedPullbackCongr hp).inv.app ((derivedPushforward f).obj E) ≫
    (DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso p f hmosp hmosf).inv.app
      ((derivedPushforward f).obj E) ≫
    (derivedPullback p).map
      ((DerivedPullbackOnRingedTopoi.derivedAdjunction f hmosf).counit.app E)

/-- **The canonical map `Rf_*E ⟶ Rc_*Lp^*E`** for a factorization `c = f ∘ p`: the adjoint
transpose, for `Lc^* ⊣ Rc_*`, of `pullbackDirectImageCounit`. -/
@[stacks 0F1E "the canonical map Rf_*E ⟶ Rc_*p⁻¹E"]
def directImageMap (hp : f.comp p = c)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).obj E ⟶
      (derivedPushforward c).obj ((derivedPullback p).obj E) :=
  (DerivedPullbackOnRingedTopoi.derivedAdjunction c hmosc).homEquiv _ _
    (pullbackDirectImageCounit p f c hmosp hmosf hp E)

section Kunneth

variable (q : RingedToposSiteHom W Y) (g : RingedToposSiteHom Y S)
  [(pullbackOnHomotopy q).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
      (ComplexShape.up ℤ))]
  (hmosq : q.u.IsMorphismOfSites Y.J W.J) (hmosg : g.u.IsMorphismOfSites S.J Y.J)
  [(Stacks.SheafOfModules.Tensor.sheafTensor W.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor W.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor S.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor S.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor W.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor S.O)
      (ComplexShape.up ℤ)]
  (hp : f.comp p = c) (hq : g.comp q = c)
  (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- **The Künneth map, via the relative cup product.**  For morphisms of ringed topoi
`p : W ⟶ X`, `f : X ⟶ S`, `q : W ⟶ Y`, `g : Y ⟶ S` and `c : W ⟶ S` with `c = f ∘ p = g ∘ q`,
and for `E ∈ D(𝒪_X)`, `K ∈ D(𝒪_Y)`, the canonical map

`Rf_*E ⊗^L_{𝒪_S} Rg_*K ⟶ Rc_*(Lp^*E ⊗^L_{𝒪_W} Lq^*K)`.

It is the canonical maps `Rf_*E ⟶ Rc_*Lp^*E` and `Rg_*K ⟶ Rc_*Lq^*K` in the two tensor factors,
followed by the relative cup product of [Stacks, Tag 0B6C] for `c`. -/
@[stacks 0F1E "the canonical map, via the relative cup product of Remark 0B6C"]
def kunnethMapOfCupProduct :
    ((derivedTensorProductFunctor S.O).obj ((derivedPushforward f).obj E)).obj
        ((derivedPushforward g).obj K) ⟶
      (derivedPushforward c).obj
        (((derivedTensorProductFunctor W.O).obj ((derivedPullback p).obj E)).obj
          ((derivedPullback q).obj K)) :=
  ((derivedTensorProductFunctor S.O).map
        (directImageMap p f c hmosp hmosf hmosc hp E)).app ((derivedPushforward g).obj K) ≫
    ((derivedTensorProductFunctor S.O).obj
        ((derivedPushforward c).obj ((derivedPullback p).obj E))).map
      (directImageMap q g c hmosq hmosg hmosc hq K) ≫
    RelativeCupProductOnRingedTopoi.relativeCupProduct c hmosc
      ((derivedPullback p).obj E) ((derivedPullback q).obj K)

/-- **The Künneth map, as an adjoint.**  The same canonical map

`Rf_*E ⊗^L_{𝒪_S} Rg_*K ⟶ Rc_*(Lp^*E ⊗^L_{𝒪_W} Lq^*K)`,

written as the adjoint, for `Lc^* ⊣ Rc_*`, of the compatibility of derived pullback with the
derived tensor product ([Stacks, Tag 07A4]) followed by the maps `Lc^*Rf_*E ⟶ Lp^*E` and
`Lc^*Rg_*K ⟶ Lq^*K` in the two factors. -/
@[stacks 0F1E "the canonical map, as the adjoint of the map on inverse images"]
def kunnethMapOfAdjoint :
    ((derivedTensorProductFunctor S.O).obj ((derivedPushforward f).obj E)).obj
        ((derivedPushforward g).obj K) ⟶
      (derivedPushforward c).obj
        (((derivedTensorProductFunctor W.O).obj ((derivedPullback p).obj E)).obj
          ((derivedPullback q).obj K)) :=
  adjunctionCupProductOfMaps (DerivedPullbackOnRingedTopoi.derivedAdjunction c hmosc)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.O))
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso c hmosc).hom
    (pullbackDirectImageCounit p f c hmosp hmosf hp E)
    (pullbackDirectImageCounit q g c hmosq hmosg hq K)

/-- **The two constructions of the Künneth map agree**: `kunnethMapOfCupProduct` equals
`kunnethMapOfAdjoint`. -/
@[stacks 0F1E "the two constructions of the remark agree"]
theorem kunnethMapOfCupProduct_eq_kunnethMapOfAdjoint :
    kunnethMapOfCupProduct p f c hmosp hmosf hmosc q g hmosq hmosg hp hq E K =
      kunnethMapOfAdjoint p f c hmosp hmosf hmosc q g hmosq hmosg hp hq E K := by
  have h := map_homEquiv_comp_adjunctionCupProduct
    (DerivedPullbackOnRingedTopoi.derivedAdjunction c hmosc)
    (Functor.uncurry.obj (derivedTensorProductFunctor S.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor W.O))
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso c hmosc).hom
    (pullbackDirectImageCounit p f c hmosp hmosf hp E)
    (pullbackDirectImageCounit q g c hmosq hmosg hq K)
  simp only [Functor.uncurry_obj_map, Category.assoc] at h
  exact h

end Kunneth

end Stacks.Cohomology.KunnethMapOnRingedTopoi

end
