module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.KunnethMap
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The Künneth map, the projection map and the base change map for a square of adjunctions

Let
```
W --q--> Y
|        |
p        g
↓        ↓
X --f--> S
```
be a square, `c : W ⟶ S` its diagonal, and suppose the inverse images `f^*, g^*, p^*, q^*, c^*`
are given as functors between categories `D(X)`, `D(Y)`, `D(W)`, `D(S)` that carry tensor
products `⊗_S`, `⊗_W`, with right adjoints `f_* , g_*, c_*` and a comparison
`μ : c^*(M ⊗_S N) ⟶ c^*M ⊗_W c^*N`. Given identifications `f^* ⋙ p^* ≅ c^*` and
`g^* ⋙ q^* ≅ c^*` of the two composite inverse images, there is a canonical map

`f_*E ⊗_S g_*K ⟶ c_*(p^*E ⊗_W q^*K)`,

the Künneth map of [Stacks, Tag 0F1E]. This file constructs it, together with the two other
canonical maps the Künneth section of the étale cohomology chapter is built from:

* the **projection map** `A ⊗_X h_*B ⟶ h_*(h^*A ⊗_Y B)` of a single adjunction `h^* ⊣ h_*`;
* the **base change map** `(f')^* g_* ⟶ h_* e^*` of a commutative square of adjunctions, and
  the composite `A ⊗ (f')^*g_*F ⟶ h_*(h^*A ⊗ e^*F)` of the two which is the canonical map of
  [Stacks, Tag 0F1J] and [Stacks, Tag 0F1N].

## Why a separate abstract version

`Stacks.Cohomology.KunnethMapOnRingedTopoi.kunnethMapOfAdjoint` builds the Künneth map for
morphisms of ringed topoi `AlgebraicGeometry.RingedTopos.{u, u, u}`, and it takes the two
factorizations of the diagonal as **equalities** `f.comp p = c` and `g.comp q = c` of morphisms
of ringed topoi. On a site with chosen fibre products, such as the small étale site of a scheme,
the two composite base change functors `S_ét ⥤ (X ×_S Y)_ét` of a fibre square are isomorphic
but never equal, so no choice of `c` satisfies both equalities; and the small étale site is not a
`RingedTopos.{u, u, u}`. The construction below asks for nothing but the adjunctions, the tensor
comparison and the two **isomorphisms** of composite inverse images, at arbitrary universes, and
`kunnethMapOfAdjoint_eq_kunnethMap` shows that the ringed-topos map is its special case.

## Main definitions

All in the namespace `Stacks.Cohomology.AbstractKunnethMap`.

* `pullbackPushforwardCounit` — the map `c^*f_*E ⟶ p^*E` attached to `f^* ⋙ p^* ≅ c^*`.
* `directImageMap` — its adjoint transpose `f_*E ⟶ c_*p^*E`.
* `externalProduct` — the external product `(E, K) ↦ p^*E ⊗_W q^*K`.
* `kunnethMap` — **the Künneth map** `f_*E ⊗_S g_*K ⟶ c_*(p^*E ⊗_W q^*K)`, and `kunnethNatTrans`,
  the same map as a natural transformation of bifunctors.
* `projectionMap` — the projection map `A ⊗_X h_*B ⟶ h_*(h^*A ⊗_Y B)`.
* `baseChangeMap` — the base change map `(f')^*g_* ⟶ h_*e^*`, the mate of `(f')^* ⋙ h^* ≅
  g^* ⋙ e^*`.
* `tensorBaseChangeMap` — the canonical map `A ⊗ (f')^*g_*F ⟶ h_*(h^*A ⊗ e^*F)`.

## Main results

* `kunnethMap_eq_cupProduct` — the Künneth map is the two maps `f_*E ⟶ c_*p^*E` and
  `g_*K ⟶ c_*q^*K` followed by the relative cup product of `c`: the two constructions of
  [Stacks, Tag 0F1E] agree.
* `kunnethMap_naturality` — the Künneth map is natural in both variables.
* `projectionMap_eq_kunnethMap` — the projection map is the Künneth map of the square with
  `f = id` and `q = id`.
* `baseChangeMap_counit` — the defining property of the base change map.
* `tensorBaseChangeMap_eq_adjunctionCupProductOfMaps` — the canonical map of Tags 0F1J and 0F1N
  is the adjoint of `h^*(A ⊗ (f')^*g_*F) ⟶ h^*A ⊗ h^*(f')^*g_*F ≅ h^*A ⊗ e^*g^*g_*F ⟶
  h^*A ⊗ e^*F`, which is how the source describes it.
* `kunnethMapOfAdjoint_eq_kunnethMap` — the Künneth map of morphisms of ringed topoi in
  `Stacks.Cohomology.KunnethMapOnRingedTopoi` is `kunnethMap` at the derived adjunctions and the
  isomorphism of [Stacks, Tag 0D6D].

## References

* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.AbstractKunnethMap

open KunnethMapOnRingedTopoi RelativeCupProductOnRingedTopoi

/-! ### The Künneth map of a square -/

section Square

/-- Precomposing `adjunctionCupProductOfMaps` with `A` of a pair of maps precomposes `u` and `v`
with `L` of these maps. -/
private theorem map_comp_adjunctionCupProductOfMaps {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) {M M' N N' : C} {G H : D} (a : M ⟶ M') (b : N ⟶ N')
    (u : L.obj M' ⟶ G) (v : L.obj N' ⟶ H) :
    A.map (a ×ₘ b) ≫ adjunctionCupProductOfMaps adj A B α u v =
      adjunctionCupProductOfMaps adj A B α (L.map a ≫ u) (L.map b ≫ v) := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionCupProductOfMaps
  rw [Adjunction.homEquiv_naturality_left_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  have ha := α.naturality (a ×ₘ b)
  change L.map (A.map (a ×ₘ b)) ≫ α.app (M', N') =
    α.app (M, N) ≫ B.map (L.map a ×ₘ L.map b) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  simp

/-- Postcomposing `adjunctionCupProductOfMaps` with `R (B (g ×ₘ h))` postcomposes `u` and `v`. -/
private theorem adjunctionCupProductOfMaps_comp_map {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
    (α : A ⋙ L ⟶ L.prod L ⋙ B) {M N : C} {G G' H H' : D} (u : L.obj M ⟶ G) (v : L.obj N ⟶ H)
    (g : G ⟶ G') (h : H ⟶ H') :
    adjunctionCupProductOfMaps adj A B α u v ≫ R.map (B.map (g ×ₘ h)) =
      adjunctionCupProductOfMaps adj A B α (u ≫ g) (v ≫ h) := by
  simp [adjunctionCupProductOfMaps, ← Adjunction.homEquiv_naturality_right, ← Functor.map_comp]

variable {DW DX DY DS : Type*} [Category* DW] [Category* DX] [Category* DY] [Category* DS]
  (TS : DS × DS ⥤ DS) (TW : DW × DW ⥤ DW)
  {fPull : DS ⥤ DX} {fPush : DX ⥤ DS} (adjf : fPull ⊣ fPush)
  {gPull : DS ⥤ DY} {gPush : DY ⥤ DS} (adjg : gPull ⊣ gPush)
  {cPull : DS ⥤ DW} {cPush : DW ⥤ DS} (adjc : cPull ⊣ cPush)
  (pPull : DX ⥤ DW) (qPull : DY ⥤ DW)
  (μ : TS ⋙ cPull ⟶ cPull.prod cPull ⋙ TW)
  (ep : fPull ⋙ pPull ≅ cPull) (eq : gPull ⋙ qPull ≅ cPull)

/-- The map `c^*f_*E ⟶ p^*E` attached to an identification `f^* ⋙ p^* ≅ c^*`: the inverse of
that identification at `f_*E`, followed by `p^*` of the counit of `f^* ⊣ f_*`. -/
def pullbackPushforwardCounit (E : DX) : cPull.obj (fPush.obj E) ⟶ pPull.obj E :=
  ep.inv.app (fPush.obj E) ≫ pPull.map (adjf.counit.app E)

/-- The canonical map `f_*E ⟶ c_*p^*E` of [Stacks, Tag 0F1E]: the adjoint transpose, for
`c^* ⊣ c_*`, of `pullbackPushforwardCounit`. -/
def directImageMap (E : DX) : fPush.obj E ⟶ cPush.obj (pPull.obj E) :=
  adjc.homEquiv _ _ (pullbackPushforwardCounit adjf pPull ep E)

/-- The external product `(E, K) ↦ p^*E ⊗_W q^*K` of an object over `X` and an object over `Y`,
an object over the corner `W` of the square. -/
abbrev externalProduct : DX × DY ⥤ DW := pPull.prod qPull ⋙ TW

/-- **The Künneth map** `f_*E ⊗_S g_*K ⟶ c_*(p^*E ⊗_W q^*K)` of [Stacks, Tag 0F1E], built from
two isomorphisms `f^* ⋙ p^* ≅ c^*` and `g^* ⋙ q^* ≅ c^*` rather than from equalities: the
adjoint, for `c^* ⊣ c_*`, of the comparison `μ` followed in the two factors by the maps
`c^*f_*E ⟶ p^*E` and `c^*g_*K ⟶ q^*K`. -/
def kunnethMap (E : DX) (K : DY) :
    TS.obj (fPush.obj E, gPush.obj K) ⟶ cPush.obj (TW.obj (pPull.obj E, qPull.obj K)) :=
  adjunctionCupProductOfMaps adjc TS TW μ (pullbackPushforwardCounit adjf pPull ep E)
    (pullbackPushforwardCounit adjg qPull eq K)

/-- **The two constructions of [Stacks, Tag 0F1E] agree.** The Künneth map is the canonical maps
`f_*E ⟶ c_*p^*E` and `g_*K ⟶ c_*q^*K` in the two tensor factors, followed by the relative cup
product `c_*A ⊗ c_*B ⟶ c_*(A ⊗ B)` of [Stacks, Tag 0B6C]. -/
theorem kunnethMap_eq_cupProduct (E : DX) (K : DY) :
    kunnethMap TS TW adjf adjg adjc pPull qPull μ ep eq E K =
      TS.map (directImageMap adjf adjc pPull ep E ×ₘ directImageMap adjg adjc qPull eq K) ≫
        adjunctionCupProduct adjc TS TW μ (pPull.obj E) (qPull.obj K) :=
  (map_homEquiv_comp_adjunctionCupProduct adjc TS TW μ _ _).symm

/-- The map `c^*f_*E ⟶ p^*E` is natural in `E`. -/
theorem pullbackPushforwardCounit_naturality {E E' : DX} (a : E ⟶ E') :
    cPull.map (fPush.map a) ≫ pullbackPushforwardCounit adjf pPull ep E' =
      pullbackPushforwardCounit adjf pPull ep E ≫ pPull.map a := by
  have h := ep.inv.naturality (fPush.map a)
  dsimp at h
  simp only [pullbackPushforwardCounit, ← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp, Adjunction.counit_naturality]

/-- **The Künneth map is natural in both variables.** -/
theorem kunnethMap_naturality {E E' : DX} {K K' : DY} (a : E ⟶ E') (b : K ⟶ K') :
    TS.map (fPush.map a ×ₘ gPush.map b) ≫
        kunnethMap TS TW adjf adjg adjc pPull qPull μ ep eq E' K' =
      kunnethMap TS TW adjf adjg adjc pPull qPull μ ep eq E K ≫
        cPush.map (TW.map (pPull.map a ×ₘ qPull.map b)) := by
  unfold kunnethMap
  rw [map_comp_adjunctionCupProductOfMaps, adjunctionCupProductOfMaps_comp_map,
    pullbackPushforwardCounit_naturality, pullbackPushforwardCounit_naturality]

/-- **The Künneth map as a natural transformation** `f_*(-) ⊗_S g_*(-) ⟶ c_*(p^*(-) ⊗_W q^*(-))`
of bifunctors `D(X) × D(Y) ⥤ D(S)`. -/
@[simps]
def kunnethNatTrans :
    fPush.prod gPush ⋙ TS ⟶ externalProduct TW pPull qPull ⋙ cPush where
  app EK := kunnethMap TS TW adjf adjg adjc pPull qPull μ ep eq EK.1 EK.2
  naturality _ _ ab := kunnethMap_naturality TS TW adjf adjg adjc pPull qPull μ ep eq ab.1 ab.2

end Square

/-! ### The projection map -/

section Projection

variable {DX DY : Type*} [Category* DX] [Category* DY]
  (TX : DX × DX ⥤ DX) (TY : DY × DY ⥤ DY)
  {hPull : DX ⥤ DY} {hPush : DY ⥤ DX} (adjh : hPull ⊣ hPush)
  (μ : TX ⋙ hPull ⟶ hPull.prod hPull ⋙ TY)

/-- **The projection map** `A ⊗_X h_*B ⟶ h_*(h^*A ⊗_Y B)` of an adjunction `h^* ⊣ h_*` and a
comparison `μ : h^*(M ⊗ N) ⟶ h^*M ⊗ h^*N`: the adjoint of `μ` followed by the counit
`h^*h_*B ⟶ B` in the second factor. -/
def projectionMap (A : DX) (B : DY) :
    TX.obj (A, hPush.obj B) ⟶ hPush.obj (TY.obj (hPull.obj A, B)) :=
  adjunctionCupProductOfMaps adjh TX TY μ (𝟙 (hPull.obj A)) (adjh.counit.app B)

/-- **The projection map is a Künneth map**: the one of the square with `f = id` and `q = id`,
the diagonal and the second side being `h`. -/
theorem projectionMap_eq_kunnethMap (A : DX) (B : DY) :
    projectionMap TX TY adjh μ A B =
      kunnethMap TX TY Adjunction.id adjh adjh hPull (𝟭 DY) μ hPull.leftUnitor hPull.rightUnitor
        A B := by
  simp [projectionMap, kunnethMap, pullbackPushforwardCounit]

/-- The projection map is natural in both variables. -/
theorem projectionMap_naturality {A A' : DX} {B B' : DY} (a : A ⟶ A') (b : B ⟶ B') :
    TX.map (a ×ₘ hPush.map b) ≫ projectionMap TX TY adjh μ A' B' =
      projectionMap TX TY adjh μ A B ≫ hPush.map (TY.map (hPull.map a ×ₘ b)) := by
  rw [projectionMap_eq_kunnethMap, projectionMap_eq_kunnethMap]
  exact kunnethMap_naturality TX TY Adjunction.id adjh adjh hPull (𝟭 DY) μ hPull.leftUnitor
      hPull.rightUnitor a b

end Projection

/-! ### The base change map, and its composite with the projection map -/

section BaseChange

variable {DX' DS' DT DY : Type*} [Category* DX'] [Category* DS'] [Category* DT] [Category* DY]
  {gPull : DS' ⥤ DT} {gPush : DT ⥤ DS'} (adjg : gPull ⊣ gPush)
  {hPull : DX' ⥤ DY} {hPush : DY ⥤ DX'} (adjh : hPull ⊣ hPush)
  (f'Pull : DS' ⥤ DX') (ePull : DT ⥤ DY)
  (β : f'Pull ⋙ hPull ≅ gPull ⋙ ePull)

/-- **The base change map** `(f')^* g_* ⟶ h_* e^*` of a square
```
X' <-h-- Y
|f'      |e
S' <-g-- T
```
whose inverse images commute through `β : (f')^* ⋙ h^* ≅ g^* ⋙ e^*`: the mate of `β` for the
adjunctions `g^* ⊣ g_*` and `h^* ⊣ h_*`. -/
def baseChangeMap : gPush ⋙ f'Pull ⟶ ePull ⋙ hPush :=
  mateEquiv adjg adjh β.hom

/-- **The defining property of the base change map**: transposed across `h^* ⊣ h_*` it is `β`
at `g_*F` followed by `e^*` of the counit of `g^* ⊣ g_*`. -/
theorem baseChangeMap_counit (F : DT) :
    hPull.map ((baseChangeMap adjg adjh f'Pull ePull β).app F) ≫ adjh.counit.app _ =
      β.hom.app (gPush.obj F) ≫ ePull.map (adjg.counit.app F) :=
  mateEquiv_counit adjg adjh β.hom F

variable (TX' : DX' × DX' ⥤ DX') (TY : DY × DY ⥤ DY)
  (μ : TX' ⋙ hPull ⟶ hPull.prod hPull ⋙ TY)

/-- **The canonical map** `A ⊗ (f')^*g_*F ⟶ h_*(h^*A ⊗ e^*F)` of [Stacks, Tag 0F1J] and
[Stacks, Tag 0F1N] (there with `A = p^*E`): the base change map in the second factor followed
by the projection map. -/
def tensorBaseChangeMap (A : DX') (F : DT) :
    TX'.obj (A, f'Pull.obj (gPush.obj F)) ⟶ hPush.obj (TY.obj (hPull.obj A, ePull.obj F)) :=
  TX'.map (𝟙 A ×ₘ (baseChangeMap adjg adjh f'Pull ePull β).app F) ≫
    projectionMap TX' TY adjh μ A (ePull.obj F)

/-- **The canonical map of Tags 0F1J and 0F1N, as the source describes it**: the adjoint, for
`h^* ⊣ h_*`, of `h^*(A ⊗ (f')^*g_*F) ⟶ h^*A ⊗ h^*(f')^*g_*F`, followed in the second factor by
`h^*(f')^*g_*F ≅ e^*g^*g_*F ⟶ e^*F`. -/
theorem tensorBaseChangeMap_eq_adjunctionCupProductOfMaps (A : DX') (F : DT) :
    tensorBaseChangeMap adjg adjh f'Pull ePull β TX' TY μ A F =
      adjunctionCupProductOfMaps adjh TX' TY μ (𝟙 (hPull.obj A))
        (β.hom.app (gPush.obj F) ≫ ePull.map (adjg.counit.app F)) := by
  rw [tensorBaseChangeMap, projectionMap, map_comp_adjunctionCupProductOfMaps,
    ← baseChangeMap_counit adjg adjh f'Pull ePull β F]
  simp

end BaseChange

/-! ### The Künneth map of morphisms of ringed topoi is a special case -/

section RingedTopoi

open _root_.AlgebraicGeometry CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite

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
  (q : RingedToposSiteHom W Y) (g : RingedToposSiteHom Y S)
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

/-- **The Künneth map of morphisms of ringed topoi is the abstract one.** The map
`Stacks.Cohomology.KunnethMapOnRingedTopoi.kunnethMapOfAdjoint`, built from equalities
`f ∘ p = c = g ∘ q`, is `kunnethMap` at the derived adjunctions `Lf^* ⊣ Rf_*`, `Lg^* ⊣ Rg_*`,
`Lc^* ⊣ Rc_*`, the comparison of [Stacks, Tag 07A4] for `c`, and the identifications
`Lf^* ⋙ Lp^* ≅ L(f ∘ p)^* = Lc^*` and `Lg^* ⋙ Lq^* ≅ L(g ∘ q)^* = Lc^*` of [Stacks, Tag 0D6D]. -/
theorem kunnethMapOfAdjoint_eq_kunnethMap :
    letI := DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy (f.comp p)
      (RingedToposSiteHom.isMorphismOfSites_comp_u p f hmosp hmosf)
    letI := DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy (g.comp q)
      (RingedToposSiteHom.isMorphismOfSites_comp_u q g hmosq hmosg)
    kunnethMapOfAdjoint p f c hmosp hmosf hmosc q g hmosq hmosg hp hq E K =
      kunnethMap (Functor.uncurry.obj (derivedTensorProductFunctor S.O))
        (Functor.uncurry.obj (derivedTensorProductFunctor W.O))
        (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmosf)
        (DerivedPullbackOnRingedTopoi.derivedAdjunction g hmosg)
        (DerivedPullbackOnRingedTopoi.derivedAdjunction c hmosc)
        (derivedPullback p) (derivedPullback q)
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso c hmosc).hom
        (DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso p f hmosp hmosf ≪≫
          DerivedBaseChangeOnTopoi.derivedPullbackCongr hp)
        (DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso q g hmosq hmosg ≪≫
          DerivedBaseChangeOnTopoi.derivedPullbackCongr hq) E K := by
  simp only [kunnethMapOfAdjoint, kunnethMap, pullbackPushforwardCounit,
    KunnethMapOnRingedTopoi.pullbackDirectImageCounit, Iso.trans_inv, NatTrans.comp_app,
    Category.assoc]

end RingedTopoi

end Stacks.Cohomology.AbstractKunnethMap

end
