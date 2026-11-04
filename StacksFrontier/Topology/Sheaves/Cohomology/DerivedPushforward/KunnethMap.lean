module

public import StacksFrontier.CategoryTheory.BifunctorProdMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
import StacksCore.Tactic.StacksAttribute

/-!
# The relative Künneth map

Let `a : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `b : (Y, 𝒪_Y) ⟶ (S, 𝒪_S)` be morphisms of ringed spaces and
let `p : (W, 𝒪_W) ⟶ X`, `q : W ⟶ Y` be morphisms with `p ≫ a = f = q ≫ b`.  For `K ∈ D(𝒪_X)`
and `M ∈ D(𝒪_Y)` there is a canonical morphism

`Ra_*K ⊗^L_{𝒪_S} Rb_*M ⟶ Rf_*(Lp^*K ⊗^L_{𝒪_W} Lq^*M)`,

Equation 36.23.0.1 of the Stacks project.  It is the adjoint transpose under `Lf^* ⊣ Rf_*` of

`Lf^*(Ra_*K ⊗^L Rb_*M) ≅ Lf^*Ra_*K ⊗^L Lf^*Rb_*M ⟶ Lp^*K ⊗^L Lq^*M`,

whose first map is the monoidality of derived pullback and whose second is the tensor product
of the two maps `Lf^*Ra_*K ≅ Lp^*La^*Ra_*K ⟶ Lp^*K` and `Lf^*Rb_*M ≅ Lq^*Lb^*Rb_*M ⟶ Lq^*M`
got from the composition isomorphism for derived pullback and the counit of `La^* ⊣ Ra_*`
(resp. `Lb^* ⊣ Rb_*`).

The Stacks project takes `W = X ×_S Y` with its two projections; the fibre product is not used
in the construction, so the two projections and the two factorizations of `f` are taken as data
here, which specializes to the statement of the source.

## Main definitions

* `Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap`: the abstract comparison morphism
  `A(R₁K, R₂M) ⟶ R(B(P₁K, P₂M))` attached to an adjunction `L ⊣ R`, two bifunctors, a morphism
  of bifunctors `A ⋙ L ⟶ (L × L) ⋙ B` and two natural maps `R₁ ⋙ L ⟶ P₁`, `R₂ ⋙ L ⟶ P₂`.
* `Stacks.Cohomology.DerivedKunneth.pullbackCounitLegComp` and
  `Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg`: the natural map
  `L(p ≫ a)^*Ra_* ⟶ Lp^*` given by the composition isomorphism of Stacks 0D5S and the counit of
  the derived adjunction of Stacks 079W, and its transport along a factorization `p ≫ a = f`.
* `Stacks.Cohomology.DerivedKunneth.kunnethMap`: the relative Künneth morphism.

## Main results

* `Stacks.Cohomology.DerivedKunneth.kunnethMap_eq`: the Künneth morphism is the abstract
  comparison morphism for `Lf^* ⊣ Rf_*`, the two derived tensor products, the monoidality
  isomorphism of Stacks 079U and the two counit legs.
* `Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left` and
  `Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right`: the Künneth morphism is natural
  in `K` and in `M`, for arbitrary derived modules and with no flatness, quasi-coherence or Tor
  independence hypothesis.

## References

* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedKunneth

section Abstract

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C₁ : Type u₃} [Category.{v₃} C₁] {C₂ : Type u₄} [Category.{v₄} C₂]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
  (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {R₁ : C₁ ⥤ C} {P₁ : C₁ ⥤ D} (β : R₁ ⋙ L ⟶ P₁)
  {R₂ : C₂ ⥤ C} {P₂ : C₂ ⥤ D} (γ : R₂ ⋙ L ⟶ P₂)

/-- The abstract Künneth map `A(R₁K, R₂M) ⟶ R(B(P₁K, P₂M))`: the adjoint transpose of `α`
followed by the tensor product of `β` and `γ`. -/
def adjunctionBitensorMap (K : C₁) (M : C₂) :
    A.obj (R₁.obj K, R₂.obj M) ⟶ R.obj (B.obj (P₁.obj K, P₂.obj M)) :=
  adj.homEquiv _ _ (α.app (R₁.obj K, R₂.obj M) ≫ B.map (β.app K ×ₘ γ.app M))

/-- The abstract Künneth map is natural in both arguments. -/
@[reassoc]
lemma adjunctionBitensorMap_natural {K K' : C₁} {M M' : C₂} (k : K ⟶ K') (m : M ⟶ M') :
    A.map (R₁.map k ×ₘ R₂.map m) ≫ adjunctionBitensorMap adj A B α β γ K' M' =
      adjunctionBitensorMap adj A B α β γ K M ≫ R.map (B.map (P₁.map k ×ₘ P₂.map m)) := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionBitensorMap
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  have ha := α.naturality (R₁.map k ×ₘ R₂.map m)
  change L.map (A.map (R₁.map k ×ₘ R₂.map m)) ≫ α.app (R₁.obj K', R₂.obj M') =
    α.app (R₁.obj K, R₂.obj M) ≫ B.map (L.map (R₁.map k) ×ₘ L.map (R₂.map m)) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp]
  congr 2
  exact Prod.ext (β.naturality k) (γ.naturality m)

/-- **The abstract Künneth map at a pure pair.** The adjoint transpose of `A` of a pair of
morphisms `s : Z₁ ⟶ R₁K` and `t : Z₂ ⟶ R₂M` followed by the abstract Künneth map is the
comparison of bifunctors at `(Z₁, Z₂)` followed by `B` of the two transported morphisms
`Ls ≫ β` and `Lt ≫ γ`. -/
theorem homEquiv_symm_adjunctionBitensorMap {Z₁ Z₂ : C} {K : C₁} {M : C₂} (s : Z₁ ⟶ R₁.obj K)
    (t : Z₂ ⟶ R₂.obj M) :
    (adj.homEquiv _ _).symm (A.map (s ×ₘ t) ≫ adjunctionBitensorMap adj A B α β γ K M) =
      α.app (Z₁, Z₂) ≫ B.map ((L.map s ≫ β.app K) ×ₘ (L.map t ≫ γ.app M)) := by
  rw [adjunctionBitensorMap, Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
    ← Category.assoc, bifunctor_comparison_naturality A B α s t, Category.assoc,
    ← bifunctor_map_comp_both]

end Abstract

section Curried

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C₁ : Type u₃} [Category.{v₃} C₁] {C₂ : Type u₄} [Category.{v₄} C₂]

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (TA : C ⥤ C ⥤ C) (TB : D ⥤ D ⥤ D)
  (α : Functor.uncurry.obj TA ⋙ L ⟶ L.prod L ⋙ Functor.uncurry.obj TB)
  {R₁ : C₁ ⥤ C} {P₁ : C₁ ⥤ D} (β : R₁ ⋙ L ⟶ P₁)
  {R₂ : C₂ ⥤ C} {P₂ : C₂ ⥤ D} (γ : R₂ ⋙ L ⟶ P₂)

/-- Naturality of the abstract Künneth map in the first argument, with both bifunctors written
in curried form. -/
lemma adjunctionBitensorMap_natural_left_curried {K K' : C₁} (k : K ⟶ K') (M : C₂) :
    (TA.map (R₁.map k)).app (R₂.obj M) ≫ adjunctionBitensorMap adj
        (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α β γ K' M =
      adjunctionBitensorMap adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α β γ K M ≫
        R.map ((TB.map (P₁.map k)).app (P₂.obj M)) := by
  simpa only [CategoryTheory.Functor.map_id, uncurry_map_id_right] using
    adjunctionBitensorMap_natural adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α β γ
      k (𝟙 M)

/-- Naturality of the abstract Künneth map in the second argument, with both bifunctors written
in curried form. -/
lemma adjunctionBitensorMap_natural_right_curried (K : C₁) {M M' : C₂} (m : M ⟶ M') :
    (TA.obj (R₁.obj K)).map (R₂.map m) ≫ adjunctionBitensorMap adj
        (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α β γ K M' =
      adjunctionBitensorMap adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α β γ K M ≫
        R.map ((TB.obj (P₁.obj K)).map (P₂.map m)) := by
  simpa only [CategoryTheory.Functor.map_id, uncurry_map_id_left] using
    adjunctionBitensorMap_natural adj (Functor.uncurry.obj TA) (Functor.uncurry.obj TB) α β γ
      (𝟙 K) m

end Curried

attribute [local instance] HasDerivedCategory.standard

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)

/-- The counit leg `L(p ≫ a)^*Ra_* ⟶ Lp^*`: the composition isomorphism of Stacks 0D5S for the
derived pullbacks along `p` and `a`, followed by `Lp^*` of the counit of `La^* ⊣ Ra_*`. -/
def pullbackCounitLegComp :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (p ≫ a) ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p :=
  Functor.whiskerLeft (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a)
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p a).inv ≫
    (Functor.associator (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p)).inv ≫
    Functor.whiskerRight
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction a).counit
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p) ≫
    (Functor.leftUnitor
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p)).hom

/-- The counit leg `Lf^*Ra_* ⟶ Lp^*` attached to a factorization `p ≫ a = f`, the transport of
`pullbackCounitLegComp` along the resulting equality of derived pullback functors. -/
def pullbackCounitLeg (f : W ⟶ S) (hp : p ≫ a = f) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p :=
  eqToHom (congrArg (fun z : W ⟶ S =>
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback z) hp.symm) ≫
    pullbackCounitLegComp a p

variable (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

variable [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The relative Künneth morphism**
`Ra_*K ⊗^L_{𝒪_S} Rb_*M ⟶ Rf_*(Lp^*K ⊗^L_{𝒪_W} Lq^*M)`, Equation 36.23.0.1: the adjoint
transpose of the monoidality isomorphism of Stacks 079U for `Lf^*` followed by the tensor
product of the two counit legs.  It is defined for arbitrary `K ∈ D(𝒪_X)` and `M ∈ D(𝒪_Y)`. -/
@[stacks 0FLP]
def kunnethMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a).obj K)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward b).obj M) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p).obj K)).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback q).obj M)) :=
  adjunctionBitensorMap
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf))
    (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (pullbackCounitLeg a p f hp) (pullbackCounitLeg b q f hq) K M

/-- The relative Künneth morphism is the abstract Künneth map for the derived adjunction
`Lf^* ⊣ Rf_*`, the derived tensor products on `S` and on `W`, the monoidality isomorphism of
Stacks 079U and the two counit legs. -/
theorem kunnethMap_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethMap a b p q f hp hq K M =
      adjunctionBitensorMap
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf))
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
        (pullbackCounitLeg a p f hp) (pullbackCounitLeg b q f hq) K M :=
  rfl

/-- The relative Künneth morphism is natural in the derived module on `X`. -/
@[stacks 0FLP "naturality in the complex on the first factor"]
theorem kunnethMap_natural_left
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (k : K ⟶ K')
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a).map k)).app
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward b).obj M) ≫
        kunnethMap a b p q f hp hq K' M =
      kunnethMap a b p q f hp hq K M ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf).map
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p).map k)).app
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback q).obj M)) :=
  adjunctionBitensorMap_natural_left_curried
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (pullbackCounitLeg a p f hp) (pullbackCounitLeg b q f hq) k M

/-- The relative Künneth morphism is natural in the derived module on `Y`. -/
@[stacks 0FLP "naturality in the complex on the second factor"]
theorem kunnethMap_natural_right
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (m : M ⟶ M') :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward a).obj K)).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward b).map m) ≫
        kunnethMap a b p q f hp hq K M' =
      kunnethMap a b p q f hp hq K M ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward f).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf).obj
              ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback p).obj K)).map
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback q).map m)) :=
  adjunctionBitensorMap_natural_right_curried
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.sheaf)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (pullbackCounitLeg a p f hp) (pullbackCounitLeg b q f hq) K m

end Stacks.Cohomology.DerivedKunneth

end
