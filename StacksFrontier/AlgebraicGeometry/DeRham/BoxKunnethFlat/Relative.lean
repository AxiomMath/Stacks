module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMapUnbounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderBiproducts

/-!
# The global cup product of the box product through its relative map

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y`, `f = p ∘ a`, and let
`𝓕^•`, `𝓖^•` be complexes of quasi-coherent modules with differentials differential operators of
finite order on `X/S` and on `Y/S`.  The global cup product of [Stacks, Tag 0FLR],
`Stacks.Cohomology.BoxKunneth.globalBoxCupProduct`, is the global Künneth map of
[Stacks, Tag 0G7V] for the inverse-image ringed spaces followed by derived global sections of
steps (4) and (5).  This file rewrites it as

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ≅ RΓ(S, Ra_*𝓕^•) ⊗^𝐋_A RΓ(S, Rb_*𝓖^•) ⟶ RΓ(S, Ra_*𝓕^• ⊗^𝐋 Rb_*𝓖^•)
  ⟶ RΓ(S, Rf_*Tot(𝓕^• ⊠ 𝓖^•)) ≅ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`,

the Leray isomorphisms, the global cup product on `S`, and derived global sections of the
*relative* map `Ra_*𝓕^• ⊗^𝐋 Rb_*𝓖^• ⟶ Rf_*Tot(𝓕^• ⊠ 𝓖^•)` (the relative Künneth map of
[Stacks, Tag 0FLP] for the inverse-image ringed spaces followed by `Rf_*` of steps (4) and (5)),
and proves that the relative map is natural in morphisms of complexes of differential operators
in each variable.

## Main definitions

* `Stacks.Cohomology.BoxKunnethFlat.relativeBoxMap`: the relative map.

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.globalBoxCupProduct_eq_relative`: the factorization.
* `Stacks.Cohomology.BoxKunnethFlat.relativeBoxMap_natural_left` and `_natural_right`:
  naturality.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open Stacks.Cohomology.BoxKunneth
open scoped CategoryTheory.Prod

universe u

/-! ### Total complexes of a bifunctor along a map in one variable -/

section Generic

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D] [HasZeroMorphisms C₁]
  [HasZeroMorphisms C₂] [Preadditive D] (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms]

/-- On a summand, the total complex of a bifunctor along a map in the first variable. -/
@[reassoc]
theorem ι_mapBifunctorMap_id_right {K₁ L₁ : CochainComplex C₁ ℤ} (f : K₁ ⟶ L₁)
    (K₂ : CochainComplex C₂ ℤ) [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)] (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K₁ K₂ F (ComplexShape.up ℤ) i j n h ≫
        (HomologicalComplex.mapBifunctorMap f (𝟙 K₂) F (ComplexShape.up ℤ)).f n =
      (F.map (f.f i)).app (K₂.X j) ≫ HomologicalComplex.ιMapBifunctor L₁ K₂ F (ComplexShape.up ℤ) i
          j n h := by
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- On a summand, the total complex of a bifunctor along a map in the second variable. -/
@[reassoc]
theorem ι_mapBifunctorMap_id_left (K₁ : CochainComplex C₁ ℤ) {K₂ L₂ : CochainComplex C₂ ℤ}
    (g : K₂ ⟶ L₂) [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K₁ L₂ F (ComplexShape.up ℤ)] (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K₁ K₂ F (ComplexShape.up ℤ) i j n h ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 K₁) g F (ComplexShape.up ℤ)).f n =
      (F.obj (K₁.X i)).map (g.f j) ≫ HomologicalComplex.ιMapBifunctor K₁ L₂ F (ComplexShape.up ℤ) i
          j n h := by
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The diagram chase behind the naturality of a summandwise comparison of total complexes. -/
theorem chase_total {E : Type*} [Category E] {x₀ x₁ x₁' y₁ y₁' y₁'' z z' : E}
    (ι : x₀ ⟶ x₁) (m : x₁ ⟶ x₁') (c' : x₁' ⟶ z') (c : x₁ ⟶ z) (mB : z ⟶ z')
    (t : x₀ ⟶ y₁) (ι' : y₁ ⟶ x₁') (r' : y₁ ⟶ y₁') (ιB' : y₁' ⟶ z') (r : x₀ ⟶ y₁'')
    (ιB : y₁'' ⟶ z) (bm : y₁'' ⟶ y₁')
    (A1 : ι ≫ m = t ≫ ι') (A2 : ι' ≫ c' = r' ≫ ιB') (A3 : ι ≫ c = r ≫ ιB)
    (A4 : ιB ≫ mB = bm ≫ ιB') (A5 : t ≫ r' = r ≫ bm) :
    ι ≫ m ≫ c' = ι ≫ c ≫ mB := by
  rw [reassoc_of% A1, A2, reassoc_of% A3, A4, reassoc_of% A5]

end Generic

namespace Stacks.Cohomology.BoxKunnethFlat

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The category of finite-order differential operators has binary biproducts. -/
instance hasBinaryBiproducts_finiteOrder :
    HasBinaryBiproducts (FiniteOrderDifferentialOperatorCategory a) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-- The box-product bifunctor is additive in its first variable. -/
instance boxProductRelativeCurried_additive : (boxProductRelativeCurried a b).Additive where
  map_add {F F'} {D D'} := by
    refine NatTrans.ext (funext fun G => ?_)
    change (boxProductRelative a b).map (X := (F, G)) (Y := (F', G)) (D + D', 𝟙 G) =
      (boxProductRelative a b).map (X := (F, G)) (Y := (F', G)) (D, 𝟙 G) +
        (boxProductRelative a b).map (X := (F, G)) (Y := (F', G)) (D', 𝟙 G)
    rw [boxProductRelative_map, boxProductRelative_map, boxProductRelative_map, boxHom_add_left,
      Functor.map_add]
    rfl

/-- The box-product bifunctor is additive in its second variable. -/
instance boxProductRelativeCurried_obj_additive (F : FiniteOrderDifferentialOperatorCategory a) :
    ((boxProductRelativeCurried a b).obj F).Additive where
  map_add {G G'} {E E'} := by
    change (boxProductRelative a b).map (X := (F, G)) (Y := (F, G')) (𝟙 F, E + E') =
      (boxProductRelative a b).map (X := (F, G)) (Y := (F, G')) (𝟙 F, E) +
        (boxProductRelative a b).map (X := (F, G)) (Y := (F, G')) (𝟙 F, E')
    rw [boxProductRelative_map, boxProductRelative_map, boxProductRelative_map, boxHom_add_right,
      Functor.map_add]
    rfl

variable (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)

/-- **The relative map** `Ra_*𝓕^• ⊗^𝐋_{𝒪_S} Rb_*𝓖^• ⟶ Rf_*Tot(𝓕^• ⊠ 𝓖^•)`: the relative Künneth
map of [Stacks, Tag 0FLP] for the inverse-image ringed spaces, followed by `Rf_*` of steps (4)
and (5) of [Stacks, Tag 0FLR]. -/
def relativeBoxMap :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj
          (HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b)
              (ComplexShape.up ℤ))) :=
  Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a))
      (fstProjection_comp a b) (sndProjection_comp a b)
      (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (boxTotalComplexDerivedComparison a b K L)

section General

variable {S' X' Y' W' : RingedSpace.{u, u}} (a' : X' ⟶ S') (b' : Y' ⟶ S') (p : W' ⟶ X')
  (q : W' ⟶ Y') (f : W' ⟶ S') (hp : p ≫ a' = f) (hq : q ≫ b' = f)
  (κ : GlobalCupProduct S')

/-- **The global Künneth map of [Stacks, Tag 0G7V], followed by derived global sections of a
map out of its target**, as the Leray isomorphisms, the global cup product, derived global
sections on the base of the relative Künneth map followed by `Rf_*` of the map, and the Leray
isomorphism on the target. -/
theorem kunnethGlobalMap_comp_sectionsOverBase_map
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')))
    {T : DerivedCategory (SheafOfModules.{u} (structureSheafRing W'))}
    (g : ((derivedTensorProductFunctor W'.sheaf).obj ((derivedPullback p).obj K)).obj
      ((derivedPullback q).obj M) ⟶ T) :
    kunnethGlobalMap a' b' p q f hp hq κ K M ≫ (sectionsOverBase f).map g =
      (Functor.uncurry.obj (tensorBase S')).map
          ((lerayIso a').inv.app K ×ₘ (lerayIso b').inv.app M) ≫
        κ.app ((derivedPushforward a').obj K, (derivedPushforward b').obj M) ≫
        (baseSections S').map
          (Stacks.Cohomology.DerivedKunneth.kunnethMap a' b' p q f hp hq K M) ≫
        (baseSections S').map ((derivedPushforward f).map g) ≫
        (lerayIso f).hom.app T := by
  rw [kunnethGlobalMap_eq]
  simp only [Category.assoc]
  rw [← (lerayIso f).hom.naturality g]
  rfl

end General

/-- **The global cup product of [Stacks, Tag 0FLR] through the relative map**: the Leray
isomorphisms in each tensor factor, the global cup product on `S`, derived global sections of
the two factors of `relativeBoxMap`, and the Leray isomorphism on the target. -/
theorem globalBoxCupProduct_eq_relative :
    globalBoxCupProduct a b K L =
      (Functor.uncurry.obj (tensorBase S.toRingedSpace)).map
          ((lerayIso (inverseImageBaseProjection a)).inv.app
              (DerivedCategory.Q.obj (leftComplex a K)) ×ₘ
            (lerayIso (inverseImageBaseProjection b)).inv.app
              (DerivedCategory.Q.obj (rightComplex b L))) ≫
        (globalCupProductCanonical S.toRingedSpace).app
          ((derivedPushforward (inverseImageBaseProjection a)).obj
              (DerivedCategory.Q.obj (leftComplex a K)),
            (derivedPushforward (inverseImageBaseProjection b)).obj
              (DerivedCategory.Q.obj (rightComplex b L))) ≫
        (baseSections S.toRingedSpace).map
          (Stacks.Cohomology.DerivedKunneth.kunnethMap (inverseImageBaseProjection a)
            (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
            (inverseImageBaseProjection (pullback.fst a b ≫ a))
            (fstProjection_comp a b) (sndProjection_comp a b)
            (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L))) ≫
        (baseSections S.toRingedSpace).map
          ((derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
            (boxTotalComplexDerivedComparison a b K L)) ≫
        (lerayIso (inverseImageBaseProjection (pullback.fst a b ≫ a))).hom.app
          (DerivedCategory.Q.obj
            (HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b)
              (ComplexShape.up ℤ))) :=
  (globalBoxCupProduct_eq a b K L).trans
    (kunnethGlobalMap_comp_sectionsOverBase_map (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (globalCupProductCanonical S.toRingedSpace)
      (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L))
      (boxTotalComplexDerivedComparison a b K L))

/-! ### Naturality of steps (4) and (5) and of the relative map -/

section Naturality

variable {a b}

/-- The diagram chase behind `pullbackComplexComparison_naturality`. -/
private theorem chase_pullbackComplexComparison {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {x₀ x₁ x₂ x₃ : C} {y₂ y₃ y₄ y₅ : D}
    (q : x₀ ⟶ x₁) (i : x₁ ⟶ x₃) (i' : x₀ ⟶ x₂) (h : x₂ ⟶ x₃)
    (c : G.obj x₃ ⟶ y₃) (c' : G.obj x₂ ⟶ y₂) (k : y₂ ⟶ y₃) (o : y₃ ⟶ y₅) (o' : y₂ ⟶ y₄)
    (r : y₄ ⟶ y₅)
    (h₁ : q ≫ i = i' ≫ h) (h₂ : G.map h ≫ c = c' ≫ k) (h₃ : k ≫ o = o' ≫ r) :
    G.map q ≫ G.map i ≫ c ≫ o = (G.map i' ≫ c' ≫ o') ≫ r := by
  rw [← G.map_comp_assoc, h₁, G.map_comp_assoc, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- The comparison `Lg^* ⟶ g^*` is natural in the complex. -/
theorem pullbackComplexComparison_naturality {Z Z' : RingedSpace.{u, u}} (g : Z ⟶ Z')
    {C C' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ} (φ : C ⟶ C') :
    (derivedPullback.{u, u + 1, u + 1} g).map (DerivedCategory.Q.map φ) ≫
        pullbackComplexComparison g C' =
      pullbackComplexComparison g C ≫
        DerivedCategory.Q.map (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
            φ) :=
  chase_pullbackComplexComparison (derivedPullback.{u, u + 1, u + 1} g)
    (DerivedCategory.Q.map φ)
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z'))).inv.app C')
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z'))).inv.app C)
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ))
    ((derivedPullbackComparison g).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C'))
    ((derivedPullbackComparison g).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)))
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z))).hom.app
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C'))
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z))).hom.app
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))
    (DerivedCategory.Q.map (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))
    ((DerivedCategory.quotientCompQhIso _).inv.naturality φ)
    ((derivedPullbackComparison g).naturality ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        φ))
    ((DerivedCategory.quotientCompQhIso _).hom.naturality
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map φ))

/-- `p^{-1}` of a morphism of complexes of differential operators on `X/S`. -/
abbrev leftInverseImageMap {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ}
    (φ : K ⟶ K') : leftInverseImageComplex a b K ⟶ leftInverseImageComplex a b K' :=
  ((modulePullback (fstProjection a b)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)

/-- `q^{-1}` of a morphism of complexes of differential operators on `Y/S`. -/
abbrev rightInverseImageMap {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ}
    (ψ : L ⟶ L') : rightInverseImageComplex a b L ⟶ rightInverseImageComplex a b L' :=
  ((modulePullback (sndProjection a b)).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)

variable (a b)

/-- **Step (5) is natural in the complex on `X`.** -/
theorem boxTotalComplexComparison_naturality_left
    {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ} (φ : K ⟶ K')
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    HomologicalComplex.mapBifunctorMap (leftInverseImageMap (b := b) φ)
        (𝟙 (rightInverseImageComplex a b L)) (inverseImageSheafTensor a b) (ComplexShape.up ℤ) ≫
      boxTotalComplexComparison a b K' L =
    boxTotalComplexComparison a b K L ≫
      HomologicalComplex.mapBifunctorMap φ (𝟙 L) (boxProductRelativeCurried a b)
        (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => HomologicalComplex.mapBifunctor.hom_ext
    (fun i j h => ?_))
  simp only [HomologicalComplex.comp_f]
  exact chase_total _ _ _ _ _ _ _ _ _ _ _ _
    (ι_mapBifunctorMap_id_right (inverseImageSheafTensor a b) (leftInverseImageMap (b := b) φ)
      (rightInverseImageComplex a b L) i j n h)
    (ι_boxTotalComplexComparison a b K' L i j n h)
    (ι_boxTotalComplexComparison a b K L i j n h)
    (ι_mapBifunctorMap_id_right (boxProductRelativeCurried a b) φ L i j n h)
    (relativeBoxComparison_naturality_fst a b (φ.f i) (L.X j))

/-- **Step (5) is natural in the complex on `Y`.** -/
theorem boxTotalComplexComparison_naturality_right
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (ψ : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap (𝟙 (leftInverseImageComplex a b K))
        (rightInverseImageMap (a := a) ψ) (inverseImageSheafTensor a b) (ComplexShape.up ℤ) ≫
      boxTotalComplexComparison a b K L' =
    boxTotalComplexComparison a b K L ≫
      HomologicalComplex.mapBifunctorMap (𝟙 K) ψ (boxProductRelativeCurried a b)
        (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => HomologicalComplex.mapBifunctor.hom_ext
    (fun i j h => ?_))
  simp only [HomologicalComplex.comp_f]
  exact chase_total _ _ _ _ _ _ _ _ _ _ _ _
    (ι_mapBifunctorMap_id_left (inverseImageSheafTensor a b) (leftInverseImageComplex a b K)
      (rightInverseImageMap (a := a) ψ) i j n h)
    (ι_boxTotalComplexComparison a b K L' i j n h)
    (ι_boxTotalComplexComparison a b K L i j n h)
    (ι_mapBifunctorMap_id_left (boxProductRelativeCurried a b) K ψ i j n h)
    (relativeBoxComparison_naturality_snd a b (K.X i) (ψ.f j))

/-- The diagram chase behind the naturality of steps (4) and (5) and of the relative map. -/
private theorem chase_four {E : Type*} [Category E] {x₀ x₁ x₂ x₃ x₄ y₀ y₁ y₂ y₃ y₄ : E}
    (X : x₀ ⟶ y₀) (P : y₀ ⟶ y₁) (Q : y₁ ⟶ y₂) (T : y₂ ⟶ y₃) (U : y₃ ⟶ y₄)
    (P' : x₀ ⟶ x₁) (Q' : x₁ ⟶ x₂) (T' : x₂ ⟶ x₃) (U' : x₃ ⟶ x₄) (Y : x₄ ⟶ y₄)
    (Z₁ : x₁ ⟶ y₁) (Z₂ : x₂ ⟶ y₂) (Z₃ : x₃ ⟶ y₃)
    (h₁ : X ≫ P = P' ≫ Z₁) (h₂ : Z₁ ≫ Q = Q' ≫ Z₂) (h₃ : Z₂ ≫ T = T' ≫ Z₃)
    (h₄ : Z₃ ≫ U = U' ≫ Y) :
    X ≫ P ≫ Q ≫ T ≫ U = (P' ≫ Q' ≫ T' ≫ U') ≫ Y := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

/-- Dropping an identity from the middle of a composite. -/
private theorem drop_id {E : Type*} [Category E] {x y z : E} (A : x ⟶ y) (m : y ⟶ y)
    (B : y ⟶ z) (C : x ⟶ z) (hm : m = 𝟙 y) (h : A ≫ m ≫ B = C) : A ≫ B = C := by
  rwa [hm, Category.id_comp] at h

/-- Dropping an identity from the front of a composite. -/
private theorem drop_id_left {E : Type*} [Category E] {x y z : E} (m : x ⟶ x)
    (A : x ⟶ y) (B : y ⟶ z) (C : x ⟶ z) (hm : m = 𝟙 x) (h : m ≫ A ≫ B = C) : A ≫ B = C := by
  rwa [hm, Category.id_comp] at h

/-- A bifunctor applied to the image of an identity in its first variable. -/
private theorem bifunctor_map_map_id {B C D E : Type*} [Category B] [Category C] [Category D]
    [Category E] (F : C ⥤ D ⥤ E) (G : B ⥤ C) (x : B) (y : D) :
    (F.map (G.map (𝟙 x))).app y = 𝟙 _ := by
  simp

/-- A bifunctor carries a commuting square in its first variable to one of components. -/
private theorem bifunctor_map_square {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {a b c d : C} {f : a ⟶ b} {g : b ⟶ d} {h : a ⟶ c} {k : c ⟶ d}
    (w : f ≫ g = h ≫ k) (Z : D) :
    (F.map f).app Z ≫ (F.map g).app Z = (F.map h).app Z ≫ (F.map k).app Z := by
  rw [← NatTrans.comp_app, ← F.map_comp, w, F.map_comp, NatTrans.comp_app]

/-- A functor carries a commuting square to a commuting square. -/
private theorem functor_map_square {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {a b c d : C} {f : a ⟶ b} {g : b ⟶ d} {h : a ⟶ c} {k : c ⟶ d} (w : f ≫ g = h ≫ k) :
    G.map f ≫ G.map g = G.map h ≫ G.map k := by
  rw [← G.map_comp, w, G.map_comp]

/-- **Steps (4) and (5) are natural in the complex on `X`.** -/
theorem boxTotalComplexDerivedComparison_naturality_left
    {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ} (φ : K ⟶ K')
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    ((derivedTensorProductFunctor.{u, u + 1}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).map
        ((derivedPullback.{u, u + 1, u + 1} (fstProjection a b)).map
          (DerivedCategory.Q.map (((toInverseImageModules a).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)))).app
        ((derivedPullback.{u, u + 1, u + 1} (sndProjection a b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ≫
      boxTotalComplexDerivedComparison a b K' L =
    boxTotalComplexDerivedComparison a b K L ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
        (boxProductRelativeCurried a b) (ComplexShape.up ℤ)) := by
  have h₃ := drop_id _ _ _ _
      (by rw [DerivedCategory.Q.map_id]; exact CategoryTheory.Functor.map_id _ _)
    ((canonicalDerivedTensorProduct
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality
    (leftInverseImageMap (b := b) φ) (𝟙 (rightInverseImageComplex a b L)))
  dsimp only [boxTotalComplexDerivedComparison]
  exact chase_four _ _ _ _ _ _ _ _ _ _ _ _ _
    (bifunctor_map_square _ (pullbackComplexComparison_naturality (fstProjection a b)
      (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) _)
    (((derivedTensorProductFunctor (SheafedSpace.sheaf
      (inverseImageBase (pullback.fst a b ≫ a)))).map
        (DerivedCategory.Q.map (leftInverseImageMap (b := b) φ))).naturality
      (pullbackComplexComparison (sndProjection a b) (rightComplex b L))).symm
    h₃
    (functor_map_square _ (boxTotalComplexComparison_naturality_left a b φ L))

/-- **Steps (4) and (5) are natural in the complex on `Y`.** -/
theorem boxTotalComplexDerivedComparison_naturality_right
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (ψ : L ⟶ L') :
    ((derivedTensorProductFunctor.{u, u + 1}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
        ((derivedPullback.{u, u + 1, u + 1} (fstProjection a b)).obj
          (DerivedCategory.Q.obj (leftComplex a K)))).map
        ((derivedPullback.{u, u + 1, u + 1} (sndProjection a b)).map
          (DerivedCategory.Q.map (((toInverseImageModules b).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ))) ≫
      boxTotalComplexDerivedComparison a b K L' =
    boxTotalComplexDerivedComparison a b K L ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) ψ
        (boxProductRelativeCurried a b) (ComplexShape.up ℤ)) := by
  have h₃ := drop_id_left _ _ _ _ (bifunctor_map_map_id _ _ _ _)
    ((canonicalDerivedTensorProduct
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality
    (𝟙 (leftInverseImageComplex a b K)) (rightInverseImageMap (a := a) ψ))
  dsimp only [boxTotalComplexDerivedComparison]
  exact chase_four _ _ _ _ _ _ _ _ _ _ _ _ _
    (((derivedTensorProductFunctor (SheafedSpace.sheaf
      (inverseImageBase (pullback.fst a b ≫ a)))).map
        (pullbackComplexComparison (fstProjection a b) (leftComplex a K))).naturality
      ((derivedPullback.{u, u + 1, u + 1} (sndProjection a b)).map
          (DerivedCategory.Q.map (((toInverseImageModules b).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ))))
    (functor_map_square _ (pullbackComplexComparison_naturality (sndProjection a b)
      (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)))
    h₃
    (functor_map_square _ (boxTotalComplexComparison_naturality_right a b K ψ))

/-- The diagram chase behind the naturality of the relative map. -/
private theorem chase_functor {E E' : Type*} [Category E] [Category E'] (G : E ⥤ E')
    {x₀ y₀ : E'} {z₀ z₁ t₀ t₁ : E} (X : x₀ ⟶ y₀) (k' : y₀ ⟶ G.obj z₁) (k : x₀ ⟶ G.obj z₀)
    (Z : z₀ ⟶ z₁) (D' : z₁ ⟶ t₁) (D : z₀ ⟶ t₀) (Y : t₀ ⟶ t₁)
    (h₁ : X ≫ k' = k ≫ G.map Z) (h₂ : Z ≫ D' = D ≫ Y) :
    X ≫ k' ≫ G.map D' = (k ≫ G.map D) ≫ G.map Y := by
  rw [reassoc_of% h₁, ← G.map_comp, h₂, G.map_comp, Category.assoc]

/-- **The relative map is natural in the complex on `X`.** -/
theorem relativeBoxMap_natural_left
    {K K' : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ} (φ : K ⟶ K')
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).map
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).map
            (DerivedCategory.Q.map (((toInverseImageModules a).mapHomologicalComplex
              (ComplexShape.up ℤ)).map φ)))).app
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ≫
      relativeBoxMap a b K' L =
    relativeBoxMap a b K L ≫
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ (𝟙 L)
          (boxProductRelativeCurried a b) (ComplexShape.up ℤ))) :=
  chase_functor _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a))
      (fstProjection_comp a b) (sndProjection_comp a b)
      (DerivedCategory.Q.map (((toInverseImageModules a).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ)) (DerivedCategory.Q.obj (rightComplex b L)))
    (boxTotalComplexDerivedComparison_naturality_left a b φ L)

/-- **The relative map is natural in the complex on `Y`.** -/
theorem relativeBoxMap_natural_right
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
    {L L' : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ} (ψ : L ⟶ L') :
    ((derivedTensorProductFunctor.{u, u + 1} (SheafedSpace.sheaf S.toRingedSpace)).obj
          ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).map
        ((derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection b)).map
          (DerivedCategory.Q.map (((toInverseImageModules b).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ))) ≫
      relativeBoxMap a b K L' =
    relativeBoxMap a b K L ≫
      (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) ψ
          (boxProductRelativeCurried a b) (ComplexShape.up ℤ))) :=
  chase_functor _ _ _ _ _ _ _ _
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a))
      (fstProjection_comp a b) (sndProjection_comp a b)
      (DerivedCategory.Q.obj (leftComplex a K))
      (DerivedCategory.Q.map (((toInverseImageModules b).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ψ)))
    (boxTotalComplexDerivedComparison_naturality_right a b K ψ)

end Naturality

end Stacks.Cohomology.BoxKunnethFlat

end
