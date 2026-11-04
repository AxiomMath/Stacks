module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.SingleCrossingGlue
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.CrossingChain
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.ShiftedSingles

/-!
# The relative box map at single complexes

Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and quasi-separated morphisms of schemes and let
`𝓕`, `𝓖` be finite-order differential operator modules with `𝓖` flat over `S`.  The relative box
map of [Stacks, Tag 0FLR] (the relative Künneth map of the inverse-image ringed spaces followed by
`Rf_*` of steps (4) and (5)) at `𝓕[-i]` and `𝓖[-j]` is an isomorphism: along the morphisms of
ringed spaces `τ : X ⟶ (X, a^{-1}𝒪_S)` it is the scheme Künneth map of [Stacks, Tag 0FU4] at
`𝓕[-i]` and `𝓖[-j]`, up to isomorphisms.

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.isIso_kunnethMap_comp_congr`: invertibility of a Künneth map
  followed by a map does not depend on the presentation of the morphisms.

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.DeRhamDirectImage
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory
open scoped CategoryTheory.Prod

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  TopCat.Presheaf.IsSheaf

namespace Stacks.Cohomology.BoxKunnethFlat

section Congr

variable {S X Y W : RingedSpace.{u, u}} (p : W ⟶ X) (q : W ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Invertibility of a Künneth map followed by a map does not depend on the presentation of the
morphisms**: equal morphisms give the same invertibility. -/
theorem isIso_kunnethMap_comp_congr {a₁ a₂ : X ⟶ S} {b₁ b₂ : Y ⟶ S} {f₁ f₂ : W ⟶ S}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hf : f₁ = f₂) (hp₁ : p ≫ a₁ = f₁) (hq₁ : q ≫ b₁ = f₁)
    (hp₂ : p ≫ a₂ = f₂) (hq₂ : q ≫ b₂ = f₂)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    {T : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))}
    (φ : ((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj E)).obj
      ((derivedPullback q).obj M) ⟶ T)
    (h : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a₁ b₁ p q f₁ hp₁ hq₁ E M ≫
      (derivedPushforward f₁).map φ)) :
    IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a₂ b₂ p q f₂ hp₂ hq₂ E M ≫
      (derivedPushforward f₂).map φ) := by
  subst ha hb hf
  exact h

/-- **The Künneth map is natural in both variables at once.** -/
theorem kunnethMap_natural_both (a : X ⟶ S) (b : Y ⟶ S) (f : W ⟶ S) (hp : p ≫ a = f)
    (hq : q ≫ b = f) {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (σX : E ⟶ E')
    (σY : M ⟶ M') :
    ((derivedTensorProductFunctor S.sheaf).map ((derivedPushforward a).map σX)).app
        ((derivedPushforward b).obj M) ≫
      ((derivedTensorProductFunctor S.sheaf).obj ((derivedPushforward a).obj E')).map
        ((derivedPushforward b).map σY) ≫
      Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq E' M' =
    Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq E M ≫
      (derivedPushforward f).map
        (((derivedTensorProductFunctor W.sheaf).map ((derivedPullback p).map σX)).app
            ((derivedPullback q).obj M) ≫
          ((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj E')).map
            ((derivedPullback q).map σY)) := by
  rw [Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right, ← Category.assoc,
    Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left, Category.assoc, ← Functor.map_comp]

end Congr

/-- A functor out of a product category carries a pair of isomorphisms to an isomorphism. -/
theorem isIso_map_prod {C D : Type*} [Category* C] [Category* D] (T : C × C ⥤ D) {a a' b b' : C}
    (x : a ⟶ a') (y : b ⟶ b') [IsIso x] [IsIso y] : IsIso (T.map (x ×ₘ y)) := by
  have : IsIso (x ×ₘ y) :=
    (CategoryTheory.isIso_prod_iff (f := x ×ₘ y)).mpr
        ⟨inferInstanceAs (IsIso x), inferInstanceAs (IsIso y)⟩
  infer_instance

/-- `T(L₁ π₁, L₂ π₂)` followed by `T(L₁(π₁⁻¹ ≫ x), L₂(π₂⁻¹ ≫ y))` is `T(L₁ x, L₂ y)`. -/
theorem map_prod_comp_inv {C₁ C₂ D E : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [Category* E] (T : D × D ⥤ E) (L₁ : C₁ ⥤ D) (L₂ : C₂ ⥤ D) {a a' a'' : C₁} {b b' b'' : C₂}
        (π₁ : a ≅ a') (π₂ : b ≅ b')
    (x : a ⟶ a'') (y : b ⟶ b'') :
    T.map (L₁.map π₁.hom ×ₘ L₂.map π₂.hom) ≫ T.map (L₁.map (π₁.inv ≫ x) ×ₘ L₂.map (π₂.inv ≫ y)) =
      T.map (L₁.map x ×ₘ L₂.map y) := by
  rw [← T.map_comp, prod_comp, ← L₁.map_comp, ← L₂.map_comp, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc]

section Naturality

variable {Z X' Y' : RingedSpace.{u, u}} (p' : Z ⟶ X') (q' : Z ⟶ Y')
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The chase behind `pullbackToTensor_naturality`, every object and morphism a variable. -/
private theorem chase_tensor_naturality {D E : Type*} [Category* D] [Category* E] (T : D × D ⥤ E)
    {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : D} {z₁ z₂ : E} (x₁ : a₁ ⟶ a₂) (x₂ : a₂ ⟶ a₄) (x₃ : a₁ ⟶ a₃)
    (x₄ : a₃ ⟶ a₄) (y₁ : b₁ ⟶ b₂) (y₂ : b₂ ⟶ b₄) (y₃ : b₁ ⟶ b₃) (y₄ : b₃ ⟶ b₄)
    (t' : T.obj (a₄, b₄) ⟶ z₂) (t : T.obj (a₃, b₃) ⟶ z₁) (m : z₁ ⟶ z₂)
    (h1 : x₁ ≫ x₂ = x₃ ≫ x₄) (h2 : y₁ ≫ y₂ = y₃ ≫ y₄) (h3 : T.map (x₄ ×ₘ y₄) ≫ t' = t ≫ m) :
    T.map (x₁ ×ₘ y₁) ≫ T.map (x₂ ×ₘ y₂) ≫ t' = (T.map (x₃ ×ₘ y₃) ≫ t) ≫ m := by
  have e : ((x₃ ≫ x₄) ×ₘ (y₃ ≫ y₄) : (a₁, b₁) ⟶ (a₄, b₄)) = (x₃ ×ₘ y₃) ≫ (x₄ ×ₘ y₄) := rfl
  rw [← Category.assoc, ← T.map_comp, prod_comp, h1, h2, e, T.map_comp, Category.assoc, h3,
    Category.assoc]

/-- The comparison `Lg^*K ⟶ g^*K` of steps (4)–(5) is the component of the natural
transformation `Lg^* ∘ Q ⟶ Q ∘ g^*`. -/
theorem pullbackComplexComparison_eq_natTrans {Z₁ Z₂ : RingedSpace.{u, u}} (g : Z₁ ⟶ Z₂)
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing Z₂)) ℤ) :
    Stacks.Cohomology.BoxKunneth.pullbackComplexComparison g C = (derivedPullbackNatTrans g).app
        C :=
  (AlgebraicGeometry.FlatKunneth.derivedPullbackNatTrans_app_eq g C).symm

/-- **The derived-to-total comparison after the two pullbacks is natural in both complexes.** -/
theorem pullbackToTensor_naturality
    {K K' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X') ℤ}
    {L L' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y') ℤ}
    (x : K ⟶ K') (y : L ⟶ L') :
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
        ((derivedPullback p').map (DerivedCategory.Q.map x) ×ₘ
          (derivedPullback q').map (DerivedCategory.Q.map y)) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
          ((derivedPullbackNatTrans p').app K' ×ₘ (derivedPullbackNatTrans q').app L') ≫
        (derivedToTensorNatTrans Z).app ((pullbackComplex p').obj K', (pullbackComplex q').obj L') =
    ((Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
          ((derivedPullbackNatTrans p').app K ×ₘ (derivedPullbackNatTrans q').app L) ≫
        (derivedToTensorNatTrans Z).app ((pullbackComplex p').obj K, (pullbackComplex q').obj L)) ≫
      DerivedCategory.Q.map
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Z.sheaf)).map ((pullbackComplex p').map x ×ₘ (pullbackComplex q').map y)) :=
  chase_tensor_naturality (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)) _ _ _ _ _ _
    _ _ _ _ _ ((derivedPullbackNatTrans p').naturality x)
    ((derivedPullbackNatTrans q').naturality y)
    ((derivedToTensorNatTrans Z).naturality
      ((pullbackComplex p').map x ×ₘ (pullbackComplex q').map y))

/-- **Steps (4) of [Stacks, Tag 0FLR] through the natural transformation `Lg^* ∘ Q ⟶ Q ∘ g^*`**:
the two comparisons `Lp'^* ⟶ p'^*`, `Lq'^* ⟶ q'^*` tensored together and followed by the
derived-to-total comparison. -/
theorem pullbackComplexComparison_toTensor
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X')) ℤ)
    (B : CochainComplex (SheafOfModules.{u} (structureSheafRing Y')) ℤ)
    {T : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    (h : DerivedCategory.Q.obj
        ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Z.sheaf)).obj ((pullbackComplex p').obj A, (pullbackComplex q').obj B)) ⟶ T) :
    ((derivedTensorProductFunctor Z.sheaf).map
          (Stacks.Cohomology.BoxKunneth.pullbackComplexComparison p' A)).app
        ((derivedPullback q').obj (DerivedCategory.Q.obj B)) ≫
      ((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj
          (((RingedSpaceModuleAdjunction.modulePullback p').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A))).map
        (Stacks.Cohomology.BoxKunneth.pullbackComplexComparison q' B) ≫
      (canonicalDerivedTensorProduct Z.sheaf).toTensor
          (((RingedSpaceModuleAdjunction.modulePullback p').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A)
          (((RingedSpaceModuleAdjunction.modulePullback q').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj B) ≫ h =
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
        ((derivedPullbackNatTrans p').app A ×ₘ (derivedPullbackNatTrans q').app B) ≫
      (derivedToTensorNatTrans Z).app ((pullbackComplex p').obj A, (pullbackComplex q').obj B) ≫
          h := by
  rw [pullbackComplexComparison_eq_natTrans, pullbackComplexComparison_eq_natTrans]
  exact (Category.assoc _ _ _).symm

/-- `pullbackToTensor_naturality` with the total complex of the pair of maps. -/
theorem pullbackToTensor_naturality'
    {K K' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X') ℤ}
    {L L' : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y') ℤ}
    (x : K ⟶ K') (y : L ⟶ L') :
    (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
        ((derivedPullback p').map (DerivedCategory.Q.map x) ×ₘ
          (derivedPullback q').map (DerivedCategory.Q.map y)) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
          ((derivedPullbackNatTrans p').app K' ×ₘ (derivedPullbackNatTrans q').app L') ≫
        (derivedToTensorNatTrans Z).app ((pullbackComplex p').obj K', (pullbackComplex q').obj L') =
    ((Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf)).map
          ((derivedPullbackNatTrans p').app K ×ₘ (derivedPullbackNatTrans q').app L) ≫
        (derivedToTensorNatTrans Z).app ((pullbackComplex p').obj K, (pullbackComplex q').obj L)) ≫
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMapReg ((pullbackComplex p').map x)
        ((pullbackComplex q').map y) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            Z.sheaf)
        (ComplexShape.up ℤ)) :=
  (pullbackToTensor_naturality p' q' x y).trans
    (congrArg (_ ≫ DerivedCategory.Q.map ·) (totalComplexPair_map _ _ _))

end Naturality

section Single

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (F : FiniteOrderDifferentialOperatorCategory a)
  (G : FiniteOrderDifferentialOperatorCategory b) (i j : ℤ)

/-- The square of the projection `p` against `a` read through the inverse-image ringed spaces. -/
theorem fst_comp_toInverseImageBase_comp :
    (pullback.fst a b).toLRSHom.toShHom ≫ (toInverseImageBase a) ≫ (inverseImageBaseProjection a) =
        (toInverseImageBase (pullback.fst a b ≫ a)) ≫ (inverseImageBaseProjection
        (pullback.fst a b ≫ a)) := by
  rw [toInverseImageBase_comp, toInverseImageBase_comp]
  rfl

/-- The square of the projection `q` against `b` read through the inverse-image ringed spaces. -/
theorem snd_comp_toInverseImageBase_comp :
    (pullback.snd a b).toLRSHom.toShHom ≫ (toInverseImageBase b) ≫ (inverseImageBaseProjection b) =
        (toInverseImageBase (pullback.fst a b ≫ a)) ≫ (inverseImageBaseProjection
        (pullback.fst a b ≫ a)) := by
  rw [toInverseImageBase_comp, toInverseImageBase_comp]
  exact Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b

/-- **The scheme Künneth map of [Stacks, Tag 0FU4] at `𝓕[-i]` and `𝓖[-j]`, along the
factorizations through the inverse-image ringed spaces**, is an isomorphism. -/
theorem isIso_kunnethMap_toInverseImageBase [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b]
    [QuasiSeparated b] (hG : IsFlatOver b.toLRSHom.toShHom G.module) :
    IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap
        ((toInverseImageBase a) ≫ (inverseImageBaseProjection a))
        ((toInverseImageBase b) ≫ (inverseImageBaseProjection b))
        ((pullback.fst a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶ X.toRingedSpace)
        ((pullback.snd a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶ Y.toRingedSpace)
        ((toInverseImageBase (pullback.fst a b ≫ a)) ≫
            (inverseImageBaseProjection (pullback.fst a b ≫ a)))
            (fst_comp_toInverseImageBase_comp a b) (snd_comp_toInverseImageBase_comp a b)
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
            F.module)) (DerivedCategory.Q.obj ((HomologicalComplex.single Y.Modules
            (ComplexShape.up ℤ) j).obj G.module)) ≫
      (derivedPushforward ((toInverseImageBase (pullback.fst a b ≫ a)) ≫
          (inverseImageBaseProjection (pullback.fst a b ≫ a)))).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf)).map
          ((derivedPullbackNatTrans ((pullback.fst a b).toLRSHom.toShHom :
              (pullback a b).toRingedSpace ⟶ X.toRingedSpace)).app
              ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj F.module) ×ₘ
              (derivedPullbackNatTrans ((pullback.snd a b).toLRSHom.toShHom :
              (pullback a b).toRingedSpace ⟶ Y.toRingedSpace)).app
              ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)) ≫
        (derivedToTensorNatTrans (pullback a b).toRingedSpace).app
          ((pullbackComplex ((pullback.fst a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶
              X.toRingedSpace)).obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) i).obj
              F.module), (pullbackComplex ((pullback.snd a b).toLRSHom.toShHom :
              (pullback a b).toRingedSpace ⟶ Y.toRingedSpace)).obj
              ((HomologicalComplex.single Y.Modules (ComplexShape.up ℤ) j).obj G.module)))) := by
  have := F.isQuasicoherent
  have := G.isQuasicoherent
  exact isIso_kunnethMap_comp_congr ((pullback.fst a b).toLRSHom.toShHom :
      (pullback a b).toRingedSpace ⟶ X.toRingedSpace)
    ((pullback.snd a b).toLRSHom.toShHom : (pullback a b).toRingedSpace ⟶ Y.toRingedSpace)
    (toInverseImageBase_comp a).symm (toInverseImageBase_comp b).symm
    (toInverseImageBase_comp (pullback.fst a b ≫ a)).symm _ _ _ _ _ _ _
    (AlgebraicGeometry.FlatKunneth.isIso_kunnethMap_comp_toTensor_singleObj a b F.module G.module
      hG i j)

/-- Step (5) at single complexes, out of the total complex of the degreewise pullbacks. -/
def boxTotalComplexComparisonSingle :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor
        (inverseImageBase (pullback.fst a b ≫ a)).sheaf)).obj
        ((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
        (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)),
        (pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
        (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G))) ⟶
      HomologicalComplex.mapBifunctor ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)
          (Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried a b)
        (ComplexShape.up ℤ) :=
  Stacks.Cohomology.BoxKunneth.boxTotalComplexComparison a b
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)

/-- The generic identity at the single complexes, in the shape of steps (4)–(5). -/
theorem pullbackComplexToTensor_single :
    Stacks.Cohomology.BoxKunneth.boxTotalComplexDerivedComparison a b
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G) =
      (Functor.uncurry.obj (derivedTensorProductFunctor
          (inverseImageBase (pullback.fst a b ≫ a)).sheaf)).map
          ((derivedPullbackNatTrans (Stacks.Cohomology.BoxKunneth.fstProjection a b)).app
              (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)) ×ₘ
              (derivedPullbackNatTrans (Stacks.Cohomology.BoxKunneth.sndProjection a b)).app
              (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G))) ≫
        (derivedToTensorNatTrans (inverseImageBase (pullback.fst a b ≫ a))).app
          ((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
              (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)),
              (pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
              (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G))) ≫
        DerivedCategory.Q.map (boxTotalComplexComparisonSingle a b F G i j) :=
  pullbackComplexComparison_toTensor (Stacks.Cohomology.BoxKunneth.fstProjection a b)
      (Stacks.Cohomology.BoxKunneth.sndProjection a b)
      (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F))
      (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G))
    (DerivedCategory.Q.map (boxTotalComplexComparisonSingle a b F G i j))

/-- **Steps (4)–(5) at single complexes, through the comparisons `Lp^* ⟶ p^*` as a natural
transformation.** -/
theorem boxTotalComplexDerivedComparison_single_eq :
    Stacks.Cohomology.BoxKunneth.boxTotalComplexDerivedComparison a b
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G) =
      ((Functor.uncurry.obj (derivedTensorProductFunctor
          (inverseImageBase (pullback.fst a b ≫ a)).sheaf)).map
          ((derivedPullbackNatTrans (Stacks.Cohomology.BoxKunneth.fstProjection a b)).app
              (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)) ×ₘ
              (derivedPullbackNatTrans (Stacks.Cohomology.BoxKunneth.sndProjection a b)).app
              (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G))) ≫
        (derivedToTensorNatTrans (inverseImageBase (pullback.fst a b ≫ a))).app
          ((pullbackComplex (Stacks.Cohomology.BoxKunneth.fstProjection a b)).obj
              (((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj F)),
              (pullbackComplex (Stacks.Cohomology.BoxKunneth.sndProjection a b)).obj
              (((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj G)))) ≫
      DerivedCategory.Q.map (boxTotalComplexComparisonSingle a b F G i j) :=
  (pullbackComplexToTensor_single a b F G i j).trans (Category.assoc _ _ _).symm

/-- `τ : X ⟶ (X, a^{-1}𝒪_S)` is the identity on spaces, hence a closed embedding. -/
theorem isClosedEmbedding_toInverseImageBase {Z T : Scheme.{u}} (f : Z ⟶ T) :
    Topology.IsClosedEmbedding (ConcreteCategory.hom (toInverseImageBase f).hom.base) :=
  Topology.IsClosedEmbedding.id

/-- **The direct image along `τ` is exact**: `Q(τ_*C) ≅ Rτ_*(QC)`. -/
def pushforwardComparisonQIso {Z T : Scheme.{u}} (f : Z ⟶ T)
    (C : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace)
        ℤ) :
    DerivedCategory.Q.obj ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
        (toInverseImageBase f)).obj C) ≅
      (derivedPushforward (toInverseImageBase f)).obj (DerivedCategory.Q.obj C) :=
  haveI := Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_pushforwardComparisonQ
    (toInverseImageBase f) (isClosedEmbedding_toInverseImageBase f) C
  asIso (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
    (toInverseImageBase f) C)

/-- The square of the second projection, with the base's spelling of the projection. -/
theorem toInverseImageBase_comp_sndProjection :
    toInverseImageBase (pullback.fst a b ≫ a) ≫ Stacks.Cohomology.BoxKunneth.sndProjection a b =
      (pullback.snd a b).toLRSHom.toShHom ≫ toInverseImageBase b :=
  toInverseImageBase_comp_relativeInverseImageProjectionOfFactors (pullback.snd a b) b
    (pullback.fst a b ≫ a) pullback.condition.symm

end Single

end Stacks.Cohomology.BoxKunnethFlat

end
