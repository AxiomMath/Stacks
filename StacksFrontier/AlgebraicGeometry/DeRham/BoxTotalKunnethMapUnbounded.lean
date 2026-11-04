module

public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalComparisonExists
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxTotalKunnethMapCanonical
import StacksCore.Tactic.StacksAttribute

/-!
# The global cup product of the box product of two unbounded complexes

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, write `f = p ∘ a = q ∘ b` and set `A = Γ(S, 𝒪_S)`. Let `𝓕^•` on `X` and `𝓖^•` on `Y`
be `ℤ`-indexed complexes of quasi-coherent modules whose differentials are differential operators
of finite order on `X/S` and on `Y/S`, with no boundedness condition. The box product of
[Stacks, Tag 0G46] turns them into a double complex of `f^{-1}𝒪_S`-modules on `W`, whose total
complex, formed with direct sums of `f^{-1}𝒪_S`-modules, is `Tot(𝓕^• ⊠ 𝓖^•)`. This file
constructs the global cup product of [Stacks, Tag 0FLR]

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

in `D(A)`, as the composite of the five maps of the source.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.boxProductRelativeCurried`: the bifunctor
  `(𝓕, 𝓖) ↦ 𝓕 ⊠ 𝓖`, read over `f^{-1}𝒪_S`.
* `Stacks.Cohomology.BoxKunneth.boxDoubleComparison`: the morphism of double complexes
  `p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^• ⟶ 𝓕^• ⊠ 𝓖^•` given by the degreewise comparisons.
* `Stacks.Cohomology.BoxKunneth.boxTotalComplexComparison`: **step (5)**,
  `Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•) ⟶ Tot(𝓕^• ⊠ 𝓖^•)`.
* `Stacks.Cohomology.BoxKunneth.boxTotalComplexDerivedComparison`: **steps (4) and (5)** in
  `D(f^{-1}𝒪_S)`.
* `Stacks.Cohomology.BoxKunneth.globalBoxCupProduct`: **the map of [Stacks, Tag 0FLR].**

## Main results

* `Stacks.Cohomology.BoxKunneth.ι_boxTotalComplexComparison`: on the summand of degree `(i, j)`
  step (5) is the degreewise comparison `p^{-1}𝓕^i ⊗ q^{-1}𝓖^j ⟶ 𝓕^i ⊠ 𝓖^j`.
* `Stacks.Cohomology.BoxKunneth.globalBoxCupProduct_eq`: the map is the global Künneth map
  `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical` of [Stacks, Tag 0G7V] for the
  inverse-image ringed spaces, which is steps (1) to (3) with step (3) the global cup product of
  [Stacks, Section 0FKU], followed by derived global sections of steps (4) and (5).

## Implementation notes

*Where the total complex is formed.* The source forms `Tot(𝓕^• ⊠ 𝓖^•)` from a double complex of
quasi-coherent modules whose maps are differential operators, so its maps are `f^{-1}𝒪_S`-linear
and its total complex is a complex of `f^{-1}𝒪_S`-modules, formed with arbitrary direct sums.
The double complex is the image of the box-product double complex of finite-order differential
operators under `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.toInverseImageModules`,
and the total complex is taken there.

*Steps (1) to (3) are taken with the derived inverse image.* Along the projection
`(W, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)` the inverse image of the structure sheaf is the structure sheaf,
so the derived inverse image `Lp^*` computes `p^{-1}`; the canonical comparison `Lp^*𝓕 ⟶ p^{-1}𝓕`
is the first factor of step (4).

## References

* [Stacks Project, Tag 0FLR](https://stacks.math.columbia.edu/tag/0FLR)
* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

universe u

/-! ### A morphism of double complexes out of degreewise data -/

section Generic

open CategoryTheory.Functor in
/-- **A morphism of double complexes `T(K'^•, L'^•) ⟶ B(K^•, L^•)` from degreewise maps.** For a
bifunctor `T` and a functor `B` on a product category, maps `T(K'^i, L'^j) ⟶ B(K^i, L^j)`
commuting with the two differentials form a morphism between the double complexes obtained by
applying `T` to `K'^•, L'^•` and the curried `B` to `K^•, L^•`. -/
def CategoryTheory.Functor.mapBifunctorHomologicalComplexHomMk
    {C₁ C₂ M D : Type*} [Category* C₁] [Category* C₂] [Category* M] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms M] [Preadditive D]
    (T : M ⥤ M ⥤ D) [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (B : C₁ × C₂ ⥤ D) [(curryObj B).PreservesZeroMorphisms]
    [∀ X, ((curryObj B).obj X).PreservesZeroMorphisms]
    (K' L' : CochainComplex M ℤ) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    (φ : ∀ i j, (T.obj (K'.X i)).obj (L'.X j) ⟶ B.obj (K.X i, L.X j))
    (h₁ : ∀ i j, (T.map (K'.d i (i + 1))).app (L'.X j) ≫ φ (i + 1) j =
      φ i j ≫ B.map (X := (K.X i, L.X j)) (Y := (K.X (i + 1), L.X j)) (K.d i (i + 1), 𝟙 (L.X j)))
    (h₂ : ∀ i j, (T.obj (K'.X i)).map (L'.d j (j + 1)) ≫ φ i (j + 1) =
      φ i j ≫ B.map (X := (K.X i, L.X j)) (Y := (K.X i, L.X (j + 1))) (𝟙 (K.X i), L.d j (j + 1))) :
    ((T.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K').obj L' ⟶
      (((curryObj B).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K).obj L :=
  HomologicalComplex₂.homMk (fun ij => φ ij.1 ij.2)
    (by rintro i _ j rfl; exact (h₁ i j).symm)
    (by rintro i j _ rfl; exact (h₂ i j).symm)

/-- The component of `mapBifunctorHomologicalComplexHomMk` in bidegree `(i, j)` is the given
map. -/
theorem CategoryTheory.Functor.mapBifunctorHomologicalComplexHomMk_f_f
    {C₁ C₂ M D : Type*} [Category* C₁] [Category* C₂] [Category* M] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms M] [Preadditive D]
    (T : M ⥤ M ⥤ D) [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (B : C₁ × C₂ ⥤ D) [(curryObj B).PreservesZeroMorphisms]
    [∀ X, ((curryObj B).obj X).PreservesZeroMorphisms]
    (K' L' : CochainComplex M ℤ) (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    (φ : ∀ i j, (T.obj (K'.X i)).obj (L'.X j) ⟶ B.obj (K.X i, L.X j))
    (h₁ : ∀ i j, (T.map (K'.d i (i + 1))).app (L'.X j) ≫ φ (i + 1) j =
      φ i j ≫ B.map (X := (K.X i, L.X j)) (Y := (K.X (i + 1), L.X j)) (K.d i (i + 1), 𝟙 (L.X j)))
    (h₂ : ∀ i j, (T.obj (K'.X i)).map (L'.d j (j + 1)) ≫ φ i (j + 1) =
      φ i j ≫ B.map (X := (K.X i, L.X j)) (Y := (K.X i, L.X (j + 1))) (𝟙 (K.X i), L.d j (j + 1)))
    (i j : ℤ) :
    ((mapBifunctorHomologicalComplexHomMk T B K' L' K L φ h₁ h₂).f i).f j = φ i j :=
  rfl

end Generic

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **The box-product bifunctor `(𝓕, 𝓖) ↦ 𝓕 ⊠ 𝓖` read over `f^{-1}𝒪_S`**, in curried form. -/
abbrev boxProductRelativeCurried :
    FiniteOrderDifferentialOperatorCategory a ⥤
      FiniteOrderDifferentialOperatorCategory b ⥤
        Modules (inverseImageBase (pullback.fst a b ≫ a)) :=
  Functor.curryObj (boxProductRelative a b)

/-- For a fixed `𝓕`, the functor `𝓖 ↦ 𝓕 ⊠ 𝓖` preserves zero morphisms. -/
instance boxProductRelativeCurried_obj_preservesZeroMorphisms
    (F : FiniteOrderDifferentialOperatorCategory a) :
    ((boxProductRelativeCurried a b).obj F).PreservesZeroMorphisms where
  map_zero := by
    intro G G'
    exact ((boxProductRelative_map a b (𝟙 F) (0 : G ⟶ G')).trans
      (congrArg (toInverseImageModules (pullback.fst a b ≫ a)).map
        (boxHom_zero_right (𝟙 F)))).trans (Functor.map_zero _ _ _)

/-- The functor `𝓕 ↦ (𝓖 ↦ 𝓕 ⊠ 𝓖)` preserves zero morphisms. -/
instance boxProductRelativeCurried_preservesZeroMorphisms :
    (boxProductRelativeCurried a b).PreservesZeroMorphisms where
  map_zero := by
    intro F F'
    refine NatTrans.ext (funext fun G => ?_)
    refine (((boxProductRelative_map a b (0 : F ⟶ F') (𝟙 G)).trans
      (congrArg (toInverseImageModules (pullback.fst a b ≫ a)).map
        (boxHom_zero_left (𝟙 G)))).trans (Functor.map_zero _ _ _)).trans ?_
    rfl

variable (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)

/-- The source double complex `p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•`. -/
abbrev inverseImageTensorDouble :
    HomologicalComplex₂ (Modules (inverseImageBase (pullback.fst a b ≫ a)))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((inverseImageSheafTensor a b).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj (leftInverseImageComplex a b K)).obj (rightInverseImageComplex a b L)

/-- The target double complex `𝓕^• ⊠ 𝓖^•`, read over `f^{-1}𝒪_S`. -/
abbrev boxDouble :
    HomologicalComplex₂ (Modules (inverseImageBase (pullback.fst a b ≫ a)))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((boxProductRelativeCurried a b).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj K).obj L

/-- **The morphism of double complexes `p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^• ⟶ 𝓕^• ⊠ 𝓖^•`**,
whose component in bidegree `(i, j)` is the degreewise comparison
`p^{-1}𝓕^i ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^j ⟶ 𝓕^i ⊠ 𝓖^j`; it commutes with the two differentials by the
naturality of the comparison in the two differential operators. -/
def boxDoubleComparison : inverseImageTensorDouble a b K L ⟶ boxDouble a b K L :=
  Functor.mapBifunctorHomologicalComplexHomMk (inverseImageSheafTensor a b) (boxProductRelative a b)
    (leftInverseImageComplex a b K) (rightInverseImageComplex a b L) K L
    (fun i j => relativeBoxComparison a b (K.X i) (L.X j))
    (relativeBoxComparison_naturality_d_fst a b K L)
    (relativeBoxComparison_naturality_d_snd a b K L)

/-- **Step (5) of the construction of [Stacks, Tag 0FLR]**, the morphism of complexes
`Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•) ⟶ Tot(𝓕^• ⊠ 𝓖^•)` given on the summands by the
degreewise comparisons. -/
def boxTotalComplexComparison : inverseImageTensorTotal a b K L ⟶
    HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (boxDoubleComparison a b K L) (ComplexShape.up ℤ)

/-- **On the summand of degree `(i, j)` step (5) is the degreewise comparison**
`p^{-1}𝓕^i ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^j ⟶ 𝓕^i ⊠ 𝓖^j` followed by the inclusion of the summand. -/
theorem ι_boxTotalComplexComparison (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor (leftInverseImageComplex a b K)
        (rightInverseImageComplex a b L) (inverseImageSheafTensor a b)
        (ComplexShape.up ℤ) i j n h ≫ (boxTotalComplexComparison a b K L).f n =
      relativeBoxComparison a b (K.X i) (L.X j) ≫
        HomologicalComplex.ιMapBifunctor K L (boxProductRelativeCurried a b)
          (ComplexShape.up ℤ) i j n h :=
  HomologicalComplex₂.ιTotal_map (φ := boxDoubleComparison a b K L) (i₁ := i) (i₂ := j)
    (i₁₂ := n) (h := h)

/-- **Steps (4) and (5) of the construction of [Stacks, Tag 0FLR]**, the map

`Lp^*𝓕^• ⊗^𝐋_{f^{-1}𝒪_S} Lq^*𝓖^• ⟶ Tot(𝓕^• ⊠ 𝓖^•)`

in `D(f^{-1}𝒪_S)`: the two derived-to-degreewise inverse image comparisons, the comparison of the
derived with the nonderived tensor product of [Stacks, Tag 06YU], and step (5). -/
def boxTotalComplexDerivedComparison :
    ((derivedTensorProductFunctor.{u, u + 1}
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          ((derivedPullback.{u, u + 1, u + 1} (fstProjection a b)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((derivedPullback.{u, u + 1, u + 1} (sndProjection a b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      DerivedCategory.Q.obj
        (HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b) (ComplexShape.up ℤ)) :=
  ((derivedTensorProductFunctor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).map
        (pullbackComplexComparison (fstProjection a b) (leftComplex a K))).app
      ((derivedPullback (sndProjection a b)).obj
        (DerivedCategory.Q.obj (rightComplex b L))) ≫
    ((derivedTensorProductFunctor
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          (DerivedCategory.Q.obj (leftInverseImageComplex a b K))).map
        (pullbackComplexComparison (sndProjection a b) (rightComplex b L)) ≫
    (canonicalDerivedTensorProduct
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor
        (leftInverseImageComplex a b K) (rightInverseImageComplex a b L) ≫
    DerivedCategory.Q.map (boxTotalComplexComparison a b K L)

/-- **The global cup product of [Stacks, Tag 0FLR]**

`RΓ(X, 𝓕^•) ⊗^𝐋_A RΓ(Y, 𝓖^•) ⟶ RΓ(X ×_S Y, Tot(𝓕^• ⊠ 𝓖^•))`

in `D(A)` for `A = Γ(S, 𝒪_S)`, for `𝓕^•` on `X/S` and `𝓖^•` on `Y/S` arbitrary `ℤ`-indexed
complexes of quasi-coherent modules whose differentials are differential operators of finite
order. It is the composite of the two pullback maps on derived global sections, the global cup
product of [Stacks, Section 0FKU] (together these are the global Künneth map
`Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical` of [Stacks, Tag 0G7V] for the
inverse-image ringed spaces), and derived global sections of steps (4) and (5). -/
@[stacks 0FLR "the map, as the composite of the five maps of the source: steps (1) to (3) are the \
global Künneth map of Tag 0G7V at the global cup product `globalCupProductCanonical` of Section \
0FKU, the pullbacks being `Lp^*`, which computes `p^{-1}` along `(X ×_S Y, f^{-1}𝒪_S) ⟶ (X, \
a^{-1}𝒪_S)`; steps (4) and (5) are `boxTotalComplexDerivedComparison`"]
def globalBoxCupProduct :
    ((tensorBase S.toRingedSpace).obj
          ((sectionsOverBase (inverseImageBaseProjection a)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((sectionsOverBase (inverseImageBaseProjection b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).obj
        (DerivedCategory.Q.obj
          (HomologicalComplex.mapBifunctor K L (boxProductRelativeCurried a b)
            (ComplexShape.up ℤ))) :=
  kunnethGlobalMapCanonical (inverseImageBaseProjection a) (inverseImageBaseProjection b)
      (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a))
      (fstProjection_comp a b) (sndProjection_comp a b)
      (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
    (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (boxTotalComplexDerivedComparison a b K L)

/-- **The map is the five-step composite**: the global Künneth map of [Stacks, Tag 0G7V] at the
global cup product of [Stacks, Section 0FKU], followed by derived global sections of steps (4)
and (5). -/
@[stacks 0FLR "the map is the composite of steps (1) to (3), the global Künneth map of Tag 0G7V \
  at the global cup product of Section 0FKU, with derived global sections of steps (4) and (5)"]
theorem globalBoxCupProduct_eq :
    globalBoxCupProduct a b K L =
      kunnethGlobalMap (inverseImageBaseProjection a) (inverseImageBaseProjection b)
          (fstProjection a b) (sndProjection a b)
          (inverseImageBaseProjection (pullback.fst a b ≫ a))
          (fstProjection_comp a b) (sndProjection_comp a b)
          (globalCupProductCanonical S.toRingedSpace)
          (DerivedCategory.Q.obj (leftComplex a K)) (DerivedCategory.Q.obj (rightComplex b L)) ≫
        (sectionsOverBase (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
          (boxTotalComplexDerivedComparison a b K L) :=
  rfl

end Stacks.Cohomology.BoxKunneth

end
