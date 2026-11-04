module

public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxRelativeTensor
public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxTotal
public import StacksFrontier.AlgebraicGeometry.RingedSpaceModuleSpellings
public import StacksFrontier.Homology.KFlat.Pullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapOfSheaves

/-!
# The comparison `Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•) ⟶ Tot(𝓕^• ⊠ 𝓖^•)`

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections `p`
and `q`, and write `f = p ∘ a = q ∘ b`. Let `𝓕^•` and `𝓖^•` be `ℤ`-indexed complexes of
quasi-coherent modules whose differentials are differential operators of finite order on `X/S`
and on `Y/S`. The box product of [Stacks, Tag 0G46] turns them into a double complex, whose
total complex is `Tot(𝓕^• ⊠ 𝓖^•)`; all of its differentials are `f^{-1}𝒪_S`-linear, so it is a
complex of `f^{-1}𝒪_S`-modules on `W` and can be pushed forward to `S`.

This file forms that complex, the degreewise tensor product
`Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•)`, and the last two steps of the construction of the
Künneth maps of [Stacks, Tag 0G4A]: the comparison between the derived and the nonderived tensor
product of the two inverse images, and the passage to the box product.

## Main definitions

* `Stacks.Cohomology.BoxKunneth.pullbackComplexComparison`: the canonical comparison
  `Lg^*K ⟶ g^*K` from the derived to the degreewise pullback of a complex of modules along a
  morphism of ringed spaces.
* `Stacks.Cohomology.BoxKunneth.boxTotal`: `Tot(𝓕^• ⊠ 𝓖^•)`, the total complex of the
  box-product double complex, in the category of finite-order differential operators on
  `X ×_S Y / S`, for `𝓕^•` and `𝓖^•` strictly bounded below.
* `Stacks.Cohomology.BoxKunneth.boxTotalModules`: the same complex read over `f^{-1}𝒪_S`.
* `Stacks.Cohomology.BoxKunneth.inverseImageTensorTotal`:
  `Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•)`.
* `Stacks.Cohomology.BoxKunneth.BoxTotalComparison`: a morphism of complexes
  `Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•) ⟶ Tot(𝓕^• ⊠ 𝓖^•)` whose summandwise components are
  the degreewise comparisons `p^{-1}𝓕^i ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^j ⟶ 𝓕^i ⊠ 𝓖^j`; this is step (5)
  of the construction of [Stacks, Tag 0G4A].
* `Stacks.Cohomology.BoxKunneth.boxTotalDerivedComparison`: steps (4) and (5) together, the map
  `Lp^*𝓕^• ⊗^𝐋_{f^{-1}𝒪_S} Lq^*𝓖^• ⟶ Tot(𝓕^• ⊠ 𝓖^•)` in `D(f^{-1}𝒪_S)`.

## Main results

* `Stacks.Cohomology.BoxKunneth.boxTotal_d`: the differential of `Tot(𝓕^• ⊠ 𝓖^•)` on the
  summand of degree `(i, j)` is `d_𝓕 ⊠ 1 + (-1)^i (1 ⊠ d_𝓖)`, the sign convention of
  [Stacks, Tag 012Z].
* `Stacks.Cohomology.BoxKunneth.BoxTotalComparison.hom_unique`: any two step-(5) comparisons
  have the same underlying morphism of complexes.
* `Stacks.Cohomology.BoxKunneth.boxTotalDerivedComparison_eq`: steps (4) and (5) form the
  composite of the two derived-to-degreewise inverse image comparisons, the derived-to-nonderived
  tensor comparison of [Stacks, Tag 06YU], and the step-(5) comparison.

## References

* [Stacks Project, Tag 0G4A](https://stacks.math.columbia.edu/tag/0G4A)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.DerivedTensor.RingedSite
open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

universe u

namespace Stacks.Cohomology.BoxKunneth

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-! ### The derived-to-degreewise comparison for the inverse image of a complex -/

section Pullback

variable {Z Z' : RingedSpace.{u, u}} (g : Z ⟶ Z')

/-- The comparison `Lg^*K ⟶ g^*K` for a complex of modules on a morphism of ringed spaces:
the counit of the left derived functor `Lg^*` at `K`, read through the identification of the two
localization functors. -/
def pullbackComplexComparison (C : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ) :
    (derivedPullback.{u, u + 1, u + 1} g).obj (DerivedCategory.Q.obj C) ⟶
      DerivedCategory.Q.obj
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  (derivedPullback g).map
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z'))).inv.app C) ≫
    (derivedPullbackComparison g).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z))).hom.app
      (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)

/-- The comparison is the counit of `Lg^*`, conjugated by the two identifications of the
localization functor of the derived category with the one of the homotopy category. -/
theorem pullbackComplexComparison_eq
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ) :
    pullbackComplexComparison g C =
      (derivedPullback.{u, u + 1, u + 1} g).map
          ((DerivedCategory.quotientCompQhIso
            (SheafOfModules.{u} (structureSheafRing Z'))).inv.app C) ≫
        (derivedPullbackComparison g).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ≫
        (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Z))).hom.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
  rfl

end Pullback

/-! ### The two projections of the fibre product, over the base -/

section Projections

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The first projection as a morphism of ringed spaces `(W, f^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)`,
with `W = X ×_S Y` and `f = p ∘ a`. -/
abbrev fstProjection : inverseImageBase (pullback.fst a b ≫ a) ⟶ inverseImageBase a :=
  relativeInverseImageProjection (pullback.fst a b) a

/-- The second projection as a morphism of ringed spaces `(W, f^{-1}𝒪_S) ⟶ (Y, b^{-1}𝒪_S)`. -/
abbrev sndProjection : inverseImageBase (pullback.fst a b ≫ a) ⟶ inverseImageBase b :=
  sndRelativeInverseImageProjection a b

/-- The triangle over `S` for a projection presented as a factorization: the transported
canonical morphism followed by the projection to `S` is the projection to `S`. -/
theorem relativeInverseImageProjectionOfFactors_comp {W X' S' : Scheme.{u}} (p : W ⟶ X')
    (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g) :
    relativeInverseImageProjectionOfFactors p c g hg ≫ inverseImageBaseProjection c =
      inverseImageBaseProjection g := by
  subst hg
  exact relativeInverseImageProjection_comp p c

/-- The first projection is a morphism over `S`. -/
theorem fstProjection_comp :
    fstProjection a b ≫ inverseImageBaseProjection a =
      inverseImageBaseProjection (pullback.fst a b ≫ a) :=
  relativeInverseImageProjection_comp _ _

/-- The second projection is a morphism over `S`. -/
theorem sndProjection_comp :
    sndProjection a b ≫ inverseImageBaseProjection b =
      inverseImageBaseProjection (pullback.fst a b ≫ a) :=
  relativeInverseImageProjectionOfFactors_comp _ _ _ _

end Projections

/-! ### The two total complexes -/

section Complexes

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)

/-- The complex `𝓕^•` read as a complex of `a^{-1}𝒪_S`-modules: a finite-order differential
operator on `X/S` is `a^{-1}𝒪_S`-linear. -/
abbrev leftComplex : CochainComplex (Modules (inverseImageBase a)) ℤ :=
  ((toInverseImageModules a).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The complex `𝓖^•` read as a complex of `b^{-1}𝒪_S`-modules. -/
abbrev rightComplex : CochainComplex (Modules (inverseImageBase b)) ℤ :=
  ((toInverseImageModules b).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

/-- The complex `p^{-1}𝓕^•` of `f^{-1}𝒪_S`-modules on `X ×_S Y`. -/
abbrev leftInverseImageComplex
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ) :
    CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℤ :=
  ((modulePullback (fstProjection a b)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (leftComplex a K)

/-- The complex `q^{-1}𝓖^•` of `f^{-1}𝒪_S`-modules on `X ×_S Y`. -/
abbrev rightInverseImageComplex
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ) :
    CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℤ :=
  ((modulePullback (sndProjection a b)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (rightComplex b L)

/-- `Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•)`, the total complex of the degreewise nonderived
tensor product of the two inverse images. -/
abbrev inverseImageTensorTotal :
    CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℤ :=
  @HomologicalComplex.mapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _
    (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
      (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)) _

variable (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]

/-- `Tot(𝓕^• ⊠ 𝓖^•)`, the total complex of the box-product double complex of [Stacks, Tag 0G46],
a complex of quasi-coherent modules on `X ×_S Y` whose differentials are differential operators
of finite order on `X ×_S Y / S`, for `𝓕^•` and `𝓖^•` strictly bounded below. -/
def boxTotal : CochainComplex
    (FiniteOrderDifferentialOperatorCategory (pullback.fst a b ≫ a)) ℤ :=
  have := hasMapBifunctor_up_ℤ K L n₁ n₂
  HomologicalComplex.mapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)

/-- `boxTotal` is the total complex `HomologicalComplex.mapBifunctor` of the box-product
bicomplex, for any instance of `HomologicalComplex.HasMapBifunctor`. -/
theorem boxTotal_eq
    [HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)] :
    boxTotal a b K L n₁ n₂ =
      HomologicalComplex.mapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ) :=
  rfl

/-- `Tot(𝓕^• ⊠ 𝓖^•)` read as a complex of `f^{-1}𝒪_S`-modules. -/
abbrev boxTotalModules (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] :
    CochainComplex (Modules (inverseImageBase (pullback.fst a b ≫ a))) ℤ :=
  ((toInverseImageModules (pullback.fst a b ≫ a)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (boxTotal a b K L n₁ n₂)

/-- The inclusion of the summand `𝓕^i ⊠ 𝓖^j` into `Tot(𝓕^• ⊠ 𝓖^•)^n`, `i + j = n`, read over
`f^{-1}𝒪_S`. -/
def boxTotalι (i j n : ℤ) (h : i + j = n) :
    (boxProductRelative a b).obj (K.X i, L.X j) ⟶ (boxTotalModules a b K L n₁ n₂).X n :=
  have := hasMapBifunctor_up_ℤ K L n₁ n₂
  (toInverseImageModules (pullback.fst a b ≫ a)).map
    (HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ) i j n h)

/-- The inclusion of a summand is the one of the total complex, read over `f^{-1}𝒪_S`. -/
theorem boxTotalι_eq
    [HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)]
    (i j n : ℤ) (h : i + j = n) :
    boxTotalι a b K L n₁ n₂ i j n h =
      (toInverseImageModules (pullback.fst a b ≫ a)).map
        (HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b)
          (ComplexShape.up ℤ) i j n h) :=
  rfl

/-- The differential of `Tot(𝓕^• ⊠ 𝓖^•)` on the summand `𝓕^i ⊠ 𝓖^j` is
`d_𝓕 ⊠ 1 + (-1)^i (1 ⊠ d_𝓖)`, the sign convention of [Stacks, Tag 012Z]. -/
theorem boxTotal_d
    [HomologicalComplex.HasMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)]
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ) i j n h ≫
        (boxTotal a b K L n₁ n₂).d n (n + 1) =
      boxHom (K.d i (i + 1)) (𝟙 (L.X j)) ≫
          HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)
            (i + 1) j (n + 1) (by dsimp; lia) +
        i.negOnePow • (boxHom (𝟙 (K.X i)) (L.d j (j + 1)) ≫
          HomologicalComplex.ιMapBifunctor K L (boxProductCurried a b) (ComplexShape.up ℤ)
            i (j + 1) (n + 1) (by dsimp; lia)) :=
  ιMapBifunctor_d_up_ℤ K L i j n h

/-! ### The step-(5) comparison -/

/-- Step (5) of the construction of [Stacks, Tag 0G4A]: a morphism of complexes
`Tot(p^{-1}𝓕^• ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^•) ⟶ Tot(𝓕^• ⊠ 𝓖^•)` whose component on the summand of
degree `(i, j)` is the degreewise comparison
`p^{-1}𝓕^i ⊗_{f^{-1}𝒪_S} q^{-1}𝓖^j ⟶ 𝓕^i ⊠ 𝓖^j` followed by the inclusion of the summand. -/
structure BoxTotalComparison where
  /-- The morphism of complexes. -/
  hom : inverseImageTensorTotal a b K L ⟶ boxTotalModules a b K L n₁ n₂
  /-- Its component on the summand of degree `(i, j)` is the degreewise comparison of
  `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison`. -/
  ι_hom (i j n : ℤ) (h : i + j = n) :
    @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
        (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
        (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms
          _ M _ _)
        (ComplexShape.up ℤ) _
        (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
          (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
          (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)) _
        i j n h ≫ hom.f n =
      relativeBoxComparison a b (K.X i) (L.X j) ≫ boxTotalι a b K L n₁ n₂ i j n h

/-- Any two step-(5) comparisons have the same underlying morphism of complexes. -/
theorem BoxTotalComparison.hom_unique (c c' : BoxTotalComparison a b K L n₁ n₂) :
    c.hom = c'.hom :=
  HomologicalComplex.hom_ext _ _ fun n =>
    @HomologicalComplex.mapBifunctor.hom_ext _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
      (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
      (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
      (ComplexShape.up ℤ) _
      (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
        (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))
        (leftInverseImageComplex a b K) (rightInverseImageComplex a b L)) _ _ _ _ _
      fun i j h => (c.ι_hom i j n h).trans (c'.ι_hom i j n h).symm

/-- There is at most one step-(5) comparison. -/
instance BoxTotalComparison.subsingleton :
    Subsingleton (BoxTotalComparison a b K L n₁ n₂) where
  allEq c c' := by
    obtain ⟨τ, hτ⟩ := c
    obtain ⟨τ', hτ'⟩ := c'
    obtain rfl : τ = τ' := BoxTotalComparison.hom_unique a b K L n₁ n₂ ⟨τ, hτ⟩ ⟨τ', hτ'⟩
    rfl

/-! ### Steps (4) and (5) in the derived category -/

/-- Steps (4) and (5) of the construction of [Stacks, Tag 0G4A], the map

`Lp^*𝓕^• ⊗^𝐋_{f^{-1}𝒪_S} Lq^*𝓖^• ⟶ Tot(𝓕^• ⊠ 𝓖^•)`

in `D(f^{-1}𝒪_S)`: the two derived-to-degreewise inverse image comparisons, followed by the
comparison of the derived with the nonderived tensor product of [Stacks, Tag 06YU], followed by
the step-(5) comparison `c`. -/
def boxTotalDerivedComparison (c : BoxTotalComparison a b K L n₁ n₂) :
    ((derivedTensorProductFunctor.{u, u + 1}
            (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).obj
          ((derivedPullback.{u, u + 1, u + 1} (fstProjection a b)).obj
            (DerivedCategory.Q.obj (leftComplex a K)))).obj
        ((derivedPullback.{u, u + 1, u + 1} (sndProjection a b)).obj
          (DerivedCategory.Q.obj (rightComplex b L))) ⟶
      DerivedCategory.Q.obj (boxTotalModules a b K L n₁ n₂) :=
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
    DerivedCategory.Q.map c.hom

/-- Steps (4) and (5) are the composite of the two derived-to-degreewise inverse image
comparisons, the derived-to-nonderived tensor comparison of [Stacks, Tag 06YU] and the step-(5)
comparison. -/
theorem boxTotalDerivedComparison_eq (c : BoxTotalComparison a b K L n₁ n₂) :
    boxTotalDerivedComparison a b K L n₁ n₂ c =
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
        DerivedCategory.Q.map c.hom :=
  rfl

/-- Steps (4) and (5) do not depend on the step-(5) comparison. -/
theorem boxTotalDerivedComparison_unique (c c' : BoxTotalComparison a b K L n₁ n₂) :
    boxTotalDerivedComparison a b K L n₁ n₂ c = boxTotalDerivedComparison a b K L n₁ n₂ c' :=
  congrArg (boxTotalDerivedComparison a b K L n₁ n₂) (Subsingleton.elim c c')

end Complexes

end Stacks.Cohomology.BoxKunneth

end
