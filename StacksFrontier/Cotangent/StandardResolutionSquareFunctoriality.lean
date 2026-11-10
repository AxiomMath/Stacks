module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.StandardResolutionFunctoriality

/-!
# Functoriality of the cotangent complex in a square of ring maps

A commutative square of ring maps `A → A'`, `B → B'` compatible with the algebra structures
induces the canonical variables-to-variables map `P_• → P'_•` of the two standard resolutions
(`CommAlgCat.standardResolutionSquareMap`), and hence a map of cotangent complexes
`L_{B/A} → L_{B'/A'}`, `B`-linear when the target is read over `B` along `sq.map`. This file
builds that map of complexes and assembles the whole of
`CommAlgCat.SquareFunctorialityData` for the square.

The map is built degreewise out of `KaehlerDifferential.map A A' Pₙ P'ₙ`: the `Pₙ`-linear map
`ω ↦ 1 ⊗ (Ω-map) ω` into `B' ⊗[P'ₙ] Ω[P'ₙ⁄A']` extends, by the extension-of-scalars adjunction,
to a `B`-linear map out of `B ⊗[Pₙ] Ω[Pₙ⁄A]`. These degreewise maps commute with every simplicial
operator, so they form a map of simplicial modules; the alternating-face-map complex of that map
is then reindexed into cohomological degrees by `HomologicalComplex.extendMap`.

## Main definitions

* `CommAlgCat.squareCotangentAdjoint` and `CommAlgCat.squareCotangentTermMap`: the degreewise
  map of base-changed differential modules and the `Pₙ`-linear map it is adjoint to.
* `CommAlgCat.squareCotangentSimplicialMap`: the induced map of simplicial `B`-modules.
* `CommAlgCat.squareCotangentMooreMap` and `CommAlgCat.squareCotangentComplexMap`: the induced
  map of alternating-face-map complexes and of cotangent complexes.
* `CommAlgCat.squareFunctoriality`: the canonical functoriality datum of the square.

## Main results

* `CommAlgCat.squareCotangentTermMap_D` and
  `CommAlgCat.squareCotangentComplexMap_differential`: the induced maps send the pure
  differential `1 ⊗ d p` to `1 ⊗ d (u p)`.
* `CommAlgCat.squareCotangentComplexMap_f`: in cohomological degree `-n` the map of complexes is
  the degreewise map, read through the canonical degree isomorphisms.
* `CommAlgCat.squareFunctoriality_resolution_id` and
  `CommAlgCat.squareFunctoriality_resolution_comp`: the datum is functorial in the square.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings TensorProduct

universe u v w

namespace CommAlgCat

variable {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
  {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}

/-- The `Pₙ`-linear map `Ω[Pₙ⁄A] → B' ⊗[P'ₙ] Ω[P'ₙ⁄A']`, `ω ↦ 1 ⊗ ω`, attached to a commutative
square of ring maps. -/
noncomputable def squareCotangentAdjoint (sq : AlgebraSquare.{u, v, w} A A' B B')
    (n : SimplexCategoryᵒᵖ) :
    ModuleCat.of ((standardResolution.{u, max w v} A B).left.obj n)
        (KaehlerDifferential A ((standardResolution.{u, max w v} A B).left.obj n)) ⟶
      (ModuleCat.restrictScalars
          (standardResolutionAugmentationHom.{u, max w v} A B n)).obj
        ((ModuleCat.restrictScalars sq.map).obj (cotangentTerm.{w, max u v} A' B' n)) := by
  let P := (standardResolution.{u, max w v} A B).left.obj n
  let P' := (standardResolution.{w, max u v} A' B').left.obj n
  let u := standardResolutionSquareMap.{u, v, w} sq n
  let ε := standardResolutionAugmentationHom.{u, max w v} A B n
  let ε' := standardResolutionAugmentationHom.{w, max u v} A' B' n
  letI : Algebra A A' := sq.base.toAlgebra
  letI : Algebra P P' := u.toAlgebra
  letI : Algebra A P' := ((algebraMap A' P').comp sq.base).toAlgebra
  letI : Algebra P' B' := ε'.toAlgebra
  letI : Algebra P B' := (sq.map.comp ε).toAlgebra
  haveI : IsScalarTower P P' B' := IsScalarTower.of_algebraMap_eq fun p =>
    (standardResolutionSquareMap_augmentation_app sq n p).symm
  haveI : IsScalarTower A A' P' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A P P' := IsScalarTower.of_algebraMap_eq fun a =>
    (standardResolutionSquareMap_algebraMap sq n a).symm
  haveI : SMulCommClass A' P P' :=
    ⟨fun a' p x => by simp only [Algebra.smul_def, mul_left_comm]⟩
  let M := ModuleCat.of P (KaehlerDifferential A P)
  let N := (ModuleCat.restrictScalars sq.map).obj (cotangentTerm.{w, max u v} A' B' n)
  exact ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars ε).obj N)
    { toFun := fun ω => (1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P' ω)
      map_add' x y := by
        change (1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P' (x + y)) = _
        rw [map_add, TensorProduct.tmul_add]
        rfl
      map_smul' p x := by
        change (1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P' (p • x)) =
          sq.map (ε p) • ((1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P' x))
        rw [map_smul, TensorProduct.tmul_smul]
        rfl }

/-- The `B`-linear map `B ⊗[Pₙ] Ω[Pₙ⁄A] → B' ⊗[P'ₙ] Ω[P'ₙ⁄A']` of degreewise cotangent terms
induced by a commutative square of ring maps: the `B`-linear extension of
`CommAlgCat.squareCotangentAdjoint`. -/
noncomputable def squareCotangentTermMap (sq : AlgebraSquare.{u, v, w} A A' B B')
    (n : SimplexCategoryᵒᵖ) :
    cotangentTerm.{u, max w v} A B n ⟶
      (ModuleCat.restrictScalars sq.map).obj (cotangentTerm.{w, max u v} A' B' n) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (standardResolutionAugmentationHom.{u, max w v} A B n) (squareCotangentAdjoint sq n)

/-- The value of the degreewise map on the pure differential `1 ⊗ d p`. -/
@[simp]
theorem squareCotangentTermMap_D (sq : AlgebraSquare.{u, v, w} A A' B B')
    (n : SimplexCategoryᵒᵖ) (p : (standardResolution.{u, max w v} A B).left.obj n) :
    squareCotangentTermMap.{u, v, w} sq n (cotangentTermDifferential.{u, max w v} A B n p) =
      cotangentTermDifferential.{w, max u v} A' B' n
        (standardResolutionSquareMap.{u, v, w} sq n p) := by
  have key : squareCotangentTermMap.{u, v, w} sq n
        (cotangentTermDifferential.{u, max w v} A B n p) =
      (1 : B) • (squareCotangentAdjoint.{u, v, w} sq n)
        (KaehlerDifferential.D A ((standardResolution.{u, max w v} A B).left.obj n) p) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (standardResolutionAugmentationHom.{u, max w v} A B n) (squareCotangentAdjoint sq n) (1 : B)
      (KaehlerDifferential.D A ((standardResolution.{u, max w v} A B).left.obj n) p)
  rw [key, one_smul]
  let P := (standardResolution.{u, max w v} A B).left.obj n
  let P' := (standardResolution.{w, max u v} A' B').left.obj n
  let u := standardResolutionSquareMap.{u, v, w} sq n
  let ε := standardResolutionAugmentationHom.{u, max w v} A B n
  let ε' := standardResolutionAugmentationHom.{w, max u v} A' B' n
  let _ : Algebra A A' := sq.base.toAlgebra
  let _ : Algebra P P' := u.toAlgebra
  let _ : Algebra A P' := ((algebraMap A' P').comp sq.base).toAlgebra
  let _ : Algebra P' B' := ε'.toAlgebra
  let _ : Algebra P B' := (sq.map.comp ε).toAlgebra
  have : IsScalarTower P P' B' := IsScalarTower.of_algebraMap_eq fun q =>
    (standardResolutionSquareMap_augmentation_app sq n q).symm
  have : IsScalarTower A A' P' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A P P' := IsScalarTower.of_algebraMap_eq fun a =>
    (standardResolutionSquareMap_algebraMap sq n a).symm
  have : SMulCommClass A' P P' := ⟨fun a' q x => by simp only [Algebra.smul_def, mul_left_comm]⟩
  change (1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P'
    (KaehlerDifferential.D A P p)) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- The degreewise maps commute with every simplicial operator. -/
theorem squareCotangentTermMap_naturality (sq : AlgebraSquare.{u, v, w} A A' B B')
    {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    cotangentMap.{u, max w v} A B g ≫ squareCotangentTermMap.{u, v, w} sq j =
      squareCotangentTermMap.{u, v, w} sq i ≫
        (ModuleCat.restrictScalars sq.map).map (cotangentMap.{w, max u v} A' B' g) := by
  refine cotangentTerm_hom_ext.{u, max w v} A B i _ _ fun p => ?_
  change squareCotangentTermMap.{u, v, w} sq j
      (cotangentMap.{u, max w v} A B g (cotangentTermDifferential.{u, max w v} A B i p)) =
    (ModuleCat.restrictScalars sq.map).map (cotangentMap.{w, max u v} A' B' g)
      (squareCotangentTermMap.{u, v, w} sq i (cotangentTermDifferential.{u, max w v} A B i p))
  rw [cotangentMap_D, squareCotangentTermMap_D, squareCotangentTermMap_D,
    standardResolutionSquareMap_naturality]
  exact (cotangentMap_D.{w, max u v} A' B' g _).symm

/-- The map of simplicial `B`-modules `Ω[P•⁄A] ⊗[P•] B → Ω[P'•⁄A'] ⊗[P'•] B'` induced by a
commutative square of ring maps, the target being read as a simplicial `B`-module along
`sq.map`. -/
noncomputable def squareCotangentSimplicialMap (sq : AlgebraSquare.{u, v, w} A A' B B') :
    (cotangentSimplicialModule.{u, max w v} A B).object ⟶
      ((SimplicialObject.whiskering _ _).obj (ModuleCat.restrictScalars sq.map)).obj
        (cotangentSimplicialModule.{w, max u v} A' B').object where
  app n := squareCotangentTermMap.{u, v, w} sq n
  naturality _ _ g := squareCotangentTermMap_naturality.{u, v, w} sq g

/-- The map of alternating-face-map (Moore) complexes induced by a commutative square of ring
maps, the target being read over `B` along `sq.map`. -/
noncomputable def squareCotangentMooreMap (sq : AlgebraSquare.{u, v, w} A A' B B') :
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u w v} B)).obj
        (cotangentSimplicialModule.{u, max w v} A B).object ⟶
      ((ModuleCat.restrictScalars sq.map).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u w v} B')).obj
          (cotangentSimplicialModule.{w, max u v} A' B').object) :=
  (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u w v} B)).map
      (squareCotangentSimplicialMap.{u, v, w} sq) ≫
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
        (ModuleCat.restrictScalars sq.map)).app
      (cotangentSimplicialModule.{w, max u v} A' B').object).inv

/-- In degree `n` the map of Moore complexes is the degreewise map of cotangent terms. -/
@[simp]
theorem squareCotangentMooreMap_f (sq : AlgebraSquare.{u, v, w} A A' B B') (n : ℕ) :
    (squareCotangentMooreMap.{u, v, w} sq).f n = squareCotangentTermMap.{u, v, w} sq (op ⦋n⦌) :=
  Category.comp_id _

/-- The map of cotangent complexes `L_{B/A} → L_{B'/A'}` induced by a commutative square of ring
maps: the induced map of simplicial modules, pushed through the alternating-face-map complex and
through the reindexing which places simplicial degree `n` in cohomological degree `-n`. -/
noncomputable def squareCotangentComplexMap (sq : AlgebraSquare.{u, v, w} A A' B B') :
    cotangentComplex.{u, max w v} A B ⟶
      ((ModuleCat.restrictScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{w, max u v} A' B') :=
  HomologicalComplex.extendMap (squareCotangentMooreMap.{u, v, w} sq)
      (ComplexShape.embeddingUpIntLE 0) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso
      (ModuleCat.restrictScalars sq.map)
      ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u w v} B')).obj
        (cotangentSimplicialModule.{w, max u v} A' B').object)
      (ComplexShape.embeddingUpIntLE 0)).hom

/-- In cohomological degree `-n` the map of cotangent complexes is the degreewise map of
cotangent terms, read through the two canonical degree isomorphisms. -/
theorem squareCotangentComplexMap_f (sq : AlgebraSquare.{u, v, w} A A' B B') (n : ℕ) :
    (squareCotangentComplexMap.{u, v, w} sq).f (-(n : ℤ)) =
      (cotangentComplex_degreeIso.{u, max w v} A B n).hom ≫
        squareCotangentTermMap.{u, v, w} sq (op ⦋n⦌) ≫
          (ModuleCat.restrictScalars sq.map).map
            (cotangentComplex_degreeIso.{w, max u v} A' B' n).inv := by
  have h : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  simp only [squareCotangentComplexMap, cotangentComplex,
    HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ h,
    squareCotangentMooreMap_f, cotangentComplex_degreeIso]
  rfl

/-- The map of cotangent complexes sends the pure differential `1 ⊗ d p` in simplicial degree `n`
to the pure differential `1 ⊗ d (u p)`, where `u : Pₙ → P'ₙ` is the induced map of standard
resolutions. -/
theorem squareCotangentComplexMap_differential (sq : AlgebraSquare.{u, v, w} A A' B B') (n : ℕ)
    (p : (standardResolution.{u, max w v} A B).left.obj (op ⦋n⦌)) :
    (cotangentComplex_degreeIso.{w, max u v} A' B' n).hom
        ((squareCotangentComplexMap.{u, v, w} sq).f (-(n : ℤ))
          ((cotangentComplex_degreeIso.{u, max w v} A B n).inv
            (cotangentTermDifferential.{u, max w v} A B (op ⦋n⦌) p))) =
      cotangentTermDifferential.{w, max u v} A' B' (op ⦋n⦌)
        (standardResolutionSquareMap.{u, v, w} sq (op ⦋n⦌) p) := by
  rw [squareCotangentComplexMap_f]
  change (cotangentComplex_degreeIso.{w, max u v} A' B' n).hom
      ((cotangentComplex_degreeIso.{w, max u v} A' B' n).inv
        (squareCotangentTermMap.{u, v, w} sq (op ⦋n⦌)
          ((cotangentComplex_degreeIso.{u, max w v} A B n).hom
            ((cotangentComplex_degreeIso.{u, max w v} A B n).inv
              (cotangentTermDifferential.{u, max w v} A B (op ⦋n⦌) p))))) = _
  rw [Iso.inv_hom_id_apply]
  exact (Iso.inv_hom_id_apply _ _).trans (squareCotangentTermMap_D.{u, v, w} sq (op ⦋n⦌) p)

/-- The functoriality of the cotangent complex in the pair of rings: a commutative square
`A → A'`, `B → B'` of ring maps induces a canonical map of standard resolutions, taking variables
to variables, and hence a canonical `B`-linear map of complexes `L_{B/A} → L_{B'/A'}`, given on
differentials by `1 ⊗ d p ↦ 1 ⊗ d (u p)`. -/
noncomputable def squareFunctoriality (sq : AlgebraSquare.{u, v, w} A A' B B') :
    SquareFunctorialityData.{u, v, w} sq where
  resolution n := standardResolutionSquareMap.{u, v, w} sq n
  resolution_naturality g p := standardResolutionSquareMap_naturality.{u, v, w} sq g p
  resolution_algebraMap n a := standardResolutionSquareMap_algebraMap.{u, v, w} sq n a
  resolution_augmentation n p := standardResolutionSquareMap_augmentation_app.{u, v, w} sq n p
  resolution_zero_X b := standardResolutionSquareMap_zero_X.{u, v, w} sq b
  resolution_succ_X n q := standardResolutionSquareMap_succ_X.{u, v, w} sq n q
  complexMap := squareCotangentComplexMap.{u, v, w} sq
  complexMap_differential n p := squareCotangentComplexMap_differential.{u, v, w} sq n p

/-- The functoriality of the cotangent complex is natural in squares: the identity square induces
the identity on standard resolutions. -/
theorem squareFunctoriality_resolution_id (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
    (n : SimplexCategoryᵒᵖ) :
    (squareFunctoriality.{u, v, u} (AlgebraSquare.id.{u, v} A B)).resolution n =
      RingHom.id ((standardResolution.{u, max u v} A B).left.obj n) :=
  standardResolutionSquareMap_id.{u, v} A B n

/-- The functoriality of the cotangent complex is natural in squares: a composition of squares
induces the composition on standard resolutions. -/
theorem squareFunctoriality_resolution_comp {A A' A'' : Type u} [CommRing A] [CommRing A']
    [CommRing A''] {B : CommAlgCat.{max u v} A} {B' : CommAlgCat.{max u v} A'}
    {B'' : CommAlgCat.{max u v} A''} (sq : AlgebraSquare.{u, v, u} A A' B B')
    (sq' : AlgebraSquare.{u, v, u} A' A'' B' B'') (n : SimplexCategoryᵒᵖ) :
    (squareFunctoriality.{u, v, u} (sq.comp sq')).resolution n =
      ((squareFunctoriality.{u, v, u} sq').resolution n).comp
        ((squareFunctoriality.{u, v, u} sq).resolution n) :=
  standardResolutionSquareMap_comp.{u, v} sq sq' n

end CommAlgCat

end
