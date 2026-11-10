module

public import StacksFrontier.Cotangent.AnyResolutionQuasiIso
public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.Cotangent.TensorProductDifferentials
public import StacksFrontier.Cotangent.TensorProductResolution

/-!
# The cotangent complex of a tensor product of Tor independent algebras

Let `A` and `B` be algebras over a ring `R`. The functoriality maps of Tag 08PN for the ring maps
`A → A ⊗_R B` and `B → A ⊗_R B` give a map of complexes of `A ⊗_R B`-modules

`L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A ⟶ L_{A ⊗_R B/R}`,

whose source represents `L_{A/R} ⊗^L_A (A ⊗_R B) ⊕ L_{B/R} ⊗^L_B (A ⊗_R B)`. Its cone is the
object `E` of Equation 92.15.0.1. If `A` and `B` are Tor independent over `R`, the map is a
quasi-isomorphism, so `E = 0` and
`L_{A ⊗_R B/R} = L_{A/R} ⊗^L_A (A ⊗_R B) ⊕ L_{B/R} ⊗^L_B (A ⊗_R B)`.

## Main definitions

* `CommAlgCat.tensorStandardResolutionMap`: the canonical morphism `P_• ⊗_R Q_• ⟶ S_•` from the
  tensor product of the standard resolutions of `A` and of `B` to that of `A ⊗_R B`.
* `CommAlgCat.tensorLeftInclusion`, `CommAlgCat.tensorRightInclusion`: the inclusions of
  `R ⊗_R P_•` and of `R ⊗_R Q_•` into `P_• ⊗_R Q_•`, over `A ⊗_R B`.
* `CommAlgCat.cotangentTensorProductComplex`: the complex `L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A`.
* `CommAlgCat.cotangentTensorProductComplexMap`: the map of complexes above.
* `CommAlgCat.cotangentTensorProductLeftMap`, `CommAlgCat.cotangentTensorProductRightMap`: the
  canonical maps `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}` and
  `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}` in `D(A ⊗_R B)`.
* `CommAlgCat.tensorProductCotangentCone`: the object `E`, the cone of the map of complexes.

## Main results

* `CommAlgCat.quasiIso_tensorCotangentMooreMap`: the map is a quasi-isomorphism on
  alternating-face-map complexes.
* `CommAlgCat.cotangentComplex_tensorProduct_of_torIndependent`: for Tor independent `A` and `B`,
  `E = 0`, the canonical map out of `L_{A/R} ⊗^L_A (A ⊗_R B) ⊕ L_{B/R} ⊗^L_B (A ⊗_R B)` is an
  isomorphism, and the map of complexes is a quasi-isomorphism.
* `CommAlgCat.TensorProductNineDiagram.isZero_upperRight_of_torIndependent`: the vanishing of the
  upper right corner of any nine diagram of Equation 92.15.0.1 whose middle row and middle column
  start with the canonical maps.

## References

* [Stacks Project, Tag 09DA](https://stacks.math.columbia.edu/tag/09DA)
* [Stacks Project, Tag 09D9](https://stacks.math.columbia.edu/tag/09D9)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory Opposite
open AlgebraicTopology
open scoped TensorProduct

universe u

namespace CommAlgCat

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The inclusion `A → A ⊗_R B`, as a map of `R`-algebras into `A ⊗_R B` read over `R`. -/
abbrev tensorIncludeLeft :
    (CommAlgCat.of R A : Type u) →ₐ[R] (CommAlgCat.of R (A ⊗[R] B) : Type u) :=
  Algebra.TensorProduct.includeLeft

/-- The inclusion `B → A ⊗_R B`, as a map of `R`-algebras into `A ⊗_R B` read over `R`. -/
abbrev tensorIncludeRight :
    (CommAlgCat.of R B : Type u) →ₐ[R] (CommAlgCat.of R (A ⊗[R] B) : Type u) :=
  Algebra.TensorProduct.includeRight

section Maps

variable (n : SimplexCategoryᵒᵖ)

/-- The canonical map `P_n → S_n` from the standard resolution of `A` to that of `A ⊗_R B`. -/
def tensorStandardLeftMap :
    ((standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n : Type u) →ₐ[R]
      ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).left.obj n : Type u) :=
  (standardResolutionBaseChangeMap (tensorIncludeLeft R A B) n).comp
    (Algebra.TensorProduct.lid R _).symm.toAlgHom

/-- The canonical map `Q_n → S_n` from the standard resolution of `B` to that of `A ⊗_R B`. -/
def tensorStandardRightMap :
    ((standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n : Type u) →ₐ[R]
      ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).left.obj n : Type u) :=
  (standardResolutionBaseChangeMap (tensorIncludeRight R A B) n).comp
    (Algebra.TensorProduct.lid R _).symm.toAlgHom

/-- The map `P_n ⊗_R Q_n → S_n`, `p ⊗ q ↦ u(p) v(q)`. -/
def tensorStandardMap :
    ((tensorStandardResolution R A B).obj n : Type u) →ₐ[R]
      ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).left.obj n : Type u) :=
  Algebra.TensorProduct.lift (tensorStandardLeftMap R A B n) (tensorStandardRightMap R A B n)
    fun _ _ => Commute.all _ _

/-- The map `P_n → S_n` sends `p` to the image of `1 ⊗ p` under base change along
`A → A ⊗_R B`. -/
@[simp]
theorem tensorStandardLeftMap_apply (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n) :
    tensorStandardLeftMap R A B n p =
      standardResolutionBaseChangeMap (tensorIncludeLeft R A B) n ((1 : R) ⊗ₜ[R] p) :=
  rfl

/-- The map `Q_n → S_n` sends `q` to the image of `1 ⊗ q` under base change along
`B → A ⊗_R B`. -/
@[simp]
theorem tensorStandardRightMap_apply (n : SimplexCategoryᵒᵖ)
    (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n) :
    tensorStandardRightMap R A B n q =
      standardResolutionBaseChangeMap (tensorIncludeRight R A B) n ((1 : R) ⊗ₜ[R] q) :=
  rfl

/-- The map `P_n ⊗_R Q_n → S_n` sends `p ⊗ q` to the product of the images of `p` and `q`. -/
theorem tensorStandardMap_tmul (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n)
    (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n) :
    tensorStandardMap R A B n (p ⊗ₜ[R] q) =
      tensorStandardLeftMap R A B n p * tensorStandardRightMap R A B n q :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- The augmentation of `S_n` sends the image of `p ∈ P_n` to `ε(p) ⊗ 1` in `A ⊗_R B`. -/
theorem tensorStandardLeftMap_augmentation (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n) :
    ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).hom.app n).hom
        (tensorStandardLeftMap R A B n p) =
      ((standardResolution.{u, u} R (CommAlgCat.of R A)).hom.app n).hom p ⊗ₜ[R] (1 : B) := by
  rw [tensorStandardLeftMap_apply, standardResolutionBaseChangeMap_augmentation]
  refine (augmentationBaseChange_app_tmul (tensorIncludeLeft R A B) _ n 1 p).trans ?_
  rw [map_one, one_mul]
  rfl

/-- The augmentation of `S_n` sends the image of `q ∈ Q_n` to `1 ⊗ ε(q)` in `A ⊗_R B`. -/
theorem tensorStandardRightMap_augmentation (n : SimplexCategoryᵒᵖ)
    (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n) :
    ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).hom.app n).hom
        (tensorStandardRightMap R A B n q) =
      (1 : A) ⊗ₜ[R] ((standardResolution.{u, u} R (CommAlgCat.of R B)).hom.app n).hom q := by
  rw [tensorStandardRightMap_apply, standardResolutionBaseChangeMap_augmentation]
  refine (augmentationBaseChange_app_tmul (tensorIncludeRight R A B) _ n 1 q).trans ?_
  rw [map_one, one_mul]
  rfl

/-- The map `P_• ⊗_R Q_• ⟶ S_•` lies over `A ⊗_R B`. -/
theorem tensorStandardMap_augmentation (n : SimplexCategoryᵒᵖ) :
    ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).hom.app n).hom.comp
        (tensorStandardMap R A B n) =
      ((tensorStandardResolutionAugmentation R A B).app n).hom := by
  refine Algebra.TensorProduct.ext' fun p q => ?_
  change ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).hom.app n).hom
      (tensorStandardMap R A B n (p ⊗ₜ[R] q)) = _
  rw [tensorStandardMap_tmul, map_mul, tensorStandardLeftMap_augmentation,
    tensorStandardRightMap_augmentation, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

/-- The maps `P_n ⊗_R Q_n → S_n` commute with the simplicial operators. -/
theorem tensorStandardMap_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    (tensorStandardMap R A B j).comp ((tensorStandardResolution R A B).map g).hom =
      ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).left.map g).hom.comp
        (tensorStandardMap R A B i) := by
  refine Algebra.TensorProduct.ext' fun p q => ?_
  change tensorStandardMap R A B j
      (((standardResolution.{u, u} R (CommAlgCat.of R A)).left.map g).hom p ⊗ₜ[R]
        ((standardResolution.{u, u} R (CommAlgCat.of R B)).left.map g).hom q) =
    ((standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).left.map g).hom
      (tensorStandardMap R A B i (p ⊗ₜ[R] q))
  rw [tensorStandardMap_tmul, tensorStandardMap_tmul, map_mul, tensorStandardLeftMap_apply,
    tensorStandardRightMap_apply, tensorStandardLeftMap_apply, tensorStandardRightMap_apply]
  congr 1
  · exact standardResolutionBaseChangeMap_naturality (tensorIncludeLeft R A B) g (1 ⊗ₜ p)
  · exact standardResolutionBaseChangeMap_naturality (tensorIncludeRight R A B) g (1 ⊗ₜ q)

/-- **The canonical morphism `P_• ⊗_R Q_• ⟶ S_•` of augmented simplicial `R`-algebras over
`A ⊗_R B`**, from the tensor product of the standard resolutions of `A` and `B` to the standard
resolution of `A ⊗_R B`. -/
def tensorStandardResolutionMap :
    resolutionOver (tensorStandardResolutionAugmentation R A B) ⟶
      resolutionOver (standardResolution.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).hom where
  app n := Over.homMk (CommAlgCat.ofHom (tensorStandardMap R A B n))
    (CommAlgCat.hom_ext (tensorStandardMap_augmentation R A B n))
  naturality _ _ g :=
    Over.OverMorphism.ext (CommAlgCat.hom_ext (tensorStandardMap_naturality R A B g))

/-- The map `R ⊗_R P_n → P_n ⊗_R Q_n`, `r ⊗ p ↦ r p ⊗ 1`. -/
def tensorLeftInclusionMap :
    (R ⊗[R] ((standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n : Type u)) →ₐ[R]
      ((tensorStandardResolution R A B).obj n : Type u) :=
  Algebra.TensorProduct.includeLeft.comp (Algebra.TensorProduct.lid R _).toAlgHom

/-- The map `R ⊗_R Q_n → P_n ⊗_R Q_n`, `r ⊗ q ↦ 1 ⊗ r q`. -/
def tensorRightInclusionMap :
    (R ⊗[R] ((standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n : Type u)) →ₐ[R]
      ((tensorStandardResolution R A B).obj n : Type u) :=
  Algebra.TensorProduct.includeRight.comp (Algebra.TensorProduct.lid R _).toAlgHom

/-- The map `R ⊗_R P_n → P_n ⊗_R Q_n` sends `r ⊗ p` to `r p ⊗ 1`. -/
theorem tensorLeftInclusionMap_tmul (r : R)
    (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n) :
    tensorLeftInclusionMap R A B n (r ⊗ₜ[R] p) = (r • p) ⊗ₜ[R] (1 : (standardResolution.{u, u} R
      (CommAlgCat.of R B)).left.obj n) :=
  rfl

/-- The map `R ⊗_R Q_n → P_n ⊗_R Q_n` sends `r ⊗ q` to `1 ⊗ r q`. -/
theorem tensorRightInclusionMap_tmul (r : R)
    (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n) :
    tensorRightInclusionMap R A B n (r ⊗ₜ[R] q) = (1 : (standardResolution.{u, u} R
      (CommAlgCat.of R A)).left.obj n) ⊗ₜ[R] (r • q) :=
  rfl

end Maps

/-- **The inclusion of `R ⊗_R P_•` into `P_• ⊗_R Q_•`**, as a morphism of augmented simplicial
`R`-algebras over `A ⊗_R B`; the source is the base change along `R → R` of the standard
resolution of `A`, augmented to `A ⊗_R B` through `A → A ⊗_R B`. -/
def tensorLeftInclusion :
    resolutionOver (augmentationBaseChange (B := CommAlgCat.of R A)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B)
        (standardResolution.{u, u} R (CommAlgCat.of R A)).hom) ⟶
      resolutionOver (tensorStandardResolutionAugmentation R A B) where
  app n := Over.homMk (CommAlgCat.ofHom (tensorLeftInclusionMap R A B n)) (by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext'
    intro r (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n)
    change ((tensorStandardResolutionAugmentation R A B).app n).hom ((r • p) ⊗ₜ[R] 1) =
      ((augmentationBaseChange (B := CommAlgCat.of R A) (B' := CommAlgCat.of R (A ⊗[R] B))
        (tensorIncludeLeft R A B) (standardResolution.{u, u} R (CommAlgCat.of R A)).hom).app
          n).hom (r ⊗ₜ[R] p)
    rw [tensorStandardResolutionAugmentation_app_tmul, augmentationBaseChange_app_tmul, map_one,
      map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rfl)
  naturality i j g := by
    apply Over.OverMorphism.ext
    refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun r
      (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj i) => ?_)
    change (r • ((standardResolution.{u, u} R (CommAlgCat.of R A)).left.map g).hom p) ⊗ₜ[R] 1 =
      (((standardResolution.{u, u} R (CommAlgCat.of R A)).left.map g).hom (r • p)) ⊗ₜ[R]
        ((standardResolution.{u, u} R (CommAlgCat.of R B)).left.map g).hom 1
    rw [map_smul, map_one]

/-- **The inclusion of `R ⊗_R Q_•` into `P_• ⊗_R Q_•`**, as a morphism of augmented simplicial
`R`-algebras over `A ⊗_R B`. -/
def tensorRightInclusion :
    resolutionOver (augmentationBaseChange (B := CommAlgCat.of R B)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B)
        (standardResolution.{u, u} R (CommAlgCat.of R B)).hom) ⟶
      resolutionOver (tensorStandardResolutionAugmentation R A B) where
  app n := Over.homMk (CommAlgCat.ofHom (tensorRightInclusionMap R A B n)) (by
    apply CommAlgCat.hom_ext
    apply Algebra.TensorProduct.ext'
    intro r (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n)
    change ((tensorStandardResolutionAugmentation R A B).app n).hom (1 ⊗ₜ[R] (r • q)) =
      ((augmentationBaseChange (B := CommAlgCat.of R B) (B' := CommAlgCat.of R (A ⊗[R] B))
        (tensorIncludeRight R A B) (standardResolution.{u, u} R (CommAlgCat.of R B)).hom).app
          n).hom (r ⊗ₜ[R] q)
    rw [tensorStandardResolutionAugmentation_app_tmul, augmentationBaseChange_app_tmul, map_one,
      map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact TensorProduct.tmul_smul r _ _)
  naturality i j g := by
    apply Over.OverMorphism.ext
    refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun r
      (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj i) => ?_)
    change 1 ⊗ₜ[R] (r • ((standardResolution.{u, u} R (CommAlgCat.of R B)).left.map g).hom q) =
      ((standardResolution.{u, u} R (CommAlgCat.of R A)).left.map g).hom 1 ⊗ₜ[R]
        (((standardResolution.{u, u} R (CommAlgCat.of R B)).left.map g).hom (r • q))
    rw [map_smul, map_one]

/-- Followed by the map to the standard resolution of `A ⊗_R B`, the inclusion of `R ⊗_R P_•` is
the canonical map `R ⊗_R P_• ⟶ S_•` of Tag 08QQ for the square `R → A`, `R → A ⊗_R B`. -/
theorem tensorLeftInclusion_comp_tensorStandardResolutionMap :
    tensorLeftInclusion R A B ≫ tensorStandardResolutionMap R A B =
      resolutionOverStandardBaseChangeMap (B := CommAlgCat.of R A)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B) := by
  ext n : 2
  refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun r
    (p : (standardResolution.{u, u} R (CommAlgCat.of R A)).left.obj n) => ?_)
  change tensorStandardMap R A B n (tensorLeftInclusionMap R A B n (r ⊗ₜ[R] p)) =
    standardResolutionBaseChangeMap (tensorIncludeLeft R A B) n (r ⊗ₜ[R] p)
  rw [tensorLeftInclusionMap_tmul, tensorStandardMap_tmul, map_one, mul_one,
    tensorStandardLeftMap_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

/-- Followed by the map to the standard resolution of `A ⊗_R B`, the inclusion of `R ⊗_R Q_•` is
the canonical map `R ⊗_R Q_• ⟶ S_•` of Tag 08QQ for the square `R → B`, `R → A ⊗_R B`. -/
theorem tensorRightInclusion_comp_tensorStandardResolutionMap :
    tensorRightInclusion R A B ≫ tensorStandardResolutionMap R A B =
      resolutionOverStandardBaseChangeMap (B := CommAlgCat.of R B)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B) := by
  ext n : 2
  refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun r
    (q : (standardResolution.{u, u} R (CommAlgCat.of R B)).left.obj n) => ?_)
  change tensorStandardMap R A B n (tensorRightInclusionMap R A B n (r ⊗ₜ[R] q)) =
    standardResolutionBaseChangeMap (tensorIncludeRight R A B) n (r ⊗ₜ[R] q)
  rw [tensorRightInclusionMap_tmul, tensorStandardMap_tmul, map_one, one_mul,
    tensorStandardRightMap_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

/-- Additive functors preserve binary biproducts. -/
private instance preservesBinaryBiproducts_of_additive {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBiproducts F

/-- An additive functor carries `biprod.desc f g` to the comparison isomorphism followed by the
map out of the biproduct of the images. -/
private theorem biprod_desc_map_eq_mapBiprod_inv_comp {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D)
    [F.Additive] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprod.desc (F.map f) (F.map g) = (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) := by
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext' <;> simp [← F.map_comp]

/-- A morphism out of a binary biproduct in a functor category is an isomorphism as soon as it is
one after evaluation at every object. -/
theorem isIso_biprod_desc_of_isIso_app {J C : Type*} [Category J] [Category C] [Preadditive C]
    [HasBinaryBiproducts C] [HasBinaryBiproducts (J ⥤ C)] {F G H : J ⥤ C} (f : F ⟶ H) (g : G ⟶ H)
    (h : ∀ n, IsIso (biprod.desc (f.app n) (g.app n))) : IsIso (biprod.desc f g) := by
  have : ∀ n, IsIso ((biprod.desc f g).app n) := fun n => by
    have : IsIso (biprod.desc (((evaluation J C).obj n).map f) (((evaluation J C).obj n).map g)) :=
      h n
    rw [biprod_desc_map_eq_mapBiprod_inv_comp] at this
    exact IsIso.of_isIso_comp_left (((evaluation J C).obj n).mapBiprod F G).inv
      (((evaluation J C).obj n).map (biprod.desc f g))
  exact NatIso.isIso_of_isIso_app _

/-- Precomposing the two components of a map out of a binary biproduct with isomorphisms is
precomposing the map with the induced isomorphism of biproducts. -/
theorem biprod_desc_iso_comp {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {X X' Y Y' Z : C} (a : X ≅ X') (b : Y ≅ Y') (f : X' ⟶ Z)
    (g : Y' ⟶ Z) :
    biprod.desc (a.hom ≫ f) (b.hom ≫ g) = (biprod.mapIso a b).hom ≫ biprod.desc f g := by
  apply biprod.hom_ext' <;> simp

/-- Precomposing the two components of a map out of a binary biproduct with isomorphisms
preserves its invertibility. -/
theorem isIso_biprod_desc_iso_comp {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] {X X' Y Y' Z : C} (a : X ≅ X') (b : Y ≅ Y') (f : X' ⟶ Z)
    (g : Y' ⟶ Z) (h : IsIso (biprod.desc f g)) : IsIso (biprod.desc (a.hom ≫ f) (b.hom ≫ g)) := by
  rw [biprod_desc_iso_comp]
  infer_instance

/-- If an additive functor carries a map out of a binary biproduct to an isomorphism, then the
map out of the biproduct of the images induced by the images of its components is an
isomorphism. -/
theorem isIso_biprod_desc_map_of_isIso {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : C ⥤ D) [F.Additive]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsIso (F.map (biprod.desc f g))) :
    IsIso (biprod.desc (F.map f) (F.map g)) := by
  rw [biprod_desc_map_eq_mapBiprod_inv_comp]
  infer_instance

/-- The map `(R ⊗_R P_n) ⊗_R (R ⊗_R Q_n) → P_n ⊗_R Q_n` induced by the two inclusions is the
tensor product of the two unitors, hence bijective. -/
theorem bijective_overTensorLift_tensorInclusion (n : SimplexCategoryᵒᵖ) :
    Function.Bijective (overTensorLift ((tensorLeftInclusion R A B).app n)
      ((tensorRightInclusion R A B).app n)) := by
  change Function.Bijective (Algebra.TensorProduct.lift (tensorLeftInclusionMap R A B n)
    (tensorRightInclusionMap R A B n) fun _ _ => Commute.all _ _)
  have h : Algebra.TensorProduct.lift (tensorLeftInclusionMap R A B n)
      (tensorRightInclusionMap R A B n) (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.lid R _).toAlgHom
        (Algebra.TensorProduct.lid R _).toAlgHom := by
    refine Algebra.TensorProduct.ext' fun a b => ?_
    change ((Algebra.TensorProduct.lid R _) a ⊗ₜ[R] 1) *
        (1 ⊗ₜ[R] (Algebra.TensorProduct.lid R _) b) =
      (Algebra.TensorProduct.lid R _) a ⊗ₜ[R] (Algebra.TensorProduct.lid R _) b
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact Algebra.TensorProduct.map_bijective (AlgEquiv.bijective _) (AlgEquiv.bijective _)

/-- **The differentials of `P_• ⊗_R Q_•` split.** The map
`(R ⊗_R P_•)-differentials ⊕ (R ⊗_R Q_•)-differentials ⟶ (P_• ⊗_R Q_•)-differentials` of
simplicial `A ⊗_R B`-modules induced by the two inclusions is an isomorphism. -/
theorem isIso_biprod_desc_whiskerRight_tensorInclusion :
    IsIso (biprod.desc
      (Functor.whiskerRight (tensorLeftInclusion R A B) overDifferentialsFunctor)
      (Functor.whiskerRight (tensorRightInclusion R A B) overDifferentialsFunctor)) :=
  isIso_biprod_desc_of_isIso_app _ _ fun n =>
    isIso_biprod_desc_overDifferentialsFunctor_map _ _
      (bijective_overTensorLift_tensorInclusion R A B n)

/-- **The cotangent complex of `A ⊗_R B` from those of `A` and `B`, on alternating-face-map
complexes.** The map out of the direct sum of the extensions of scalars of the complexes of
`L_{A/R}` and of `L_{B/R}` to `A ⊗_R B` whose components are the functoriality maps of Tag 08PN
for `A → A ⊗_R B` and for `B → A ⊗_R B`. -/
def tensorCotangentMooreMap :
    ((ModuleCat.extendScalars (tensorIncludeLeft R A B).toRingHom).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R A))).obj
          (cotangentSimplicialModule.{u, u} R (CommAlgCat.of R A)).object) ⊞
      ((ModuleCat.extendScalars (tensorIncludeRight R A B).toRingHom).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R B))).obj
          (cotangentSimplicialModule.{u, u} R (CommAlgCat.of R B)).object) ⟶
      (alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).obj
        (cotangentSimplicialModule.{u, u} R (CommAlgCat.of R (A ⊗[R] B))).object :=
  biprod.desc (cotangentExtendScalarsMooreMap (B := CommAlgCat.of R A)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B))
    (cotangentExtendScalarsMooreMap (B := CommAlgCat.of R B)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B))

/-- If `A` and `B` are Tor independent over `R`, the map `tensorCotangentMooreMap` is a
quasi-isomorphism. -/
theorem quasiIso_tensorCotangentMooreMap
    (hTor : RingTheory.TorIndependence.TorIndependent R A B) :
    QuasiIso (tensorCotangentMooreMap R A B) := by
  have hψ := cotangentComputedByEveryResolution R (CommAlgCat.of R (A ⊗[R] B))
    (tensorStandardResolution R A B) (tensorStandardResolutionAugmentation R A B)
    (isPolynomialAlgebra_tensorStandardResolution R A B)
    (isResolution_tensorStandardResolution R A B hTor) (tensorStandardResolutionMap R A B)
  have hsplit := isIso_biprod_desc_whiskerRight_tensorInclusion R A B
  have hfac : tensorCotangentMooreMap R A B =
      biprod.desc
        (((cotangentBaseChangeComparisonIso (B := CommAlgCat.of R A)
          (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B)).hom ≫
          (alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).map
            (Functor.whiskerRight (tensorLeftInclusion R A B) overDifferentialsFunctor)) ≫
          (alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).map
            (Functor.whiskerRight (tensorStandardResolutionMap R A B) overDifferentialsFunctor))
        (((cotangentBaseChangeComparisonIso (B := CommAlgCat.of R B)
          (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B)).hom ≫
          (alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).map
            (Functor.whiskerRight (tensorRightInclusion R A B) overDifferentialsFunctor)) ≫
          (alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).map
            (Functor.whiskerRight (tensorStandardResolutionMap R A B)
              overDifferentialsFunctor)) := by
    unfold tensorCotangentMooreMap
    congr 1
    · rw [cotangentExtendScalarsMooreMap_eq,
        ← tensorLeftInclusion_comp_tensorStandardResolutionMap, Functor.whiskerRight_comp,
        Functor.map_comp, Category.assoc]
    · rw [cotangentExtendScalarsMooreMap_eq,
        ← tensorRightInclusion_comp_tensorStandardResolutionMap, Functor.whiskerRight_comp,
        Functor.map_comp, Category.assoc]
  have h₃ := isIso_biprod_desc_map_of_isIso
    (alternatingFaceMapComplex (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B))))
    (Functor.whiskerRight (tensorLeftInclusion R A B) overDifferentialsFunctor)
    (Functor.whiskerRight (tensorRightInclusion R A B) overDifferentialsFunctor)
    (Functor.map_isIso _ _)
  have h₄ := isIso_biprod_desc_iso_comp
    (cotangentBaseChangeComparisonIso (B := CommAlgCat.of R A)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B))
    (cotangentBaseChangeComparisonIso (B := CommAlgCat.of R B)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B)) _ _ h₃
  rw [hfac, ← biprod.desc_comp]
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := hψ)

/-! ### The cotangent complex of `A ⊗_R B` -/

section Derived

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- The complex `L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A` of `A ⊗_R B`-modules: the direct sum of the
degreewise extensions of scalars of `L_{A/R}` along `A → A ⊗_R B` and of `L_{B/R}` along
`B → A ⊗_R B`, whose terms are `(A ⊗_R B) ⊗_A (L_{A/R})_n = (L_{A/R})_n ⊗_R B` and
`(A ⊗_R B) ⊗_B (L_{B/R})_n = (L_{B/R})_n ⊗_R A`. -/
def cotangentTensorProductComplex : CochainComplex (ModuleCat.{u} (A ⊗[R] B)) ℤ :=
  (((ModuleCat.extendScalars (tensorIncludeLeft R A B).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} R (CommAlgCat.of R A))) ⊞
    (((ModuleCat.extendScalars (tensorIncludeRight R A B).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} R (CommAlgCat.of R B)))

/-- **The map of complexes `L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A ⟶ L_{A ⊗_R B/R}`**, out of
`CommAlgCat.cotangentTensorProductComplex`: its two components are the functoriality maps of
Tag 08PN for `A → A ⊗_R B` and for `B → A ⊗_R B`, read through extension of scalars. -/
def cotangentTensorProductComplexMap :
    cotangentTensorProductComplex R A B ⟶ cotangentComplex.{u, u} R (CommAlgCat.of R (A ⊗[R] B)) :=
  biprod.desc (cotangentExtendScalarsComplexMap (B := CommAlgCat.of R A)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B))
    (cotangentExtendScalarsComplexMap (B := CommAlgCat.of R B)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B))

/-- Precomposing the two components of a map out of a binary biproduct with the inverses of
isomorphisms preserves being a quasi-isomorphism. -/
private theorem quasiIso_biprod_desc_inv_comp {ι : Type*} {c : ComplexShape ι} {C : Type*}
    [Category C] [Abelian C] {X X' Y Y' Z : HomologicalComplex C c} (a : X ≅ X') (b : Y ≅ Y')
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : QuasiIso (biprod.desc f g)) :
    QuasiIso (biprod.desc (a.inv ≫ f) (b.inv ≫ g)) := by
  rw [show biprod.desc (a.inv ≫ f) (b.inv ≫ g) = _ from biprod_desc_iso_comp a.symm b.symm f g]
  exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso _) (hφ' := h)

/-- If `A` and `B` are Tor independent over `R`, the map of complexes
`L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A ⟶ L_{A ⊗_R B/R}` is a quasi-isomorphism. -/
theorem quasiIso_cotangentTensorProductComplexMap
    (hTor : RingTheory.TorIndependence.TorIndependent R A B) :
    QuasiIso (cotangentTensorProductComplexMap R A B) := by
  have h₁ : QuasiIso (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
      (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).map (tensorCotangentMooreMap R A B)) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 (quasiIso_tensorCotangentMooreMap R A B hTor)
  have h₂ : QuasiIso (biprod.desc
      (HomologicalComplex.extendMap (cotangentExtendScalarsMooreMap (B := CommAlgCat.of R A)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B))
        (ComplexShape.embeddingUpIntLE (0 : ℤ)))
      (HomologicalComplex.extendMap (cotangentExtendScalarsMooreMap (B := CommAlgCat.of R B)
        (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B))
        (ComplexShape.embeddingUpIntLE (0 : ℤ)))) := by
    have h := quasiIso_comp (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
      (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).mapBiprod _ _).inv
      (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
        (ModuleCat.{u} (CommAlgCat.of R (A ⊗[R] B)))).map (tensorCotangentMooreMap R A B))
      (hφ := quasiIso_of_isIso _) (hφ' := h₁)
    rwa [tensorCotangentMooreMap, ← biprod_desc_map_eq_mapBiprod_inv_comp] at h
  exact quasiIso_biprod_desc_inv_comp _ _ _ _ h₂

/-- **The canonical map `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`** of the ring maps
`R → A → A ⊗_R B`: the functoriality map of Tag 08PN, read through the identification of the
derived base change with the degreewise one. -/
def cotangentTensorProductLeftMap :
    cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B) ⟶
      cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) :=
  (cotangentComplexDerivedBaseChangeTermwiseIso R (CommAlgCat.of R A) (A ⊗[R] B)).hom ≫
    DerivedCategory.Q.map (cotangentExtendScalarsComplexMap (B := CommAlgCat.of R A)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B))

/-- **The canonical map `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`** of the ring maps
`R → B → A ⊗_R B`. -/
def cotangentTensorProductRightMap :
    cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
      cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) :=
  (cotangentComplexDerivedBaseChangeTermwiseIso R (CommAlgCat.of R B) (A ⊗[R] B)).hom ≫
    DerivedCategory.Q.map (cotangentExtendScalarsComplexMap (B := CommAlgCat.of R B)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B))

/-- **The object `E` of Equation 92.15.0.1**: the cone of the map of complexes
`L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A ⟶ L_{A ⊗_R B/R}`, whose source represents
`L_{A/R} ⊗^L_A (A ⊗_R B) ⊕ L_{B/R} ⊗^L_B (A ⊗_R B)`. -/
abbrev tensorProductCotangentCone : DerivedCategory (ModuleCat.{u} (A ⊗[R] B)) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCone (cotangentTensorProductComplexMap R A B))

/-- If `A` and `B` are Tor independent `R`-algebras, then the object `E` of Equation 92.15.0.1 —
the cone of the map of complexes
`L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A ⟶ L_{A ⊗_R B/R}` given by the functoriality maps — is zero;
the canonical map
`L_{A/R} ⊗^L_A (A ⊗_R B) ⊕ L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}` is an isomorphism in
`D(A ⊗_R B)`; and this is represented by the complex `L_{A/R} ⊗_R B ⊕ L_{B/R} ⊗_R A` of
`A ⊗_R B`-modules, the map of complexes being a quasi-isomorphism. -/
@[stacks 09DA]
theorem cotangentComplex_tensorProduct_of_torIndependent
    (hTor : RingTheory.TorIndependence.TorIndependent R A B) :
    IsZero (tensorProductCotangentCone R A B) ∧
      IsIso (biprod.desc (cotangentTensorProductLeftMap R A B)
        (cotangentTensorProductRightMap R A B)) ∧
      QuasiIso (cotangentTensorProductComplexMap R A B) := by
  have hq := quasiIso_cotangentTensorProductComplexMap R A B hTor
  have hQ : IsIso (DerivedCategory.Q.map (cotangentTensorProductComplexMap R A B)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  refine ⟨Triangle.isZero₃_of_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished (cotangentTensorProductComplexMap R A B))
    hQ, ?_, hq⟩
  have h := isIso_biprod_desc_map_of_isIso (DerivedCategory.Q (C := ModuleCat.{u} (A ⊗[R] B)))
    (cotangentExtendScalarsComplexMap (B := CommAlgCat.of R A)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeLeft R A B))
    (cotangentExtendScalarsComplexMap (B := CommAlgCat.of R B)
      (B' := CommAlgCat.of R (A ⊗[R] B)) (tensorIncludeRight R A B)) hQ
  exact isIso_biprod_desc_iso_comp _ _ _ _ h

/-- **The object `E` of the nine diagram of Equation 92.15.0.1 vanishes for Tor independent
algebras.** If the middle row and the middle column of the diagram are triangles whose first
morphisms are the canonical maps `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}` and
`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`, then the upper right corner is zero. -/
theorem TensorProductNineDiagram.isZero_upperRight_of_torIndependent
    (D : TensorProductNineDiagram R A B)
    (hTor : RingTheory.TorIndependence.TorIndependent R A B)
    (hA : D.mapA = cotangentTensorProductLeftMap R A B)
    (hB : D.mapB = cotangentTensorProductRightMap R A B) :
    IsZero D.upperRight := by
  have h : IsIso (biprod.desc D.mapA D.mapB) := by
    rw [hA, hB]
    exact (cotangentComplex_tensorProduct_of_torIndependent R A B hTor).2.1
  have hup : D.mapA ≫ D.projA = 0 := comp_distTriang_mor_zero₁₂ _ D.rowDistinguished
  have hδ : D.projA ≫ D.shiftA = 0 := comp_distTriang_mor_zero₂₃ _ D.rowDistinguished
  have hvp : IsIso (D.mapB ≫ D.projA) :=
    isIso₃_of_isIso₁₂
      (Triangle.homMk
        (binaryBiproductTriangle
          (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))
          (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B)))
        (Triangle.mk D.mapA D.projA D.shiftA)
        (𝟙 _) (biprod.desc D.mapA D.mapB) (D.mapB ≫ D.projA)
        (by simp [binaryBiproductTriangle])
        (by refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [binaryBiproductTriangle, hup])
        (by simp [binaryBiproductTriangle, hδ]))
      (binaryBiproductTriangle_distinguished _ _) D.rowDistinguished (IsIso.id _) h
  exact Triangle.isZero₃_of_isIso₁ _ D.rightColumnDistinguished hvp

end Derived

end CommAlgCat

end
