module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.ExtendScalars
public import StacksFrontier.Cotangent.StandardResolution
public import StacksFrontier.RingTheory.Kaehler.Defs

/-!
# The cotangent complex of a ring map

For a commutative `A`-algebra `B`, the standard simplicial resolution `P` of `B` gives a
simplicial `B`-module whose term in degree `n` is `B ⊗[Pₙ] Ω[Pₙ⁄A]`. Its associated chain
complex is the cotangent complex `L_{B/A}`.

## Main definitions

* `CommAlgCat.standardResolutionAugmentationHom`: the ring homomorphism from a term of the
  standard resolution to `B` given by the augmentation.
* `CommAlgCat.cotangentTerm` and `CommAlgCat.cotangentTermDifferential`: the degreewise
  base-changed module of differentials and its pure differentials `1 ⊗ d p`.
* `CommAlgCat.CotangentSimplicialModuleData`: the data of a simplicial `B`-module together with
  the identifications of its terms and of its action on pure differentials.
* `CommAlgCat.cotangentSimplicialModule`: the simplicial module of base-changed Kähler
  differentials of the standard resolution; its action on pure differentials is
  `CommAlgCat.cotangentSimplicialModule_map_differential`.
* `CommAlgCat.cotangentComplex`: its associated integer-indexed cochain complex.

## Main results

* `CommAlgCat.cotangentComplex_degreeIso` identifies degree `-n` with the base-changed
  differentials in simplicial degree `n`.
* `CommAlgCat.cotangentComplex_isZero_pos` and `CommAlgCat.cotangentComplex_d` describe the
  other degrees and the differential.

## Implementation notes

The simplicial module is specified by its terms and by its action on the generators `1 ⊗ d p`.
The latter records the canonical naturality with respect to all faces and degeneracies. The
associated complex reindexes the alternating-face (Moore) chain complex, which is canonically
homotopy equivalent to the normalized complex, so that simplicial degree `n` occurs in
cohomological degree `-n`.

The two facts about scalar extension that the degreewise maps need — the value of the adjunction
on a pure tensor and extensionality against the pure differentials — are proved once and for all
in `StacksFrontier.Cotangent.ExtendScalars`.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings TensorProduct

universe u v

namespace CommAlgCat

/-- The augmentation of the standard resolution, as a ring homomorphism to `B`. -/
noncomputable abbrev standardResolutionAugmentationHom (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ) :
    (standardResolution A B).left.obj n →+* B := by
  have h : (standardResolution A B).left.obj n →+* (standardResolution A B).right := by
    exact ((standardResolution A B).hom.app n).hom.toRingHom
  rw [standardResolution_right A B] at h
  exact h

/-- The augmentation condition on a morphism of the standard resolution, read as an identity of
ring homomorphisms. Simplicial operators satisfy it by naturality
(`standardResolutionAugmentationHom_naturality`), but so do morphisms which are not simplicial
operators, and those are the ones a contraction of the resolution is built from. -/
theorem standardResolutionAugmentationHom_comp_of_over (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ}
    (g : (standardResolution A B).left.obj i ⟶ (standardResolution A B).left.obj j)
    (hg : g ≫ (standardResolution A B).hom.app j = (standardResolution A B).hom.app i) :
    (standardResolutionAugmentationHom A B j).comp g.hom.toRingHom =
      standardResolutionAugmentationHom A B i := by
  ext p
  simpa [standardResolutionAugmentationHom] using
    congrArg (fun k : (standardResolution A B).left.obj i ⟶ B => k p) hg

/-- The augmentation is compatible with every simplicial operator. -/
theorem standardResolutionAugmentationHom_naturality (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (standardResolutionAugmentationHom A B j).comp
      ((standardResolution A B).left.map f).hom.toRingHom =
        standardResolutionAugmentationHom A B i :=
  standardResolutionAugmentationHom_comp_of_over A B _
    ((standardResolution A B).hom.naturality f)

/-- The `n`th module of base-changed differentials in the standard resolution. -/
@[implicit_reducible]
noncomputable def cotangentTerm (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ) : ModuleCat.{max u v} B :=
  (ModuleCat.extendScalars (standardResolutionAugmentationHom A B n)).obj
    (ModuleCat.of ((standardResolution A B).left.obj n)
      (KaehlerDifferential A ((standardResolution A B).left.obj n)))

/-- The pure differential `1 ⊗ d p` in the base-changed differential module. -/
noncomputable def cotangentTermDifferential (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution A B).left.obj n) :
    cotangentTerm A B n :=
  (1 : B) ⊗ₜ KaehlerDifferential.D A ((standardResolution A B).left.obj n) p

/-- Data of the simplicial module obtained from the differentials of the standard resolution and
extension of scalars along its augmentation. -/
structure CotangentSimplicialModuleData (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) where
  /-- The underlying simplicial `B`-module. -/
  object : SimplicialObject (ModuleCat.{max u v} B)
  /-- Identification of its terms with the base-changed modules of differentials. -/
  termIso : ∀ n, object.obj n ≅ cotangentTerm A B n
  /-- Its simplicial maps send a pure differential to the pure differential of the image. -/
  map_differential : ∀ {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (p : (standardResolution A B).left.obj i),
    ((termIso i).inv ≫ object.map f ≫ (termIso j).hom)
      (cotangentTermDifferential A B i p) =
    cotangentTermDifferential A B j ((standardResolution A B).left.map f p)

/-- The `Pᵢ`-linear map `Ω[Pᵢ⁄A] → B ⊗[Pⱼ] Ω[Pⱼ⁄A]`, `ω ↦ 1 ⊗ ω`, attached to a morphism
`g : Pᵢ ⟶ Pⱼ` of the standard resolution lying over `B`; it is adjoint to `cotangentPush`. -/
noncomputable def cotangentPushAdjoint (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ}
    (g : (standardResolution A B).left.obj i ⟶ (standardResolution A B).left.obj j)
    (hg : (standardResolutionAugmentationHom A B j).comp g.hom.toRingHom =
      standardResolutionAugmentationHom A B i) :
    ModuleCat.of ((standardResolution A B).left.obj i)
      (KaehlerDifferential A ((standardResolution A B).left.obj i)) ⟶
    (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B i)).obj
      (cotangentTerm A B j) := by
  let P := (standardResolution A B).left.obj i
  let Q := (standardResolution A B).left.obj j
  letI : Algebra P Q := g.hom.toRingHom.toAlgebra
  letI : Algebra P B := (standardResolutionAugmentationHom A B i).toAlgebra
  letI : Algebra Q B := (standardResolutionAugmentationHom A B j).toAlgebra
  haveI : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  haveI : IsScalarTower P Q B := IsScalarTower.of_algebraMap_eq' hg.symm
  let M := ModuleCat.of P (KaehlerDifferential A P)
  let N := cotangentTerm A B j
  let ε := standardResolutionAugmentationHom A B i
  let d : M ⟶ (ModuleCat.restrictScalars ε).obj N :=
    ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars ε).obj N)
      { toFun := fun x => (1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x)
        map_add' := by
          intro x y
          change (TensorProduct.mk Q B (KaehlerDifferential A Q) 1)
              (KaehlerDifferential.map A A P Q (x + y)) = _
          rw [map_add]
          exact (TensorProduct.mk Q B (KaehlerDifferential A Q) 1).map_add _ _
        map_smul' := by
          intro p x
          change (1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q (p • x)) =
            ε p • ((1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x))
          rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          congr 1 }
  exact d

/-- The `B`-linear map `B ⊗[Pᵢ] Ω[Pᵢ⁄A] → B ⊗[Pⱼ] Ω[Pⱼ⁄A]` induced by a morphism `g : Pᵢ ⟶ Pⱼ`
of the standard resolution lying over `B`: the `B`-linear extension of `cotangentPushAdjoint`.
For a simplicial operator this is `cotangentMap`, the structure map of
`cotangentSimplicialModule`; the point of the general version is that it applies to morphisms
which are not simplicial operators, such as the morphisms of a contraction. -/
noncomputable def cotangentPush (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ}
    (g : (standardResolution A B).left.obj i ⟶ (standardResolution A B).left.obj j)
    (hg : (standardResolutionAugmentationHom A B j).comp g.hom.toRingHom =
      standardResolutionAugmentationHom A B i) :
    cotangentTerm A B i ⟶ cotangentTerm A B j :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (standardResolutionAugmentationHom A B i) (cotangentPushAdjoint A B g hg)

/-- The value of `cotangentPush` on the pure differential `1 ⊗ d p`. -/
@[simp]
theorem cotangentPush_D (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ}
    (g : (standardResolution A B).left.obj i ⟶ (standardResolution A B).left.obj j)
    (hg : (standardResolutionAugmentationHom A B j).comp g.hom.toRingHom =
      standardResolutionAugmentationHom A B i)
    (p : (standardResolution A B).left.obj i) :
    cotangentPush A B g hg (cotangentTermDifferential A B i p) =
      cotangentTermDifferential A B j (g p) := by
  have key : cotangentPush A B g hg (cotangentTermDifferential A B i p) =
      (1 : B) • (cotangentPushAdjoint A B g hg)
        (KaehlerDifferential.D A ((standardResolution A B).left.obj i) p) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (standardResolutionAugmentationHom A B i) (cotangentPushAdjoint A B g hg) (1 : B)
      (KaehlerDifferential.D A ((standardResolution A B).left.obj i) p)
  rw [key, one_smul]
  let P := (standardResolution A B).left.obj i
  let Q := (standardResolution A B).left.obj j
  let _ : Algebra P Q := g.hom.toRingHom.toAlgebra
  let _ : Algebra P B := (standardResolutionAugmentationHom A B i).toAlgebra
  let _ : Algebra Q B := (standardResolutionAugmentationHom A B j).toAlgebra
  have : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  have : IsScalarTower P Q B := IsScalarTower.of_algebraMap_eq' hg.symm
  show (1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q (KaehlerDifferential.D A P p)) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- The `Pᵢ`-linear map `Ω[Pᵢ⁄A] → B ⊗[Pⱼ] Ω[Pⱼ⁄A]` whose associated extension of scalars is the
simplicial structure map of the cotangent simplicial module: `cotangentPushAdjoint` at a
simplicial operator, which lies over `B` by naturality of the augmentation. -/
noncomputable def cotangentMapAdjoint (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    ModuleCat.of ((standardResolution A B).left.obj i)
      (KaehlerDifferential A ((standardResolution A B).left.obj i)) ⟶
    (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B i)).obj
      (cotangentTerm A B j) :=
  cotangentPushAdjoint A B ((standardResolution A B).left.map f)
    (standardResolutionAugmentationHom_naturality A B f)

/-- The simplicial structure map of the cotangent simplicial module: `cotangentPush` at a
simplicial operator. -/
noncomputable def cotangentMap (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    cotangentTerm A B i ⟶ cotangentTerm A B j :=
  cotangentPush A B ((standardResolution A B).left.map f)
    (standardResolutionAugmentationHom_naturality A B f)

/-- The value of `cotangentMap` on the pure differential `1 ⊗ d p`. -/
@[simp]
theorem cotangentMap_D (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (p : (standardResolution A B).left.obj i) :
    cotangentMap A B f (cotangentTermDifferential A B i p) =
      cotangentTermDifferential A B j ((standardResolution A B).left.map f p) :=
  cotangentPush_D A B ((standardResolution A B).left.map f)
    (standardResolutionAugmentationHom_naturality A B f) p

/-- Two `B`-linear maps out of `cotangentTerm A B i` which agree on every pure differential
`1 ⊗ d p` are equal: the differentials `d p` span `Ω[Pᵢ⁄A]`. -/
theorem cotangentTerm_hom_ext (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (i : SimplexCategoryᵒᵖ)
    {N : ModuleCat.{max u v} B} (α β : cotangentTerm A B i ⟶ N)
    (h : ∀ p : (standardResolution A B).left.obj i,
      α (cotangentTermDifferential A B i p) =
        β (cotangentTermDifferential A B i p)) : α = β :=
  ModuleCat.extendScalars_kaehlerDifferential_hom_ext
    (standardResolutionAugmentationHom A B i) α β h

/-- The map `ω ↦ 1 ⊗ ω` of `Pₙ`-modules into `cotangentTerm A B n`. Being a morphism of
`Pₙ`-modules, it packages the additivity and semilinearity of `1 ⊗ -` in one place. -/
noncomputable def cotangentTermMk (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ) :
    ModuleCat.of ((standardResolution A B).left.obj n)
        (KaehlerDifferential A ((standardResolution A B).left.obj n)) ⟶
      (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B n)).obj
        (cotangentTerm A B n) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
    (standardResolutionAugmentationHom A B n) (𝟙 (cotangentTerm A B n))

/-- `cotangentTermMk` sends `d p` to the pure differential `1 ⊗ d p`. -/
theorem cotangentTermMk_D (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution A B).left.obj n) :
    cotangentTermMk A B n (KaehlerDifferential.D A _ p) =
      cotangentTermDifferential A B n p := rfl

/-- `1 ⊗ d -` is additive. -/
theorem cotangentTermDifferential_add (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ)
    (p q : (standardResolution A B).left.obj n) :
    cotangentTermDifferential A B n (p + q) =
      cotangentTermDifferential A B n p + cotangentTermDifferential A B n q := by
  rw [← cotangentTermMk_D, ← cotangentTermMk_D, ← cotangentTermMk_D, map_add, map_add]
  rfl

/-- `1 ⊗ d 1 = 0`. -/
theorem cotangentTermDifferential_one (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ) :
    cotangentTermDifferential A B n 1 = 0 := by
  rw [← cotangentTermMk_D, Derivation.map_one_eq_zero, map_zero]
  rfl

/-- `1 ⊗ d -` kills the image of `A`. -/
theorem cotangentTermDifferential_algebraMap (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ) (a : A) :
    cotangentTermDifferential A B n
      (algebraMap A ((standardResolution A B).left.obj n) a) = 0 := by
  rw [← cotangentTermMk_D, Derivation.map_algebraMap, map_zero]
  rfl

/-- The Leibniz rule for `1 ⊗ d -`: the coefficients are the augmentation values. -/
theorem cotangentTermDifferential_mul (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : SimplexCategoryᵒᵖ)
    (p q : (standardResolution A B).left.obj n) :
    cotangentTermDifferential A B n (p * q) =
      standardResolutionAugmentationHom A B n p • cotangentTermDifferential A B n q +
      standardResolutionAugmentationHom A B n q • cotangentTermDifferential A B n p := by
  rw [← cotangentTermMk_D, ← cotangentTermMk_D, ← cotangentTermMk_D, Derivation.leibniz,
    map_add, map_smul, map_smul]
  rfl

/-- The canonical simplicial `B`-module `Ω[P•⁄A] ⊗[P•] B`. -/
@[stacks 08PN "the simplicial module"]
noncomputable def cotangentSimplicialModule (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) : CotangentSimplicialModuleData A B :=
  { object :=
      { obj := cotangentTerm A B
        map := fun f => cotangentMap A B f
        map_id := by
          intro i
          apply cotangentTerm_hom_ext A B i
          intro p
          simp
        map_comp := by
          intro i j k f g
          apply cotangentTerm_hom_ext A B i
          intro p
          simp }
    termIso := fun n => Iso.refl _
    map_differential := by
      intro i j f p
      simp }

/-- The simplicial maps of the cotangent simplicial module send a pure differential to the pure
differential of its image. -/
theorem cotangentSimplicialModule_map_differential (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (p : (standardResolution A B).left.obj i) :
    (cotangentSimplicialModule A B).object.map f (cotangentTermDifferential A B i p) =
      cotangentTermDifferential A B j ((standardResolution A B).left.map f p) :=
  cotangentMap_D A B f p

/-- The cotangent complex `L_{B/A}` associated to the standard resolution. -/
@[stacks 08PN "the associated complex"]
noncomputable def cotangentComplex (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (cotangentSimplicialModule A B).object).extend
      (ComplexShape.embeddingUpIntLE 0))

/-- The term in cohomological degree `-n` is the base-changed differentials of the `n`th algebra
in the standard resolution. -/
noncomputable def cotangentComplex_degreeIso (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (cotangentComplex A B).X (-(n : ℤ)) ≅ cotangentTerm A B (op ⦋n⦌) :=
  (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
      (cotangentSimplicialModule A B).object).extendXIso
        (ComplexShape.embeddingUpIntLE 0) (by simp))

/-- The cotangent complex vanishes in positive cohomological degrees. -/
theorem cotangentComplex_isZero_pos (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (m : ℤ) (hm : 0 < m) :
    IsZero ((cotangentComplex A B).X m) :=
  ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (cotangentSimplicialModule A B).object).isZero_extend_X
      (ComplexShape.embeddingUpIntLE 0) m
      ((ComplexShape.notMem_range_embeddingUpIntLE_iff (p := 0) m).2 hm)

/-- In adjacent negative degrees, the differential is the alternating sum of the simplicial face
maps, transported by the canonical degree isomorphisms. -/
theorem cotangentComplex_d (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (n : ℕ) :
    (cotangentComplex A B).d (-(n + 1 : ℕ) : ℤ) (-(n : ℤ)) =
      (cotangentComplex_degreeIso A B (n + 1)).hom ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          (cotangentSimplicialModule A B).object n ≫
      (cotangentComplex_degreeIso A B n).inv := by
  show (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (cotangentSimplicialModule A B).object).extend
      (ComplexShape.embeddingUpIntLE 0)).d _ _ = _
  rw [HomologicalComplex.extend_d_eq (i := n + 1) (j := n)
    (hi := by simp) (hj := by simp), AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  rfl

end CommAlgCat

end
