module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModuleExtTotal
public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModuleLeftFunctor

/-!
# The change-of-rings tensor complex comparison is natural in the left variable

`DifferentialGraded.absExtTensorRightIso` identifies the change-of-rings tensor complex of Tag
06Y6 built from the complex underlying `L` with the complex of homogeneous components of
`DifferentialGradedModule.absoluteTensorModule L N`. This file makes that identification natural
in `L`, which is the shape
`CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp` consumes.

Degreewise the square is checked on a bigraded summand through
`HomologicalComplex.mapBifunctor.hom_ext`: on the summand `(A ⊗_R L^p) ⊗_A N^q` the induced map
is `LinearMap.rTensor` of the base change of `φ` on `L^p`, and the identification sends
`(a ⊗ x) ⊗ y` to the pure tensor `x ⊗ a y`, so both routes give `φ x ⊗ a y`.

## Main definitions

* `DifferentialGraded.absExtTensorRightNatIso`: **the comparison as an isomorphism of functors**
  of the left variable.

## Main results

* `DifferentialGraded.absExtSummand_naturality`: the square on a bigraded summand.
* `DifferentialGraded.absExtForward_naturality`: the square of complexes.

## Implementation notes

As in `StacksFrontier/Algebra/DifferentialGraded/Module/AbsoluteTensorModuleExtTotal.lean`, every
statement opens with `letI := f.toAlgebra`, because `ModuleCat.extendScalars` builds the algebra
structure from the bare ring homomorphism and the degreewise identification holds by `rfl` only
there. The whisker the bifunctor produces is converted to `LinearMap.rTensor` of the base-changed
map by the `rfl` lemma `DifferentialGraded.curriedTensor_extendScalarsLarge_map` before the square
is stated, for the same reason as for the differential: stated against the whisker, the defeq
check exhausts the heartbeat budget.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) is the derived
  change-of-rings tensor product.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGraded

open DifferentialGradedAlgebra DifferentialGradedModule

attribute [local instance] DifferentialGradedModule.degreeZeroOppositeModule
  DifferentialGradedModule.degreeZeroOppositeModule_isScalarTower
  DifferentialGradedModule.degreeZeroComponentModule
  DifferentialGradedModule.degreeZeroComponent_smulCommClass
  DifferentialGradedModule.degreeZeroComponent_isScalarTower
  DifferentialGradedModule.absModRightModule DifferentialGradedModule.absModRightScalarTower
  DifferentialGradedModule.absModDecomposition
  DifferentialGradedModule.absModOppositeModule DifferentialGradedModule.absModGradingModule
  DifferentialGradedModule.absModSummandModule
  DifferentialGradedModule.absModSummand_isScalarTower

attribute [local instance 10000] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal

variable {R A : Type u} [CommRing R] [CommRing A]

/-! ### The induced map on the extended complex -/

/-- The base change of a homomorphism of differential graded modules, as a morphism between the
terms of the extended complexes. As with `DifferentialGraded.extendScalarsLargeDiff`, this
spelling — not a `ModuleCat.of` one — is what can be rewritten inside the bifunctor's action. -/
def extendScalarsLargeMap (f : R →+* A) :
    letI := f.toAlgebra
    ∀ {A₁ : DifferentialGradedAlgebra.{u, u} R} {L L' : DifferentialGradedModule.{u, u, u} A₁}
      (_φ : L ⟶ L') (p : ℤ),
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).X p ⟶
        ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L'.toCochainComplex).X p := by
  letI := f.toAlgebra
  intro A₁ L L' φ p
  exact (ModuleCat.ofHom (LinearMap.baseChange A (φ.gradedMap p)) :
    ModuleCat.of A (A ⊗[R] L.grading p) ⟶ ModuleCat.of A (A ⊗[R] L'.grading p))

/-- In degree `p`, the base change of a homomorphism `φ` of differential graded modules is
`DifferentialGraded.extendScalarsLargeMap f φ p`. -/
theorem extendScalarsLarge_map_f (f : R →+* A) :
    letI := f.toAlgebra
    ∀ {A₁ : DifferentialGradedAlgebra.{u, u} R} {L L' : DifferentialGradedModule.{u, u, u} A₁}
      (φ : L ⟶ L') (p : ℤ),
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).map φ.toCochainMap).f p =
        extendScalarsLargeMap f φ p := by
  let := f.toAlgebra
  intro A₁ L L' φ p
  rfl

/-- The whisker of the bifunctor at the base-changed map, as `LinearMap.rTensor`:
`DifferentialGraded.curriedTensor_map_app` after
`DifferentialGraded.extendScalarsLarge_map_f`. -/
theorem curriedTensor_extendScalarsLarge_map (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} {L L' : DifferentialGradedModule.{u, u, u} A₁}
      (φ : L ⟶ L') (p q : ℤ),
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).map
            (((CochainComplex.extendScalarsLarge.{u, u, u} f).map φ.toCochainMap).f p)).app
          ((degreeZeroComplex N).X q) =
        ModuleCat.ofHom (LinearMap.rTensor (N.grading q)
          (LinearMap.baseChange A (φ.gradedMap p))) := by
  let := f.toAlgebra
  intro N A₁ L L' φ p q
  rw [extendScalarsLarge_map_f f φ p]
  rfl

/-! ### The square on a bigraded summand -/

/-- **The comparison square on a bigraded summand**, in elements: both routes send `(a ⊗ x) ⊗ y`
to the pure tensor `φ x ⊗ a y`. -/
theorem absModSummandToGrading_naturality (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} {L L' : DifferentialGradedModule.{u, u, u} A₁}
      (φ : L ⟶ L') (p q n : ℤ) (h : p + q = n) (a : A) (x : L.grading p) (y : N.grading q),
      ((absModSummandToGrading L' N p q n h
            (LinearMap.baseChange A (φ.gradedMap p) (a ⊗ₜ[R] x) ⊗ₜ[A] y) :
          (absoluteTensorModule L' N).grading n) : L'.M ⊗[R] N.M) =
        ((absModLeftMap φ N).gradedMap n
            (absModSummandToGrading L N p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] y)) :
          L'.M ⊗[R] N.M) := by
  let := f.toAlgebra
  intro N A₁ L L' φ p q n h a x y
  rw [LinearMap.baseChange_tmul,
    absModSummandToGrading_tmul L' N p q n h a (φ.gradedMap p x) y]
  change _ = (absModLeftMap φ N).toFun
    ((absModSummandToGrading L N p q n h ((a ⊗ₜ[R] x) ⊗ₜ[A] y) :
      (absoluteTensorModule L N).grading n) : L.M ⊗[R] N.M)
  rw [absModSummandToGrading_tmul L N p q n h a x y, absModLeftMap_tmul]
  rfl

/-- **The comparison square on a bigraded summand**, as an identity of morphisms of `A`-modules:
the base change of `φ` tensored with `N^q` followed by the forward summand map is the forward
summand map followed by `φ ⊗ 1` on the homogeneous component. -/
theorem absExtSummand_naturality (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} {L L' : DifferentialGradedModule.{u, u, u} A₁}
      (φ : L ⟶ L') (p q n : ℤ) (h : p + q = n),
      ModuleCat.ofHom (LinearMap.rTensor (N.grading q)
            (LinearMap.baseChange A (φ.gradedMap p))) ≫ absExtSummand f N L' p q n h =
        absExtSummand f N L p q n h ≫ (degreeZeroComplexMap (absModLeftMap φ N)).f n := by
  let := f.toAlgebra
  intro N A₁ L L' φ p q n h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul w y =>
    induction w using TensorProduct.inductionOn with
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | tmul a x =>
      apply Subtype.ext
      exact absModSummandToGrading_naturality f N φ p q n h a x y

/-! ### The square of complexes -/

/-- **The forward comparison is natural in the left variable.** On the bigraded summand of
degrees `(p, q)` the square is `DifferentialGraded.absExtSummand_naturality`: the only leg the
bifunctor produces is `LinearMap.rTensor` of the base change of `φ` on `L^p`, the second
argument being an identity. -/
theorem absExtForward_naturality (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} {L L' : DifferentialGradedModule.{u, u, u} A₁}
      (φ : L ⟶ L') (n : ℤ),
      (HomologicalComplex.mapBifunctorMap
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).map φ.toCochainMap)
            (𝟙 (degreeZeroComplex N)) (MonoidalCategory.curriedTensor (ModuleCat.{u} A))
            (ComplexShape.up ℤ)).f n ≫ absExtForward f N L' n =
        absExtForward f N L n ≫ (degreeZeroComplexMap (absModLeftMap φ N)).f n := by
  let := f.toAlgebra
  intro N A₁ L L' φ n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc _ _ _ _ p q n hpq, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp, absExtForward_ι_comp,
    curriedTensor_extendScalarsLarge_map f N φ p q, ← Category.assoc,
    absExtForward_ι_comp]
  exact absExtSummand_naturality f N φ p q n hpq

/-! ### The isomorphism of functors -/

/-- **The change-of-rings tensor complex of Tag 06Y6 is the complex of homogeneous components of
`L ⊗_R N`, naturally in `L`.** This is `DifferentialGraded.absExtTensorRightIso` as an
isomorphism of functors of the left variable, which is the shape
`CategoryTheory.LocalizerMorphism.isLeftDerivedFunctor_iff_precomp` asks for. -/
def absExtTensorRightNatIso (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      (A₁ : DifferentialGradedAlgebra.{u, u} R),
      DifferentialGradedModule.forgetToCochainComplex.{u, u, u} A₁ ⋙
            CochainComplex.extendScalarsLarge.{u, u, u} f ⋙
            CochainComplex.tensorRightLarge.{u, u} (degreeZeroComplex N) ≅
        absoluteTensorLeftFunctor (A := A₁) N ⋙ degreeZeroComponentFunctor R A := by
  letI := f.toAlgebra
  intro N A₁
  refine NatIso.ofComponents (fun L => absExtTensorRightIso f N L) ?_
  intro L L' φ
  exact HomologicalComplex.hom_ext _ _ (fun n => absExtForward_naturality f N φ n)

end DifferentialGraded

end
