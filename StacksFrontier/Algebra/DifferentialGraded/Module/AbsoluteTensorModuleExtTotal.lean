module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModuleALinear
public import StacksFrontier.Homology.KFlat.LargeUniverse

/-!
# The tensor product of two differential graded modules as a change-of-rings tensor complex

Let `R` and `A` be commutative rings, let `f : R → A` be a ring homomorphism, let `N` be a right
differential graded module over `A` placed in degree zero and let `L` be a right differential
graded module over an arbitrary differential graded `R`-algebra. Then the complex of `A`-modules
of the homogeneous components of `DifferentialGradedModule.absoluteTensorModule L N` **is** the
change-of-rings tensor complex of Tag 06Y6 built from the complex underlying `L`:

`(extendScalarsLarge f ⋙ tensorRightLarge (degreeZeroComplex N)).obj L.toCochainComplex ≅`
`degreeZeroComplex (absoluteTensorModule L N)`.

Degreewise this is the bigraded decomposition of the degree-`n` part of `L ⊗_R N`
(`DifferentialGradedModule.absModComponentAEquiv`) conjugated by the base-change comparison
`(A ⊗_R L^p) ⊗_A N^q ≅ L^p ⊗_R N^q`
(`DifferentialGradedModule.absModSummandBaseChange`), both `A`-linear.

The two differentials agree because both carry the Koszul sign `(-1)^p`. The mathematical content
is `DifferentialGradedModule.absModSummandToGrading_differential_linear`, which says that on each
bigraded summand the differential of `L ⊗_R N` is the sum of the two legs that
`HomologicalComplex.mapBifunctor.d₁` and `d₂` produce, the second carrying that sign; those legs
are the `LinearMap.rTensor` and `LinearMap.lTensor` that the lifted monoidal structure on
`ModuleCat A` puts there, by `DifferentialGraded.curriedTensor_extendScalarsLarge_d` and
`DifferentialGraded.curriedTensor_degreeZeroComplex_d`.

This is the `A`-linear refinement of `DifferentialGraded.absModTotalIso`, which is the same
statement for the complexes of `R`-modules, and it is the identification that the derived
change-of-rings API of Tag 06Y6 consumes: a functor carrying a left-derived counit into
`extendScalarsLarge f ⋙ tensorRightLarge L` is what
`CochainComplex.DerivedTensor.exists_derivedTensorNatTrans_isIso_of_quasiIso` accepts.

## Main definitions

* `DifferentialGraded.absExtForward` and `DifferentialGraded.absExtBackward`: the two degreewise
  comparison maps.
* `DifferentialGraded.absExtTotalIso`: **the isomorphism of complexes of `A`-modules**, and
  `DifferentialGraded.absExtTensorRightIso`, the same isomorphism with its source spelled as the
  image of `CochainComplex.extendScalarsLarge f ⋙ CochainComplex.tensorRightLarge _`.

## Main results

* `DifferentialGraded.absExtForward_ι` and `DifferentialGraded.absExtBackward_summand`: the two
  maps on a bigraded summand.
* `DifferentialGraded.absExtForward_backward` and
  `DifferentialGraded.absExtBackward_forward`: the two comparison maps are mutually inverse in
  every degree.
* `DifferentialGraded.absExtSummand_d` and `DifferentialGraded.absExtForward_comm`: **the forward
  comparison is a chain map**, summandwise and in total.

## Implementation notes

*Why the statements carry a `letI`.* `ModuleCat.extendScalars` is defined for a bare ring
homomorphism and builds the algebra structure `f.toAlgebra` locally, which is *not*
definitionally the ambient `Algebra R A` instance even when `f` is the structure map — the
degreewise identification
`((extendScalarsLarge f).obj L.toCochainComplex).X p = ModuleCat.of A (A ⊗_R L^p)` holds by `rfl`
only at `f.toAlgebra`. Every statement below therefore opens with `letI := f.toAlgebra` and
quantifies `N` inside it, since the type of `N` mentions
`DifferentialGradedAlgebra.degreeZero R A`. Nothing is lost: the whole `A`-linear layer in
`StacksFrontier/Algebra/DifferentialGraded/Module/AbsoluteTensorModuleALinear.lean` is generic in
the `Algebra R A` instance, so it applies at `f.toAlgebra` with no transport, and
`DifferentialGradedModule.degreeZero_algebraMap_toAlgebra` connects the result back to the ambient
instance when a consumer needs that.

*The lifted monoidal structure.* The total complex is formed against the large-universe monoidal
structure on `ModuleCat A`, which is what `CochainComplex.tensorRightLarge` uses; Mathlib's own
instance would otherwise be selected here, where the module universe equals the ring's.

*Why the internals are spelled at `HomologicalComplex.tensorObj`.* The source complex has two
spellings, `(extendScalarsLarge f ⋙ tensorRightLarge _).obj _` and
`HomologicalComplex.tensorObj _ _`, which are the same term; but only the second is type-correct
at the transparency at which `HomologicalComplex.mapBifunctor.hom_ext` rewrites, so every
statement below uses it.

*How the differential square is assembled, and why in this order.* Three things have to be
arranged before the summandwise square can be applied to the bigraded goal.

First, the summand comparison is named once, as `DifferentialGraded.absExtSummand`, rather than
written inline inside `HomologicalComplex.mapBifunctorDesc`: inline, the summand carries the
`Module A` structure `ModuleCat` supplies while
`DifferentialGradedModule.absModSummandToGrading` carries the one
`DifferentialGradedModule.absModGradingModule` does, and although the two are definitionally
equal the elaborator does not identify them inside the composite.

Second, every object in the square is spelled at a complex's own terms --- `(degreeZeroComplex
_).X n`, `(degreeZeroComplex _).d n (n + 1)` by way of
`DifferentialGradedModule.degreeZeroComplexDiff`, and
`DifferentialGraded.extendScalarsLargeDiff` --- and never at `ModuleCat.of A (_.grading n)`.
`degreeZeroComplex` is built by `CochainComplex.of`, so `(degreeZeroComplex X).X n` does not
*reduce* to `ModuleCat.of A (X.grading n)`; the two are interchangeable only up to unfolding, and
a statement carrying the second spelling cannot be rewritten into a goal carrying the first. The
differentials are the sharp case: `DifferentialGraded.extendScalarsLarge_d` has its right-hand
side at the `ModuleCat.of` spelling, so rewriting with it underneath
`CategoryTheory.Functor.map` --- which is where the bifunctor's whiskers put it --- leaves an
application that is not type-correct at the transparency at which it is rechecked. Hence
`DifferentialGraded.extendScalarsLarge_d_self`, whose right-hand side is at the complex's own
terms.

Third, the square is stated with `LinearMap.rTensor` and `LinearMap.lTensor` of the plain
differentials, and the bifunctor's whiskers are converted to those separately
(`DifferentialGraded.curriedTensor_extendScalarsLarge_d`,
`DifferentialGraded.curriedTensor_degreeZeroComplex_d`, both `rfl` after one rewrite). Stated
against the whiskers as the bifunctor produces them, `ModuleCat.hom_ext` followed by
`DifferentialGradedModule.absModSummandToGrading_differential_linear` exhausts the heartbeat
budget in `isDefEq`.

One further detail of the rewrite order inside `DifferentialGraded.absExtForward_comm`:
`CategoryTheory.Linear.units_smul_comp` must precede `CategoryTheory.Category.assoc`, because
`HomologicalComplex.mapBifunctor.d₁_eq` and `d₂_eq` produce legs of the shape
`(ε • (whisker ≫ ι)) ≫ forward`, where the sign binds the composite; `Category.assoc` alone makes
no progress on them. The simp set that the `R`-linear analogue
`DifferentialGraded.absModTotalForward_comm` uses does not work here either --- the
`ιMapBifunctor ≫ mapBifunctorDesc` composites survive it --- which is why
`DifferentialGraded.absExtForward_ι_comp` is stated and used explicitly.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6) is the derived
  change-of-rings tensor product, and [Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0) the
  total complex of a tensor product double complex.
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

/-! ### The forward comparison -/

/-- The forward comparison on a single bigraded summand, named at the spelling the monoidal
structure on `ModuleCat A` produces. Pinning it here fixes the `A`-module structure of the
summand once and for all: stated inline inside
`HomologicalComplex.mapBifunctorDesc`, the summand carries the module structure `ModuleCat`
supplies while `DifferentialGradedModule.absModSummandToGrading` carries the one
`DifferentialGradedModule.absModGradingModule` does, and although the two are definitionally
equal the elaborator will not identify them inside the composite. -/
def absExtSummand (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p q n : ℤ) (_ : p + q = n),
      MonoidalCategoryStruct.tensorObj
          (((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).X p)
          ((degreeZeroComplex N).X q) ⟶
        (degreeZeroComplex (absoluteTensorModule L N)).X n := by
  letI := f.toAlgebra
  intro N A₁ L p q n h
  exact ModuleCat.ofHom (absModSummandToGrading L N p q n h)

/-! ### Bridges to the clean spellings

Each of these replaces a term the bifunctor or the complexes produce by the corresponding plain
linear map, and each holds by `rfl` or by unfolding one definition. They are what keeps the
differential square below cheap: stated against the `MonoidalCategory.curriedTensor` whiskers
directly, the square's defeq check exhausts the heartbeat budget.

`DifferentialGraded.curriedTensor_map_app` and `DifferentialGraded.curriedTensor_obj_map` record
the two defeqs — the bifunctor's actions *are* `LinearMap.rTensor` and `LinearMap.lTensor` — that
make `DifferentialGraded.curriedTensor_extendScalarsLarge_d` and
`DifferentialGraded.curriedTensor_degreeZeroComplex_d` close by `rfl`; those last two are the
ones the square uses, since they also carry the differential into its clean spelling. -/

/-- The bifunctor's action in the first variable is `LinearMap.rTensor`. -/
theorem curriedTensor_map_app {X Y : ModuleCat.{u} A} (g : X ⟶ Y) (Z : ModuleCat.{u} A) :
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).map g).app Z =
      ModuleCat.ofHom (g.hom.rTensor Z) := rfl

/-- The bifunctor's action in the second variable is `LinearMap.lTensor`. -/
theorem curriedTensor_obj_map (X : ModuleCat.{u} A) {Y Z : ModuleCat.{u} A} (g : Y ⟶ Z) :
    ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).obj X).map g =
      ModuleCat.ofHom (g.hom.lTensor X) := rfl

/-- The differential of the complex of homogeneous components. -/
theorem degreeZeroComplex_d [Algebra R A]
    (X : DifferentialGradedModule.{u, u, u} (degreeZero R A)) (n : ℤ) :
    (degreeZeroComplex X).d n (n + 1) = ModuleCat.ofHom (degreeZeroDifferential (A := A) X n) := by
  simp [degreeZeroComplex]

/-- The differential of the extended complex is the base change of the differential. -/
theorem extendScalarsLarge_d (f : R →+* A) :
    letI := f.toAlgebra
    ∀ {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p : ℤ),
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).d p (p + 1) =
        ModuleCat.ofHom (LinearMap.baseChange A (L.gradedDifferential p)) := by
  let := f.toAlgebra
  intro A₁ L p
  simp only [CochainComplex.extendScalarsLarge, Functor.mapHomologicalComplex_obj_d,
    DifferentialGradedModule.toCochainComplex_d]
  rfl

/-- The base-changed differential of `L`, as a morphism between the terms of the extended
complex. This spelling, not the `ModuleCat.of` one of
`DifferentialGraded.extendScalarsLarge_d`, is what can be rewritten *inside* the bifunctor's
action: `CategoryTheory.Functor.map` is applied to it, so replacing it by a morphism whose type
is spelled `ModuleCat.of A (A ⊗[R] L.grading p) ⟶ _` makes the application ill-typed at the
transparency at which it is rechecked. -/
def extendScalarsLargeDiff (f : R →+* A) :
    letI := f.toAlgebra
    ∀ {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p : ℤ),
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).X p ⟶
        ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).X (p + 1) := by
  letI := f.toAlgebra
  intro A₁ L p
  exact (ModuleCat.ofHom (LinearMap.baseChange A (L.gradedDifferential p)) :
    ModuleCat.of A (A ⊗[R] L.grading p) ⟶ ModuleCat.of A (A ⊗[R] L.grading (p + 1)))

/-- The differential of the extended complex is `DifferentialGraded.extendScalarsLargeDiff`. -/
theorem extendScalarsLarge_d_self (f : R →+* A) :
    letI := f.toAlgebra
    ∀ {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p : ℤ),
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).d p (p + 1) =
        extendScalarsLargeDiff f L p := by
  let := f.toAlgebra
  intro A₁ L p
  exact extendScalarsLarge_d f L p

/-- The `d₁` whisker of the bifunctor, as `LinearMap.rTensor` of the base-changed differential
of `L`: `DifferentialGraded.curriedTensor_map_app` after
`DifferentialGraded.extendScalarsLarge_d_self`. -/
theorem curriedTensor_extendScalarsLarge_d (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p q : ℤ),
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).map
            (((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).d
              p (p + 1))).app ((degreeZeroComplex N).X q) =
        ModuleCat.ofHom (LinearMap.rTensor (N.grading q)
          (LinearMap.baseChange A (L.gradedDifferential p))) := by
  let := f.toAlgebra
  intro N A₁ L p q
  rw [extendScalarsLarge_d_self f L p]
  rfl

/-- The `d₂` whisker of the bifunctor, as `LinearMap.lTensor` of the differential of `N`:
`DifferentialGraded.curriedTensor_obj_map` after
`DifferentialGradedModule.degreeZeroComplex_d_self`. -/
theorem curriedTensor_degreeZeroComplex_d (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p q : ℤ),
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).obj
            (((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex).X p)).map
          ((degreeZeroComplex N).d q (q + 1)) =
        ModuleCat.ofHom (LinearMap.lTensor (A ⊗[R] L.grading p)
          (degreeZeroDifferential (A := A) N q)) := by
  let := f.toAlgebra
  intro N A₁ L p q
  rw [degreeZeroComplex_d_self]
  rfl

/-- **The differential square on a bigraded summand.** Stated with `LinearMap.rTensor` and
`LinearMap.lTensor` of the plain differentials rather than with the bifunctor's whiskers, which
is what makes it provable: it is then exactly
`DifferentialGradedModule.absModSummandToGrading_differential_linear` read through
`ModuleCat.ofHom`. The outer differential is
`DifferentialGradedModule.degreeZeroComplexDiff`, not
`ModuleCat.ofHom (degreeZeroDifferential _ n)`: the two are definitionally equal, but only the
first has the source and target spelled as the terms of `degreeZeroComplex`, which is what the
square in `DifferentialGraded.absExtForward_comm` presents. -/
theorem absExtSummand_d (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p q n : ℤ) (h : p + q = n),
      absExtSummand f N L p q n h ≫ degreeZeroComplexDiff (absoluteTensorModule L N) n =
        ModuleCat.ofHom (LinearMap.rTensor (N.grading q)
              (LinearMap.baseChange A (L.gradedDifferential p))) ≫
            absExtSummand f N L (p + 1) q (n + 1) (by omega) +
          (p.negOnePow : ℤ) • (ModuleCat.ofHom (LinearMap.lTensor (A ⊗[R] L.grading p)
              (degreeZeroDifferential (A := A) N q)) ≫
            absExtSummand f N L p (q + 1) (n + 1) (by omega)) := by
  let := f.toAlgebra
  intro N A₁ L p q n h
  exact ModuleCat.hom_ext (absModSummandToGrading_differential_linear L N p q n h)

/-- The degree-`n` component of the map from the change-of-rings tensor complex to the complex of
homogeneous components of `L ⊗_R N`: on each bigraded summand it is
`DifferentialGraded.absExtSummand`. -/
def absExtForward (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n : ℤ),
      (HomologicalComplex.tensorObj
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
          (degreeZeroComplex N)).X n ⟶
        (degreeZeroComplex (absoluteTensorModule L N)).X n := by
  letI := f.toAlgebra
  intro N A₁ L n
  exact HomologicalComplex.mapBifunctorDesc (fun p q h => absExtSummand f N L p q n h)

/-- On the image of a bigraded summand, `DifferentialGraded.absExtForward` is
`DifferentialGradedModule.absModSummandToGrading`. -/
theorem absExtForward_ι (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p q n : ℤ) (h : p + q = n)
      (w : (A ⊗[R] L.grading p) ⊗[A] N.grading q),
      absExtForward f N L n
          (HomologicalComplex.ιTensorObj
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
            (degreeZeroComplex N) p q n h w) =
        absModSummandToGrading L N p q n h w := by
  let := f.toAlgebra
  intro N A₁ L p q n h w
  have h' := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := (CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
    (K₂ := degreeZeroComplex N)
    (F := MonoidalCategory.curriedTensor (ModuleCat.{u} A)) (c := ComplexShape.up ℤ)
    (fun p q h => absExtSummand f N L p q n h) p q h
  exact congrArg (fun g => g w) h'

/-! ### The backward comparison -/

/-- The map from the bigraded pieces of total degree `n` into the change-of-rings tensor complex:
on each summand it is the inverse of the base-change comparison followed by the inclusion. -/
def absExtBackwardLinear (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n : ℤ),
      absModComponents L N n →ₗ[A]
        (HomologicalComplex.tensorObj
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
          (degreeZeroComplex N)).X n := by
  letI := f.toAlgebra
  intro N A₁ L n
  exact DirectSum.toModule A _ _ (fun pq =>
    (HomologicalComplex.ιTensorObj
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
      (degreeZeroComplex N) pq.val.1 pq.val.2 n pq.property).hom ∘ₗ
      (absModSummandBaseChange L N pq.val.1 pq.val.2).symm.toLinearMap)

/-- On a bigraded summand, `DifferentialGraded.absExtBackwardLinear` is the inverse of the
base-change comparison followed by the inclusion of that summand. -/
theorem absExtBackwardLinear_lof (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
      (z : L.grading pq.val.1 ⊗[R] N.grading pq.val.2),
      absExtBackwardLinear f N L n (absModSummandLof L N n pq z) =
        HomologicalComplex.ιTensorObj
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
          (degreeZeroComplex N) pq.val.1 pq.val.2 n pq.property
          ((absModSummandBaseChange L N pq.val.1 pq.val.2).symm z) := by
  let := f.toAlgebra
  intro N A₁ L n pq z
  change DirectSum.toModule A _ _ _ (absModSummandLof L N n pq z) = _
  rw [absModSummandLof, DirectSum.toModule_lof]
  rfl

/-- The degree-`n` component of the map from the complex of homogeneous components of `L ⊗_R N`
back to the change-of-rings tensor complex. -/
def absExtBackward (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n : ℤ),
      (degreeZeroComplex (absoluteTensorModule L N)).X n ⟶
        (HomologicalComplex.tensorObj
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
          (degreeZeroComplex N)).X n := by
  letI := f.toAlgebra
  intro N A₁ L n
  exact ModuleCat.ofHom
    (absExtBackwardLinear f N L n ∘ₗ (absModComponentAEquiv L N n).symm.toLinearMap)

/-- The backward map undoes the forward summand map. -/
theorem absExtBackward_summand (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p q n : ℤ) (h : p + q = n) (w : (A ⊗[R] L.grading p) ⊗[A] N.grading q),
      absExtBackward f N L n (absModSummandToGrading L N p q n h w) =
        HomologicalComplex.ιTensorObj
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
          (degreeZeroComplex N) p q n h w := by
  let := f.toAlgebra
  intro N A₁ L p q n h w
  have hsymm : (absModComponentAEquiv L N n).symm
      (absModSummandToGrading L N p q n h w) =
      absModSummandLof L N n ⟨(p, q), h⟩ (absModSummandBaseChange L N p q w) := by
    apply (absModComponentAEquiv L N n).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  change absExtBackwardLinear f N L n ((absModComponentAEquiv L N n).symm _) = _
  rw [hsymm, absExtBackwardLinear_lof, LinearEquiv.symm_apply_apply]

/-! ### The two round trips -/

/-- The forward comparison composed with `DifferentialGraded.absExtBackwardLinear` is the
bigraded decomposition `DifferentialGradedModule.absModComponentAEquiv`. -/
theorem absExtForward_comp_backwardLinear (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n : ℤ),
      (absExtForward f N L n).hom ∘ₗ absExtBackwardLinear f N L n =
        (absModComponentAEquiv L N n).toLinearMap := by
  let := f.toAlgebra
  intro N A₁ L n
  refine DirectSum.linearMap_ext A fun pq => LinearMap.ext fun z => ?_
  change (absExtForward f N L n).hom (absExtBackwardLinear f N L n
    (absModSummandLof L N n pq z)) = absModComponentAEquiv L N n (absModSummandLof L N n pq z)
  rw [absExtBackwardLinear_lof f N L n pq z]
  refine (absExtForward_ι f N L pq.val.1 pq.val.2 n pq.property
    ((absModSummandBaseChange L N pq.val.1 pq.val.2).symm z)).trans ?_
  rw [absModSummandToGrading]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

/-- The backward comparison followed by the forward comparison is the identity. -/
theorem absExtBackward_forward (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n : ℤ), absExtBackward f N L n ≫ absExtForward f N L n = 𝟙 _ := by
  let := f.toAlgebra
  intro N A₁ L n
  apply ModuleCat.hom_ext
  change (absExtForward f N L n).hom ∘ₗ
      (absExtBackwardLinear f N L n ∘ₗ (absModComponentAEquiv L N n).symm.toLinearMap) =
    LinearMap.id
  rw [← LinearMap.comp_assoc, absExtForward_comp_backwardLinear]
  exact LinearMap.ext fun z => (absModComponentAEquiv L N n).apply_symm_apply z

/-- The forward comparison followed by the backward comparison is the identity. -/
theorem absExtForward_backward (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n : ℤ), absExtForward f N L n ≫ absExtBackward f N L n = 𝟙 _ := by
  let := f.toAlgebra
  intro N A₁ L n
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q h =>
    ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
  change absExtBackward f N L n (absExtForward f N L n
    (HomologicalComplex.ιTensorObj
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
      (degreeZeroComplex N) p q n h w)) = _
  rw [absExtForward_ι f N L p q n h w]
  exact absExtBackward_summand f N L p q n h w

/-! ### The differential square -/

/-- The forward comparison on a summand, as an identity of morphisms: this is
`HomologicalComplex.ι_mapBifunctorDesc` instantiated explicitly. It is stated because the simp
set that the `R`-linear analogue `DifferentialGraded.absModTotalForward_comm` uses does not fire
here — `DifferentialGraded.absExtForward` does unfold, but the
`ιMapBifunctor ≫ mapBifunctorDesc` composites survive it. -/
theorem absExtForward_ι_comp (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (p q n : ℤ) (h : p + q = n),
      HomologicalComplex.ιTensorObj
            ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
            (degreeZeroComplex N) p q n h ≫ absExtForward f N L n =
        absExtSummand f N L p q n h := by
  let := f.toAlgebra
  intro N A₁ L p q n h
  exact ModuleCat.hom_ext (LinearMap.ext fun w => absExtForward_ι f N L p q n h w)

/-- **The forward comparison is a chain map.** On the bigraded summand of degrees `(p, q)` the
square is `DifferentialGraded.absExtSummand_d`: the two legs that
`HomologicalComplex.mapBifunctor.d₁` and `d₂` produce are `LinearMap.rTensor` of the base-changed
differential of `L` and `LinearMap.lTensor` of the differential of `N`, and the signs the total
complex puts on them are `ComplexShape.ε₁ = 1` and `ComplexShape.ε₂ = (-1)^p`. -/
theorem absExtForward_comm (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁)
      (n m : ℤ) (_ : n + 1 = m),
      absExtForward f N L n ≫ (degreeZeroComplex (absoluteTensorModule L N)).d n m =
        (HomologicalComplex.tensorObj
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
          (degreeZeroComplex N)).d n m ≫ absExtForward f N L m := by
  let := f.toAlgebra
  intro N A₁ L n m hnm
  subst m
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have h₁ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
  have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  have ha : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p + 1, q) = n + 1 := by
    change p + 1 + q = n + 1
    omega
  have hb : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q + 1) = n + 1 := by
    change p + (q + 1) = n + 1
    omega
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ h₁ q (n + 1) ha,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p h₂ (n + 1) hb]
  simp only [Linear.units_smul_comp, Category.assoc]
  rw [absExtForward_ι_comp, absExtForward_ι_comp]
  conv_lhs => rw [← Category.assoc, absExtForward_ι_comp]
  rw [degreeZeroComplex_d_self, curriedTensor_extendScalarsLarge_d f N L p q,
    curriedTensor_degreeZeroComplex_d f N L p q]
  rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 1 from rfl,
    show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) =
      Int.negOnePow p from rfl, one_smul, Units.smul_def]
  exact absExtSummand_d f N L p q n hpq

/-- **The change-of-rings tensor complex of Tag 06Y6 built from `L` is the complex of homogeneous
components of `L ⊗_R N`.** In each degree this is the bigraded decomposition of the degree-`n`
part of `L ⊗_R N` conjugated by the base-change comparison
`(A ⊗_R L^p) ⊗_A N^q ≅ L^p ⊗_R N^q`, both `A`-linear; the two differentials agree because both
carry the Koszul sign `(-1)^p`.

This is the `A`-linear refinement of `DifferentialGraded.absModTotalIso`. -/
def absExtTotalIso (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁),
      HomologicalComplex.tensorObj
          ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj L.toCochainComplex)
          (degreeZeroComplex N) ≅
        degreeZeroComplex (absoluteTensorModule L N) := by
  letI := f.toAlgebra
  intro N A₁ L
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n => ⟨absExtForward f N L n, absExtBackward f N L n,
      absExtForward_backward f N L n, absExtBackward_forward f N L n⟩)
    (fun n m h => absExtForward_comm f N L n m h)

/-- `DifferentialGraded.absExtTotalIso` at the spelling the derived change-of-rings API of Tag
06Y6 consumes: the source is the image of `L.toCochainComplex` under
`CochainComplex.extendScalarsLarge f ⋙ CochainComplex.tensorRightLarge (degreeZeroComplex N)`,
which is the same term as the `HomologicalComplex.tensorObj` the proofs above use. -/
def absExtTensorRightIso (f : R →+* A) :
    letI := f.toAlgebra
    ∀ (N : DifferentialGradedModule.{u, u, u} (degreeZero R A))
      {A₁ : DifferentialGradedAlgebra.{u, u} R} (L : DifferentialGradedModule.{u, u, u} A₁),
      (CochainComplex.extendScalarsLarge.{u, u, u} f ⋙
            CochainComplex.tensorRightLarge.{u, u} (degreeZeroComplex N)).obj
          L.toCochainComplex ≅
        degreeZeroComplex (absoluteTensorModule L N) := by
  letI := f.toAlgebra
  intro N A₁ L
  exact absExtTotalIso f N L

end DifferentialGraded

end
