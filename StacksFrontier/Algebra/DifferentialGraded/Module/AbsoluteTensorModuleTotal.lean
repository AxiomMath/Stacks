module

public import StacksFrontier.Algebra.DifferentialGraded.Module.AbsoluteTensorModule

/-!
# The complex underlying a tensor product of two differential graded modules

Let `R` be a commutative ring, let `(A, d)` and `(B, d)` be differential graded `R`-algebras, let
`L` be a right differential graded `A`-module and let `N` be a right differential graded
`B`-module. The complex of `R`-modules underlying the right differential graded `B`-module
`DifferentialGradedModule.absoluteTensorModule L N` of `L ⊗_R N` is the total complex
`Tot(L ⊗_R N)` of the tensor product double complex of the complexes underlying `L` and `N`.

In each degree this is the decomposition of the degree-`n` part of `L ⊗_R N` into its bigraded
pieces `L^p ⊗_R N^q` with `p + q = n`, which is
`DifferentialGradedModule.absModComponentEquiv`, and the two differentials agree because both
carry the Koszul sign `(-1)^p` on the second summand.

This is the mirror of `DifferentialGraded.absTotalIso`, which does the same for
`DifferentialGradedModule.absoluteTensor`, the tensor product of a differential graded module
with a differential graded *algebra*. Here neither factor is an algebra, so the statement applies
to a tensor product of two arbitrary differential graded modules.

## Main definitions

* `DifferentialGraded.absModTensorComplex`: the total complex `Tot(L ⊗_R N)`.
* `DifferentialGraded.absModTotalForward` and `DifferentialGraded.absModTotalBackward`: the two
  degreewise comparison maps.

## Main results

* `DifferentialGraded.absModTotalIso`: **the total complex of `L ⊗_R N` is the complex underlying
  the differential graded module `L ⊗_R N`.**
* `DifferentialGraded.absModTotalForward_ι`: the comparison on a pure tensor of a bigraded
  summand.

## Implementation notes

*The lifted monoidal structure.* The total complex is formed against the large-universe monoidal
structure of `StacksFrontier/Algebra/Category/ModuleCat/Monoidal/LargeUniverse.lean`, as in
`StacksFrontier/Algebra/DifferentialGraded/Module/BaseChangeTensorKFlat.lean`: Mathlib's own
instance on `ModuleCat.{u} R` has higher priority and would otherwise be selected here, where the
module universe equals the ring's, and the two total complexes are then not the same term.

*Universes.* The differential graded algebras and their modules live in a single universe `u`,
following the encoding of Tag 09JJ used throughout this chapter.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W) for the signed
  differential on a tensor product, and
  [Tag 06Y0](https://stacks.math.columbia.edu/tag/06Y0) for the total complex of a tensor product
  double complex.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}
  (L : DifferentialGradedModule.{u, u, u} A) (N : DifferentialGradedModule.{u, u, u} B)

/-- `DifferentialGradedModule.absModDifferential_tmul` with the sign as a unit scalar, which is
the form the total complex's differential produces. -/
theorem absModDifferential_tmul' (p : ℤ) (b : L.grading p) (a : N.M) :
    absModDifferential L N ((b : L.M) ⊗ₜ[R] a) =
      (L.d b ⊗ₜ[R] a : L.M ⊗[R] N.M) + p.negOnePow • ((b : L.M) ⊗ₜ[R] N.d a) := by
  simpa only [Units.smul_def] using absModDifferential_tmul L N p b a

end DifferentialGradedModule

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

attribute [local instance] DifferentialGradedModule.absModRightModule
  DifferentialGradedModule.absModRightScalarTower
  DifferentialGradedModule.absModDecomposition

attribute [local instance 10000] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The total complex -/

/-- The total complex `Tot(L ⊗_R N)` of the tensor product double complex of the complexes
underlying `L` and `N`. -/
abbrev absModTensorComplex (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) : CochainComplex (ModuleCat.{u} R) ℤ :=
  HomologicalComplex.tensorObj L.toCochainComplex N.toCochainComplex

/-- The bigraded summand `L^p ⊗_R N^q`, mapped into the degree-`n` part of `L ⊗_R N`. -/
def absModTotalForwardSummand (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (p q : ℤ) {n : ℤ} (h : p + q = n) :
    ModuleCat.of R (L.grading p ⊗[R] N.grading q) ⟶
      (absoluteTensorModule L N).toCochainComplex.X n :=
  ModuleCat.ofHom <| LinearMap.codRestrict _
    (TensorProduct.map (L.grading p).subtype (N.grading q).subtype) (by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
      | tmul x y =>
        subst n
        exact absModTmul_mem L N p q x y x.property y.property)

/-- The inclusion of the bigraded summand `L^p ⊗_R N^q` into the total complex. -/
abbrev absModTensorInclusion (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ) (h : p + q = n) :
    ModuleCat.of R (L.grading p ⊗[R] N.grading q) ⟶ (absModTensorComplex L N).X n :=
  HomologicalComplex.ιTensorObj L.toCochainComplex N.toCochainComplex p q n h

/-- The degree-`n` component of the map from the total complex to the complex underlying
`L ⊗_R N`. -/
abbrev absModTotalForward (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    (absModTensorComplex L N).X n ⟶ (absoluteTensorModule L N).toCochainComplex.X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => absModTotalForwardSummand L N p q h)

/-- The inclusion of a bigraded summand into the total complex, followed by
`absModTotalForward`, is `absModTotalForwardSummand`. -/
private theorem ι_comp_absModTotalForward (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor L.toCochainComplex N.toCochainComplex
        (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) p q n h ≫
      absModTotalForward L N n = absModTotalForwardSummand L N p q h :=
  HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := L.toCochainComplex) (K₂ := N.toCochainComplex)
    (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)
    (fun p q h => absModTotalForwardSummand L N p q h) p q h

/-- The comparison map `absModTotalForward` sends the image of a pure tensor `x ⊗ y` of the
bigraded summand `L^p ⊗_R N^q` to the element `x ⊗ y` of the degree-`n` part of `L ⊗_R N`. -/
theorem absModTotalForward_ι (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ) (h : p + q = n)
    (x : L.grading p) (y : N.grading q) :
    (absModTotalForward L N n) (absModTensorInclusion L N p q n h (x ⊗ₜ[R] y)) =
      ⟨(x : L.M) ⊗ₜ[R] (y : N.M), by
        subst n; exact absModTmul_mem L N p q x y x.property y.property⟩ :=
  congrArg (fun f => f (x ⊗ₜ[R] y)) (ι_comp_absModTotalForward L N p q n h)

/-- The map from the bigraded pieces of total degree `n` into the total complex. -/
def absModTotalBackwardLinear (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    absModComponents L N n →ₗ[R] ((absModTensorComplex L N).X n) :=
  DirectSum.toModule R _ _ (fun pq =>
    (absModTensorInclusion L N pq.val.1 pq.val.2 n pq.property).hom)

/-- `absModTotalBackwardLinear` restricts on the summand indexed by `(p, q)` to the inclusion of
`L^p ⊗_R N^q` into the total complex. -/
theorem absModTotalBackwardLinear_lof (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n : ℤ)
    (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) (z : L.grading pq.val.1 ⊗[R] N.grading pq.val.2) :
    absModTotalBackwardLinear L N n (DirectSum.lof R _ _ pq z) =
      absModTensorInclusion L N pq.val.1 pq.val.2 n pq.property z := by
  simp only [absModTotalBackwardLinear, DirectSum.toModule_lof]

/-- The degree-`n` component of the map from the complex underlying `L ⊗_R N` to the total
complex: the bigraded decomposition of the degree-`n` part, followed by the inclusions. -/
def absModTotalBackward (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    (absoluteTensorModule L N).toCochainComplex.X n ⟶ (absModTensorComplex L N).X n :=
  ModuleCat.ofHom
    (absModTotalBackwardLinear L N n ∘ₗ (absModComponentEquiv L N n).symm.toLinearMap)

/-- The comparison map `absModTotalBackward` sends a pure tensor `x ⊗ y` with `x ∈ L^p` and
`y ∈ N^q` to the image of `x ⊗ y` under the inclusion of `L^p ⊗_R N^q` into the total complex. -/
theorem absModTotalBackward_pure (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (p q n : ℤ) (h : p + q = n)
    (x : L.grading p) (y : N.grading q) :
    (absModTotalBackward L N n)
        ⟨(x : L.M) ⊗ₜ[R] (y : N.M), by
          subst n; exact absModTmul_mem L N p q x y x.property y.property⟩ =
      absModTensorInclusion L N p q n h (x ⊗ₜ[R] y) := by
  have he : (absModComponentEquiv L N n).symm
        ⟨(x : L.M) ⊗ₜ[R] (y : N.M), by
          subst n; exact absModTmul_mem L N p q x y x.property y.property⟩ =
      DirectSum.lof R {pq : ℤ × ℤ // pq.1 + pq.2 = n}
        (fun pq => L.grading pq.val.1 ⊗[R] N.grading pq.val.2) ⟨(p, q), h⟩ (x ⊗ₜ[R] y) := by
    apply (absModComponentEquiv L N n).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact (absModFiberMap_lof_tmul L N n ⟨(p, q), h⟩ x y).symm
  show absModTotalBackwardLinear L N n ((absModComponentEquiv L N n).symm _) = _
  rw [he, absModTotalBackwardLinear_lof]

/-- The composite of `absModTotalBackwardLinear` with `absModTotalForward` is the bigraded
decomposition `absModComponentEquiv`. -/
theorem absModTotalForward_comp_backwardLinear (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    (absModTotalForward L N n).hom ∘ₗ absModTotalBackwardLinear L N n =
      (absModComponentEquiv L N n).toLinearMap := by
  refine DirectSum.linearMap_ext R fun pq => TensorProduct.ext' fun x y => ?_
  show (absModTotalForward L N n).hom (absModTotalBackwardLinear L N n
    (DirectSum.lof R _ _ pq (x ⊗ₜ[R] y))) = absModComponentEquiv L N n (DirectSum.lof R _ _ pq _)
  rw [absModTotalBackwardLinear_lof]
  apply Subtype.ext
  rw [absModComponentEquiv_coe, absModFiberMap_lof_tmul]
  exact congrArg Subtype.val (absModTotalForward_ι L N pq.val.1 pq.val.2 n pq.property x y)

/-- `absModTotalForward` is a left inverse of `absModTotalBackward` in each degree. -/
theorem absModTotalBackward_forward (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    absModTotalBackward L N n ≫ absModTotalForward L N n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  show (absModTotalForward L N n).hom ∘ₗ
      (absModTotalBackwardLinear L N n ∘ₗ (absModComponentEquiv L N n).symm.toLinearMap) =
    LinearMap.id
  rw [← LinearMap.comp_assoc, absModTotalForward_comp_backwardLinear]
  exact LinearMap.ext fun z => (absModComponentEquiv L N n).apply_symm_apply z

/-- `absModTotalBackward` is a left inverse of `absModTotalForward` in each degree. -/
theorem absModTotalForward_backward (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n : ℤ) :
    absModTotalForward L N n ≫ absModTotalBackward L N n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  change L.grading p at x
  change N.grading q at y
  show (absModTotalBackward L N n) ((absModTotalForward L N n)
    (absModTensorInclusion L N p q n h (x ⊗ₜ[R] y))) = _
  rw [absModTotalForward_ι, absModTotalBackward_pure]
  rfl

/-- The maps `absModTotalForward` commute with the differentials of the total complex and of the
complex underlying `L ⊗_R N`. -/
theorem absModTotalForward_comm (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) (n m : ℤ) (h : n + 1 = m) :
    absModTotalForward L N n ≫ (absoluteTensorModule L N).toCochainComplex.d n m =
      (absModTensorComplex L N).d n m ≫ absModTotalForward L N m := by
  subst m
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have h₁ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
  have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  have ha : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p + 1, q) = n + 1 := by
    change p + q = n at hpq
    show p + 1 + q = n + 1
    omega
  have hb : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q + 1) = n + 1 := by
    change p + q = n at hpq
    show p + (q + 1) = n + 1
    omega
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq (K₁ := L.toCochainComplex)
      (K₂ := N.toCochainComplex)
      (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)
      h₁ q (n + 1) ha,
    HomologicalComplex.mapBifunctor.d₂_eq (K₁ := L.toCochainComplex)
      (K₂ := N.toCochainComplex)
      (F := MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ)
      p h₂ (n + 1) hb]
  simp only [absModTotalForward, Linear.units_smul_comp, Category.assoc]
  rw [reassoc_of% ι_comp_absModTotalForward L N p q n hpq, ι_comp_absModTotalForward,
    ι_comp_absModTotalForward]
  simp only [ComplexShape.ε₁, ComplexShape.ε₂, ComplexShape.ε₁_def, one_smul]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  change L.grading p at x
  change N.grading q at y
  apply Subtype.ext
  dsimp [absModTotalForwardSummand]
  simp only [DifferentialGradedModule.toCochainComplex_d]
  dsimp
  exact absModDifferential_tmul' L N p x y

/-- **The total complex of `L ⊗_R N` is the complex underlying the differential graded module
`L ⊗_R N`.** In each degree this is the decomposition of the degree-`n` part of `L ⊗_R N` into
its bigraded pieces, and the two differentials agree because both carry the Koszul sign. -/
def absModTotalIso (L : DifferentialGradedModule.{u, u, u} A)
    (N : DifferentialGradedModule.{u, u, u} B) :
    absModTensorComplex L N ≅ (absoluteTensorModule L N).toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ⟨absModTotalForward L N n, absModTotalBackward L N n,
      absModTotalForward_backward L N n, absModTotalBackward_forward L N n⟩)
    (fun n m h => absModTotalForward_comm L N n m h)

end DifferentialGraded

end
