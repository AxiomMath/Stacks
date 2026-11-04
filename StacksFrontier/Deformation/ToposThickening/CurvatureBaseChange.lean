module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.KernelCotangentBaseChange
public import StacksFrontier.Deformation.ToposThickening.FreeLiftBaseChange
public import StacksFrontier.Homology.ExtendScalars.Monoidal

/-!
# Base change of the curvature of a lifted differential

Let `fR : R' → R` and `fS : S' → S` be surjections of commutative rings fitting into a
commuting square with `a : R' → S'` and `b : R → S`, write `I = ker fR` and `J = ker fS`, and
let `L` be a free differential lift of a complex `P` of `R`-modules along `fR`. Base change
along `a` turns `L` into a free differential lift of `S ⊗_R P` along `fS`, and the square of
its lifted differential is the base change of the square of the lifted differential of `L`.

The compatibility of the canonical obstruction map with the ring map `R' → S'` (Stacks 0DYR(3))
is verified at this cochain level: the squares of the two lifted differentials already agree as
maps of complexes.

## Main definitions

* `Deformation.Obstruction.extendScalarsTmul`: the element `s ⊗ m` of a base-changed module.
* `Deformation.Obstruction.squareZeroKernelBaseChangeMap`: the comparison `S ⊗_R I/I² → J/J²`
  as a map of `S`-modules.
* `Deformation.Obstruction.kernelComplexBaseChangeMap`: that comparison between the kernel
  modules placed in degree zero.
* `Deformation.Obstruction.kernelTensorBaseChangeMap`: the induced comparison
  `S ⊗_R (P ⊗_R I/I²) → (S ⊗_R P) ⊗_S J/J²` of total tensor complexes.

## Main results

* `Deformation.Obstruction.LiftedDifferentialCurvature.hom_baseChange`: the curvature chain map
  of the base-changed lift is the base change of the curvature chain map, read through the
  comparison of kernel tensor complexes.

## Implementation notes

The comparison of total tensor complexes is the monoidality of degreewise extension of scalars
followed by the kernel comparison; it is computed on the pure tensors that generate the
degree-`(n, 0)` summand, the only nonzero one.

Elements of a base change are written with `Deformation.Obstruction.extendScalarsTmul` rather
than with tensor notation: the `R`-module structure on `S` used by `ModuleCat.extendScalars`
comes from restriction of scalars, not from an algebra instance, and a rigid name keeps
rewriting from tripping over the two spellings.

The cartesian hypothesis `ker fS = (ker fR) · S'` is not needed: the comparison of kernel
modules exists for any commuting square, and the identity of curvature chain maps holds for
any such square.

## References

* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory TensorProduct
  CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
  CategoryTheory.Functor.Monoidal
open CochainComplex.ExtendScalars HomologicalComplex
open scoped ChangeOfRings

universe u

namespace Deformation.Obstruction

variable {R' R S' S : Type u} [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]

/-- Extension of scalars is additive, being a left adjoint. -/
lemma extendScalars_additive (b : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} b).Additive :=
  (ModuleCat.extendRestrictScalarsAdj b).left_adjoint_additive

attribute [local instance] extendScalars_additive

section Tmul

/-- The element `s ⊗ m` of the base change `S ⊗_R M` of an `R`-module along `b : R → S`. -/
noncomputable def extendScalarsTmul (b : R →+* S) {M : ModuleCat.{u} R} (s : S) (m : M) :
    (ModuleCat.extendScalars.{u, u, u} b).obj M :=
  s ⊗ₜ[R, b] m

/-- The element `s ⊗ m` is additive in `m`. -/
lemma extendScalarsTmul_add (b : R →+* S) {M : ModuleCat.{u} R} (s : S) (m m' : M) :
    extendScalarsTmul b s (m + m') = extendScalarsTmul b s m + extendScalarsTmul b s m' :=
  TensorProduct.tmul_add _ _ _

/-- The element `s ⊗ 0` is zero. -/
lemma extendScalarsTmul_zero (b : R →+* S) (M : ModuleCat.{u} R) (s : S) :
    extendScalarsTmul b s (0 : M) = 0 :=
  TensorProduct.tmul_zero _ _

/-- Scalar multiplication by `s` sends `t ⊗ m` to `(s * t) ⊗ m`. -/
lemma smul_extendScalarsTmul (b : R →+* S) {M : ModuleCat.{u} R} (s t : S) (m : M) :
    s • extendScalarsTmul b t m = extendScalarsTmul b (s * t) m :=
  rfl

/-- The element `s ⊗ m` is `s • (1 ⊗ m)`. -/
lemma extendScalarsTmul_eq_smul (b : R →+* S) {M : ModuleCat.{u} R} (s : S) (m : M) :
    extendScalarsTmul b s m = s • extendScalarsTmul b 1 m := by
  rw [smul_extendScalarsTmul, mul_one]

/-- The base change of a linear map `g` sends `s ⊗ m` to `s ⊗ g m`. -/
lemma extendScalars_map_extendScalarsTmul (b : R →+* S) {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (s : S) (m : M) :
    (ModuleCat.extendScalars.{u, u, u} b).map g (extendScalarsTmul b s m) =
      extendScalarsTmul b s (g m) :=
  rfl

end Tmul

section Comparison

/-- The comparison of the kernel modules of the two vertical maps of a commuting square, as a
map of `S`-modules `S ⊗_R I/I² → J/J²` out of the base change. -/
noncomputable def squareZeroKernelBaseChangeMap
    (fR : R' →+* R) (hfR : Function.Surjective fR)
    (fS : S' →+* S) (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a) :
    (ModuleCat.extendScalars.{u, u, u} b).obj (squareZeroKernelModule.{u, u} fR hfR) ⟶
      squareZeroKernelModule.{u, u} fS hfS := by
  letI : Algebra R S := b.toAlgebra
  letI := kernelCotangentModule fR hfR
  letI := kernelCotangentModule fS hfS
  exact (ModuleCat.ofHom (kernelCotangentBaseChange fR hfR fS hfS a hcomm) :
    ModuleCat.of S (S ⊗[R] (RingHom.ker fR).Cotangent) ⟶
      ModuleCat.of S (RingHom.ker fS).Cotangent)

/-- On the class of an element `α` of `I`, the kernel comparison is the class of `a α` in
`J`. -/
lemma squareZeroKernelBaseChangeMap_one_tmul
    (fR : R' →+* R) (hfR : Function.Surjective fR)
    (fS : S' →+* S) (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
    (α : RingHom.ker fR) :
    squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm
        (extendScalarsTmul b (1 : S)
          (show squareZeroKernelModule.{u, u} fR hfR from
            (RingHom.ker fR).toCotangent α)) =
      (show squareZeroKernelModule.{u, u} fS hfS from
        (RingHom.ker fS).toCotangent
          ⟨a (α : R'), map_ker_le_ker fR fS a b hcomm (Ideal.mem_map_of_mem _ α.2)⟩) := by
  let : Algebra R S := b.toAlgebra
  exact (kernelCotangentBaseChange_one_tmul fR hfR fS hfS a hcomm _).trans
    (kernelCotangentMap_toCotangent fR hfR fS hfS a _ hcomm α)

/-- The kernel comparison between the kernel modules placed in cohomological degree zero. -/
noncomputable def kernelComplexBaseChangeMap
    (fR : R' →+* R) (hfR : Function.Surjective fR)
    (fS : S' →+* S) (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a) :
    (mapCochainComplex b).obj (kernelComplex fR hfR) ⟶ kernelComplex fS hfS :=
  (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} b)
      (ComplexShape.up ℤ) 0).hom.app (squareZeroKernelModule.{u, u} fR hfR) ≫
    (CochainComplex.singleFunctor (ModuleCat.{u} S) 0).map
      (squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm)

private lemma kernelComplexBaseChangeMap_f_zero
    (fR : R' →+* R) (hfR : Function.Surjective fR)
    (fS : S' →+* S) (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a) :
    (ModuleCat.extendScalars.{u, u, u} b).map
        (singleObjXSelf (ComplexShape.up ℤ) 0 (squareZeroKernelModule.{u, u} fR hfR)).inv ≫
      (kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm).f 0 =
      squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (squareZeroKernelModule.{u, u} fS hfS)).inv := by
  rw [kernelComplexBaseChangeMap]
  show _ ≫ (_ ≫ _ : (mapCochainComplex b).obj (kernelComplex fR hfR) ⟶ _).f 0 = _
  rw [HomologicalComplex.comp_f, singleMapHomologicalComplex_hom_app_self]
  rw [show ((CochainComplex.singleFunctor (ModuleCat.{u} S) 0).map
      (squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm)).f 0 =
      ((HomologicalComplex.single (ModuleCat.{u} S) (ComplexShape.up ℤ) 0).map
        (squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm)).f 0 from rfl,
    HomologicalComplex.single_map_f_self]
  simp only [← Category.assoc]
  rw [← Functor.map_comp]
  simp

private lemma mu_one_tmul (b : R →+* S) (M N : ModuleCat.{u} R) (m : M) (n : N) :
    μ (ModuleCat.extendScalars.{u, u, u} b) M N
        (extendScalarsTmul b (1 : S) m ⊗ₜ[S] extendScalarsTmul b (1 : S) n) =
      extendScalarsTmul b (1 : S) (m ⊗ₜ[R] n) := by
  have h := ConcreteCategory.congr_hom (δ_μ (ModuleCat.extendScalars.{u, u, u} b) M N)
    (extendScalarsTmul b (1 : S) (m ⊗ₜ[R] n))
  rw [ModuleCat.comp_apply] at h
  exact h

private lemma monoidalIso_inv_one_tmul (b : R →+* S)
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (i j n : ℤ) (h : i + j = n)
    (p : P.X i) (q : L.X j) :
    (extendScalarsMonoidalIso b P L).inv.f n
        (extendScalarsTmul b (1 : S) (HomologicalComplex.ιTensorObj P L i j n h (p ⊗ₜ[R] q))) =
      HomologicalComplex.ιTensorObj ((mapCochainComplex b).obj P)
        ((mapCochainComplex b).obj L) i j n h
        (extendScalarsTmul b (1 : S) p ⊗ₜ[S] extendScalarsTmul b (1 : S) q) := by
  have key := ConcreteCategory.congr_hom
    (ι_extendScalarsMonoidalIso_hom b P L n i j h)
    (extendScalarsTmul b (1 : S) p ⊗ₜ[S] extendScalarsTmul b (1 : S) q)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, mu_one_tmul,
    extendScalars_map_extendScalarsTmul] at key
  rw [← key, ← ModuleCat.comp_apply,
    show (extendScalarsMonoidalIso b P L).hom.f n ≫ (extendScalarsMonoidalIso b P L).inv.f n =
      ((extendScalarsMonoidalIso b P L).hom ≫ (extendScalarsMonoidalIso b P L).inv).f n from rfl,
    (extendScalarsMonoidalIso b P L).hom_inv_id]
  rfl

/-- The comparison of total tensor complexes `S ⊗_R (P ⊗_R I/I²) → (S ⊗_R P) ⊗_S J/J²`: the
monoidality of degreewise extension of scalars followed by the kernel comparison. -/
noncomputable def kernelTensorBaseChangeMap
    (fR : R' →+* R) (hfR : Function.Surjective fR)
    (fS : S' →+* S) (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (mapCochainComplex b).obj (P ⊗ kernelComplex fR hfR) ⟶
      (mapCochainComplex b).obj P ⊗ kernelComplex fS hfS :=
  (extendScalarsMonoidalIso b P (kernelComplex fR hfR)).inv ≫
    (𝟙 ((mapCochainComplex b).obj P) ⊗ₘ kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm)

/-- The comparison of total tensor complexes on the pure tensors spanning the only nonzero
antidiagonal summand. -/
lemma kernelTensorBaseChangeMap_one_tmul
    (fR : R' →+* R) (hfR : Function.Surjective fR)
    (fS : S' →+* S) (hfS : Function.Surjective fS)
    (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (p : P.X m) (i : squareZeroKernelModule.{u, u} fR hfR) :
    (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P).f m
        (extendScalarsTmul b (1 : S) (kernelTensorInclusion fR hfR P m (p ⊗ₜ[R] i))) =
      kernelTensorInclusion fS hfS ((mapCochainComplex b).obj P) m
        (extendScalarsTmul b (1 : S) p ⊗ₜ[S]
          squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm
            (extendScalarsTmul b (1 : S) i)) := by
  have h1 : kernelTensorInclusion fR hfR P m (p ⊗ₜ[R] i) =
      HomologicalComplex.ιTensorObj P (kernelComplex fR hfR) m 0 m (by simp)
        (p ⊗ₜ[R] (singleObjXSelf (ComplexShape.up ℤ) 0
          (squareZeroKernelModule.{u, u} fR hfR)).inv i) := rfl
  have h2 : kernelTensorInclusion fS hfS ((mapCochainComplex b).obj P) m
      (extendScalarsTmul b (1 : S) p ⊗ₜ[S]
        squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm
          (extendScalarsTmul b (1 : S) i)) =
      HomologicalComplex.ιTensorObj ((mapCochainComplex b).obj P) (kernelComplex fS hfS)
        m 0 m (by simp)
        (extendScalarsTmul b (1 : S) p ⊗ₜ[S]
          (singleObjXSelf (ComplexShape.up ℤ) 0 (squareZeroKernelModule.{u, u} fS hfS)).inv
            (squareZeroKernelBaseChangeMap fR hfR fS hfS a b hcomm
              (extendScalarsTmul b (1 : S) i))) := rfl
  rw [h1, h2, kernelTensorBaseChangeMap, HomologicalComplex.comp_f,
    ModuleCat.comp_apply, monoidalIso_inv_one_tmul]
  have hmap := ConcreteCategory.congr_hom
    (HomologicalComplex.ι_mapBifunctorMap (f₁ := 𝟙 ((mapCochainComplex b).obj P))
      (f₂ := kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm)
      (F := curriedTensor (ModuleCat.{u} S)) (c := ComplexShape.up ℤ) m 0 m (by simp))
    (extendScalarsTmul b (1 : S) p ⊗ₜ[S]
      extendScalarsTmul b (1 : S) ((singleObjXSelf (ComplexShape.up ℤ) 0
        (squareZeroKernelModule.{u, u} fR hfR)).inv i))
  rw [ModuleCat.comp_apply] at hmap
  rw [show ((𝟙 ((mapCochainComplex b).obj P)) ⊗ₘ
      kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm) =
      HomologicalComplex.mapBifunctorMap (𝟙 ((mapCochainComplex b).obj P))
        (kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm)
        (curriedTensor (ModuleCat.{u} S)) (ComplexShape.up ℤ) from rfl, hmap]
  have hk := ConcreteCategory.congr_hom
    (kernelComplexBaseChangeMap_f_zero fR hfR fS hfS a b hcomm)
    (extendScalarsTmul b (1 : S) i)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    extendScalars_map_extendScalarsTmul] at hk
  show HomologicalComplex.ιTensorObj ((mapCochainComplex b).obj P) (kernelComplex fS hfS)
      m 0 m (by simp)
      (extendScalarsTmul b (1 : S) p ⊗ₜ[S]
        (kernelComplexBaseChangeMap fR hfR fS hfS a b hcomm).f 0
          (extendScalarsTmul b (1 : S)
            ((singleObjXSelf (ComplexShape.up ℤ) 0
              (squareZeroKernelModule.{u, u} fR hfR)).inv i))) = _
  rw [hk]

end Comparison

section BaseChange

variable (fR : R' →+* R) (hfR : Function.Surjective fR)
  (fS : S' →+* S) (hfS : Function.Surjective fS)
  (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)
  {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift fR P)

private lemma baseChange_reduction_one_tmul (n : ℤ) (x : L.X n) :
    letI : Algebra R' S' := a.toAlgebra
    (L.baseChange hfR hfS a b hcomm).reduction n
        ((1 : S') ⊗ₜ[R'] x : (L.baseChange hfR hfS a b hcomm).X n) =
      (extendScalarsTmul b (1 : S) (L.reduction n x) : ((mapCochainComplex b).obj P).X n) := by
  have := freeLiftBaseChangeReduction_tmul hfR fS a b hcomm L n 1 x
  rwa [map_one] at this

private lemma one_tmul_smul (n : ℤ) (α : RingHom.ker fR) (x : L.X n) :
    letI : Algebra R' S' := a.toAlgebra
    (a (α : R')) • ((1 : S') ⊗ₜ[R'] x : (L.baseChange hfR hfS a b hcomm).X n) =
      ((1 : S') ⊗ₜ[R'] ((α : R') • x) : (L.baseChange hfR hfS a b hcomm).X n) := by
  let : Algebra R' S' := a.toAlgebra
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1

/-- The kernel embedding of the base-changed curvature carries the comparison of kernel tensor
complexes to the base change of the kernel embedding. -/
private lemma kernelEmbedding_baseChange
    (c : LiftedDifferentialCurvature fR hfR P L)
    (cS : LiftedDifferentialCurvature fS hfS ((mapCochainComplex b).obj P)
      (L.baseChange hfR hfS a b hcomm))
    (m : ℤ) (z : (P ⊗ kernelComplex fR hfR).X m) :
    letI : Algebra R' S' := a.toAlgebra
    cS.kernelEmbedding m
        ((kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P).f m
          (extendScalarsTmul b (1 : S) z)) =
      ((1 : S') ⊗ₜ[R'] c.kernelEmbedding m z :
        (L.baseChange hfR hfS a b hcomm).X m) := by
  let : Algebra R' S' := a.toAlgebra
  refine kernelTensor_induction L m
    (fun z => cS.kernelEmbedding m
      ((kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P).f m
        (extendScalarsTmul b (1 : S) z)) =
      ((1 : S') ⊗ₜ[R'] c.kernelEmbedding m z :
        (L.baseChange hfR hfS a b hcomm).X m)) ?_ ?_ ?_ z
  · rw [extendScalarsTmul_zero, map_zero, map_zero, map_zero, TensorProduct.tmul_zero]
    rfl
  · intro z w hz hw
    rw [extendScalarsTmul_add, map_add, map_add, hz, hw, map_add, TensorProduct.tmul_add]
    rfl
  · intro x α
    rw [kernelTensorBaseChangeMap_one_tmul, squareZeroKernelBaseChangeMap_one_tmul,
      ← baseChange_reduction_one_tmul fR hfR fS hfS a b hcomm L m x,
      c.kernelEmbedding_tmul m x α]
    exact (cS.kernelEmbedding_tmul m ((1 : S') ⊗ₜ[R'] x)
        ⟨a (α : R'), map_ker_le_ker fR fS a b hcomm (Ideal.mem_map_of_mem _ α.2)⟩).trans
      (one_tmul_smul fR a L m α x)

/-- **Base change of the curvature of a lifted differential.** For a commuting square of ring
maps whose two vertical maps `fR : R' → R` and `fS : S' → S` are surjective, the square of the
differential of the base-changed lift of `P` is the base change of the square of the
differential of the lift of `P`, read through the comparison
`S ⊗_R (P ⊗_R I/I²) → (S ⊗_R P) ⊗_S J/J²`. -/
theorem LiftedDifferentialCurvature.hom_baseChange
    (c : LiftedDifferentialCurvature fR hfR P L)
    (cS : LiftedDifferentialCurvature fS hfS ((mapCochainComplex b).obj P)
      (L.baseChange hfR hfS a b hcomm)) :
    cS.hom = (mapCochainComplex b).map c.hom ≫
      ((ModuleCat.extendScalars.{u, u, u} b).mapCochainComplexShiftIso (2 : ℤ)).hom.app
        (P ⊗ kernelComplex fR hfR) ≫
      (shiftFunctor (CochainComplex (ModuleCat.{u} S) ℤ) (2 : ℤ)).map
        (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) := by
  let : Algebra R' S' := a.toAlgebra
  have key : ∀ (n : ℤ) (x : L.X n),
      cS.kernelEmbedding (n + 2)
          (cS.hom.f n (extendScalarsTmul b (1 : S) (L.reduction n x))) =
        cS.kernelEmbedding (n + 2)
          ((kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P).f (n + 2)
            ((ModuleCat.extendScalars.{u, u, u} b).map (c.hom.f n)
              (extendScalarsTmul b (1 : S) (L.reduction n x)))) := by
    intro n x
    have hl : cS.kernelEmbedding (n + 2)
          (cS.hom.f n (extendScalarsTmul b (1 : S) (L.reduction n x))) =
        (L.baseChange hfR hfS a b hcomm).d (n + 1) (n + 2)
          ((L.baseChange hfR hfS a b hcomm).d n (n + 1)
            ((1 : S') ⊗ₜ[R'] x : (L.baseChange hfR hfS a b hcomm).X n)) :=
      Eq.trans
        (congrArg (fun w : ((CochainComplex.extendScalars b).obj P).X n =>
          cS.kernelEmbedding (n + 2) (cS.hom.f n w))
          (baseChange_reduction_one_tmul fR hfR fS hfS a b hcomm L n x).symm)
        (cS.hom_eq_square n _)
    have hrhs : cS.kernelEmbedding (n + 2)
          ((kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P).f (n + 2)
            ((ModuleCat.extendScalars.{u, u, u} b).map (c.hom.f n)
              (extendScalarsTmul b (1 : S) (L.reduction n x)))) =
        ((1 : S') ⊗ₜ[R'] (L.d (n + 1) (n + 2) (L.d n (n + 1) x)) :
          (L.baseChange hfR hfS a b hcomm).X (n + 2)) := by
      rw [extendScalars_map_extendScalarsTmul,
        kernelEmbedding_baseChange fR hfR fS hfS a b hcomm L c cS (n + 2)
          (c.hom.f n (L.reduction n x))]
      exact congrArg
        (fun t : L.X (n + 2) =>
          ((1 : S') ⊗ₜ[R'] t : (L.baseChange hfR hfS a b hcomm).X (n + 2)))
        (c.hom_eq_square n x)
    rw [hl, hrhs]
    rfl
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ModuleCat.ExtendScalars.hom_ext fun p => ?_
  obtain ⟨x, rfl⟩ := L.reduction_surjective n p
  exact cS.kernelEmbedding_injective (n + 2) (key n x)

end BaseChange

end Deformation.Obstruction

end
