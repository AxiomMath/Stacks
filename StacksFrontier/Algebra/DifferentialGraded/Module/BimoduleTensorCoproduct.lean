module

public import StacksFrontier.Algebra.DGA.BimoduleTensorExact
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryCoproducts

/-! # Tensoring with a bimodule commutes with direct sums in the module variable

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `N` be a
differential graded `(A, B)`-bimodule. The ordinary tensor functor
`- ⊗_A N : Mod_{(A, d)} ⥤ Mod_{(B, d)}` of Tag 09LM carries the direct sum `⨁ᵢ Mᵢ` of a family
of right differential graded `A`-modules to the direct sum `⨁ᵢ (Mᵢ ⊗_A N)`.

## Main results

* `DifferentialGraded.Bimodule.isColimit_tensorCompFunctor_directSumCofan`: the images of the
  coprojections `Mᵢ ⟶ ⨁ⱼ Mⱼ` exhibit `(⨁ᵢ Mᵢ) ⊗_A N` as the direct sum of the `Mᵢ ⊗_A N`.
* `DifferentialGraded.Bimodule.preservesColimit_tensorCompFunctor`: the same statement in the
  form `CategoryTheory.Limits.PreservesColimit`.

## Implementation notes

*Everything is read off the universal property.* The value `M ⊗_A N` is specified by
`DifferentialGraded.Bimodule.TensorDGFunctorData`, so the only handles on it are the universal
balanced bilinear map `DifferentialGraded.Bimodule.tensorPure`, the extensionality principle
`DifferentialGraded.Bimodule.tensorObj_hom_ext`, and the formula
`DifferentialGraded.Bimodule.tensorCompFunctor_map_pure` for the functor on pure tensors. The
descent out of `(⨁ᵢ Mᵢ) ⊗_A N` is therefore produced by lifting the balanced bilinear map
`DifferentialGraded.Bimodule.directSumBalanced`, which is assembled from the given maps on the
summands by the universal property of the direct sum of `R`-modules.

*Why a separate induction principle.* Three of the five axioms of a balanced bilinear map are
conditions on a *homogeneous* element of the direct sum, and such an element is a finite sum of
coprojections of homogeneous elements of the summands;
`DifferentialGradedModule.directSumGrading_induction` records that, since the usual
`DirectSum.induction_on` loses the homogeneity.

*Where the honest type is used.* The carrier of `DifferentialGradedModule.directSumObj` is the
bare direct sum `⨁ᵢ (Mᵢ).M` only up to unfolding at default transparency, so the elementwise
facts are phrased at the bare direct sum and the structure fields are discharged by `exact`.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the tensor functor.
* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI), direct sums of
  differential graded modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
variable {ι : Type u} [DecidableEq ι] (N : ι → DifferentialGradedModule A)

/-- **A homogeneous element of a direct sum is a finite sum of coprojections of homogeneous
elements.** A property of the carrier of `⨁ᵢ Nᵢ` which holds at zero, at every coprojection of a
homogeneous element of degree `n`, and is stable under addition, holds at every element
homogeneous of degree `n`. -/
theorem directSumGrading_induction (n : ℤ) (motive : (⨁ i, (N i).M) → Prop)
    (zero : motive 0)
    (lof : ∀ (j : ι) (y : (N j).M), y ∈ (N j).grading n →
      motive (DirectSum.lof R ι (fun i => (N i).M) j y))
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (x : ⨁ i, (N i).M) (hx : x ∈ directSumGrading N n) : motive x := by
  classical
  have hexpand : x = ∑ j ∈ x.support, DirectSum.lof R ι (fun i => (N i).M) j (x j) := by
    refine DFinsupp.ext fun k => ?_
    simp only [DirectSum.sum_apply, DirectSum.lof_eq_of]
    rw [Finset.sum_eq_single k]
    · simp only [DirectSum.of_eq_same]
    · intro j _ hne
      exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm hne)
    · intro hk
      simp only [DirectSum.of_eq_same]
      exact DFinsupp.notMem_support_iff.mp hk
  rw [hexpand]
  exact Finset.sum_induction _ _ add zero (fun j _ => lof j (x j) (hx j))

/-- `DifferentialGradedModule.directSumGrading_induction`, with its binders at the carrier of
`DifferentialGradedModule.directSumObj` rather than at the bare direct sum. -/
theorem directSumObj_grading_induction (n : ℤ) (motive : (directSumObj N).M → Prop)
    (zero : motive 0)
    (lof : ∀ (j : ι) (y : (N j).M), y ∈ (N j).grading n →
      motive (DirectSum.lof R ι (fun i => (N i).M) j y))
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (x : (directSumObj N).M) (hx : x ∈ (directSumObj N).grading n) : motive x :=
  directSumGrading_induction N n motive zero lof add x hx

/-- A right multiple of the `j`-th coprojection of `y` is the `j`-th coprojection of the right
multiple of `y`, stated for `DirectSum.lof`. -/
theorem op_smul_lof (j : ι) (y : (N j).M) (a : A.A) :
    MulOpposite.op a • DirectSum.lof R ι (fun i => (N i).M) j y
      = DirectSum.lof R ι (fun i => (N i).M) j (MulOpposite.op a • y) := by
  rw [DirectSum.lof_eq_of (R := R), DirectSum.lof_eq_of (R := R)]
  exact op_smul_of N j y a

/-- The differential of `⨁ᵢ Nᵢ` on the `j`-th coprojection, stated at the bare direct sum. -/
theorem directSumObj_d_lof (j : ι) (y : (N j).M) :
    (directSumObj N).d (DirectSum.lof R ι (fun i => (N i).M) j y)
      = DirectSum.lof R ι (fun i => (N i).M) j ((N j).d y) := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  exact directSumD_of N j y

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}
section Decidable

variable (N : Bimodule A B) {ι : Type u} [DecidableEq ι]
  (M : ι → DifferentialGradedModule.{u, u, u} A)
  {T : DifferentialGradedModule.{u, u, u} B} (g : ∀ i, tensorObj N (M i) ⟶ T)

/-- The bilinear map underlying `DifferentialGraded.Bimodule.directSumBalanced`, at the bare
direct sum: on the `i`-th summand it is the universal pure tensor of `Mᵢ` followed by `gᵢ`. -/
def directSumBalancedLinear :
    (⨁ i, (M i).M) →ₗ[R] N.rightModule.M →ₗ[R] T.M :=
  DirectSum.toModule R ι (N.rightModule.M →ₗ[R] T.M)
    (fun i => (tensorPure N (M i)).toLinearMap.compr₂ (g i).toFun)

/-- The bilinear map of `DifferentialGraded.Bimodule.directSumBalancedLinear` on the `j`-th
coprojection. -/
theorem directSumBalancedLinear_lof (j : ι) (y : (M j).M) (z : N.rightModule.M) :
    directSumBalancedLinear N M g (DirectSum.lof R ι (fun i => (M i).M) j y) z =
      (g j).toFun ((tensorPure N (M j)).toLinearMap y z) :=
  congrArg (fun f : N.rightModule.M →ₗ[R] T.M => f z)
    (DirectSum.toModule_lof (R := R)
      (φ := fun i => (tensorPure N (M i)).toLinearMap.compr₂ (g i).toFun) j y)

/-- **The assembled bilinear map is balanced over `A`.** If moving a right scalar `a` across the
universal pure tensors of every summand replaces the second argument `y` by `w`, then the same
holds for the assembled map on every element of `⨁ᵢ Mᵢ` homogeneous of degree `p`. -/
theorem directSumBalancedLinear_smul_left (p : ℤ) {x : (directSumObj M).M}
    (hx : x ∈ (directSumObj M).grading p) (y : N.rightModule.M) (a : A.A)
    (w : N.rightModule.M)
    (hw : ∀ (j : ι) (z : (M j).M), z ∈ (M j).grading p →
      (tensorPure N (M j)).toLinearMap (MulOpposite.op a • z) y =
        (tensorPure N (M j)).toLinearMap z w) :
    directSumBalancedLinear N M g (MulOpposite.op a • x) y =
      directSumBalancedLinear N M g x w := by
  refine directSumObj_grading_induction M p
    (fun x => directSumBalancedLinear N M g (MulOpposite.op a • x) y =
      directSumBalancedLinear N M g x w) ?_ ?_ ?_ x hx
  · simp only [smul_zero, map_zero, LinearMap.zero_apply]
  · intro j z hz
    rw [op_smul_lof, directSumBalancedLinear_lof, directSumBalancedLinear_lof]
    exact congrArg (g j).toFun (hw j z hz)
  · intro x₁ x₂ h₁ h₂
    simp only [smul_add, map_add, LinearMap.add_apply, h₁, h₂]

/-- **The balanced bilinear map assembled from a family of maps out of the summands.** Given
homomorphisms `gᵢ : Mᵢ ⊗_A N ⟶ T`, the map `(x, y) ↦ gᵢ (xᵢ ⊗ y)` summed over the components of
`x` is a balanced bilinear map from `⨁ᵢ Mᵢ` and `N` to `T`. -/
def directSumBalanced : BalancedBilinearMap (directSumObj M) N T where
  toLinearMap := directSumBalancedLinear N M g
  map_grading p q x y := by
    refine directSumObj_grading_induction M p
      (fun x => directSumBalancedLinear N M g x y ∈ T.grading (p + q)) ?_ ?_ ?_ x x.property
    · simpa only [map_zero, LinearMap.zero_apply] using (T.grading (p + q)).zero_mem
    · intro j z hz
      rw [directSumBalancedLinear_lof]
      exact (g j).map_grading _ _ ((tensorPure N (M j)).map_grading p q ⟨z, hz⟩ y)
    · intro x₁ x₂ h₁ h₂
      simpa only [map_add, LinearMap.add_apply] using (T.grading (p + q)).add_mem h₁ h₂
  map_d p x y := by
    refine directSumObj_grading_induction M p
      (fun x => T.d (directSumBalancedLinear N M g x y) =
        directSumBalancedLinear N M g ((directSumObj M).d x) y +
          (p.negOnePow : ℤ) • directSumBalancedLinear N M g x (N.rightModule.d y)) ?_ ?_ ?_
      x x.property
    · simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]
    · intro j z hz
      have hg (w : (tensorObj N (M j)).M) : (g j).toFun ((tensorObj N (M j)).d w) =
          T.d ((g j).toFun w) := LinearMap.congr_fun (g j).map_d w
      rw [directSumBalancedLinear_lof, directSumObj_d_lof, directSumBalancedLinear_lof,
        directSumBalancedLinear_lof, ← hg, (tensorPure N (M j)).map_d p ⟨z, hz⟩ y, map_add,
        map_zsmul]
    · intro x₁ x₂ h₁ h₂
      simp only [map_add, LinearMap.add_apply, smul_add, h₁, h₂]
      abel
  balance p q n x y a :=
    directSumBalancedLinear_smul_left N M g p x.property y a _
      (fun j z hz => (tensorPure N (M j)).balance p q n ⟨z, hz⟩ y a)
  map_right x y b := by
    induction x using DirectSum.induction_on with
    | zero => simp only [smul_zero, map_zero, LinearMap.zero_apply]
    | of j z =>
      rw [← DirectSum.lof_eq_of (R := R), directSumBalancedLinear_lof,
        directSumBalancedLinear_lof, (tensorPure N (M j)).map_right, (g j).map_smul]
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add, LinearMap.add_apply, h₁, h₂, smul_add]

/-- The descent `(⨁ᵢ Mᵢ) ⊗_A N ⟶ T` of a family of homomorphisms `Mᵢ ⊗_A N ⟶ T`: the lift of
`DifferentialGraded.Bimodule.directSumBalanced` along the universal property of Tag 09LM. -/
def tensorDirectSumDesc : tensorObj N (directSumObj M) ⟶ T :=
  ((tensorDGFunctor N).universal (directSumObj M) T (directSumBalanced N M g)).choose

/-- The descent of `DifferentialGraded.Bimodule.tensorDirectSumDesc` on a pure tensor. -/
theorem tensorDirectSumDesc_pure (x : (directSumObj M).M) (y : N.rightModule.M) :
    (tensorDirectSumDesc N M g).toFun ((tensorPure N (directSumObj M)).toLinearMap x y) =
      directSumBalancedLinear N M g x y :=
  ((tensorDGFunctor N).universal (directSumObj M) T (directSumBalanced N M g)).choose_spec.1 x y

/-- **The ordinary tensor product commutes with direct sums in the module variable.** The images
under `- ⊗_A N` of the coprojections `Mᵢ ⟶ ⨁ⱼ Mⱼ` exhibit `(⨁ᵢ Mᵢ) ⊗_A N` as the direct sum of
the family `Mᵢ ⊗_A N`. -/
def isColimit_tensorCompFunctor_directSumCofan :
    IsColimit (Cofan.mk (f := fun i => tensorObj N (M i)) (tensorObj N (directSumObj M))
      (fun i => (tensorCompFunctor N).map (directSumInj M i))) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun s => tensorDirectSumDesc N M (fun i => s.inj i)) (fun s j => ?_) (fun s m hm => ?_)
  · refine tensorObj_hom_ext N (M j) _ _ fun x y => ?_
    change (tensorDirectSumDesc N M (fun i => s.inj i)).toFun
        (((tensorCompFunctor N).map (directSumInj M j)).toFun
          ((tensorPure N (M j)).toLinearMap x y)) =
      (s.inj j).toFun ((tensorPure N (M j)).toLinearMap x y)
    rw [tensorCompFunctor_map_pure]
    exact (tensorDirectSumDesc_pure N M (fun i => s.inj i) _ y).trans
      (directSumBalancedLinear_lof N M (fun i => s.inj i) j x y)
  · refine tensorObj_hom_ext N (directSumObj M) _ _ fun x y => ?_
    change m.toFun ((tensorPure N (directSumObj M)).toLinearMap x y) =
      (tensorDirectSumDesc N M (fun i => s.inj i)).toFun
        ((tensorPure N (directSumObj M)).toLinearMap x y)
    rw [tensorDirectSumDesc_pure N M (fun i => s.inj i)]
    induction x using DirectSum.induction_on with
    | zero =>
      have h0 : (tensorPure N (directSumObj M)).toLinearMap 0 y = 0 := by
        simp only [map_zero, LinearMap.zero_apply]
      rw [h0, map_zero, map_zero, LinearMap.zero_apply]
    | of j z =>
      have h := congrArg (fun f : tensorObj N (M j) ⟶ s.pt =>
        f.toFun ((tensorPure N (M j)).toLinearMap z y)) (hm j)
      change m.toFun (((tensorCompFunctor N).map (directSumInj M j)).toFun _) = _ at h
      rw [tensorCompFunctor_map_pure] at h
      rwa [← DirectSum.lof_eq_of (R := R), directSumBalancedLinear_lof]
    | add x₁ x₂ h₁ h₂ =>
      have hadd : (tensorPure N (directSumObj M)).toLinearMap (x₁ + x₂) y =
          (tensorPure N (directSumObj M)).toLinearMap x₁ y +
            (tensorPure N (directSumObj M)).toLinearMap x₂ y := by
        simp only [map_add, LinearMap.add_apply]
      rw [hadd, map_add, h₁, h₂, map_add, LinearMap.add_apply]

end Decidable

/-- **Tensoring with `N` preserves the direct sum of a family of right differential graded
`A`-modules**, in the form `CategoryTheory.Limits.PreservesColimit` at the chosen direct sum
`DifferentialGradedModule.directSumObj`. -/
theorem preservesColimit_tensorCompFunctor (N : Bimodule A B) {ι : Type u}
    (M : ι → DifferentialGradedModule.{u, u, u} A) :
    PreservesColimit (Discrete.functor M) (tensorCompFunctor N) := by
  classical
  exact preservesColimit_of_preserves_colimit_cocone (isColimit_directSumObj M)
    ((Cofan.isColimitMapCoconeEquiv (tensorCompFunctor N) M
      (Cofan.mk (directSumObj M) (directSumInj M))).symm
        (isColimit_tensorCompFunctor_directSumCofan N M))

end DifferentialGraded.Bimodule

end
