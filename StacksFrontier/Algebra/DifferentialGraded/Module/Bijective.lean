module

public import StacksFrontier.Algebra.DGA.Abelian

/-! # Bijective homomorphisms of differential graded modules are isomorphisms

A homomorphism of right differential graded modules whose underlying map of modules is bijective
is an isomorphism in `Mod_{(A,d)}`. The inverse map is `R`-linear, compatible with the right
`A`-action and commutes with the differentials for formal reasons — each is an identity between
elements that becomes true after applying the injective map `f`. The substance is that the
inverse preserves the grading, which says that an injective homomorphism *detects* homogeneity:
if `f x` is homogeneous of degree `n`, then `x` already is. That is a consequence of the
uniqueness of the direct sum decomposition `M = ⨁_n M^n`, and is proved here through the
degreewise projections, which commute with every homomorphism.

## Main definitions

* `DifferentialGradedModule.homogeneousProj`: the projection of a differential graded module
  onto its degree-`n` homogeneous component.
* `DifferentialGradedModule.Hom.inverse`: the inverse of a bijective homomorphism, as a
  homomorphism.
* `DifferentialGradedModule.Hom.isoOfBijective`: a bijective homomorphism, as an isomorphism.

## Main results

* `DifferentialGradedModule.Hom.homogeneousProj_comm`: a homomorphism commutes with the
  degreewise projections.
* `DifferentialGradedModule.Hom.mem_grading_of_injective`: an injective homomorphism detects
  homogeneity.
* `DifferentialGradedModule.Hom.exists_mem_grading_of_surjective`: a surjective homomorphism is
  already surjective on each homogeneous piece.
* `DifferentialGradedModule.isIso_of_bijective`: a bijective homomorphism of differential graded
  modules is an isomorphism.

## References

* [Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- The projection of a differential graded module onto its degree-`n` homogeneous component,
as an `R`-linear endomorphism of the underlying module: decompose, keep the degree-`n`
component, and include it back. -/
def homogeneousProj (M : DifferentialGradedModule A) (n : ℤ) : M.M →ₗ[R] M.M :=
  (M.grading n).subtype ∘ₗ DirectSum.component R ℤ _ n ∘ₗ
    (DirectSum.decomposeLinearEquiv M.grading).toLinearMap

/-- The degreewise projection is the degree-`n` component of the direct sum decomposition. -/
theorem homogeneousProj_apply (M : DifferentialGradedModule A) (n : ℤ) (x : M.M) :
    M.homogeneousProj n x = (DirectSum.decompose M.grading x n : M.M) := rfl

/-- The degree-`n` projection takes values in the degree-`n` piece. -/
theorem homogeneousProj_mem (M : DifferentialGradedModule A) (n : ℤ) (x : M.M) :
    M.homogeneousProj n x ∈ M.grading n :=
  (DirectSum.decompose M.grading x n).2

/-- An element of a differential graded module is homogeneous of degree `n` exactly when it is
fixed by the degree-`n` projection. -/
theorem mem_grading_iff_homogeneousProj (M : DifferentialGradedModule A) (n : ℤ) (x : M.M) :
    x ∈ M.grading n ↔ M.homogeneousProj n x = x :=
  ⟨fun hx => DirectSum.decompose_of_mem_same M.grading hx,
    fun hx => hx ▸ M.homogeneousProj_mem n x⟩

/-- A homomorphism of differential graded modules commutes with the degreewise projections:
the degree-`n` component of `f x` is the image of the degree-`n` component of `x`. -/
theorem Hom.homogeneousProj_comm {M N : DifferentialGradedModule A} (f : Hom M N) (n : ℤ) :
    f.toFun ∘ₗ M.homogeneousProj n = N.homogeneousProj n ∘ₗ f.toFun := by
  refine DirectSum.decompose_lhom_ext M.grading fun j => LinearMap.ext fun y => ?_
  obtain ⟨x, hx⟩ := y
  have hfx : f.toFun x ∈ N.grading j := f.map_grading j x hx
  by_cases h : j = n
  · subst h
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, homogeneousProj_apply,
      DirectSum.decompose_of_mem_same M.grading hx,
      DirectSum.decompose_of_mem_same N.grading hfx]
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, homogeneousProj_apply,
      DirectSum.decompose_of_mem_ne M.grading hx h,
      DirectSum.decompose_of_mem_ne N.grading hfx h, map_zero]

/-- If `f x` is homogeneous of degree `n`, then `f` maps the degree-`n` part of `x` to `f x`. -/
private theorem Hom.map_homogeneousProj_of_mem {M N : DifferentialGradedModule A} (f : Hom M N)
    {n : ℤ} {x : M.M} (hx : f.toFun x ∈ N.grading n) :
    f.toFun (M.homogeneousProj n x) = f.toFun x :=
  (LinearMap.congr_fun (f.homogeneousProj_comm n) x).trans
    ((N.mem_grading_iff_homogeneousProj n _).1 hx)

/-- An injective homomorphism of differential graded modules detects homogeneity: if `f x` is
homogeneous of degree `n`, then `x` is homogeneous of degree `n`. -/
theorem Hom.mem_grading_of_injective {M N : DifferentialGradedModule A} {f : Hom M N}
    (hf : Function.Injective f.toFun) {n : ℤ} {x : M.M} (hx : f.toFun x ∈ N.grading n) :
    x ∈ M.grading n := by
  rw [M.mem_grading_iff_homogeneousProj]
  exact hf (f.map_homogeneousProj_of_mem hx)

/-- A surjective homomorphism of differential graded modules is already surjective on each
homogeneous piece: a homogeneous element of degree `n` of the target is the image of a
homogeneous element of degree `n` of the source. -/
theorem Hom.exists_mem_grading_of_surjective {M N : DifferentialGradedModule A} {f : Hom M N}
    (hf : Function.Surjective f.toFun) {n : ℤ} {y : N.M} (hy : y ∈ N.grading n) :
    ∃ x : M.M, x ∈ M.grading n ∧ f.toFun x = y := by
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨M.homogeneousProj n x, M.homogeneousProj_mem n x, f.map_homogeneousProj_of_mem hy⟩

/-- The inverse of the underlying linear map of a bijective homomorphism of differential graded
modules. -/
def Hom.invLinearMap {M N : DifferentialGradedModule A} (f : Hom M N)
    (hf : Function.Bijective f.toFun) : N.M →ₗ[R] M.M :=
  (LinearEquiv.ofBijective f.toFun hf).symm

/-- The inverse linear map of a bijective homomorphism of differential graded modules is a
section of it. -/
theorem Hom.apply_invLinearMap {M N : DifferentialGradedModule A} (f : Hom M N)
    (hf : Function.Bijective f.toFun) (y : N.M) : f.toFun (f.invLinearMap hf y) = y :=
  (LinearEquiv.ofBijective f.toFun hf).apply_symm_apply y

/-- The inverse of a bijective homomorphism of differential graded modules, as a homomorphism of
differential graded modules. -/
def Hom.inverse {M N : DifferentialGradedModule A} (f : Hom M N)
    (hf : Function.Bijective f.toFun) : Hom N M where
  toFun := f.invLinearMap hf
  map_smul y a := hf.injective (by
    rw [f.map_smul, Hom.apply_invLinearMap, Hom.apply_invLinearMap])
  map_grading n y hy := Hom.mem_grading_of_injective (f := f) hf.injective (by
    rw [Hom.apply_invLinearMap]; exact hy)
  map_d := LinearMap.ext fun y => hf.injective (by
    have hd := LinearMap.congr_fun f.map_d (f.invLinearMap hf y)
    simp only [LinearMap.comp_apply] at hd ⊢
    rw [Hom.apply_invLinearMap, hd, Hom.apply_invLinearMap])

/-- A bijective homomorphism of differential graded modules, as an isomorphism of the category
of differential graded modules.

This is the form to use when the homomorphism is presented at the type `Hom M N` — as a field
of a structure, say — rather than as a categorical arrow `M ⟶ N`: a term whose type is spelled
`Hom M N` does not unify with `?M ⟶ ?N`, so `isIso_of_bijective` cannot be applied to it
without annotating its type. -/
def Hom.isoOfBijective {M N : DifferentialGradedModule A} (f : Hom M N)
    (hf : Function.Bijective f.toFun) : M ≅ N where
  hom := f
  inv := f.inverse hf
  hom_inv_id := by
    apply Hom.ext
    refine LinearMap.ext fun x => hf.injective ?_
    change f.toFun (f.invLinearMap hf (f.toFun x)) = f.toFun x
    rw [Hom.apply_invLinearMap]
  inv_hom_id := by
    apply Hom.ext
    refine LinearMap.ext fun y => ?_
    change f.toFun (f.invLinearMap hf y) = y
    rw [Hom.apply_invLinearMap]

/-- A homomorphism of differential graded modules whose underlying map of modules is bijective is
an isomorphism in the category of differential graded modules. -/
theorem isIso_of_bijective {M N : DifferentialGradedModule A} (f : M ⟶ N)
    (h : Function.Bijective f.toFun) : IsIso f :=
  (Hom.isoOfBijective f h).isIso_hom

end DifferentialGradedModule

end
