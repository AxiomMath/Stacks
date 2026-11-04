module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleDegreeZeroFlat
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlatOverBase
public import StacksFrontier.RingTheory.HomogeneousLocalization.DegreeZero

/-!
# Finiteness of the twist sections over a standard open of a homogeneous spectrum

Let `A` be a nonnegatively graded ring whose grading is `𝒜`, and let `f ∈ 𝒜 d` be homogeneous of
positive degree. The `t`-th twist `A(t)` of the regular graded module is the module `A` with its
grading shifted by `t`, and its degree-zero localization away from `f` is the module of sections of
the twisting sheaf `𝒪(t)` over the standard open `D₊(f)`.

This file proves that this module of sections is a *finite* module over the degree-zero
localization `A₍f₎` as soon as `A` is a finite type algebra over its degree-zero part. That is the
local, ring-theoretic content of the second assertion of Stacks tag 07ZY, and it is the module
case `M = A(t)` of Stacks tag 07Z2 (2): the degree-zero localization of a finite graded module
over a graded algebra of finite type is a finite module over the degree-zero localization of the
algebra.

## Main definitions

* `GradedModule.toSubmodules` promotes a grading of a module by `SetLike` subobjects to a grading
  by submodules over a base ring mapping into degree zero. This is the module analogue of
  `GradedRing.toSubmodules`, and it is the form of a graded module that
  `moduleLocalization_away_finite` consumes.

## Main results

* `Module.Finite.of_addEquiv`: finiteness transports along a ring homomorphism together with a
  compatible additive equivalence.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_twistLocalization`: the degree-zero part of
  the `t`-th twisted localization at a homogeneous element of positive degree is a finite
  `A₍f₎`-module.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_twistSections`: the sections of the `t`-th
  twisting sheaf over `D₊(f)` are a finite `A₍f₎`-module.

## Implementation notes

The finiteness engine `moduleLocalization_away_finite` is stated for a grading by submodules over
a base ring, and it realizes the degree-zero localization as `MLoc`, the span of the degree-zero
fractions inside the localized module. The twisting sheaf, on the other hand, is built from
`GradedModuleDegreeZeroLocalization`, which is the span of the degree-zero fractions taken with
respect to an arbitrary admissible degree for `f`. The two spans coincide: one set of generators is
contained in the other, and `degreeZeroFraction_surjective` says that every element of the larger
span is already one of the smaller generators. So the identification is the identity of the
ambient localized module, and the only genuine transport is the ring isomorphism
`HomogeneousLocalization.Away.toSubmodulesEquiv` between the two degree-zero localizations of the
ring, which does not change the underlying fraction.

The base ring is taken to be the degree-zero part `𝒜 0` itself, with the canonical algebra
structure `SetLike.GradeZero.instAlgebra`. That is the most general choice: a finite type algebra
over any base ring mapping into degree zero is a finite type algebra over `𝒜 0`.

The degree action of `ℕ` on `ℤ` is the local `VAdd ℕ ℤ` instance adding the cast, as in the files
that define the integer-graded twist of a graded ring; Mathlib provides no such instance.

## References

* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
* [Stacks Project, Tag 07Z2](https://stacks.math.columbia.edu/tag/07Z2)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

/-- The grading action of natural-number ring degrees on integer module degrees, by addition. -/
local instance twistFiniteDegreeVAdd : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

/-- **Finiteness of a module transports along a ring homomorphism together with a compatible
additive equivalence.** This is the semilinear form of `Module.Finite.equiv`: the two modules are
finite over the two rings at once as soon as some additive bijection between them intertwines the
two scalar actions through the ring map. -/
public theorem Module.Finite.of_addEquiv {R R' M M' : Type*} [Semiring R] [Semiring R']
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R' M'] (σ : R →+* R')
    (e : M ≃+ M') (he : ∀ (r : R) (x : M), e (r • x) = σ r • e x) (h : Module.Finite R M) :
    Module.Finite R' M' := by
  have := h
  exact Module.Finite.of_surjective
    ({ toFun := fun x => e x, map_add' := fun x y => map_add e x y, map_smul' := he } :
      M →ₛₗ[σ] M') e.surjective

namespace GradedModule

variable {R A σ τ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ A] [AddSubgroupClass τ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒜 𝒨]
  (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0)

/-- **A grading of the regular module whose compatibility with a `SetLike` ring grading is known
is a grading by submodules over any base ring mapping into degree zero.** The `i`-th member is the
`i`-th graded piece, with the same underlying set; it is stable under the `R`-action because
`r • x = (algebraMap R A r) * x` and multiplication by a degree-zero element preserves degrees.

This is the module analogue of `GradedRing.toSubmodules`, in the only case the degree-zero
localization of a twist needs: the module is the ring itself, regraded. -/
public def toSubmodules (i : ℤ) : Submodule R A where
  carrier := 𝒨 i
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' r x hx := by
    rw [Algebra.smul_def]
    simpa using SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) (h0 r) hx

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The promoted grading has the same members as the original one. -/
@[simp] public theorem mem_toSubmodules {i : ℤ} {x : A} :
    x ∈ toSubmodules 𝒜 𝒨 h0 i ↔ x ∈ 𝒨 i := Iff.rfl

/-- The promoted grading decomposes the module: the members, and hence the homogeneous
decomposition, are unchanged. -/
public instance instDecompositionToSubmodules [DirectSum.Decomposition 𝒨] :
    DirectSum.Decomposition (toSubmodules 𝒜 𝒨 h0) where
  decompose' := DirectSum.decompose 𝒨
  left_inv := DirectSum.Decomposition.left_inv
  right_inv := DirectSum.Decomposition.right_inv

/-- The promoted gradings are compatible, the members being unchanged on both sides. -/
public instance instGradedSMulToSubmodules :
    SetLike.GradedSMul (GradedRing.toSubmodules 𝒜 h0) (toSubmodules 𝒜 𝒨 h0) := by
  refine ⟨?_⟩
  intro i j a b ha hb
  exact SetLike.GradedSMul.smul_mem (A := 𝒜) (B := 𝒨) ha hb

end GradedModule

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-zero part of the graded ring contains the image of its own structure map. -/
private theorem algebraMap_gradeZero_mem (r : 𝒜 0) : algebraMap (𝒜 0) A r ∈ 𝒜 0 := r.2

/-- **The degree-zero part of the `t`-th twisted localization at a homogeneous element of positive
degree is a finite module over the degree-zero localization of the ring** when the ring is a
finite type algebra over its degree-zero part.

This is the local, ring-theoretic content of the second assertion of Stacks tag 07ZY: it is Stacks
tag 07Z2 (2) applied to the graded module `A(t)`, the ring regraded by a shift, which is finite
over `A` because it is `A`. -/
public theorem finite_twistLocalization [Algebra.FiniteType (𝒜 0) A] {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) (t : ℤ) :
    Module.Finite (HomogeneousLocalization.Away 𝒜 f)
      (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading 𝒜 t) f) := by
  classical
  let h0 := algebraMap_gradeZero_mem 𝒜
  let 𝒜' := GradedRing.toSubmodules 𝒜 h0
  let ℳ' := GradedModule.toSubmodules 𝒜 (twistGrading 𝒜 t) h0
  have hf' : f ∈ 𝒜' d := hf
  have hmem : ∀ y, y ∈ MLoc 𝒜' ℳ' f d ↔
      y ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading 𝒜 t) f := by
    intro y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨n, x, hx, rfl⟩ := (mem_MLoc_iff 𝒜' ℳ' f d hf' y).mp hy
      exact Submodule.subset_span ⟨d, n, hf, x, hx, rfl⟩
    · obtain ⟨n, x, hx, he⟩ :=
        degreeZeroFraction_surjective 𝒜 (twistGrading 𝒜 t) hf ⟨y, hy⟩
      have hy' : deg0frac f n x = y := congrArg Subtype.val he
      exact hy' ▸ deg0frac_mem_MLoc 𝒜' ℳ' f d n x hx
  let ε := (HomogeneousLocalization.Away.toSubmodulesEquiv 𝒜 h0 f).symm
  have hsmul (r : SLoc 𝒜' f) (z : MLocAll f (M := A)) : r • z = (ε r) • z := by
    show r.val • z = (ε r).val • z
    rw [← HomogeneousLocalization.Away.val_toSubmodulesEquiv 𝒜 h0 f (ε r),
      (HomogeneousLocalization.Away.toSubmodulesEquiv 𝒜 h0 f).apply_symm_apply r]
  exact Module.Finite.of_addEquiv ε.toRingHom
    { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl } (fun r x => Subtype.ext (hsmul r x.1))
    (moduleLocalization_away_finite 𝒜' ℳ' f d hf' hd)

/-- **The sections of the `t`-th twisting sheaf over a standard open at a homogeneous element of
positive degree are a finite module over the degree-zero localization there** when the graded ring
is a finite type algebra over its degree-zero part.

The sections over `D₊(f)` are the degree-zero part of the twisted localization, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, and that
identification is `A₍f₎`-linear for the action of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`. -/
public theorem finite_twistSections [Algebra.FiniteType (𝒜 0) A] {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) (t : ℤ) :
    Module.Finite (HomogeneousLocalization.Away 𝒜 f)
      ((twistingSheaf 𝒜 t).val.obj (.op (ProjectiveSpectrum.basicOpen 𝒜 f))) := by
  have := finite_twistLocalization 𝒜 hd hf t
  exact Module.Finite.equiv
    (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading 𝒜 t) hf hd).symm

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
