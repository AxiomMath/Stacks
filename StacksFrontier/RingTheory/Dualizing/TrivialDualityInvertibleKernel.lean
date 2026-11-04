module

public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.Homology.Tor.DerivedTensorFunctoriality
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityKFlat
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Trivial duality for a surjection with invertible kernel

Let `R → A` be a surjective homomorphism of commutative rings whose kernel `I` is an invertible
`R`-module. The conormal module `I ⊗_R A` is then an invertible `A`-module, and this file builds
its inverse `N` and identifies `RHom_R(A, R)`, the value of the derived coextension-of-scalars
functor `Dualizing.derivedHom` at the free module of rank one, with the single complex on `N` in
degree one — that is, with `N[-1]`.

The identification comes from the two-term projective resolution `0 → I → R → A → 0`: the
cohomology of `RHom_R(A, -)` is `Ext` by Stacks 0A71, and the contravariant long exact sequence
of the resolution computes `Ext^q_R(A, R)` as `0` for `q ≠ 1` and as the cokernel of
`R → Hom_R(I, R)` for `q = 1`. That cokernel is `N`: base change of linear forms
`Hom_R(I, R) → Hom_A(I ⊗_R A, A)` is surjective because `I` is projective and `R → A` is
surjective, and its kernel is exactly the multiplications `r · (I ↪ R)` because `R → End_R(I)`
is bijective for an invertible module.

## Main definitions

* `Dualizing.InvertibleKernel.conormal` — the conormal module `I ⊗_R A`, an `A`-module.
* `Dualizing.InvertibleKernel.conormalInverse` — `N`, the inverse of the conormal module.
* `Dualizing.InvertibleKernel.conormalInverseShift` — the complex `N[-1]`.
* `Dualizing.InvertibleKernel.kernelDualRestriction` — the map `R → Hom_R(I, R)` dual to the
  inclusion `I → R`, whose cokernel is `N`.
* `Dualizing.InvertibleKernel.kernelShortComplex` — the resolution `0 → I → R → A → 0`.

## Main results

* `Dualizing.InvertibleKernel.conormal_invertible` — the conormal module is invertible. This is
  the clause of **Stacks 0BZH** calling `I ⊗_R A` invertible.
* `Dualizing.InvertibleKernel.conormalInverse_tensor_conormal` — `N ⊗_A (I ⊗_R A) ≅ A`, so `N`
  really is a tensor inverse of the conormal module. This is the clause of **Stacks 0BZH**
  naming `N` as that inverse.
* `Dualizing.InvertibleKernel.kernelDualCokernelEquiv` — the cokernel of `R → Hom_R(I, R)`
  is `N`.
* `Dualizing.InvertibleKernel.extOneEquivConormalInverse`,
  `Dualizing.InvertibleKernel.extZero_eq_zero`,
  `Dualizing.InvertibleKernel.extSuccSucc_eq_zero` — `Ext^q_R(A, R)` is `N` for `q = 1` and
  zero otherwise.
* `Dualizing.InvertibleKernel.derivedHomUnitObjectIsoSingle` — `RHom_R(A, R) ≅ N[-1]` in `D(A)`.
* `Dualizing.InvertibleKernel.derivedHomIsoDerivedTensorConormalInverseShift` — **Stacks 0BZH**:
  `RHom_R(A, -) ≅ - ⊗^L_R N[-1]` as functors `D(R) ⥤ D(A)`, at an arbitrary module universe, as a
  function of Stacks 0BZE in the form of invertibility of `Stacks0BZE.comparison` at every
  K-flat complex. The conclusion holds with no hypothesis beyond
  the two above, at every module universe, as
  `nonempty_derivedHom_iso_derivedTensor_conormalInverseShift_anyModuleUniverse` of
  `StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernelAnyModuleUniverse` — and, in the
  universe of the rings themselves,
  `Dualizing.InvertibleKernel.nonempty_derivedHom_iso_derivedTensor_conormalInverseShift` of
  `StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof`.
* `Dualizing.InvertibleKernel.surjective_and_invertible_ker_quotient` — the hypotheses hold for
  every quotient by a nonzerodivisor, for instance `k[x] → k[x]/(x)`.

## Implementation notes

`N` is constructed, not assumed: it is `Hom_A(I ⊗_R A, A)`, which is a tensor inverse of
`I ⊗_R A` because `I ⊗_R A` is invertible. The shift `[-1]` is carried explicitly, as the shift
by `-1` of the single complex on `N` in degree zero; `conormalInverseShiftIso` identifies its
class in the derived category with the single object on `N` in degree one.

Stacks 0BZE — that derived coextension along a map with perfect target is derived tensor product
with `RHom_R(A, R)` — is proved in the library at module universe equal to the ring universe, the
generality of the differential graded chapter (Tag 09JJ) its proof runs through
(`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfect`), and at an arbitrary module
universe by renaming the rings along `ULift.ringEquiv`
(`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect_anyModuleUniverse` of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfectAnyModuleUniverse`).

The statement below asks for Stacks 0BZE in a *different* shape, the one
`StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlat.lean` reduces it to: invertibility of
`Stacks0BZE.comparison`, the transpose under Stacks 0A70 of the tensored derived counit, at every
K-flat complex. That is more than an abstract isomorphism of the two functors, since restriction
of scalars is conservative but not full, so it is an input to the statement rather than something
the forms above provide. The conclusion without it is
`nonempty_derivedHom_iso_derivedTensor_conormalInverseShift_anyModuleUniverse` of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernelAnyModuleUniverse`, which follows
the same chain of isomorphisms with the abstract form of Stacks 0BZE in place of the comparison.

## References

* [Stacks Project, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v

namespace Dualizing.InvertibleKernel

noncomputable section Algebraic

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The kernel of `R → A`, as an `R`-module in the module universe. -/
abbrev kernelModule : Type (max v u) := ULift.{v} (RingHom.ker (algebraMap R A))

/-- The conormal module `I ⊗_R A` of the surjection `R → A` with kernel `I`, as an
`A`-module. -/
abbrev conormal : Type (max v u) := A ⊗[R] kernelModule.{u, v} R A

/-- `N`, the inverse of the conormal module: the `A`-linear dual of `I ⊗_R A`. For an invertible
module the linear dual is a tensor inverse; see `conormalInverse_tensor_conormal`. -/
abbrev conormalInverse : Type (max v u) := Module.Dual A (conormal.{u, v} R A)

variable {R A}

/-- The kernel of `R → A`, lifted to the module universe, is invertible when the kernel is. -/
theorem kernelModule_invertible (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    Module.Invertible R (kernelModule.{u, v} R A) :=
  Module.Invertible.congr
    (ULift.moduleEquiv (R := R) (M := (RingHom.ker (algebraMap R A) : Type u))).symm

/-- **The conormal module of a surjection with invertible kernel is invertible.** Invertibility
is stable under base change, here along `R → A` itself.

This is the clause of [Stacks, Tag 0BZH] that calls `I ⊗_R A` an invertible `A`-module. Unlike
the functor identification it needs nothing beyond the two hypotheses of the tag, and it holds at
every module universe. -/
@[stacks 0BZH "the conormal module `I ⊗_R A` is an invertible `A`-module"]
theorem conormal_invertible (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    Module.Invertible A (conormal.{u, v} R A) :=
  let := kernelModule_invertible.{u, v} hI
  inferInstance

/-- **`N` is a tensor inverse of the conormal module**: `N ⊗_A (I ⊗_R A) ≅ A`.

This is the clause of [Stacks, Tag 0BZH] that names `N` as the inverse of the invertible
`A`-module `I ⊗_R A`; like `Dualizing.InvertibleKernel.conormal_invertible` it is unconditional
and holds at every module universe. -/
@[stacks 0BZH "`N` is the inverse of the invertible `A`-module `I ⊗_R A`"]
def conormalInverse_tensor_conormal
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    conormalInverse.{u, v} R A ⊗[A] conormal.{u, v} R A ≃ₗ[A] A :=
  letI := conormal_invertible.{u, v} hI
  Module.Invertible.linearEquiv A (conormal.{u, v} R A)

/-! ### The cokernel of `R → Hom_R(I, R)` -/

/-- The inclusion `I → R`, read as a linear form on the kernel. -/
def kernelInclusion : Module.Dual R (kernelModule.{u, v} R A) :=
  (RingHom.ker (algebraMap R A)).subtype ∘ₗ
    (ULift.moduleEquiv (R := R)
      (M := (RingHom.ker (algebraMap R A) : Type u))).toLinearMap

/-- `kernelInclusion` sends an element of the kernel to its underlying element of `R`. -/
@[simp]
theorem kernelInclusion_apply (x : kernelModule.{u, v} R A) :
    kernelInclusion.{u, v} (A := A) x = (x.down : R) := rfl

/-- The map `R → Hom_R(I, R)` dual to the inclusion `I → R`: it sends `r` to multiplication
by `r`. -/
def kernelDualRestriction : R →ₗ[R] Module.Dual R (kernelModule.{u, v} R A) :=
  LinearMap.toSpanSingleton R _ (kernelInclusion.{u, v} (A := A))

/-- `kernelDualRestriction r` sends `x` in the kernel to `r * x`. -/
@[simp]
theorem kernelDualRestriction_apply (r : R) (x : kernelModule.{u, v} R A) :
    kernelDualRestriction.{u, v} (R := R) (A := A) r x = r * (x.down : R) := rfl

/-- An element of `R` killing the whole kernel of `R → A` is zero: an invertible module is a
faithful module. -/
theorem eq_zero_of_mul_kernel_eq_zero
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) (r : R)
    (hr : ∀ x : RingHom.ker (algebraMap R A), r * (x : R) = 0) : r = 0 := by
  let e := Module.Invertible.linearEquiv R (RingHom.ker (algebraMap R A))
  have hzero : r • e.symm 1 = 0 := by
    induction e.symm 1 using TensorProduct.induction_on with
    | zero => simp
    | tmul φ x =>
        have hx : r • x = 0 := Subtype.ext (by simpa using hr x)
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hx]
        simp
    | add x y hx hy => simp [hx, hy]
  calc r = e (r • e.symm 1) := by simp
    _ = 0 := by rw [hzero, map_zero]

/-- `R → Hom_R(I, R)` is injective, which is what makes `Hom_R(A, R)` vanish. -/
theorem kernelDualRestriction_injective
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    Function.Injective (kernelDualRestriction.{u, v} (R := R) (A := A)) := by
  intro r s hrs
  apply sub_eq_zero.mp
  apply eq_zero_of_mul_kernel_eq_zero hI (r - s)
  intro x
  have hx := LinearMap.congr_fun hrs (ULift.up x)
  simp only [kernelDualRestriction_apply] at hx
  rw [sub_mul, hx, sub_self]

/-- Base change of linear forms along `R → A`, from `Hom_R(I, R)` to `Hom_A(I ⊗_R A, A)`. -/
def conormalDualBaseChange :
    Module.Dual R (kernelModule.{u, v} R A) →ₗ[R] conormalInverse.{u, v} R A :=
  Module.Dual.baseChange A

/-- The base change of `φ` sends `a ⊗ x` to `a * φ x`. -/
@[simp]
theorem conormalDualBaseChange_apply_tmul (φ : Module.Dual R (kernelModule.{u, v} R A)) (a : A)
    (x : kernelModule.{u, v} R A) :
    conormalDualBaseChange.{u, v} φ (a ⊗ₜ[R] x) = a * algebraMap R A (φ x) := by
  simp [conormalDualBaseChange, Algebra.smul_def, mul_comm]

/-- Base change of linear forms is surjective: `I` is projective, so an `A`-linear form on
`I ⊗_R A` lifts through the surjection `R → A` to an `R`-linear form on `I`. -/
theorem conormalDualBaseChange_surjective (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    Function.Surjective (conormalDualBaseChange.{u, v} (R := R) (A := A)) := by
  let := kernelModule_invertible.{u, v} hI
  intro ψ
  have hf' : Function.Surjective (Algebra.linearMap R A) := hf
  obtain ⟨q, hq⟩ := Module.projective_lifting_property (Algebra.linearMap R A)
    ((ψ.restrictScalars R).comp (TensorProduct.mk R A (kernelModule.{u, v} R A) 1)) hf'
  refine ⟨q, TensorProduct.AlgebraTensorModule.ext fun a x => ?_⟩
  have hqx : algebraMap R A (q x) = ψ (1 ⊗ₜ[R] x) := LinearMap.congr_fun hq x
  rw [conormalDualBaseChange_apply_tmul, hqx]
  calc a * ψ (1 ⊗ₜ[R] x) = ψ (a • (1 ⊗ₜ[R] x)) := by rw [← smul_eq_mul, map_smul]
    _ = ψ (a ⊗ₜ[R] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The kernel of base change of linear forms is exactly the image of `R → Hom_R(I, R)`. One
inclusion is that `R → A` kills `I`; the other uses that `R → End_R(I)` is bijective for an
invertible module, so a linear form on `I` taking its values in `I` is a multiplication. -/
theorem ker_conormalDualBaseChange
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    LinearMap.ker (conormalDualBaseChange.{u, v} (R := R) (A := A)) =
      LinearMap.range (kernelDualRestriction.{u, v} (R := R) (A := A)) := by
  have := kernelModule_invertible.{u, v} hI
  ext φ
  refine ⟨fun hφ => ?_, ?_⟩
  · have hφI : ∀ x : kernelModule.{u, v} R A, φ x ∈ RingHom.ker (algebraMap R A) := by
      intro x
      refine RingHom.mem_ker.2 ?_
      have hx := congrArg (fun k : conormalInverse.{u, v} R A => k (1 ⊗ₜ[R] x))
        (LinearMap.mem_ker.mp hφ)
      rwa [conormalDualBaseChange_apply_tmul, one_mul] at hx
    let θ : kernelModule.{u, v} R A →ₗ[R] kernelModule.{u, v} R A :=
      { toFun := fun x => ULift.up ⟨φ x, hφI x⟩
        map_add' := fun x y => ULift.ext _ _ (Subtype.ext (map_add φ x y))
        map_smul' := fun r x => ULift.ext _ _ (Subtype.ext (map_smul φ r x)) }
    obtain ⟨r, hr⟩ := (Module.Invertible.toModuleEnd_bijective R
      (kernelModule.{u, v} R A)).2 θ
    refine ⟨r, LinearMap.ext fun x => ?_⟩
    simpa [θ, Module.toModuleEnd_apply] using congrArg
      (fun k : kernelModule.{u, v} R A →ₗ[R] kernelModule.{u, v} R A => ((k x).down : R)) hr
  · rintro ⟨r, rfl⟩
    change conormalDualBaseChange.{u, v} _ = 0
    refine TensorProduct.AlgebraTensorModule.ext fun a x => ?_
    have hx : algebraMap R A (x.down : R) = 0 := RingHom.mem_ker.mp x.down.property
    rw [conormalDualBaseChange_apply_tmul, kernelDualRestriction_apply,
      map_mul, hx]
    simp

/-- **The cokernel of `R → Hom_R(I, R)` is `N`.** This is the module-theoretic heart of
Stacks 0BZH: the two-term resolution `0 → I → R → A → 0` turns `RHom_R(A, R)` into the two-term
complex `R → Hom_R(I, R)`, whose only cohomology is this cokernel, in degree one. -/
def kernelDualCokernelEquiv (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    (Module.Dual R (kernelModule.{u, v} R A) ⧸
      LinearMap.range (kernelDualRestriction.{u, v} (R := R) (A := A))) ≃ₗ[R]
      conormalInverse.{u, v} R A :=
  (Submodule.quotEquivOfEq _ _ (ker_conormalDualBaseChange.{u, v} hI).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      (conormalDualBaseChange_surjective.{u, v} hf hI))

/-! ### The two-term resolution `0 → I → R → A → 0` -/

/-- For a short exact sequence whose middle term is projective, `Ext^1(X₃, Y)` is the cokernel of
the restriction map `Hom(X₂, Y) → Hom(X₁, Y)`. -/
def extOneQuotientEquiv {S : ShortComplex (ModuleCat.{max v u} R)} (hS : S.ShortExact)
    [Projective S.X₂] (Y : ModuleCat.{max v u} R) :
    ((S.X₁ ⟶ Y) ⧸ LinearMap.range (Linear.leftComp R Y S.f)) ≃ₗ[R]
      Abelian.Ext S.X₃ Y 1 := by
  let δ : (S.X₁ ⟶ Y) →ₗ[R] Abelian.Ext S.X₃ Y 1 :=
    (Abelian.Ext.bilinearCompOfLinear R _ _ _ 1 0 1 (by omega) hS.extClass).comp
      (Abelian.Ext.linearEquiv₀ (R := R)).symm.toLinearMap
  have hsurj : Function.Surjective δ := by
    intro x
    obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y x
      (Abelian.Ext.eq_zero_of_projective _) (show 1 + 0 = 1 by omega)
    exact ⟨(Abelian.Ext.linearEquiv₀ (R := R)) y, by simpa [δ] using hy⟩
  have hker : LinearMap.ker δ = LinearMap.range (Linear.leftComp R Y S.f) := by
    ext x
    refine ⟨fun hx => ?_, ?_⟩
    · obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y
        (Abelian.Ext.mk₀ x) (show 1 + 0 = 1 by omega) hx
      refine ⟨(Abelian.Ext.linearEquiv₀ (R := R)) y, ?_⟩
      apply (Abelian.Ext.linearEquiv₀ (R := R)).symm.injective
      change Abelian.Ext.mk₀ (S.f ≫ (Abelian.Ext.linearEquiv₀ (R := R)) y) = _
      rwa [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_linearEquiv₀_apply]
    · rintro ⟨y, rfl⟩
      change hS.extClass.comp (Abelian.Ext.mk₀ (S.f ≫ y)) (by omega) = 0
      rw [← Abelian.Ext.mk₀_comp_mk₀]
      exact hS.extClass_comp_assoc _
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (LinearMap.quotKerEquivOfSurjective δ hsurj)

/-- The surjection `R → A`, read on the lifts to the module universe. -/
abbrev liftedAlgebraMap : ULift.{v} R →ₗ[R] ULift.{v} A :=
  (ULift.moduleEquiv (R := R) (M := A)).symm.toLinearMap ∘ₗ Algebra.linearMap R A ∘ₗ
    (ULift.moduleEquiv (R := R) (M := R)).toLinearMap

/-- The inclusion `I → R`, read on the lifts to the module universe. -/
abbrev liftedKernelInclusion : kernelModule.{u, v} R A →ₗ[R] ULift.{v} R :=
  (ULift.moduleEquiv (R := R) (M := R)).symm.toLinearMap ∘ₗ kernelInclusion.{u, v} (A := A)

/-- Multiplication by `r : R`, from the lifted base ring to the lifted free module of rank one
in the module universe. -/
abbrev multiplicationLift (r : R) : ULift.{v} R →ₗ[R] ULift.{max v u} R :=
  (ULift.moduleEquiv (R := R) (M := R)).symm.toLinearMap ∘ₗ
    (r • (LinearMap.id : R →ₗ[R] R)) ∘ₗ (ULift.moduleEquiv (R := R) (M := R)).toLinearMap

/-- The short exact sequence `0 → I → R → A → 0` of `R`-modules, in the module universe. -/
abbrev kernelShortComplex : ShortComplex (ModuleCat.{max v u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (liftedKernelInclusion.{u, v} (R := R) (A := A)))
    (ModuleCat.ofHom (liftedAlgebraMap.{u, v} (R := R) (A := A)))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply ULift.ext
      change algebraMap R A (x.down : R) = (0 : ULift.{v} A).down
      simpa using RingHom.mem_ker.mp x.down.property)

/-- Presenting `A` as `R` modulo an invertible ideal is a short exact sequence. -/
theorem kernelShortComplex_shortExact (hf : Function.Surjective (algebraMap R A)) :
    (kernelShortComplex.{u, v} (R := R) (A := A)).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨ULift.up ⟨x.down, RingHom.mem_ker.2 (congrArg ULift.down hx)⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr (fun _ _ hxy =>
    ULift.ext _ _ (Subtype.ext (congrArg ULift.down hxy)))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    intro y
    obtain ⟨r, hr⟩ := hf y.down
    exact ⟨ULift.up r, ULift.ext _ _ hr⟩)

/-- `R` itself is projective, so the middle term of the resolution is. -/
instance : Projective (kernelShortComplex.{u, v} (R := R) (A := A)).X₂ :=
  inferInstanceAs (Projective (ModuleCat.of R (ULift.{v} R)))

/-- An invertible module is finite projective, so the kernel term of the resolution is
projective. -/
theorem projective_kernelShortComplex_X₁
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    Projective (kernelShortComplex.{u, v} (R := R) (A := A)).X₁ :=
  let := kernelModule_invertible.{u, v} hI
  inferInstanceAs (Projective (ModuleCat.of R (kernelModule.{u, v} R A)))

/-- Linear forms on the kernel term of the resolution with values in the free rank one module,
identified with the `R`-linear dual of the kernel. -/
abbrev kernelHomEquivDual :
    ((kernelShortComplex.{u, v} (R := R) (A := A)).X₁ ⟶
      ModuleCat.of R (ULift.{max v u} R)) ≃ₗ[R]
      Module.Dual R (kernelModule.{u, v} R A) :=
  ModuleCat.homLinearEquiv.trans
    (LinearEquiv.arrowCongr (LinearEquiv.refl R (kernelModule.{u, v} R A))
      (ULift.moduleEquiv (R := R) (M := R)))

/-- Under that identification the restriction map from the middle term of the resolution has
image the multiplications, that is the image of `R → Hom_R(I, R)`. -/
theorem kernelHomEquivDual_map_range :
    Submodule.map (kernelHomEquivDual.{u, v} (R := R) (A := A)).toLinearMap
        (LinearMap.range (Linear.leftComp R (ModuleCat.of R (ULift.{max v u} R))
          (kernelShortComplex.{u, v} (R := R) (A := A)).f)) =
      LinearMap.range (kernelDualRestriction.{u, v} (R := R) (A := A)) := by
  ext φ
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, ⟨g, rfl⟩, rfl⟩
    refine ⟨(ConcreteCategory.hom g (ULift.up (1 : R))).down, LinearMap.ext fun x => ?_⟩
    have hsm : (x.down : R) • (ULift.up (1 : R) : ULift.{v} R) = ULift.up (x.down : R) :=
      ULift.ext _ _ (mul_one _)
    have h2 := congrArg ULift.down
      ((ConcreteCategory.hom g).map_smul (x.down : R) (ULift.up (1 : R)))
    rw [hsm] at h2
    simp only [ULift.smul_down, smul_eq_mul] at h2
    change (ConcreteCategory.hom g (ULift.up (1 : R))).down * (x.down : R) =
      (ConcreteCategory.hom g (ULift.up (x.down : R))).down
    rw [h2, mul_comm]
  · rintro ⟨r, rfl⟩
    exact ⟨Linear.leftComp R _ (kernelShortComplex.{u, v} (R := R) (A := A)).f
      (ModuleCat.ofHom (multiplicationLift.{u, v} (R := R) r)), ⟨_, rfl⟩,
      LinearMap.ext fun _ => rfl⟩

/-! ### `Ext^q_R(A, R)`: zero away from degree one, and `N` in degree one -/

/-- **`Ext^1_R(A, R) ≅ N`.** -/
def extOneEquivConormalInverse (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    Abelian.Ext (ModuleCat.of R (ULift.{v} A)) (ModuleCat.of R (ULift.{max v u} R)) 1 ≃ₗ[R]
      conormalInverse.{u, v} R A :=
  ((extOneQuotientEquiv.{u, v} (R := R) (kernelShortComplex_shortExact.{u, v} (R := R) (A := A) hf)
    (ModuleCat.of R (ULift.{max v u} R))).symm.trans
      (Submodule.Quotient.equiv _ _ (kernelHomEquivDual.{u, v} (R := R) (A := A))
        (kernelHomEquivDual_map_range.{u, v} (R := R) (A := A)))).trans
    (kernelDualCokernelEquiv.{u, v} hf hI)

/-- There is no nonzero `R`-linear map from `A` to `R`: such a map would send `1` to an element
of `R` killed by the whole invertible ideal `I`. -/
theorem linearMap_lift_eq_zero (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A)))
    (g : ULift.{v} A →ₗ[R] ULift.{max v u} R) : g = 0 := by
  have hone : g (ULift.up 1) = 0 := by
    refine ULift.ext _ _ ?_
    change (g (ULift.up 1)).down = (0 : R)
    apply eq_zero_of_mul_kernel_eq_zero hI
    intro x
    have hx : (x : R) • (ULift.up (1 : A) : ULift.{v} A) = 0 := by
      refine ULift.ext _ _ ?_
      change (x : R) • (1 : A) = (0 : A)
      rw [Algebra.smul_def, mul_one]
      exact RingHom.mem_ker.mp x.property
    have h := congrArg ULift.down (congrArg g hx)
    rw [map_smul] at h
    simp only [ULift.smul_down, smul_eq_mul, map_zero] at h
    simpa [mul_comm] using h
  refine LinearMap.ext fun y => ?_
  obtain ⟨r, hr⟩ := hf y.down
  have hy : y = r • (ULift.up (1 : A) : ULift.{v} A) := by
    refine ULift.ext _ _ ?_
    change y.down = (r : R) • (1 : A)
    rw [Algebra.smul_def, mul_one, hr]
  rw [hy, map_smul, hone, smul_zero, LinearMap.zero_apply]

/-- `Ext^0_R(A, R) = 0`. -/
theorem extZero_eq_zero (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A)))
    (x : Abelian.Ext (ModuleCat.of R (ULift.{v} A)) (ModuleCat.of R (ULift.{max v u} R)) 0) :
    x = 0 := by
  apply (Abelian.Ext.linearEquiv₀ (R := R)).injective
  rw [map_zero]
  exact ModuleCat.hom_ext (linearMap_lift_eq_zero.{u, v} (R := R) (A := A) hf hI _)

/-- `Ext^q_R(A, R) = 0` for `q ≥ 2`, because the kernel term of the resolution is projective. -/
theorem extSuccSucc_eq_zero (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) (n : ℕ)
    (x : Abelian.Ext (ModuleCat.of R (ULift.{v} A))
      (ModuleCat.of R (ULift.{max v u} R)) (n + 2)) :
    x = 0 := by
  have := projective_kernelShortComplex_X₁.{u, v} hI
  obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (kernelShortComplex_shortExact.{u, v} (R := R) (A := A) hf)
    (ModuleCat.of R (ULift.{max v u} R)) x (Abelian.Ext.eq_zero_of_projective _)
    (show 1 + (n + 1) = n + 2 by omega)
  rw [Abelian.Ext.eq_zero_of_projective y, Abelian.Ext.comp_zero] at hy
  exact hy.symm

end Algebraic

/-! ### `RHom_R(A, R)` is `N[-1]` -/

noncomputable section Derived

attribute [local instance] HasDerivedCategory.standard

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- An `R`-linear equivalence of `A`-modules is `A`-linear when `R → A` is surjective. -/
def linearEquivOfSurjectiveRestriction (f : R →+* A) (hf : Function.Surjective f)
    (M N : ModuleCat.{max v u} A)
    (e : ((ModuleCat.restrictScalars f).obj M : Type (max v u)) ≃ₗ[R]
      ((ModuleCat.restrictScalars f).obj N : Type (max v u))) : M ≃ₗ[A] N where
  __ := e.toAddEquiv
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := hf a
    exact e.map_smul r x

/-- The identity map, as an `R`-linear equivalence between an `A`-module read as an `R`-module by
restriction of scalars along `R → A` and the same module with a given `R`-action that agrees with
it. Only the two `R`-module instances differ. -/
def restrictScalarsIdEquiv (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module R M]
    (h : ∀ (r : R) (x : M), r • x = algebraMap R A r • x) :
    (((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M) :
      ModuleCat.{max v u} R) : Type (max v u)) ≃ₗ[R] M :=
  { toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun r x => (h r x).symm }

/-- The same identification, as an isomorphism of `R`-modules. -/
def restrictScalarsIdIso (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module R M]
    (h : ∀ (r : R) (x : M), r • x = algebraMap R A r • x) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M) ≅
      ModuleCat.of R M where
  hom := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M))
    (Y := ModuleCat.of R M)
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun r x => (h r x).symm }
  inv := ModuleCat.ofHom
    (X := ModuleCat.of R M)
    (Y := (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M))
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun r x => h r x }
  hom_inv_id := ModuleCat.hom_ext rfl
  inv_hom_id := ModuleCat.hom_ext rfl

/-- The lifted copy of `A`, read as an `R`-module by restriction of scalars, is the lifted copy of
`A` read as an `R`-module through the algebra structure: both actions are `r • a = f r * a`. -/
def restrictedLiftIso :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A (ULift.{v} A)) ≅
      ModuleCat.of R (ULift.{v} A) :=
  restrictScalarsIdIso.{u, v} (ULift.{v} A)
    (fun r x => ULift.ext _ _ (Algebra.smul_def r x.down))

/-- The right-derived unit of coextension of scalars, for which `Dualizing.derivedHom` has the
universal property. -/
abbrev derivedHomUnit (f : R →+* A) :
    Dualizing.coextendScalarsToDerivedCategory.{u, v} f ⟶
      DerivedCategory.Qh ⋙ Dualizing.derivedHom.{u, v} f :=
  (Dualizing.coextendScalarsToDerivedCategory.{u, v} f).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{max v u} R) (.up ℤ))

/-- **The cohomology of `RHom_R(A, R)` is `Ext^q_R(A, R)`**, by Stacks 0A71. -/
def derivedHomHomologyEquivExt (q : ℕ) :
    ((ModuleCat.restrictScalars (algebraMap R A)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) (q : ℤ)).obj
        ((Dualizing.derivedHom.{u, v} (algebraMap R A)).obj
          (Stacks0BZE.unitObject.{u, v} R))) : Type (max v u)) ≃ₗ[R]
      Abelian.Ext (ModuleCat.of R (ULift.{v} A))
        (ModuleCat.of R (ULift.{max v u} R)) q :=
  let e := Dualizing.derivedCoextendScalarsHomologyLinearEquivExt (algebraMap R A)
    (Dualizing.derivedHom.{u, v} (algebraMap R A)) (derivedHomUnit.{u, v} (algebraMap R A))
  (e.linearEquiv (Stacks0BZE.unitObject.{u, v} R) q).trans
    ((Linear.homCongr R
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).mapIso
        restrictedLiftIso.{u, v}) (Iso.refl _)).trans
      (Abelian.Ext.homLinearEquiv (R := R)).symm)

/-- **`RHom_R(A, R)` has no cohomology outside degree one.** Negative degrees vanish because the
derived argument is a single complex in degree zero; non-negative degrees are the `Ext` groups
computed from the two-term resolution. -/
theorem derivedHomHomology_isZero_of_ne_one (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) (q : ℤ) (hq : q ≠ 1) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) q).obj
      ((Dualizing.derivedHom.{u, v} (algebraMap R A)).obj
        (Stacks0BZE.unitObject.{u, v} R))) := by
  by_cases hneg : q < 0
  · let e := (Dualizing.derivedCoextendScalarsHomologyLinearEquivExt (algebraMap R A)
      (Dualizing.derivedHom.{u, v} (algebraMap R A))
      (derivedHomUnit.{u, v} (algebraMap R A))).linearEquiv
        (Stacks0BZE.unitObject.{u, v} R) q
    have : DerivedCategory.TStructure.t.IsGE (Stacks0BZE.unitObject.{u, v} R) 0 :=
      inferInstanceAs (DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{max v u} R))) 0)
    have := DerivedCategory.TStructure.t.isGE_shift
      (Stacks0BZE.unitObject.{u, v} R) 0 q (-q) (by omega)
    have h : ∀ x, e x = 0 := fun x => DerivedCategory.TStructure.t.zero (e x) 0 (-q) (by omega)
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => e.injective ((h x).trans (h y).symm)⟩
  · lift q to ℕ using (by omega : 0 ≤ q) with n
    let e := derivedHomHomologyEquivExt.{u, v} (R := R) (A := A) n
    have h : ∀ y : Abelian.Ext (ModuleCat.of R (ULift.{v} A))
        (ModuleCat.of R (ULift.{max v u} R)) n, y = 0 := by
      intro y
      match n with
      | 0 => exact extZero_eq_zero.{u, v} hf hI y
      | 1 => exact absurd rfl hq
      | (m + 2) => exact extSuccSucc_eq_zero.{u, v} hf hI m y
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun x y => e.injective ((h (e x)).trans (h (e y)).symm)⟩

/-- **`H^1(RHom_R(A, R)) ≅ N`.** -/
def derivedHomHomologyOneIso (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 1).obj
        ((Dualizing.derivedHom.{u, v} (algebraMap R A)).obj
          (Stacks0BZE.unitObject.{u, v} R)) ≅
      ModuleCat.of A (conormalInverse.{u, v} R A) :=
  (linearEquivOfSurjectiveRestriction (algebraMap R A) hf _
    (ModuleCat.of A (conormalInverse.{u, v} R A))
    (((derivedHomHomologyEquivExt.{u, v} (R := R) (A := A) 1).trans
      (extOneEquivConormalInverse.{u, v} hf hI)).trans
        (restrictScalarsIdEquiv.{u, v} (conormalInverse.{u, v} R A)
          (fun r φ => LinearMap.ext fun z => Algebra.smul_def r (φ z))).symm)).toModuleIso

/-- **Stacks 0BZH, the computation at the free module of rank one.** For a surjection `R → A`
whose kernel `I` is invertible, `RHom_R(A, R)` is the single complex on `N` in degree one, that
is `N[-1]`, where `N` is the inverse of the invertible `A`-module `I ⊗_R A`. -/
def derivedHomUnitObjectIsoSingle (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A))) :
    (Dualizing.derivedHom.{u, v} (algebraMap R A)).obj (Stacks0BZE.unitObject.{u, v} R) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 1).obj
        (ModuleCat.of A (conormalInverse.{u, v} R A)) := by
  apply Classical.choice
  set D := (Dualizing.derivedHom.{u, v} (algebraMap R A)).obj
    (Stacks0BZE.unitObject.{u, v} R) with hD
  have hLE : D.IsLE 1 := (DerivedCategory.isLE_iff D 1).2 fun q hq =>
    derivedHomHomology_isZero_of_ne_one.{u, v} hf hI q (by omega)
  have hGE : D.IsGE 1 := (DerivedCategory.isGE_iff D 1).2 fun q hq =>
    derivedHomHomology_isZero_of_ne_one.{u, v} hf hI q (by omega)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D 1
  let eY : Y ≅ ModuleCat.of A (conormalInverse.{u, v} R A) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max v u} A) 1).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 1).mapIso e.symm ≪≫
        derivedHomHomologyOneIso.{u, v} hf hI
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 1).mapIso eY⟩

end Derived

/-! ### Stacks 0BZH: `RHom_R(A, -)` is `- ⊗^L_R N[-1]` -/

noncomputable section Tensor

attribute [local instance] HasDerivedCategory.standard

open CochainComplex CochainComplex.DerivedTensor

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **Stacks 0BYK, in bundle form.** A quasi-isomorphism of right tensor factors induces an
isomorphism of the derived change-of-rings tensor functors. -/
def derivedTensorIsoOfQuasiIso (f : R →+* A)
    {L N : CochainComplex (ModuleCat.{max v u} A) ℤ} (r : L ⟶ N) [QuasiIso r]
    (S : DerivedTensorChangeOfRings f L) (T : DerivedTensorChangeOfRings f N) :
    S.F ≅ T.F := by
  apply Classical.choice
  obtain ⟨t, -, ht⟩ := exists_derivedTensorNatTrans_isIso_of_quasiIso f r S.F T.F
    S.directCounit T.directCounit
  have := ht (by assumption)
  exact ⟨asIso t⟩

/-- An isomorphism in the derived category of the right tensor factors is enough: it is a right
fraction of quasi-isomorphisms, and both legs transport the derived tensor functor. -/
def derivedTensorIsoOfDerivedIso (f : R →+* A)
    {L N : CochainComplex (ModuleCat.{max v u} A) ℤ}
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj N)
    (S : DerivedTensorChangeOfRings f L) (T : DerivedTensorChangeOfRings f N) :
    S.F ≅ T.F := by
  apply Classical.choice
  obtain ⟨P, s, hs, r, he⟩ := DerivedCategory.right_fac e.hom
  have hqs : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
  have hr : IsIso (DerivedCategory.Q.map r) := by
    have h : DerivedCategory.Q.map r = DerivedCategory.Q.map s ≫ e.hom := by
      rw [he, IsIso.hom_inv_id_assoc]
    rw [h]
    infer_instance
  have hqr : QuasiIso r := (DerivedCategory.isIso_Q_map_iff_quasiIso _ r).1 hr
  let U := canonicalDerivedTensorChangeOfRings f P
  exact ⟨(derivedTensorIsoOfQuasiIso f s U S).symm ≪≫ derivedTensorIsoOfQuasiIso f r U T⟩

variable (R A)

/-- `N[-1]`: the single complex on `N` in degree zero, shifted by `-1`. -/
abbrev conormalInverseShift : CochainComplex (ModuleCat.{max v u} A) ℤ :=
  ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A (conormalInverse.{u, v} R A)))⟦(-1 : ℤ)⟧

/-- In the derived category, `N[-1]` is the single object on `N` in degree one. -/
def conormalInverseShiftIso :
    DerivedCategory.Q.obj (conormalInverseShift.{u, v} R A) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 1).obj
        (ModuleCat.of A (conormalInverse.{u, v} R A)) :=
  DerivedCategory.Q.mapIso
    (((CochainComplex.singleFunctors (ModuleCat.{max v u} A)).shiftIso (-1) 1 0
      (by omega)).app (ModuleCat.of A (conormalInverse.{u, v} R A)))

variable {R A}

/-- **Stacks 0BZH.** Let `R → A` be a surjective homomorphism of commutative rings whose kernel
`I` is an invertible `R`-module, and let `N = Hom_A(I ⊗_R A, A)` be the inverse of the invertible
`A`-module `I ⊗_R A`. Then the functor `RHom_R(A, -) : D(R) ⥤ D(A)` is isomorphic to
`K ↦ K ⊗^L_R N[-1]`, for any model `T` of the derived change-of-rings tensor product with the
complex `N[-1]`.

The hypothesis `hBZE` is Stacks 0BZE in the shape
`StacksFrontier/RingTheory/Dualizing/TrivialDualityKFlat.lean` reduces it to: invertibility of
`Stacks0BZE.comparison`, the transpose under Stacks 0A70 of the tensored derived counit, at every
K-flat complex. That is a statement about a specific map and is stronger than an abstract
isomorphism of the two functors, so it is an input here rather than a consequence of the
abstract forms of the tag. Everything else — that `A` admits the two-term resolution, that
`I ⊗_R A` is invertible with inverse `N`, and that `RHom_R(A, R)` is `N[-1]` — is proved here, at
every module universe.

The conclusion itself needs no input beyond the surjectivity and invertibility above, at every
module universe, by
`nonempty_derivedHom_iso_derivedTensor_conormalInverseShift_anyModuleUniverse` of
`StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernelAnyModuleUniverse`, which runs
this same chain with the abstract form of Stacks 0BZE in place of the comparison and so gives a
`Nonempty` rather than data. This statement is what turns the comparison, where it is known to be
invertible, into the isomorphism itself. -/
def derivedHomIsoDerivedTensorConormalInverseShift
    (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A)))
    (hBZE : ∀ (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
      (hK : CochainComplex.KFlat.{u, max v u} K),
      IsIso (Stacks0BZE.comparison.{u, v} (algebraMap R A) K hK))
    (T : DerivedTensorChangeOfRings (algebraMap R A) (conormalInverseShift.{u, v} R A)) :
    Dualizing.derivedHom.{u, v} (algebraMap R A) ≅ T.F :=
  Stacks0BZE.cardIso.{u, v} (algebraMap R A) hBZE ≪≫
    derivedTensorIsoOfDerivedIso (algebraMap R A)
      (Stacks0BZE.dualComplexIso.{u, v} (algebraMap R A) ≪≫
        derivedHomUnitObjectIsoSingle.{u, v} hf hI ≪≫
        (conormalInverseShiftIso.{u, v} R A).symm)
      (Stacks0BZE.bundle.{u, v} (algebraMap R A)) T

/-- **Stacks 0BZH at the canonical model of the derived tensor product.** The hypothesis on the
derived tensor model in `derivedHomIsoDerivedTensorConormalInverseShift` is dischargeable: the
canonical change-of-rings bundle of Stacks 06Y6 is one. -/
def derivedHomIsoCanonicalDerivedTensorConormalInverseShift
    (hf : Function.Surjective (algebraMap R A))
    (hI : Module.Invertible R (RingHom.ker (algebraMap R A)))
    (hBZE : ∀ (K : CochainComplex (ModuleCat.{max v u} R) ℤ)
      (hK : CochainComplex.KFlat.{u, max v u} K),
      IsIso (Stacks0BZE.comparison.{u, v} (algebraMap R A) K hK)) :
    Dualizing.derivedHom.{u, v} (algebraMap R A) ≅
      (canonicalDerivedTensorChangeOfRings (algebraMap R A)
        (conormalInverseShift.{u, v} R A)).F :=
  derivedHomIsoDerivedTensorConormalInverseShift.{u, v} hf hI hBZE _

end Tensor

/-! ### The hypotheses are satisfiable

A quotient by a nonzerodivisor is a surjection with invertible kernel, so the hypotheses of
Stacks 0BZH hold for every such quotient — for instance `k[x] → k[x]/(x) = k`, or `ℤ → ℤ/2ℤ`. -/

noncomputable section Examples

variable {R : Type u} [CommRing R]

/-- A principal ideal generated by a nonzerodivisor is free of rank one. -/
def spanSingletonEquiv (x : R) (hx : ∀ r : R, r * x = 0 → r = 0) :
    R ≃ₗ[R] (Ideal.span {x} : Submodule R R) :=
  LinearEquiv.ofBijective
    ({ toFun := fun r => ⟨r * x, Ideal.mem_span_singleton.2 (dvd_mul_left x r)⟩
       map_add' := fun r s => Subtype.ext (add_mul r s x)
       map_smul' := fun r s => Subtype.ext (mul_assoc r s x) } : R →ₗ[R] _)
    ⟨fun r s h => by
      refine sub_eq_zero.mp (hx (r - s) ?_)
      rw [sub_mul, (by exact congrArg Subtype.val h : r * x = s * x), sub_self],
     fun y => by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 y.2
      exact ⟨c, Subtype.ext ((mul_comm c x).trans hc.symm)⟩⟩

/-- A principal ideal generated by a nonzerodivisor is an invertible module. -/
theorem invertible_span_singleton (x : R) (hx : ∀ r : R, r * x = 0 → r = 0) :
    Module.Invertible R (Ideal.span {x} : Submodule R R) :=
  Module.Invertible.congr (spanSingletonEquiv x hx)

/-- **The hypotheses of Stacks 0BZH hold for a quotient by a nonzerodivisor.** -/
theorem surjective_and_invertible_ker_quotient (x : R) (hx : ∀ r : R, r * x = 0 → r = 0) :
    Function.Surjective (algebraMap R (R ⧸ Ideal.span {x})) ∧
      Module.Invertible R (RingHom.ker (algebraMap R (R ⧸ Ideal.span {x}))) := by
  have hker : RingHom.ker (algebraMap R (R ⧸ Ideal.span {x})) = Ideal.span {x} :=
    Ideal.mk_ker
  exact ⟨Ideal.Quotient.mk_surjective, Module.Invertible.congr
    ((spanSingletonEquiv x hx).trans (LinearEquiv.ofEq _ _ hker.symm))⟩

/-- `ℤ → ℤ/2ℤ` is a surjection with invertible kernel, the arithmetic analogue of
`k[x] → k[x]/(x)`: Stacks 0BZH applies to it. -/
theorem surjective_and_invertible_ker_int_quotient :
    Function.Surjective (algebraMap ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)})) ∧
      Module.Invertible ℤ (RingHom.ker (algebraMap ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}))) :=
  surjective_and_invertible_ker_quotient (2 : ℤ) (fun r hr => by omega)

end Examples

end Dualizing.InvertibleKernel

end
