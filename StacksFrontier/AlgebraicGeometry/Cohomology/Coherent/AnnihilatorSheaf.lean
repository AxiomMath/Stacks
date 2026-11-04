module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Annihilator
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap

/-!
# Annihilators along an exact sequence of sheaves of modules, before and after reduction

Let `a : M ⟶ N` be a morphism of quasi-coherent `𝒪_X`-modules and let `𝒦 ⊆ 𝒪_X` be a
quasi-coherent ideal sheaf whose power `𝒦 ᵗ` annihilates both `Ker(a)` and `Coker(a)`. The remark
of [Stacks, Tag 0888] says that `𝒦 ²ᵗ` then annihilates the kernel and the cokernel of the map
`M / ℐ ⁿ M ⟶ N / ℐ ⁿ N`
induced on the quotients by any other quasi-coherent ideal sheaf `ℐ`. This file carries that
remark over sheaves of modules;
`StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/Annihilator.lean` carries it over modules over
a commutative ring, and is what the proof here reduces to.

The reduction is affine-local. Over an affine open `U` the four-term sequence
`Γ(Ker a, U) ⟶ Γ(M, U) ⟶ Γ(N, U) ⟶ Γ(Coker a, U)`
is exact — at `Γ(M, U)` because evaluation preserves kernels, at `Γ(N, U)` by
`Stacks.Algebraization.affine_sections_cokernel_exact` — and its two end modules are annihilated
by `𝒦(U) ᵗ`, so `Ideal.existsUnique_canonicalMap_of_smul_eq_bot` supplies, for `f, g ∈ 𝒦(U) ᵗ`,
the lift-and-multiply map `c : Γ(N, U) ⟶ Γ(M, U)` with `c ∘ a = f g`. The kernel clause follows
because `c` carries `ℐ(U) ⁿ Γ(N, U)` into `ℐ(U) ⁿ Γ(M, U)`; the cokernel clause does not need `c`
at all, only the exactness at `Γ(N, U)`.

## Main results

* `Stacks.Algebraization.injective_app_of_mono` — a monomorphism of sheaves of modules is
  injective on the sections over any open.
* `Stacks.Algebraization.sections_exact_kernel` — the sections of a kernel over any open are the
  sections killed by the morphism.
* `Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap` — **the remark
  of Tag 0888 over sheaves of modules**: annihilation of `Ker(a)` and `Coker(a)` by `𝒦 ᵗ` gives
  annihilation of the kernel and the cokernel of `M / ℐ ⁿ M ⟶ N / ℐ ⁿ N` by `𝒦 ²ᵗ`.

## Implementation notes

The hypotheses are quasi-coherence of `M` and of `N`, not coherence, and no Noetherian hypothesis
on `X` is needed: everything used is the affine-local description of `ℐ ⁿ M` and the exactness of
the sections functor on an affine open. The source's `t ≥ 1` is not assumed either, since the
argument never divides by `t`.

The ambient module `M / ℐ ⁿ M` is `Stacks.Algebraization.idealPowerQuotient`, the cokernel of the
inclusion of `Stacks.Algebraization.idealPowerMultiple`, and the induced map is
`Stacks.Algebraization.idealPowerQuotientMap`, whose only computation rule is
`idealPowerQuotientMap_π`. Annihilation of a sheaf of modules by a power is translated into the
elementwise affine-local statement by
`Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_sections_annihilated`, and the step
from an exponent `2 t` to a product of two elements of `𝒦(U) ᵗ` is `Ideal.mul_le` applied to the
annihilator ideal of the module of sections.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

attribute [local instance] monoSubmoduleι

/-! ### Sections of kernels and of quotients -/

/-- A monomorphism of sheaves of modules is injective on the sections over any open.

Evaluation at an open preserves finite limits, hence monomorphisms, and a monomorphism of modules
is an injection. -/
public theorem injective_app_of_mono {M N : X.Modules} (f : M ⟶ N)
    [Mono (C := X.Modules) f] (U : X.Opens) :
    Function.Injective (f.app U) := by
  let T : X.Modules ⥤ ModuleCat Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : T.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let _ : PreservesFiniteLimits T :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U)
  exact (ModuleCat.mono_iff_injective (T.map f)).1 inferInstance

/-- **The sections of a kernel.** Over any open the sections of `Ker(f)` are exactly the sections
of the source which `f` kills.

One direction is `Stacks.Algebraization.exists_kernel_section`, the other the defining equation
`Ker(f) ⟶ M ⟶ N = 0`. -/
public theorem sections_exact_kernel {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    Function.Exact (ModuleCat.Hom.hom ((kernel.ι (C := X.Modules) f).val.app (op U)))
      (ModuleCat.Hom.hom (f.val.app (op U))) := by
  intro x
  refine ⟨exists_kernel_section f U x, ?_⟩
  rintro ⟨y, rfl⟩
  exact congrArg (fun g : kernel (C := X.Modules) f ⟶ N => g.app U y)
    (kernel.condition (C := X.Modules) f)

/-! ### The remark of Tag 0888 over sheaves of modules -/

/-- Over any open, the square of sections induced by `idealPowerQuotientMap_π` commutes. -/
private theorem app_idealPowerQuotientMap_app_π (I : X.IdealSheafData) {M N : X.Modules}
    (a : M ⟶ N) (n : ℕ) (U : X.Opens) (x : Γ(M, U)) :
    ModuleCat.Hom.hom ((idealPowerQuotientMap I I n n le_rfl a).val.app (op U))
        (ModuleCat.Hom.hom ((cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι).val.app
          (op U)) x) =
      ModuleCat.Hom.hom ((cokernel.π (C := X.Modules) (idealPowerMultiple I n N).ι).val.app
        (op U)) (ModuleCat.Hom.hom (a.val.app (op U)) x) :=
  congrArg (fun g : M ⟶ idealPowerQuotient I n N => g.val.app (op U) x)
    (idealPowerQuotientMap_π I I n n le_rfl a)

/-- If `𝒦(U) ᵗ 𝒦(U) ᵗ` annihilates the sections over every affine open `U`, then `𝒦 ²ᵗ` kills
the sheaf. -/
private theorem idealPowerMultiple_two_mul_eq_bot_of_mul_le_annihilator (K : X.IdealSheafData)
    {t : ℕ} {P : X.Modules}
    (h : ∀ U : X.affineOpens, K.ideal U ^ t * K.ideal U ^ t ≤ Module.annihilator Γ(X, U) Γ(P, U)) :
    idealPowerMultiple K (2 * t) P = ⊥ :=
  (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated K (2 * t) _).2 fun U _ hr w =>
    Module.mem_annihilator.1 (h U (by rwa [← pow_add, ← two_mul])) w

/-- Over an affine open `U`, if `𝒦 ᵗ` annihilates `Ker(a)` and `Coker(a)`, then `𝒦(U) ᵗ 𝒦(U) ᵗ`
annihilates the sections of the kernel of `M / ℐ ⁿ M ⟶ N / ℐ ⁿ N`. -/
public theorem pow_mul_pow_le_annihilator_kernel_idealPowerQuotientMap
    (I K : X.IdealSheafData) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) {t : ℕ}
    (hk : idealPowerMultiple K t (kernel (C := X.Modules) a) = ⊥)
    (hc : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥) (n : ℕ) (U : X.affineOpens) :
    K.ideal U ^ t * K.ideal U ^ t ≤ Module.annihilator Γ(X, U)
      Γ(kernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a), U) := by
  refine Ideal.mul_le.2 fun f hf g hg => Module.mem_annihilator.2 fun z => ?_
  let iU : Γ(kernel (C := X.Modules) a, U) →ₗ[Γ(X, U)] Γ(M, U) :=
    ModuleCat.Hom.hom ((kernel.ι (C := X.Modules) a).val.app (op U.1))
  let aU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := ModuleCat.Hom.hom (a.val.app (op U.1))
  let pU : Γ(N, U) →ₗ[Γ(X, U)] Γ(cokernel (C := X.Modules) a, U) :=
    ModuleCat.Hom.hom ((cokernel.π (C := X.Modules) a).val.app (op U.1))
  let qMU : Γ(M, U) →ₗ[Γ(X, U)] Γ(idealPowerQuotient I n M, U) :=
    ModuleCat.Hom.hom
      ((cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι).val.app (op U.1))
  let qNU : Γ(N, U) →ₗ[Γ(X, U)] Γ(idealPowerQuotient I n N, U) :=
    ModuleCat.Hom.hom
      ((cokernel.π (C := X.Modules) (idealPowerMultiple I n N).ι).val.app (op U.1))
  let aqU : Γ(idealPowerQuotient I n M, U) →ₗ[Γ(X, U)] Γ(idealPowerQuotient I n N, U) :=
    ModuleCat.Hom.hom ((idealPowerQuotientMap I I n n le_rfl a).val.app (op U.1))
  let ιU : Γ(kernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a), U) →ₗ[Γ(X, U)]
      Γ(idealPowerQuotient I n M, U) :=
    ModuleCat.Hom.hom
      ((kernel.ι (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)).val.app (op U.1))
  have hsq : ∀ x : Γ(M, U), aqU (qMU x) = qNU (aU x) :=
    app_idealPowerQuotientMap_app_π I a n U.1
  obtain ⟨c, hcspec, -⟩ := Ideal.existsUnique_canonicalMap_of_smul_eq_bot iU aU pU
    (sections_exact_kernel a U.1) (affine_sections_cokernel_exact a U) (K.ideal U ^ t)
    (affine_smul_top_eq_bot_of_idealPowerMultiple_eq_bot hk U)
    (affine_smul_top_eq_bot_of_idealPowerMultiple_eq_bot hc U) hf hg
  obtain ⟨x, hx⟩ :=
    surjective_app_of_epi_of_isAffineOpen
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι) U (ιU z)
  have hx' : qMU x = ιU z := hx
  have hzero : aqU (qMU x) = 0 := by
    rw [hx']
    exact congrArg
      (fun g : kernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a) ⟶
        idealPowerQuotient I n N => g.val.app (op U.1) z)
      (kernel.condition (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a))
  have hax : aU x ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(N, U)) := by
    rw [← idealPowerMultiple_toSubmodule_obj_affine I n N U]
    exact (cokernel_π_app_eq_zero_iff N (idealPowerMultiple I n N) U.1 (aU x)).1
      ((hsq x).symm.trans hzero)
  have hcle : I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(N, U)) ≤
      Submodule.comap c (I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U))) :=
    Submodule.smul_le.2 fun j hj y _ => by
      rw [Submodule.mem_comap, c.map_smul]
      exact Submodule.smul_mem_smul hj Submodule.mem_top
  have hmem : (f * g) • x ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) := by
    have hcomp : c (aU x) = (f * g) • x := LinearMap.congr_fun hcspec.2 x
    exact hcomp ▸ Submodule.mem_comap.1 (hcle hax)
  have hinj : Function.Injective ιU :=
    injective_app_of_mono
      (kernel.ι (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) U.1
  apply hinj
  rw [map_zero, LinearMap.map_smul, ← hx', ← LinearMap.map_smul]
  exact (cokernel_π_app_eq_zero_iff M (idealPowerMultiple I n M) U.1 ((f * g) • x)).2
    (by rwa [idealPowerMultiple_toSubmodule_obj_affine I n M U])

/-- If `𝒦 ᵗ` annihilates `Ker(a)` and `Coker(a)`, then `𝒦 ²ᵗ` annihilates the kernel of the induced
map `M / ℐ ⁿ M ⟶ N / ℐ ⁿ N`. -/
public theorem idealPowerMultiple_kernel_idealPowerQuotientMap
    (I K : X.IdealSheafData) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) {t : ℕ}
    (hk : idealPowerMultiple K t (kernel (C := X.Modules) a) = ⊥)
    (hc : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥) (n : ℕ) :
    idealPowerMultiple K (2 * t)
      (kernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) = ⊥ :=
  idealPowerMultiple_two_mul_eq_bot_of_mul_le_annihilator K
    (pow_mul_pow_le_annihilator_kernel_idealPowerQuotientMap I K a hk hc n)

/-- If `𝒦 ᵗ` annihilates `Coker(a)`, then `𝒦 ²ᵗ` annihilates the cokernel of the induced map
`M / ℐ ⁿ M ⟶ N / ℐ ⁿ N`. -/
public theorem idealPowerMultiple_cokernel_idealPowerQuotientMap
    (I K : X.IdealSheafData) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) {t : ℕ}
    (hc : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥) (n : ℕ) :
    idealPowerMultiple K (2 * t)
      (cokernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) = ⊥ := by
  refine idealPowerMultiple_two_mul_eq_bot_of_mul_le_annihilator K fun U => ?_
  refine Ideal.mul_le.2 fun f hf g hg => Module.mem_annihilator.2 fun z => ?_
  let aU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := ModuleCat.Hom.hom (a.val.app (op U.1))
  let pU : Γ(N, U) →ₗ[Γ(X, U)] Γ(cokernel (C := X.Modules) a, U) :=
    ModuleCat.Hom.hom ((cokernel.π (C := X.Modules) a).val.app (op U.1))
  let qMU : Γ(M, U) →ₗ[Γ(X, U)] Γ(idealPowerQuotient I n M, U) :=
    ModuleCat.Hom.hom
      ((cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι).val.app (op U.1))
  let qNU : Γ(N, U) →ₗ[Γ(X, U)] Γ(idealPowerQuotient I n N, U) :=
    ModuleCat.Hom.hom
      ((cokernel.π (C := X.Modules) (idealPowerMultiple I n N).ι).val.app (op U.1))
  let aqU : Γ(idealPowerQuotient I n M, U) →ₗ[Γ(X, U)] Γ(idealPowerQuotient I n N, U) :=
    ModuleCat.Hom.hom ((idealPowerQuotientMap I I n n le_rfl a).val.app (op U.1))
  let πU : Γ(idealPowerQuotient I n N, U) →ₗ[Γ(X, U)]
      Γ(cokernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a), U) :=
    ModuleCat.Hom.hom
      ((cokernel.π (C := X.Modules)
        (idealPowerQuotientMap I I n n le_rfl a)).val.app (op U.1))
  have hsq : ∀ x : Γ(M, U), aqU (qMU x) = qNU (aU x) :=
    app_idealPowerQuotientMap_app_π I a n U.1
  obtain ⟨v, hv⟩ :=
    surjective_app_of_epi_of_isAffineOpen
      (cokernel.π (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) U z
  have hv' : πU v = z := hv
  obtain ⟨y, hy⟩ :=
    surjective_app_of_epi_of_isAffineOpen
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n N).ι) U v
  have hy' : qNU y = v := hy
  have hfy : pU (f • y) = 0 := by
    rw [LinearMap.map_smul]
    exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot hc U hf (pU y)
  obtain ⟨x, hx⟩ := (affine_sections_cokernel_exact a U _).1 hfy
  have hx' : aU x = f • y := hx
  have hgx : aU (g • x) = (f * g) • y := by
    rw [LinearMap.map_smul, hx', smul_smul, mul_comm]
  have hrange : aqU (qMU (g • x)) = (f * g) • v := by
    rw [hsq (g • x), hgx, ← hy', LinearMap.map_smul]
  rw [← hv', ← LinearMap.map_smul, ← hrange]
  exact (affine_sections_cokernel_exact
    (idealPowerQuotientMap I I n n le_rfl a) U _).2 ⟨qMU (g • x), rfl⟩

/-- Let `a : M ⟶ N` be a morphism of quasi-coherent `𝒪_X`-modules whose kernel and cokernel are
annihilated by `𝒦 ᵗ`, and let `ℐ` be any quasi-coherent ideal sheaf. Then `𝒦 ²ᵗ` annihilates both
the kernel and the cokernel of the induced map `M / ℐ ⁿ M ⟶ N / ℐ ⁿ N`.

This is the sheaf-of-modules form of `Ideal.pow_le_annihilator_ker_mapQ_of_exact` and
`Ideal.pow_le_annihilator_coker_mapQ_of_exact`. -/
@[stacks 0888 "annihilation_mod_ideal, over sheaves of modules"]
public theorem idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap
    (I K : X.IdealSheafData) {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) {t : ℕ}
    (hk : idealPowerMultiple K t (kernel (C := X.Modules) a) = ⊥)
    (hc : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥) (n : ℕ) :
    idealPowerMultiple K (2 * t)
        (kernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) = ⊥ ∧
      idealPowerMultiple K (2 * t)
        (cokernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) = ⊥ :=
  ⟨idealPowerMultiple_kernel_idealPowerQuotientMap I K a hk hc n,
    idealPowerMultiple_cokernel_idealPowerQuotientMap I K a hc n⟩

end Stacks.Algebraization

end
