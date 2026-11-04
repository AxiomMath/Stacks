module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# An epimorphism of complexes with acyclic kernel is a quasi-isomorphism

Let `𝒜` be an abelian category and `φ : K ⟶ L` an epimorphism of cochain complexes of `𝒜`.
Then `φ` is a quasi-isomorphism exactly when its kernel complex is acyclic.  Mathlib has the
direction that reads the acyclicity off the quasi-isomorphism,
`CategoryTheory.ShortComplex.ShortExact.acyclic_X₁`; this file supplies the other one, which is
how a quasi-isomorphism is *proved* when the map is surjective by construction and the content
sits in the kernel.

## Main results

* `Stacks.Homology.kernelSequence_shortExact`: the kernel sequence of an epimorphism is short
  exact.
* `Stacks.Homology.quasiIso_of_epi_of_acyclic_kernel`: an epimorphism of cochain complexes with
  acyclic kernel is a quasi-isomorphism.
* `Stacks.Homology.quasiIso_iff_acyclic_kernel`: for an epimorphism, quasi-isomorphy and
  acyclicity of the kernel are equivalent.
* `Stacks.Homology.pullback_fst_quasiIso_of_epi`: the base change of a quasi-isomorphism which
  is an epimorphism is again a quasi-isomorphism.

## Implementation notes

The two implications are the two halves of the long exact homology sequence of the kernel
sequence `0 ⟶ ker φ ⟶ K ⟶ L ⟶ 0`: monomorphy of `Hⁿ(φ)` comes from exactness at `Hⁿ(K)` with
`Hⁿ(ker φ) = 0`, and epimorphy from exactness at `Hⁿ(L)` with `Hⁿ⁺¹(ker φ) = 0`.  The
connecting map is only needed to be *zero*, so no computation of it is involved.

For the base change the kernel of `pullback.fst φ ψ` is carried isomorphically onto the kernel
of `ψ` by `CategoryTheory.Limits.isIso_kernel_map_of_isPullback`, so its acyclicity is that of
`ker ψ` transported along an isomorphism.
-/

@[expose] public section

namespace Stacks.Homology

open CategoryTheory CategoryTheory.Limits

/-- The kernel sequence `0 ⟶ ker φ ⟶ K ⟶ L ⟶ 0` of an epimorphism is short exact. -/
public theorem kernelSequence_shortExact {A : Type*} [Category* A] [Abelian A]
    {K L : A} (φ : K ⟶ L) [Epi φ] :
    (ShortComplex.kernelSequence φ).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact φ)
    inferInstance (inferInstanceAs (Epi φ))

/-- **An epimorphism of cochain complexes with acyclic kernel is a quasi-isomorphism.**

This is the half of `CategoryTheory.ShortComplex.ShortExact.acyclic_X₁` that Mathlib does not
state: it is how a comparison map which is surjective by construction is shown to be a
quasi-isomorphism, the whole content being the acyclicity of its kernel. -/
public theorem quasiIso_of_epi_of_acyclic_kernel {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) [Epi φ]
    (hker : (kernel φ).Acyclic) : QuasiIso φ := by
  have hse := kernelSequence_shortExact φ
  refine (quasiIso_iff φ).2 fun n => ?_
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have _hmono : Mono (HomologicalComplex.homologyMap φ n) :=
    (hse.homology_exact₂ n).mono_g ((hker n).isZero_homology.eq_zero_of_src _)
  have _hepi : Epi (HomologicalComplex.homologyMap φ n) :=
    (hse.homology_exact₃ n (n + 1) (by simp)).epi_f
      ((hker (n + 1)).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- For an epimorphism of cochain complexes, being a quasi-isomorphism and having acyclic kernel
are the same condition. -/
public theorem quasiIso_iff_acyclic_kernel {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) [Epi φ] :
    QuasiIso φ ↔ (kernel φ).Acyclic :=
  ⟨fun h => (kernelSequence_shortExact φ).acyclic_X₁ h,
    quasiIso_of_epi_of_acyclic_kernel φ⟩

/-- The base change of a quasi-isomorphism of cochain complexes along a morphism is again a
quasi-isomorphism, provided the quasi-isomorphism is an epimorphism: the kernel of the base
change is carried isomorphically onto the kernel of the original map. -/
public theorem pullback_fst_quasiIso_of_epi {A : Type*} [Category* A] [Abelian A]
    {K C L : CochainComplex A ℤ} (φ : K ⟶ L) (ψ : C ⟶ L) [Epi ψ] [QuasiIso ψ] :
    QuasiIso (pullback.fst φ ψ) := by
  let comparison : kernel (pullback.fst φ ψ) ⟶ kernel ψ :=
    kernel.map (pullback.fst φ ψ) ψ (pullback.snd φ ψ) φ pullback.condition
  have _hiso : IsIso comparison :=
    isIso_kernel_map_of_isPullback (IsPullback.of_hasPullback φ ψ)
  exact quasiIso_of_epi_of_acyclic_kernel _ fun n =>
    HomologicalComplex.ExactAt.of_iso ((quasiIso_iff_acyclic_kernel ψ).1 inferInstance n)
      (asIso comparison).symm

end Stacks.Homology

end
