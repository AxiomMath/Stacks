module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Recognising quasi-isomorphisms by their kernels

In an abelian category, an epimorphism of cochain complexes with acyclic kernel is a
quasi-isomorphism: the long exact sequence of the kernel sequence makes the induced map on
cohomology both a monomorphism and an epimorphism. Pulling a complex back along an epimorphic
quasi-isomorphism therefore produces a quasi-isomorphism again, because the kernel of the
projection from the pullback is the kernel of the quasi-isomorphism.

## Main results

* `Stacks.KernelQuasiIso.quasiIso_of_epi_of_acyclic_kernel`: an epimorphism with acyclic kernel
  is a quasi-isomorphism.
* `Stacks.KernelQuasiIso.pullback_fst_quasiIso_of_epi`: the first projection of the pullback of
  an arbitrary morphism along an epimorphic quasi-isomorphism is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.KernelQuasiIso

/-- The kernel sequence of an epimorphism in an abelian category is short exact. -/
theorem kernelSequence_shortExact
    {category : Type*} [Category* category] [Abelian category]
    {source target : category} (morphism : source ⟶ target) [Epi morphism] :
    (ShortComplex.kernelSequence morphism).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact morphism)
    inferInstance (inferInstanceAs (Epi morphism))

/-- An epimorphism of cochain complexes whose kernel is acyclic is a quasi-isomorphism. -/
theorem quasiIso_of_epi_of_acyclic_kernel
    {category : Type*} [Category* category] [Abelian category]
    {source target : CochainComplex category ℤ} (morphism : source ⟶ target)
    [Epi morphism] (vanishing : (kernel morphism).Acyclic) : QuasiIso morphism := by
  have sequenceExact := kernelSequence_shortExact morphism
  rw [quasiIso_iff]
  intro degree
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have mono : Mono (HomologicalComplex.homologyMap morphism degree) :=
    (sequenceExact.homology_exact₂ degree).mono_g
      ((vanishing degree).isZero_homology.eq_zero_of_src _)
  have epi : Epi (HomologicalComplex.homologyMap morphism degree) :=
    (sequenceExact.homology_exact₃ degree (degree + 1) (by simp)).epi_f
      ((vanishing (degree + 1)).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- Pulling a morphism of cochain complexes back along an epimorphic quasi-isomorphism gives a
quasi-isomorphism: the two kernels agree. -/
theorem pullback_fst_quasiIso_of_epi
    {category : Type*} [Category* category] [Abelian category]
    {source cover target : CochainComplex category ℤ}
    (morphism : source ⟶ target) (resolution : cover ⟶ target)
    [Epi resolution] [QuasiIso resolution] :
    QuasiIso (pullback.fst morphism resolution) := by
  let comparison : kernel (pullback.fst morphism resolution) ⟶ kernel resolution :=
    kernel.map (pullback.fst morphism resolution) resolution
      (pullback.snd morphism resolution) morphism pullback.condition
  have : IsIso comparison :=
    isIso_kernel_map_of_isPullback (IsPullback.of_hasPullback morphism resolution)
  have vanishing : (kernel resolution).Acyclic :=
    (kernelSequence_shortExact resolution).acyclic_X₁
      (inferInstanceAs (QuasiIso resolution))
  exact quasiIso_of_epi_of_acyclic_kernel _ fun degree =>
    HomologicalComplex.ExactAt.of_iso (vanishing degree) (asIso comparison).symm

end Stacks.KernelQuasiIso
