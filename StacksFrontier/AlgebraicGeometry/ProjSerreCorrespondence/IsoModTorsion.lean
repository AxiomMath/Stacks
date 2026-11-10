module

public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.IrrelevantQuotientFunctor

/-!
# Recognizing an isomorphism modulo the torsion subcategory on elements

Let `A` be a Noetherian graded ring and `φ : M ⟶ N` a morphism of finitely generated graded
`A`-modules. The morphism `φ` becomes an isomorphism in the quotient category
`Mod^fg_A / Mod^fg_{A, torsion}` exactly when its kernel and cokernel are irrelevant. This file
gives elementwise criteria for both:

* the kernel is irrelevant as soon as every homogeneous element of `M` killed by `φ` is killed by
  every homogeneous scalar of large enough degree;
* the cokernel is irrelevant as soon as every homogeneous element of `N` is carried into the image
  of `φ` by every homogeneous scalar of large enough degree.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIrrelevant_kernel_of_annihilated`: the
  kernel criterion.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIrrelevant_cokernel_of_mem_range`: the
  cokernel criterion.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isoModSerre_of_annihilated_of_mem_range`:
  the two together, giving that `φ` is an isomorphism modulo the torsion subcategory.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIso_toIrrelevantQuotient_map_of_elements`:
  the quotient functor then sends `φ` to an isomorphism.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 0BXE](https://stacks.math.columbia.edu/tag/0BXE)
* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DirectSum
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The uniform annihilation shape `∃ N, ∀ k ≥ N, ∀ a ∈ 𝒜 k, a • x = 0` implies irrelevance of
the element in the sense of Tag 0BXE at generation degree one. -/
private theorem isIrrelevantElement_of_annihilated {M : GradedModuleCat.{u, u, w} 𝒜} {i : ℤ}
    {x : M.carrier} (h : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ a ∈ 𝒜 k, a • x = 0) :
    IsIrrelevantElement 𝒜 1 M i x := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + i.toNat, fun n hn k hk hki a ha => hN k ?_ a ha⟩
  have hi : i ≤ (i.toNat : ℤ) := Int.self_le_toNat i
  have hn' : ((N + i.toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  push_cast at hn' hki
  lia

/-- **The kernel of a morphism of finitely generated graded modules is irrelevant** as soon as
every homogeneous element of the source which the morphism kills is annihilated by every
homogeneous scalar of large enough degree. -/
theorem isIrrelevant_kernel_of_annihilated {M N : FiniteGradedModules.{u, u, w} 𝒜} (φ : M ⟶ N)
    (hker : ∀ (i : ℤ) (y : M.obj.carrier), y ∈ M.obj.grade i → φ.hom.toLinearMap y = 0 →
      ∃ P : ℕ, ∀ k : ℕ, P ≤ k → ∀ a ∈ 𝒜 k, a • y = 0) :
    irrelevantModules.{u, u, w} 𝒜 1 (kernel φ) := by
  have := isSerreClass_moduleFinite.{u, u, w} 𝒜
  intro i x hx
  have hinj := injective_of_mono_finite 𝒜 (kernel.ι φ)
  have hmem : (kernel.ι φ).hom.toLinearMap x ∈ M.obj.grade i := (kernel.ι φ).hom.map_grade i x hx
  have hzero : φ.hom.toLinearMap ((kernel.ι φ).hom.toLinearMap x) = 0 :=
    congrArg (fun k : kernel φ ⟶ N => k.hom.toLinearMap x) (kernel.condition φ)
  obtain ⟨P, hP⟩ := hker i _ hmem hzero
  refine isIrrelevantElement_of_annihilated 𝒜 ⟨P, fun k hk a ha => hinj ?_⟩
  rw [map_zero, map_smul]
  exact hP k hk a ha

/-- **The cokernel of a morphism of finitely generated graded modules is irrelevant** as soon as
every homogeneous element of the target is carried into the image of the morphism by every
homogeneous scalar of large enough degree. -/
theorem isIrrelevant_cokernel_of_mem_range {M N : FiniteGradedModules.{u, u, w} 𝒜} (φ : M ⟶ N)
    (hcoker : ∀ (i : ℤ) (t : N.obj.carrier), t ∈ N.obj.grade i →
      ∃ P : ℕ, ∀ k : ℕ, P ≤ k → ∀ a ∈ 𝒜 k,
        ∃ m : M.obj.carrier, a • t = φ.hom.toLinearMap m) :
    irrelevantModules.{u, u, w} 𝒜 1 (cokernel φ) := by
  have := isSerreClass_moduleFinite.{u, u, w} 𝒜
  intro i c hc
  have hsurj := surjective_of_epi_finite 𝒜 (cokernel.π φ)
  obtain ⟨t, ht⟩ := hsurj c
  have hd := Stacks.GradedModule.decompose_apply_map (ℳ := N.obj.grade)
    (𝒩 := (cokernel φ).obj.grade)
    (cokernel.π φ).hom.toLinearMap.toAddMonoidHom
    (fun j z hz => (cokernel.π φ).hom.map_grade j z hz) t i
  have ht' : (cokernel.π φ).hom.toLinearMap.toAddMonoidHom t = c := ht
  have hti : (cokernel.π φ).hom.toLinearMap
      ((DirectSum.decompose N.obj.grade t i : N.obj.carrier)) = c := by
    change (cokernel.π φ).hom.toLinearMap.toAddMonoidHom _ = c
    rw [← hd, ht']
    exact DirectSum.decompose_of_mem_same (cokernel φ).obj.grade hc
  obtain ⟨P, hP⟩ := hcoker i _ (DirectSum.decompose N.obj.grade t i).2
  refine isIrrelevantElement_of_annihilated 𝒜 ⟨P, fun k hk a ha => ?_⟩
  obtain ⟨m, hm⟩ := hP k hk a ha
  have hcomp : (cokernel.π φ).hom.toLinearMap (φ.hom.toLinearMap m) = 0 :=
    congrArg (fun g : M ⟶ cokernel φ => g.hom.toLinearMap m) (cokernel.condition φ)
  rwa [← hti, ← map_smul, hm]

/-- **A morphism of finitely generated graded modules is an isomorphism modulo the torsion
subcategory** when its kernel is annihilated and its cokernel reached in large degrees. -/
theorem isoModSerre_of_annihilated_of_mem_range
    {M N : FiniteGradedModules.{u, u, w} 𝒜} (φ : M ⟶ N)
    (hker : ∀ (i : ℤ) (y : M.obj.carrier), y ∈ M.obj.grade i → φ.hom.toLinearMap y = 0 →
      ∃ P : ℕ, ∀ k : ℕ, P ≤ k → ∀ a ∈ 𝒜 k, a • y = 0)
    (hcoker : ∀ (i : ℤ) (t : N.obj.carrier), t ∈ N.obj.grade i →
      ∃ P : ℕ, ∀ k : ℕ, P ≤ k → ∀ a ∈ 𝒜 k,
        ∃ m : M.obj.carrier, a • t = φ.hom.toLinearMap m) :
    haveI := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1)) φ :=
  have := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  ⟨isIrrelevant_kernel_of_annihilated 𝒜 φ hker,
    isIrrelevant_cokernel_of_mem_range 𝒜 φ hcoker⟩

/-- **The quotient functor sends such a morphism to an isomorphism.** -/
theorem isIso_toIrrelevantQuotient_map_of_elements
    {M N : FiniteGradedModules.{u, u, w} 𝒜} (φ : M ⟶ N)
    (hker : ∀ (i : ℤ) (y : M.obj.carrier), y ∈ M.obj.grade i → φ.hom.toLinearMap y = 0 →
      ∃ P : ℕ, ∀ k : ℕ, P ≤ k → ∀ a ∈ 𝒜 k, a • y = 0)
    (hcoker : ∀ (i : ℤ) (t : N.obj.carrier), t ∈ N.obj.grade i →
      ∃ P : ℕ, ∀ k : ℕ, P ≤ k → ∀ a ∈ 𝒜 k,
        ∃ m : M.obj.carrier, a • t = φ.hom.toLinearMap m) :
    IsIso ((toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos).map φ) := by
  have := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  exact Localization.inverts (toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos)
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1)) φ
    (isoModSerre_of_annihilated_of_mem_range 𝒜 φ hker hcoker)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
