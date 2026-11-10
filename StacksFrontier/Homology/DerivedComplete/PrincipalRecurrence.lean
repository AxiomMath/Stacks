module

public import Mathlib
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic

/-!
# Derived completeness through the recurrence operator on sequences

Let `A` be a commutative ring, `f : A` and `M` an `A`-module. The *recurrence operator* of `f`
on sequences in `M` is `(aₙ) ↦ (aₙ - f · aₙ₊₁)`. The module `M` is derived complete at `f` — that
is, the complex concentrated in degree zero at `M` satisfies `T(M, f) = 0` — exactly when this
operator is bijective. Bijectivity of a recurrence operator is a two-out-of-three property in a
short exact sequence of modules, so the derived complete modules with respect to an ideal `I` form
a weak Serre subcategory of `ModuleCat A`.

## Main definitions

* `recurrence`: the operator `(aₙ) ↦ (aₙ - f · aₙ₊₁)` on `ℕ → M`, as an `A`-linear map.

## Main results

* `isDerivedCompleteModule_iff_forall_bijective_recurrence`: derived completeness of a module
  with respect to `I` is bijectivity of the recurrence operator of every `f ∈ I`.
* `bijective_recurrence_X₃`, `bijective_recurrence_X₂`, `bijective_recurrence_X₁`: the
  two-out-of-three property of recurrence bijectivity along a short exact sequence.
* `isWeakSerreClass_isDerivedCompleteModule`: the derived complete `A`-modules with respect to `I`
  form a weak Serre subcategory of `ModuleCat A`.

## Implementation notes

The comparison between the derived category condition `IsIso (oneSubSmulShift K f)` and the
bijectivity of the recurrence operator goes through the homology of a countable product, which is
the product of the homologies by Stacks 07KC; this is the same route as
`isIso_homology_map_oneSubSmulShift_iff` in `StacksFrontier.Homology.DerivedComplete.CompleteAdic`.
The two-out-of-three statements are phrased for a short exact sequence of plain modules given by
an injection `i`, a surjection `p` with `p ∘ i = 0` and the inclusion `ker p ≤ range i`, so that
they apply equally to kernels, cokernels and extensions in `ModuleCat A`.

## References

* [The Stacks Project, Tag 091U](https://stacks.math.columbia.edu/tag/091U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u v

namespace DerivedCompleteRecurrence

attribute [local instance] KoszulCompletion.derivedCountableProducts

section Defs

variable {A : Type*} [CommRing A]

/-- The recurrence operator `(aₙ) ↦ (aₙ - f · aₙ₊₁)` on sequences in an `A`-module. -/
def recurrence {M : Type*} [AddCommGroup M] [Module A M] (f : A) :
    (ℕ → M) →ₗ[A] (ℕ → M) :=
  LinearMap.id - f • LinearMap.funLeft A M Nat.succ

/-- The `n`-th term of the recurrence operator applied to `a` is `a n - f • a (n + 1)`. -/
theorem recurrence_apply {M : Type*} [AddCommGroup M] [Module A M] (f : A) (a : ℕ → M) (n : ℕ) :
    recurrence f a n = a n - f • a (n + 1) := rfl

/-- The recurrence operator commutes with applying a linear map pointwise. -/
theorem recurrence_map_apply {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (f : A) (g : M →ₗ[A] N) (a : ℕ → M) (n : ℕ) :
    recurrence f (fun m => g (a m)) n = g (recurrence f a n) := by
  simp only [recurrence_apply, map_sub, map_smul]

/-- On a subsingleton module every recurrence operator is bijective. -/
theorem bijective_recurrence_of_subsingleton {M : Type*} [AddCommGroup M] [Module A M]
    [Subsingleton M] (f : A) : Function.Bijective (recurrence (M := M) f) :=
  ⟨fun _ _ _ => funext fun _ => Subsingleton.elim _ _,
    fun a => ⟨a, funext fun _ => Subsingleton.elim _ _⟩⟩

end Defs

section TwoOutOfThree

variable {A : Type*} [CommRing A] {M₁ M₂ M₃ : Type*}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]
  {f : A} {i : M₁ →ₗ[A] M₂} {p : M₂ →ₗ[A] M₃}

/-- Function-level form of `recurrence_map_apply`. -/
private theorem recurrence_map {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (f : A) (g : M →ₗ[A] N) (a : ℕ → M) :
    recurrence f (fun m => g (a m)) = fun n => g (recurrence f a n) :=
  funext (recurrence_map_apply f g a)

/-- If `M₁` and `M₂` are recurrence complete at `f`, then so is `M₃`: the cokernel case. -/
theorem bijective_recurrence_X₃ (hp : Function.Surjective p)
    (hpi : ∀ x : M₁, p (i x) = 0) (hex : ∀ x : M₂, p x = 0 → ∃ y : M₁, i y = x)
    (h₁ : Function.Surjective (recurrence (M := M₁) f))
    (h₂ : Function.Bijective (recurrence (M := M₂) f)) :
    Function.Bijective (recurrence (M := M₃) f) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun d hd => ?_, fun c => ?_⟩
  · choose b hb using fun n => hp (d n)
    have hpb : ∀ n, p (recurrence f b n) = 0 := by
      intro n
      rw [recurrence_apply, map_sub, map_smul, hb, hb]
      simpa [recurrence_apply] using congrFun hd n
    choose y hy using fun n => hex _ (hpb n)
    obtain ⟨y', hy'⟩ := h₁ y
    have key : (fun n => i (y' n)) = b := h₂.1 <| by
      rw [recurrence_map, hy']
      exact funext hy
    funext n
    rw [← hb n, ← congrFun key n, hpi]
    rfl
  · choose b hb using fun n => hp (c n)
    obtain ⟨y, hy⟩ := h₂.2 b
    refine ⟨fun n => p (y n), ?_⟩
    rw [recurrence_map, hy]
    exact funext hb

/-- If `M₁` and `M₃` are recurrence complete at `f`, then so is `M₂`: the extension case. -/
theorem bijective_recurrence_X₂ (hi : Function.Injective i) (hp : Function.Surjective p)
    (_hpi : ∀ x : M₁, p (i x) = 0) (hex : ∀ x : M₂, p x = 0 → ∃ y : M₁, i y = x)
    (h₁ : Function.Bijective (recurrence (M := M₁) f))
    (h₃ : Function.Bijective (recurrence (M := M₃) f)) :
    Function.Bijective (recurrence (M := M₂) f) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun d hd => ?_, fun b => ?_⟩
  · have hpd : (fun n => p (d n)) = 0 := h₃.1 <| by
      rw [map_zero, recurrence_map, hd]
      funext n
      simp
    choose y hy using fun n => hex (d n) (congrFun hpd n)
    have hiy : ∀ n, i (recurrence f y n) = 0 := by
      intro n
      rw [← recurrence_map_apply, show (fun m => i (y m)) = d from funext hy]
      simpa using congrFun hd n
    have hry : recurrence f y = 0 := funext fun n => hi ((hiy n).trans (map_zero i).symm)
    have hy0 : y = 0 := h₁.1 (by rw [hry, map_zero])
    funext n
    rw [← hy n, hy0]
    simp
  · obtain ⟨c, hc⟩ := h₃.2 (fun n => p (b n))
    choose y hy using fun n => hp (c n)
    have hpy : ∀ n, p (b n - recurrence f y n) = 0 := by
      intro n
      rw [map_sub, sub_eq_zero, ← recurrence_map_apply,
        show (fun m => p (y m)) = c from funext hy, hc]
    choose z hz using fun n => hex _ (hpy n)
    obtain ⟨z', hz'⟩ := h₁.2 z
    refine ⟨fun n => y n + i (z' n), funext fun n => ?_⟩
    have hiz : recurrence f (fun m => i (z' m)) n = b n - recurrence f y n := by
      rw [recurrence_map_apply, hz']
      exact hz n
    have hsplit : recurrence f (fun m => y m + i (z' m)) n
        = recurrence f y n + recurrence f (fun m => i (z' m)) n := by
      simp only [recurrence_apply, smul_add]
      abel
    rw [hsplit, hiz]
    abel

/-- If `M₂` and `M₃` are recurrence complete at `f`, then so is `M₁`: the kernel case. -/
theorem bijective_recurrence_X₁ (hi : Function.Injective i)
    (hpi : ∀ x : M₁, p (i x) = 0) (hex : ∀ x : M₂, p x = 0 → ∃ y : M₁, i y = x)
    (h₂ : Function.Bijective (recurrence (M := M₂) f))
    (h₃ : Function.Injective (recurrence (M := M₃) f)) :
    Function.Bijective (recurrence (M := M₁) f) := by
  refine ⟨fun a a' haa => ?_, fun a => ?_⟩
  · have key : (fun n => i (a n)) = fun n => i (a' n) := by
      apply h₂.1
      funext n
      rw [recurrence_map_apply, recurrence_map_apply, haa]
    exact funext fun n => hi (congrFun key n)
  · obtain ⟨b, hb⟩ := h₂.2 (fun n => i (a n))
    have hpb : (fun n => p (b n)) = 0 := h₃ <| by
      rw [map_zero]
      funext n
      rw [recurrence_map_apply, hb]
      exact hpi (a n)
    choose a' ha' using fun n => hex (b n) (congrFun hpb n)
    refine ⟨a', funext fun n => hi ?_⟩
    rw [← recurrence_map_apply, show (fun m => i (a' m)) = b from funext ha', hb]

end TwoOutOfThree

section Bridge

attribute [local instance] homologicalHomologyFunctorLinear derivedHomologyFunctorLinear


variable {A : Type u} [CommRing A]

/-- Derived completeness at `f` is invariant under isomorphism. -/
theorem isDerivedCompleteAt_iff_of_iso {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] {K L : C} (e : K ≅ L) (f : A) :
    IsDerivedCompleteAt K f ↔ IsDerivedCompleteAt L f := by
  have : IsIso (Limits.Pi.map (fun _ : ℕ => e.hom)) := by
    refine ⟨⟨Limits.Pi.map (fun _ : ℕ => e.inv), ?_, ?_⟩⟩
    all_goals
      apply Pi.hom_ext
      intro n
      simp [Category.assoc]
  rw [isDerivedCompleteAt_iff_isIso, isDerivedCompleteAt_iff_isIso,
    ← isIso_comp_right_iff _ (Limits.Pi.map (fun _ : ℕ => e.hom)),
    oneSubSmulShift_naturality, isIso_comp_left_iff]

/-- Derived completeness with respect to `I` is invariant under isomorphism. -/
theorem isDerivedComplete_of_iso {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] {I : Ideal A} {K L : C} (e : K ≅ L)
    (h : IsDerivedComplete I K) : IsDerivedComplete I L :=
  fun f hf => (isDerivedCompleteAt_iff_of_iso e f).mp (h f hf)

/-- The endomorphism `1 - f · shift` of a countable product of copies of a module is an
isomorphism exactly when the recurrence operator of `f` on sequences is bijective. -/
theorem isIso_oneSubSmulShift_moduleCat_iff (M : ModuleCat.{v} A) (f : A) :
    IsIso (oneSubSmulShift M f) ↔ Function.Bijective (recurrence (M := M) f) := by
  let e := ModuleCat.piIsoPi (fun _ : ℕ => M)
  let d := ModuleCat.ofHom (recurrence (A := A) (M := M) f)
  have h : e.inv ≫ oneSubSmulShift M f = d ≫ e.inv := by
    apply Pi.hom_ext
    intro n
    simp only [oneSubSmulShift, milnorMap, e, Category.assoc, Pi.lift_comp_π,
      Preadditive.comp_sub, Linear.comp_smul, Category.comp_id,
      ModuleCat.piIsoPi_inv_kernel_ι]
    ext a
    rfl
  rw [← isIso_comp_left_iff e.inv, h, isIso_comp_right_iff,
    ConcreteCategory.isIso_iff_bijective]
  rfl

/-- A module is derived complete at `f` exactly when the recurrence operator of `f` on sequences
in that module is bijective. -/
theorem isDerivedCompleteAt_single_iff_bijective_recurrence (M : ModuleCat.{v} A) (f : A) :
    IsDerivedCompleteAt ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) f ↔
      Function.Bijective (recurrence (M := M) f) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app M
  have hzero : IsIso (oneSubSmulShift
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).obj K) f) ↔
      Function.Bijective (recurrence (M := M) f) :=
    (isDerivedCompleteAt_iff_of_iso (C := ModuleCat.{v} A) e f).trans
      (isIso_oneSubSmulShift_moduleCat_iff M f)
  rw [isDerivedCompleteAt_iff_isIso, DerivedCategory.isIso_iff]
  refine ⟨fun h => hzero.mp ((isIso_homology_map_oneSubSmulShift_iff A K f 0).mp (h 0)),
    fun h n => (isIso_homology_map_oneSubSmulShift_iff A K f n).mpr ?_⟩
  obtain rfl | hn := eq_or_ne n 0
  · exact hzero.mpr h
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K) := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE K 0 n hn
      · exact DerivedCategory.isZero_of_isLE K 0 n hn
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact (isIso_oneSubSmulShift_moduleCat_iff _ f).mpr (bijective_recurrence_of_subsingleton f)

/-- **Stacks 091S, recurrence form.** A module is derived complete with respect to `I` exactly
when the recurrence operator of every `f ∈ I` on sequences in that module is bijective. -/
theorem isDerivedCompleteModule_iff_forall_bijective_recurrence (I : Ideal A)
    (M : ModuleCat.{v} A) :
    IsDerivedCompleteModule I M ↔ ∀ f ∈ I, Function.Bijective (recurrence (M := M) f) :=
  forall₂_congr fun f _ => isDerivedCompleteAt_single_iff_bijective_recurrence M f

end Bridge

section SerreClass

attribute [local instance] homologicalHomologyFunctorLinear derivedHomologyFunctorLinear

attribute [local instance] KoszulCompletion.derivedCountableProducts

variable {A : Type u} [CommRing A]

/-- The object property on `ModuleCat A` cut out by derived completeness with respect to `I`. -/
def completeModules (I : Ideal A) : ObjectProperty (ModuleCat.{v} A) :=
  fun M => IsDerivedCompleteModule I M

/-- A module satisfies `completeModules I` exactly when it is derived complete with respect to
`I`. -/
theorem completeModules_iff (I : Ideal A) (M : ModuleCat.{v} A) :
    completeModules I M ↔ IsDerivedCompleteModule I M := Iff.rfl

/-- Derived complete modules with respect to `I` are closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_completeModules (I : Ideal A) :
    (completeModules.{u, v} I).IsClosedUnderIsomorphisms where
  of_iso e hM :=
    isDerivedComplete_of_iso ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).mapIso e) hM

/-- Some zero object of `ModuleCat A` is derived complete with respect to `I`. -/
instance containsZero_completeModules (I : Ideal A) :
    (completeModules.{u, v} I).ContainsZero :=
  ⟨⟨ModuleCat.of A PUnit.{v + 1}, ModuleCat.isZero_iff_subsingleton.mpr inferInstance,
    (isDerivedCompleteModule_iff_forall_bijective_recurrence I _).mpr
      fun f _ => bijective_recurrence_of_subsingleton f⟩⟩

/-- The module-theoretic kernel of a map of derived complete modules is derived complete. -/
theorem completeModules_ker (I : Ideal A) {M N : ModuleCat.{v} A} (g : M ⟶ N)
    (hM : completeModules I M) (hN : completeModules I N) :
    completeModules.{u, v} I (ModuleCat.of A (LinearMap.ker g.hom)) := by
  rw [completeModules_iff, isDerivedCompleteModule_iff_forall_bijective_recurrence] at hM hN ⊢
  intro f hf
  exact bijective_recurrence_X₁ (i := (LinearMap.ker g.hom).subtype) (p := g.hom)
    Subtype.val_injective (fun x => x.2) (fun x hx => ⟨⟨x, hx⟩, rfl⟩) (hM f hf) (hN f hf).1

/-- The module-theoretic cokernel of a map of derived complete modules is derived complete. -/
theorem completeModules_rangeQuotient (I : Ideal A) {M N : ModuleCat.{v} A} (g : M ⟶ N)
    (hM : completeModules I M) (hN : completeModules I N) :
    completeModules.{u, v} I (ModuleCat.of A (N ⧸ LinearMap.range g.hom)) := by
  rw [completeModules_iff, isDerivedCompleteModule_iff_forall_bijective_recurrence] at hM hN ⊢
  intro f hf
  exact bijective_recurrence_X₃ (i := g.hom) (p := (LinearMap.range g.hom).mkQ)
    (Submodule.mkQ_surjective _) (fun x => (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩)
    (fun x hx => (Submodule.Quotient.mk_eq_zero _).1 hx) (hM f hf).2 (hN f hf)

/-- Derived complete modules with respect to `I` are closed under kernels in `ModuleCat A`. -/
instance isClosedUnderKernels_completeModules (I : Ideal A) :
    (completeModules.{u, v} I).IsClosedUnderKernels where
  kernels_le := by
    rintro X ⟨g, k, hk, hM, hN⟩
    exact ObjectProperty.prop_of_iso _ (IsLimit.conePointUniqueUpToIso (kernelIsKernel g) hk)
      (ObjectProperty.prop_of_iso _ (ModuleCat.kernelIsoKer g).symm
        (completeModules_ker I g hM hN))

/-- Derived complete modules with respect to `I` are closed under cokernels in `ModuleCat A`. -/
instance isClosedUnderCokernels_completeModules (I : Ideal A) :
    (completeModules.{u, v} I).IsClosedUnderCokernels where
  cokernels_le := by
    rintro X ⟨g, k, hk, hM, hN⟩
    exact ObjectProperty.prop_of_iso _
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel g) hk)
      (ObjectProperty.prop_of_iso _ (ModuleCat.cokernelIsoRangeQuotient g).symm
        (completeModules_rangeQuotient I g hM hN))

/-- Derived complete modules with respect to `I` are closed under extensions in `ModuleCat A`. -/
instance isClosedUnderExtensions_completeModules (I : Ideal A) :
    (completeModules.{u, v} I).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [completeModules_iff, isDerivedCompleteModule_iff_forall_bijective_recurrence] at h₁ h₃ ⊢
    intro f hf
    exact bijective_recurrence_X₂ (i := S.f.hom) (p := S.g.hom)
      hS.moduleCat_injective_f hS.moduleCat_surjective_g (fun x => by simp)
      (fun x hx => LinearMap.mem_range.mp
        (hS.exact.moduleCat_range_eq_ker.ge (LinearMap.mem_ker.mpr hx)))
      (h₁ f hf) (h₃ f hf)

/-- **Stacks 091U, first part.** The derived complete `A`-modules with respect to `I` form a weak
Serre subcategory of `ModuleCat A`. -/
instance isWeakSerreClass_isDerivedCompleteModule (I : Ideal A) :
    (completeModules.{u, v} I).IsWeakSerreClass where

end SerreClass

end DerivedCompleteRecurrence

end

end
