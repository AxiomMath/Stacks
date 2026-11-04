module

public import Mathlib.Algebra.Homology.ExactSequence
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic

/-! # Weak Serre subcategories

Stacks tag 02MO (2) defines a *weak Serre subcategory* of an abelian category `A` as a nonempty
full subcategory `C` such that for every exact `A₀ → A₁ → A₂ → A₃ → A₄` with `A₀, A₁, A₃, A₄` in
`C`, also `A₂` is in `C`. Tag 0754 characterises these as the strictly full subcategories which
contain `0` and are closed under kernels, cokernels and extensions.

`IsWeakSerreClass` below is the 0754 form, matching how Mathlib packages
`CategoryTheory.ObjectProperty.IsSerreClass`: closure conditions rather than a single exactness
condition. `prop_obj₂_of_exact` recovers the 02MO (2) condition from it.

Note that condition (2) of 0754, strict fullness, is a genuine hypothesis here — unlike for a
Serre class, where closure under subobjects already forces it.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- **Stacks 0754**, conditions (1)–(4): a *weak Serre subcategory* is a strictly full subcategory
which contains `0` and is closed under kernels, cokernels and extensions.

`prop_obj₂_of_exact` shows this satisfies the definition in 02MO (2). -/
@[stacks 0754 "conditions (1)-(4), as the definition"]
class IsWeakSerreClass : Prop extends P.ContainsZero, P.IsClosedUnderIsomorphisms,
    P.IsClosedUnderKernels, P.IsClosedUnderCokernels, P.IsClosedUnderExtensions where

/-- A Serre subcategory is a weak Serre subcategory: subobjects give kernels and quotients give
cokernels, so every condition is already available. -/
instance (priority := 100) [P.IsSerreClass] : P.IsWeakSerreClass where

lemma exists_prop_of_isWeakSerreClass [P.IsWeakSerreClass] : ∃ X, P X :=
  have ⟨Z, _, hZ⟩ := P.exists_prop_of_containsZero
  ⟨Z, hZ⟩

section Moreover

variable [P.IsWeakSerreClass]

/-- **Stacks 0754**, "moreover": a weak Serre subcategory is an abelian category. -/
@[stacks 0754 "moreover: a weak Serre subcategory is abelian"]
lemma abelian_of_isWeakSerreClass : Nonempty (Abelian P.FullSubcategory) := ⟨inferInstance⟩

/-- **Stacks 0754**, "moreover": the inclusion functor is exact, here its left exactness. -/
@[stacks 0754 "moreover: the inclusion functor preserves finite limits"]
lemma preservesFiniteLimits_ι_of_isWeakSerreClass : PreservesFiniteLimits P.ι :=
  have {X Y : P.FullSubcategory} (f : X ⟶ Y) := P.preservesKernels_ι f
  P.ι.preservesFiniteLimits_of_preservesKernels

/-- **Stacks 0754**, "moreover": the inclusion functor is exact, here its right exactness. -/
@[stacks 0754 "moreover: the inclusion functor preserves finite colimits"]
lemma preservesFiniteColimits_ι_of_isWeakSerreClass : PreservesFiniteColimits P.ι :=
  have {X Y : P.FullSubcategory} (f : X ⟶ Y) := P.preservesCokernels_ι f
  P.ι.preservesFiniteColimits_of_preservesCokernels

end Moreover

/-- **Stacks 02MO (2).** A weak Serre subcategory in the sense of 0754 contains the middle term of
every five term exact sequence whose other four terms belong to it.

The middle term is an extension of `ker (A₃ ⟶ A₄)` by `coker (A₀ ⟶ A₁)`: exactness at `A₁` makes
`coker (A₀ ⟶ A₁) ⟶ A₂` a monomorphism, exactness at `A₃` makes `A₂ ⟶ ker (A₃ ⟶ A₄)` an
epimorphism, and the resulting short complex is exact because it differs from `A₁ ⟶ A₂ ⟶ A₃` by
an epimorphism on the left and a monomorphism on the right. -/
@[stacks 02MO "part 2"]
theorem prop_obj₂_of_exact [P.IsWeakSerreClass] (S : ComposableArrows C 4) (hS : S.Exact)
    (h₀ : P (S.obj' 0)) (h₁ : P (S.obj' 1)) (h₃ : P (S.obj' 3)) (h₄ : P (S.obj' 4)) :
    P (S.obj' 2) := by
  have w₀ : S.map' 0 1 ≫ S.map' 1 2 = 0 := hS.toIsComplex.zero' 0 1 2
  have w₁ : S.map' 1 2 ≫ S.map' 2 3 = 0 := hS.toIsComplex.zero' 1 2 3
  have w₃ : S.map' 2 3 ≫ S.map' 3 4 = 0 := hS.toIsComplex.zero' 2 3 4
  -- `coker (A₀ ⟶ A₁) ⟶ A₂` is mono by exactness at `A₁`, `A₂ ⟶ ker (A₃ ⟶ A₄)` epi at `A₃`
  have hmono : Mono (cokernel.desc _ _ w₀) := (hS.exact' 0 1 2).mono_cokernelDesc
  have hepi : Epi (kernel.lift _ _ w₃) := (hS.exact' 2 3 4).epi_kernelLift
  -- `coker (A₀ ⟶ A₁) ⟶ A₂ ⟶ A₃` is exact: it differs from `A₁ ⟶ A₂ ⟶ A₃` by an epi on the left
  have wM : cokernel.desc _ _ w₀ ≫ S.map' 2 3 = 0 := by
    rw [← cancel_epi (cokernel.π (S.map' 0 1)), cokernel.π_desc_assoc, comp_zero, w₁]
  have hM : (ShortComplex.mk (cokernel.desc _ _ w₀) (S.map' 2 3) wM).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := S.sc' hS.toIsComplex 1 2 3)
      (S₂ := ShortComplex.mk (cokernel.desc _ _ w₀) (S.map' 2 3) wM)
      ⟨cokernel.π _, 𝟙 _, 𝟙 _, by simp, by simp⟩).1 (hS.exact' 1 2 3)
  -- replacing `A₃` by `ker (A₃ ⟶ A₄)` is a mono on the right, so exactness survives
  have hz : cokernel.desc _ _ w₀ ≫ kernel.lift _ _ w₃ = 0 := by
    rw [← cancel_mono (kernel.ι (S.map' 3 4))]; simp [wM]
  exact P.prop_X₂_of_shortExact (S := ShortComplex.mk _ _ hz)
    (ShortComplex.ShortExact.mk'
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        (S₁ := ShortComplex.mk (cokernel.desc _ _ w₀) (kernel.lift _ _ w₃) hz)
        (S₂ := ShortComplex.mk (cokernel.desc _ _ w₀) (S.map' 2 3) wM)
        ⟨𝟙 _, 𝟙 _, kernel.ι _, by simp, by simp⟩).2 hM) hmono hepi)
    (P.prop_cokernel _ h₀ h₁) (P.prop_kernel _ h₃ h₄)

/-- A short complex with zero first map and monomorphic second map is exact. -/
private lemma exact_of_mono_of_eq_zero (S : ShortComplex C) (hf : S.f = 0) [Mono S.g] :
    S.Exact :=
  (ShortComplex.exact_iff_mono S hf).2 inferInstance

/-- A short complex with zero second map and epimorphic first map is exact. -/
private lemma exact_of_epi_of_eq_zero (S : ShortComplex C) (hg : S.g = 0) [Epi S.f] :
    S.Exact :=
  (ShortComplex.exact_iff_epi S hg).2 inferInstance

section Converse

variable {P}
variable (hP : ∀ S : ComposableArrows C 4, S.Exact → P (S.obj' 0) → P (S.obj' 1) →
  P (S.obj' 3) → P (S.obj' 4) → P (S.obj' 2))

include hP

/-- Feed an explicit exact `A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄` to the five term condition, presented as
three exact short complexes rather than as a `ComposableArrows`. -/
lemma prop_mid_of_exact₄ {A₀ A₁ A₂ A₃ A₄ : C} {f₀ : A₀ ⟶ A₁} {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃}
    {f₃ : A₃ ⟶ A₄} (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₀ : P A₀) (h₁ : P A₁) (h₃ : P A₃) (h₄ : P A₄) : P A₂ :=
  hP (ComposableArrows.mk₄ f₀ f₁ f₂ f₃)
    (ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₀ e₀)
      (ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₁ e₁)
        (ComposableArrows.exact₂_mk _ w₂ e₂)))
    h₀ h₁ h₃ h₄

/-- Condition (1): apply the five term condition to `X ⟶ X ⟶ 0 ⟶ X ⟶ X`. -/
lemma prop_zero_of_prop_obj₂ {X : C} (hX : P X) : P (0 : C) :=
  prop_mid_of_exact₄ hP (f₀ := 𝟙 X) (f₁ := (0 : X ⟶ 0)) (f₂ := (0 : (0 : C) ⟶ X)) (f₃ := 𝟙 X)
    (by simp) (by simp) (by simp)
    (exact_of_epi_of_eq_zero _ rfl)
    (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C))
    (exact_of_mono_of_eq_zero _ rfl) hX hX hX hX

omit hP in
lemma containsZero_of_prop_obj₂ (h₀ : P (0 : C)) : P.ContainsZero :=
  ⟨0, isZero_zero C, h₀⟩

/-- Condition (2), strict fullness: apply the condition to `0 ⟶ 0 ⟶ Y ⟶ X ⟶ 0`, using that an
isomorphism is both a monomorphism and an epimorphism. -/
lemma isClosedUnderIsomorphisms_of_prop_obj₂ (h₀ : P (0 : C)) : P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX :=
    prop_mid_of_exact₄ hP (f₀ := (0 : (0 : C) ⟶ 0)) (f₁ := (0 : (0 : C) ⟶ Y)) (f₂ := e.inv)
      (f₃ := (0 : X ⟶ 0)) (by simp) (by simp) (by simp)
      (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C))
      (exact_of_mono_of_eq_zero _ rfl)
      (exact_of_epi_of_eq_zero _ rfl) h₀ h₀ hX h₀

/-- Condition (3) for kernels: apply the condition to `0 ⟶ 0 ⟶ ker f ⟶ X ⟶ Y`. -/
lemma isClosedUnderKernels_of_prop_obj₂ [P.IsClosedUnderIsomorphisms] (h₀ : P (0 : C)) :
    P.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    refine P.prop_of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk) ?_
    exact prop_mid_of_exact₄ hP (f₀ := (0 : (0 : C) ⟶ 0)) (f₁ := (0 : (0 : C) ⟶ kernel f))
      (f₂ := kernel.ι f) (f₃ := f) (by simp) (by simp) (by simp)
      (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C))
      (exact_of_mono_of_eq_zero _ rfl)
      (ShortComplex.kernelSequence_exact f) h₀ h₀ hf.1 hf.2

/-- Condition (3) for cokernels: apply the condition to `X ⟶ Y ⟶ coker f ⟶ 0 ⟶ 0`. -/
lemma isClosedUnderCokernels_of_prop_obj₂ [P.IsClosedUnderIsomorphisms] (h₀ : P (0 : C)) :
    P.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    refine P.prop_of_iso (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk) ?_
    exact prop_mid_of_exact₄ hP (f₀ := f) (f₁ := cokernel.π f) (f₂ := (0 : cokernel f ⟶ 0))
      (f₃ := (0 : (0 : C) ⟶ 0)) (by simp) (by simp) (by simp)
      (ShortComplex.cokernelSequence_exact f)
      (exact_of_epi_of_eq_zero _ rfl)
      (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)) hf.1 hf.2 h₀ h₀

/-- Condition (4): a short exact sequence padded with zeros is a five term exact sequence. -/
lemma isClosedUnderExtensions_of_prop_obj₂ (h₀ : P (0 : C)) : P.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    exact prop_mid_of_exact₄ hP (f₀ := (0 : (0 : C) ⟶ S.X₁)) (f₁ := S.f) (f₂ := S.g)
      (f₃ := (0 : S.X₃ ⟶ 0)) (by simp) S.zero (by simp)
      (exact_of_mono_of_eq_zero _ rfl) hS.exact
      (exact_of_epi_of_eq_zero _ rfl) h₀ h₁ h₃ h₀

end Converse

/-- **Stacks 0754.** The closure conditions defining `IsWeakSerreClass` are equivalent to the
definition of a weak Serre subcategory in 02MO (2): being nonempty and containing the middle term
of every five term exact sequence whose other four terms belong to it. -/
@[stacks 0754]
theorem isWeakSerreClass_iff_prop_obj₂_of_exact :
    P.IsWeakSerreClass ↔ (∃ X, P X) ∧
      ∀ S : ComposableArrows C 4, S.Exact → P (S.obj' 0) → P (S.obj' 1) →
        P (S.obj' 3) → P (S.obj' 4) → P (S.obj' 2) := by
  refine ⟨fun _ ↦ ⟨P.exists_prop_of_isWeakSerreClass, fun S hS h₀ h₁ h₃ h₄ ↦
    P.prop_obj₂_of_exact S hS h₀ h₁ h₃ h₄⟩, fun ⟨⟨X, hX⟩, hP⟩ ↦ ?_⟩
  have h₀ := prop_zero_of_prop_obj₂ hP hX
  have := containsZero_of_prop_obj₂ h₀
  have := isClosedUnderIsomorphisms_of_prop_obj₂ hP h₀
  have := isClosedUnderKernels_of_prop_obj₂ hP h₀
  have := isClosedUnderCokernels_of_prop_obj₂ hP h₀
  have := isClosedUnderExtensions_of_prop_obj₂ hP h₀
  exact { }

end CategoryTheory.ObjectProperty
