module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import StacksCore.Tactic.StacksAttribute

/-! # Serre subcategories and weak Serre subcategories

Stacks tag 02MO defines, for an abelian category `A`:

1. a *Serre subcategory* of `A` is a nonempty full subcategory `C` such that for every exact
   sequence `A → B → C` with `A` and `C` in `C`, also `B` is in `C`;
2. a *weak Serre subcategory* of `A` is a nonempty full subcategory `C` such that for every
   exact sequence `A₀ → A₁ → A₂ → A₃ → A₄` with `A₀, A₁, A₃, A₄` in `C`, also `A₂` is in `C`.

Full subcategories closed under isomorphism are `CategoryTheory.ObjectProperty`. Part 1 is
already in Mathlib as `CategoryTheory.ObjectProperty.IsSerreClass`, packaged as closure under
subobjects, quotients and extensions rather than as the single exactness condition above;
`CategoryTheory.ObjectProperty.isSerreClass_iff_prop_X₂_of_exact` proves the two agree, which is
tag 02MP and is what makes the `add_to_stacks` claim below auditable. The *moreover* clause of
02MP — a Serre subcategory is abelian and the inclusion is exact — is not formalized here.

Part 2 has no counterpart in Mathlib; `CategoryTheory.ObjectProperty.IsWeakSerreClass` is defined
in `StacksCore.CategoryTheory.Abelian.SerreClass.Weak`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

add_to_stacks 02MO "part 1, packaged as closure under subobjects, quotients and extensions;
`isSerreClass_iff_prop_X₂_of_exact` identifies this with the definition in the Stacks project."
  CategoryTheory.ObjectProperty.IsSerreClass

add_to_stacks 02MQ "the objects killed by an exact functor are `Functor.kernel F`, which is by
definition the inverse image along `F` of the Serre class of zero objects. So the tag is the
composition of this instance with `instIsSerreClassIsZero`, and needs no proof of its own:
`inferInstance` closes it. As for 02MO, `isSerreClass_iff_prop_X₂_of_exact` is what makes
`IsSerreClass` the Stacks notion here."
  instIsSerreClassInverseImageOfPreservesFiniteLimitsOfPreservesFiniteColimits

section

variable {P}
variable (hP : ∀ S : ShortComplex C, S.Exact → P S.X₁ → P S.X₃ → P S.X₂)

include hP

/-- The zero object is in a nonempty subcategory closed under middle terms of exact sequences:
apply the condition to `X → 0 → X`, which is exact at its zero middle term. -/
lemma prop_zero_of_prop_X₂_of_exact {X : C} (hX : P X) : P 0 :=
  hP (ShortComplex.mk (0 : X ⟶ 0) (0 : (0 : C) ⟶ X) (by simp))
    (ShortComplex.exact_of_isZero_X₂ _ (isZero_zero C)) hX hX

/-- Such a subcategory contains a zero object. -/
lemma containsZero_of_prop_X₂_of_exact {X : C} (hX : P X) : P.ContainsZero :=
  ⟨0, isZero_zero C, prop_zero_of_prop_X₂_of_exact hP hX⟩

/-- Such a subcategory is closed under subobjects: `0 → A → B` is exact at `A` exactly when
`A → B` is a monomorphism. -/
lemma isClosedUnderSubobjects_of_prop_X₂_of_exact (h₀ : P 0) : P.IsClosedUnderSubobjects :=
  ⟨fun {A _} i _ hB ↦ hP (ShortComplex.mk (0 : (0 : C) ⟶ A) i (by simp))
    ((ShortComplex.exact_iff_mono _ rfl).2 inferInstance) h₀ hB⟩

/-- Such a subcategory is closed under quotients: `A → B → 0` is exact at `B` exactly when
`A → B` is an epimorphism. -/
lemma isClosedUnderQuotients_of_prop_X₂_of_exact (h₀ : P 0) : P.IsClosedUnderQuotients :=
  ⟨fun {_ B} p _ hA ↦ hP (ShortComplex.mk p (0 : B ⟶ (0 : C)) (by simp))
    ((ShortComplex.exact_iff_epi _ rfl).2 inferInstance) hA h₀⟩

/-- Such a subcategory is closed under extensions, a short exact sequence being in particular
exact at its middle term. -/
lemma isClosedUnderExtensions_of_prop_X₂_of_exact : P.IsClosedUnderExtensions :=
  ⟨fun hS h₁ h₃ ↦ hP _ hS.exact h₁ h₃⟩

end

/-- **Stacks 02MP.** Mathlib's `ObjectProperty.IsSerreClass` — zero, subobjects, quotients,
extensions — is the Stacks project's Serre subcategory: nonempty, and containing the middle term
of every exact sequence whose outer terms belong to it.

Condition (2), strict fullness, is not a hypothesis here: an `ObjectProperty` is a predicate on
objects, and a Serre class is closed under isomorphism, so it holds by construction. -/
@[stacks 02MP "the equivalence part"]
theorem isSerreClass_iff_prop_X₂_of_exact :
    P.IsSerreClass ↔ (∃ X, P X) ∧
      ∀ S : ShortComplex C, S.Exact → P S.X₁ → P S.X₃ → P S.X₂ := by
  refine ⟨fun _ ↦ ?_, fun ⟨⟨_, hX⟩, hP⟩ ↦ ?_⟩
  · obtain ⟨Z, _, hZ⟩ := P.exists_prop_of_containsZero
    exact ⟨⟨Z, hZ⟩, fun _ hS h₁ h₃ ↦ P.prop_X₂_of_exact hS h₁ h₃⟩
  · have h₀ := prop_zero_of_prop_X₂_of_exact hP hX
    have := containsZero_of_prop_X₂_of_exact hP hX
    have := isClosedUnderSubobjects_of_prop_X₂_of_exact hP h₀
    have := isClosedUnderQuotients_of_prop_X₂_of_exact hP h₀
    have := isClosedUnderExtensions_of_prop_X₂_of_exact hP
    exact { }

/-- A binary product is an extension: `0 → X → X ⊞ Y → Y → 0` is split short exact. Stated for
closure under extensions rather than for `IsSerreClass`, so that it serves weak Serre classes
(which are not closed under subobjects) as well. -/
instance [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderBinaryProducts :=
  IsClosedUnderLimitsOfShape.mk' (fun _ ⟨F, hF⟩ ↦ P.prop_of_iso
    ((biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
    (prop_biprod P (hF ⟨.left⟩) (hF ⟨.right⟩)))

instance [P.ContainsZero] [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderFiniteProducts := IsClosedUnderFiniteProducts.mk'

@[stacks 02MP "Serre Subcategory is abelian"]
private lemma abelian_of_isSerreClass [P.IsSerreClass] :
    Nonempty (Abelian P.FullSubcategory) := ⟨inferInstance⟩

@[stacks 02MP "inclusion functor is exact"]
lemma preservesFiniteLimits_ι [P.IsSerreClass] : PreservesFiniteLimits P.ι :=
  have {X Y : P.FullSubcategory} (f : X ⟶ Y) := P.preservesKernels_ι f
  P.ι.preservesFiniteLimits_of_preservesKernels

end CategoryTheory.ObjectProperty
