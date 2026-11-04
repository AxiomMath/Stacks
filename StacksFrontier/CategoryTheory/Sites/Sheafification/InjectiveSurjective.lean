module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injective and surjective maps of sheaves of sets

## Main definitions

* `IsInjective`, `IsSurjectiveSheafType`: injectivity and surjectivity of a map of sheaves of
  sets in the sense of Stacks 00WL and 00WM.

## Main results

* `isSurjective_iff_isLocallySurjective`: surjectivity agrees with Mathlib's
  `Sheaf.IsLocallySurjective`.
* `mono_iff_isInjective`, `epi_iff_isSurjective`,
  `isIso_iff_isInjective_and_isSurjective`: injective (resp. surjective) maps are exactly the
  monomorphisms (resp. epimorphisms) of `Sh(C)`, and a map is an isomorphism if and only if it
  is both.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A morphism of sheaves of sets is *injective* (Stacks 00WL) if it is injective on sections
over every object. -/
def IsInjective {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) : Prop :=
  ∀ U : Cᵒᵖ, Function.Injective (φ.hom.app U)

/-- A morphism of sheaves of sets is *surjective* (Stacks 00WM) if every section of the target
is locally in the image. -/
def IsSurjectiveSheafType {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) : Prop :=
  ∀ ⦃U : C⦄ (s : G.obj.obj (op U)),
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
        ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map f.op s

/-- Surjectivity in the sense of Stacks 00WM agrees with `Sheaf.IsLocallySurjective`. -/
lemma isSurjective_iff_isLocallySurjective
    {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) :
    IsSurjectiveSheafType J φ ↔ Sheaf.IsLocallySurjective φ := by
  refine ⟨fun h ↦ ⟨?_⟩,
    fun h _ s ↦ ⟨Presheaf.imageSieve φ.hom s, h.imageSieve_mem s, fun _ _ hf ↦ hf⟩⟩
  intro U s
  obtain ⟨S, hS, hSf⟩ := h s
  exact J.superset_covering (fun _ f hf ↦ hSf f hf) hS

/-- A morphism of sheaves of sets is a monomorphism in the category of sheaves if and only if it
is injective. -/
@[stacks 00WN "(1)", sga "3 I 1.2" "more general"]
theorem mono_iff_isInjective {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) :
    Mono φ ↔ IsInjective J φ := by
  rw [Sheaf.Hom.mono_iff_presheaf_mono J (Type max v u) φ, NatTrans.mono_iff_mono_app]
  exact forall_congr' fun _ ↦ mono_iff_injective _

/-- A morphism of sheaves of sets is an epimorphism in the category of sheaves if and only if it
is surjective. -/
@[stacks 00WN "(2)",
  sga "3 I 1.2" "more general",
  sga "3 IV 4.4.3" "special case",
  sga "3 IV 4.4.8" "special case",
  sga "3 VIB 10.15" "more general",
  sga "3 VIIA 8.1.4" "partial",
  sga "4 II 5.1" "special case"]
theorem epi_iff_isSurjective {F G : Sheaf J (Type max v u)} (φ : F ⟶ G) :
    Epi φ ↔ IsSurjectiveSheafType J φ :=
  ((isSurjective_iff_isLocallySurjective J φ).trans (Sheaf.isLocallySurjective_iff_epi φ)).symm

/-- A morphism of sheaves of sets is an isomorphism if and only if it is both injective and
surjective. -/
@[stacks 00WN "(3)",
  sga "3 IV 4.4.4" "iso ⇔ inj + surj",
  sga "3 IV 4.3.2.1" "more general",
  sga "4 II 4.2" "special case"]
theorem isIso_iff_isInjective_and_isSurjective {F G : Sheaf J (Type max v u)}
    (φ : F ⟶ G) :
    IsIso φ ↔ IsInjective J φ ∧ IsSurjectiveSheafType J φ := by
  refine ⟨fun _ ↦ ⟨(mono_iff_isInjective J φ).mp inferInstance,
    (epi_iff_isSurjective J φ).mp inferInstance⟩, fun ⟨hi, hs⟩ ↦ ?_⟩
  have : Mono φ := (mono_iff_isInjective J φ).mpr hi
  have : Epi φ := (epi_iff_isSurjective J φ).mpr hs
  exact isIso_of_mono_of_epi φ
