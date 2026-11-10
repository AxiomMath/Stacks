module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Injectives and adjoint functors

A functor with an exact left adjoint preserves injectives; if the left adjoint of an adjunction
preserves monomorphisms and reflects zero objects, functorial injective embeddings transfer from
the target of the left adjoint to its source; a partially defined adjoint extends to a left
adjoint. The transfer of enough injectives along such an adjunction is
`CategoryTheory.EnoughInjectives.of_adjunction`.
-/

@[expose] public section

section

/-!
## A functor with an exact left adjoint preserves injectives

Let `𝒜` and `𝓑` be abelian categories and let `u : 𝒜 ⥤ 𝓑`, `v : 𝓑 ⥤ 𝒜` be
additive functors with `v ⊣ u`. We compare the conditions

* (a) `v` preserves monomorphisms,
* (b) `v` is exact (preserves finite limits and colimits),
* (c) `u` preserves injective objects.

Then (a) ⇔ (b) ⇒ (c). If `𝒜` has enough injectives, all three are equivalent.
-/

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- (a) ⇒ (b): If `v` is a left adjoint additive functor between abelian
categories which preserves monomorphisms, then `v` is exact. -/
theorem isExact_of_preservesMonomorphisms
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u) [v.PreservesMonomorphisms] :
    (PreservesFiniteLimits v ∧ PreservesFiniteColimits v) := by
  have : PreservesColimits v := adj.leftAdjoint_preservesColimits
  have : v.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels v
  have : PreservesFiniteLimits v := Functor.preservesFiniteLimits_of_preservesHomology v
  exact ⟨inferInstance, inferInstance⟩

/-- (b) ⇒ (a): If `v` is exact, then `v` preserves monomorphisms. -/
theorem preservesMonomorphisms_of_isExact
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (hv : (PreservesFiniteLimits v ∧ PreservesFiniteColimits v)) :
    v.PreservesMonomorphisms :=
  have : PreservesFiniteLimits v := hv.1
  preservesMonomorphisms_of_preservesLimitsOfShape v

/-- (b) ⇒ (c): If `v` is exact, then its right adjoint `u` preserves injective
objects. -/
@[sga "4 V 0.2", sga "4½ Arcata 2.3.3" "more general"]
theorem preservesInjectiveObjects_of_isExact
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u) (hv : (PreservesFiniteLimits v ∧ PreservesFiniteColimits v)) :
    u.PreservesInjectiveObjects :=
  have := preservesMonomorphisms_of_isExact u v hv
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

/-- Conjunction of (a) ⇔ (b) and (b) ⇒ (c). -/
@[stacks 015Z "first part", sga "4 V 0.2" "1) (i) ⇒ (ii)"]
theorem preservesInjectiveObjects_of_exact_of_adjunction
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive] (adj : v ⊣ u) :
    (v.PreservesMonomorphisms ↔ (PreservesFiniteLimits v ∧ PreservesFiniteColimits v)) ∧
      ((PreservesFiniteLimits v ∧ PreservesFiniteColimits v) → u.PreservesInjectiveObjects) :=
  ⟨⟨fun _ ↦ isExact_of_preservesMonomorphisms u v adj,
    preservesMonomorphisms_of_isExact u v⟩,
    preservesInjectiveObjects_of_isExact u v adj⟩

/-- Assuming `A` has enough injectives, the three conditions are equivalent. -/
@[stacks 015Z "full statement", sga "4 V 0.2" "1) (i)⇔(ii)"]
theorem exact_iff_preservesInjectiveObjects_of_adjunction
    [EnoughInjectives A]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive] (adj : v ⊣ u) :
    (v.PreservesMonomorphisms ↔ (PreservesFiniteLimits v ∧ PreservesFiniteColimits v)) ∧
      ((PreservesFiniteLimits v ∧ PreservesFiniteColimits v) ↔ u.PreservesInjectiveObjects) :=
  ⟨(preservesInjectiveObjects_of_exact_of_adjunction u v adj).1,
    ⟨preservesInjectiveObjects_of_isExact u v adj,
    fun _ ↦
      have := Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects adj
      isExact_of_preservesMonomorphisms u v adj⟩⟩

end

add_to_stacks 0160 "under v.ReflectsMonomorphisms" CategoryTheory.EnoughInjectives.of_adjunction
add_to_sga "4 V 0.2" "2)" CategoryTheory.EnoughInjectives.of_adjunction

section

/-!
## Functorial injective embeddings and adjunctions
-/

open CategoryTheory Limits

/-- Functorial injective embeddings give a natural monomorphism `𝟭 C ⟶ J` into an endofunctor
with injective values. -/
private lemma exists_natTrans_of_hasFunctorialInjectiveEmbeddings {C : Type*} [Category C]
    [Abelian C] (h : HasFunctorialInjectiveEmbeddings C) :
    ∃ (J : C ⥤ C) (η : 𝟭 C ⟶ J), (∀ X, Injective (J.obj X)) ∧ ∀ X, Mono (η.app X) := by
  obtain ⟨J, h₁, h₂, h₃⟩ := h
  refine ⟨J ⋙ Arrow.rightFunc, eqToHom h₁.symm ≫ Functor.whiskerLeft J Arrow.leftToRight, h₃,
    fun X => ?_⟩
  rw [NatTrans.comp_app, eqToHom_app]
  exact mono_comp' inferInstance (h₂ X)

/-- A natural monomorphism `η : 𝟭 C ⟶ J` into an endofunctor with injective values gives
functorial injective embeddings `X ↦ (η_X : X ⟶ J X)`. -/
private lemma hasFunctorialInjectiveEmbeddings_of_natTrans {C : Type*} [Category C] [Abelian C]
    (J : C ⥤ C) (η : 𝟭 C ⟶ J) (hJ : ∀ X, Injective (J.obj X)) (hη : ∀ X, Mono (η.app X)) :
    HasFunctorialInjectiveEmbeddings C :=
  ⟨{ obj X := Arrow.mk (η.app X)
     map f := Arrow.homMk f (J.map f) (η.naturality f) }, rfl, hη, hJ⟩

/-- `u(JA(v Y))` is injective in `B` whenever `JA.obj (v.obj Y)` is injective in `A`
and `v` preserves monomorphisms. -/
private lemma injective_uJAvY
    {A : Type*} [Category A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) (adj : v ⊣ u)
    (JA : A ⥤ A) (Y : B)
    (hJA : Injective (JA.obj (v.obj Y)))
    (hv_mono : ∀ {X Z : B} (f : X ⟶ Z) [Mono f], Mono (v.map f)) :
    Injective ((v ⋙ JA ⋙ u).obj Y) := by
  refine Injective.mk ?_
  intro X Z g f hf
  change X ⟶ u.obj (JA.obj (v.obj Y)) at g
  have : Mono (v.map f) := hv_mono f
  obtain ⟨h', hh'⟩ := hJA.factors ((adj.homEquiv X _).symm g) (v.map f)
  refine ⟨adj.homEquiv Z _ h', (adj.homEquiv X _).symm.injective ?_⟩
  rw [adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, hh']

/-- If the left adjoint `v` preserves monomorphisms and reflects zero objects, then
`v.map k = 0` implies `k = 0`. -/
private lemma eq_zero_of_vmap_eq_zero
    {A : Type*} [Category A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [v.Additive] (adj : v ⊣ u)
    (hv_mono : ∀ {X Z : B} (f : X ⟶ Z) [Mono f], Mono (v.map f))
    (h_reflectZero : ∀ (X : B), IsZero (v.obj X) → IsZero X)
    {Z Y : B} (k : Z ⟶ Y) (hk : v.map k = 0) : k = 0 := by
  have : v.IsLeftAdjoint := ⟨u, ⟨adj⟩⟩
  have : Mono (v.map (image.ι k)) := hv_mono (image.ι k)
  have h_iota_zero : v.map (image.ι k) = 0 := by
    rwa [← cancel_epi (v.map (factorThruImage k)), comp_zero, ← v.map_comp, image.fac]
  rw [← image.fac k, (h_reflectZero _ (IsZero.of_mono_eq_zero _ h_iota_zero)).eq_of_src
    (image.ι k) 0, comp_zero]

/-- Let `A` and `B` be abelian categories, `u : A ⥤ B` and `v : B ⥤ A` additive functors.
Assume `u` is right adjoint to `v`, `v` transforms injective maps into injective maps, `A` has
enough injectives, `v B = 0` implies `B = 0`, and `A` has functorial injective embeddings. Then
`B` has functorial injective embeddings. -/
@[stacks 0161]
theorem hasFunctorialInjectiveEmbeddings_of_adjunction
    (A : Type*) [Category A] [Abelian A]
    (B : Type*) [Category B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A)
    [u.Additive] [v.Additive]
    (adj : v ⊣ u)
    (hv_mono : ∀ {X Y : B} (f : X ⟶ Y) [Mono f], Mono (v.map f))
    [EnoughInjectives A]
    (h_reflectZero : ∀ (X : B), IsZero (v.obj X) → IsZero X)
    (hA : HasFunctorialInjectiveEmbeddings A) :
    HasFunctorialInjectiveEmbeddings B := by
  obtain ⟨JA, ηA, hJA, hηA⟩ := exists_natTrans_of_hasFunctorialInjectiveEmbeddings hA
  refine hasFunctorialInjectiveEmbeddings_of_natTrans (v ⋙ JA ⋙ u)
    (adj.unit ≫ Functor.whiskerLeft v (Functor.whiskerRight ηA u))
    (fun Y => injective_uJAvY u v adj JA Y (hJA _) hv_mono) fun Y => ?_
  change Mono (adj.unit.app Y ≫ u.map (ηA.app (v.obj Y)))
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z k hk
  have := hηA (v.obj Y)
  have h1 : v.map k ≫ ηA.app (v.obj Y) = 0 := by
    have hcounit := adj.counit_naturality (ηA.app (v.obj Y))
    have htriangle := adj.left_triangle_components (X := Y)
    have step : v.map k ≫ ηA.app (v.obj Y) =
        v.map (k ≫ adj.unit.app Y ≫ u.map (ηA.app (v.obj Y)))
          ≫ adj.counit.app (JA.obj (v.obj Y)) := by grind
    rw [step, hk, Functor.map_zero, zero_comp]
  exact eq_zero_of_vmap_eq_zero u v adj hv_mono h_reflectZero k
    ((cancel_mono (ηA.app (v.obj Y))).mp (h1.trans zero_comp.symm))

end

section

/-!
## A partially defined adjoint extends to a left adjoint

Let `𝒜` and `𝓑` be abelian categories and `u : 𝒜 ⥤ 𝓑` a functor. Suppose there
is a set `S ⊂ Ob(𝓑)` such that

1. every object of `𝓑` is a quotient of an object of `S`, and
2. for every `P ∈ S`, the functor `A ↦ Hom_𝓑(P, u A)` is corepresentable on `𝒜`.

Then `u` admits a left adjoint.
-/

open CategoryTheory Opposite Limits

/-- Every object of `𝓑` is a quotient of an element of `S`: for every `Y : 𝓑` there is
`P ∈ S` together with an epimorphism `P ⟶ Y`. -/
def QuotientOfFamily {B : Type*} [Category B] (S : Set B) : Prop :=
  ∀ (Y : B), ∃ (P : B), P ∈ S ∧ ∃ (f : P ⟶ Y), Epi f

/-- For every `P ∈ S` there is `Q : 𝒜` with `Hom_𝒜(Q, A) = Hom_𝓑(P, u A)` functorially in
`A`, that is, a natural isomorphism of functors `𝒜 ⥤ Type` between `coyoneda.obj (op Q)` and
`u ⋙ coyoneda.obj (op P)`. -/
def PartialAdjointData {A B : Type*} [Category A] [Category B]
    (u : A ⥤ B) (S : Set B) : Prop :=
  ∀ (P : B), P ∈ S → ∃ (Q : A),
    Nonempty ((coyoneda.obj (op Q) : A ⥤ Type _) ≅ (u ⋙ coyoneda.obj (op P)))

section Helpers

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
variable (u : A ⥤ B) (S : Set B)

set_option linter.unusedSectionVars false in
/-- For every `P ∈ S`, the functor `u ⋙ coyoneda.obj (op P) : 𝒜 ⥤ Type` is
corepresentable. -/
lemma corepresentable_of_mem_S
    (h2 : PartialAdjointData u S) (P : B) (hP : P ∈ S) :
    (u ⋙ coyoneda.obj (op P)).IsCorepresentable := by
  obtain ⟨Q, ⟨iso⟩⟩ := h2 P hP
  exact Functor.IsCorepresentable.mk' iso

/-- In an abelian category, every epi `f : P₀ ⟶ Y` is a cokernel of its
kernel inclusion `kernel.ι f`. -/
lemma nonempty_epi_isColimit_cokernel_kernel
    {C : Type*} [Category C] [Abelian C]
    {P₀ Y : C} (f : P₀ ⟶ Y) [Epi f] :
    Nonempty (IsColimit (CokernelCofork.ofπ f (kernel.condition f))) :=
  ⟨Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι f) (kernel.condition f))
    (kernelIsKernel f)⟩

/-- If `f : P₀ ⟶ Y` is a cokernel of `ι : K ⟶ P₀` and `g : P₁ ⟶ K` is an
epimorphism, then `f` is also a cokernel of the composite `g ≫ ι : P₁ ⟶ P₀`. -/
lemma nonempty_isColimit_cokernel_of_epi_comp
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {K P₀ Y P₁ : C} {ι : K ⟶ P₀} {f : P₀ ⟶ Y} (w₀ : ι ≫ f = 0)
    (hf : Nonempty (IsColimit (CokernelCofork.ofπ f w₀)))
    (g : P₁ ⟶ K) [Epi g]
    (w : (g ≫ ι) ≫ f = 0) :
    Nonempty (IsColimit (CokernelCofork.ofπ f w)) := by
  obtain ⟨hf_wit⟩ := hf
  exact ⟨isCokernelEpiComp hf_wit g rfl⟩

/-- If every object of `B` is a quotient of an element of `S`, then every object `Y` of `B` is
the cokernel of a morphism `P₁ ⟶ P₀` between elements of `S`. -/
lemma exists_cokernel_presentation
    (h1 : QuotientOfFamily S) (Y : B) :
    ∃ (P₀ P₁ : B) (_ : P₀ ∈ S) (_ : P₁ ∈ S) (a : P₁ ⟶ P₀) (f : P₀ ⟶ Y)
      (w : a ≫ f = 0), Nonempty (IsColimit (CokernelCofork.ofπ f w)) := by
  obtain ⟨P₀, hP₀, f, _⟩ := h1 Y
  obtain ⟨P₁, hP₁, g, _⟩ := h1 (kernel f)
  refine ⟨P₀, P₁, hP₀, hP₁, g ≫ kernel.ι f, f, by simp, ?_⟩
  exact nonempty_isColimit_cokernel_of_epi_comp (kernel.condition f)
    (nonempty_epi_isColimit_cokernel_kernel f) g _

/-- For every `Y : 𝓑`, the functor `u ⋙ coyoneda.obj (op Y)` is corepresentable. -/
lemma corepresentable_of_quotient
    (h1 : QuotientOfFamily S) (h2 : PartialAdjointData u S) (Y : B) :
    (u ⋙ coyoneda.obj (op Y)).IsCorepresentable := by
  obtain ⟨P₀, P₁, hP₀, hP₁, a, f, w, ⟨hcolim⟩⟩ :=
    exists_cokernel_presentation S h1 Y
  refine Functor.leftAdjointObjIsDefined_of_isColimit hcolim ?_
  rintro (_ | _)
  · exact corepresentable_of_mem_S u S h2 P₁ hP₁
  · exact corepresentable_of_mem_S u S h2 P₀ hP₀

end Helpers

/-- Let `𝒜` and `𝓑` be abelian categories, `u : 𝒜 ⥤ 𝓑` a functor, and suppose
there is `S ⊆ Ob(𝓑)` such that every object of `𝓑` is a quotient of some
object of `S` and, for every `P ∈ S`, the functor `A ↦ Hom_𝓑(P, u A)` is
corepresentable. Then `u` admits a left adjoint. -/
@[stacks 0793]
theorem isRightAdjoint_of_partialAdjointData
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (u : A ⥤ B) (S : Set B)
    (h1 : QuotientOfFamily S)
    (h2 : PartialAdjointData u S) :
    u.IsRightAdjoint := by
  apply Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
  ext Y
  simp [Functor.leftAdjointObjIsDefined,
        corepresentable_of_quotient u S h1 h2 Y]

end
