module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Injective objects of abelian categories

Stacks, Homological Algebra, Section 12.27. The definition of an injective object (0135), products
of injectives (0137) and enough injectives (0138) are Mathlib's; their tags are attached below.
This file adds parts of the characterisation of injective objects (0136, completed in
`StacksFrontier.CategoryTheory.Preadditive.Injective.Characterization`) and functorial injective
embeddings (0139).
-/

@[expose] public section

add_to_stacks 0135 CategoryTheory.Injective
add_to_sga "4 I 7.11" CategoryTheory.Injective
add_to_stacks 0137 CategoryTheory.Injective.instPiObj
add_to_stacks 0138 CategoryTheory.EnoughInjectives
add_to_sga "3 I 5.3.1.1" CategoryTheory.EnoughInjectives
add_to_sga "4 I 7.13" CategoryTheory.EnoughInjectives
add_to_sga "4 II 6.9" CategoryTheory.EnoughInjectives
add_to_sga "4 V 0.1.1" CategoryTheory.EnoughInjectives
add_to_sga "6 II 3.1" CategoryTheory.EnoughInjectives
add_to_ega "0 11.4.3" CategoryTheory.EnoughInjectives

section

/-!
## Stacks Tag 0136

Characterization of injective objects in an abelian category.

The Stacks tag asserts that, for an object `I` of an abelian category `𝒜`, the
following are equivalent:

1. `I` is injective.
2. The functor `B ↦ Hom_𝒜(B, I)` is exact.
3. Every short exact sequence `0 ⟶ I ⟶ A ⟶ B ⟶ 0` is split.
4. `Ext_𝒜(B, I) = 0` for every object `B`.

This file proves the equivalence `(1) ↔ (3)` and the implication `(1) → (4)`; the full
equivalence of the four conditions, `injective_tfae`, is in
`StacksFrontier.CategoryTheory.Preadditive.Injective.Characterization`.
-/

open CategoryTheory CategoryTheory.Limits

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- Condition (3) of Stacks 0136: every short exact sequence starting at `I` is split. -/
def EverySESStartingAtSplits (I : 𝒜) : Prop :=
  ∀ (A B : 𝒜) (f : I ⟶ A) (g : A ⟶ B) (w : f ≫ g = 0),
    (ShortComplex.mk f g w).ShortExact →
    Nonempty (ShortComplex.mk f g w).Splitting

/-- (1) → (3): if `I` is injective, every short exact sequence `0 ⟶ I ⟶ A ⟶ B ⟶ 0` is split. -/
private lemma every_ses_splits_of_injective (I : 𝒜) (hI : Injective I) :
    EverySESStartingAtSplits I := by
  intro A B f g w hS
  have : Injective I := hI
  exact ⟨hS.splittingOfInjective⟩

/-- (3) → (1): if every short exact sequence starting at `I` is split, then `I` is injective. -/
private lemma injective_of_every_ses_splits (I : 𝒜)
    (hS : EverySESStartingAtSplits I) : Injective I := by
  refine ⟨?_⟩
  intro X Y g₀ m hm
  let P := pushout m g₀
  let i : I ⟶ P := pushout.inr m g₀
  have hi_mono : Mono i := inferInstance
  let π : P ⟶ cokernel i := cokernel.π i
  have hw : i ≫ π = 0 := cokernel.condition i
  have hSE : (ShortComplex.mk i π hw).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  obtain ⟨σ⟩ := hS P (cokernel i) i π hw hSE
  refine ⟨pushout.inl m g₀ ≫ σ.r, ?_⟩
  rw [← Category.assoc, pushout.condition, Category.assoc]
  exact (g₀ ≫= σ.f_r).trans (Category.comp_id g₀)

/-- `I` is injective iff every short exact sequence `0 ⟶ I ⟶ A ⟶ B ⟶ 0` is split. -/
theorem injective_iff_everySES_splits (I : 𝒜) :
    Injective I ↔ EverySESStartingAtSplits I :=
  ⟨every_ses_splits_of_injective I, injective_of_every_ses_splits I⟩

/-- If `I` is injective then `Ext¹(B, I) = 0` (encoded as `Subsingleton (Ext B I 1)`) for every
object `B`. -/
theorem subsingleton_ext_one_of_injective [HasExt 𝒜]
    (I : 𝒜) (hI : Injective I) (B : 𝒜) :
    Subsingleton (Abelian.Ext B I 1) := by
  have : Injective I := hI
  simpa using Abelian.Ext.subsingleton_of_injective B I 0

end

section

/-!
## Stacks Tag 0139

Functorial injective embeddings for an abelian category.
-/

open CategoryTheory

universe v u

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- **Condition (1)** of Stacks Tag 0139:
the composition `s ∘ J` of the candidate functor `J : 𝒜 ⥤ Arrow 𝒜` with the
source functor `s = Arrow.leftFunc : Arrow 𝒜 ⥤ 𝒜` equals the identity on `𝒜`. -/
def IsFunctorialInjectiveEmbeddings₁ (J : 𝒜 ⥤ Arrow 𝒜) : Prop :=
  J ⋙ Arrow.leftFunc = 𝟭 𝒜

/-- **Condition (2)** of Stacks Tag 0139:
for every object `A` of `𝒜`, the morphism `J(A) : s(J(A)) ⟶ t(J(A))` is a
monomorphism (the categorical analogue of "injective" for a morphism in an
abelian category). -/
def IsFunctorialInjectiveEmbeddings₂ (J : 𝒜 ⥤ Arrow 𝒜) : Prop :=
  ∀ A : 𝒜, Mono (J.obj A).hom

/-- **Condition (3)** of Stacks Tag 0139:
for every object `A` of `𝒜`, the target `t(J(A))` of the arrow `J(A)` is an
injective object of `𝒜`. -/
def IsFunctorialInjectiveEmbeddings₃ (J : 𝒜 ⥤ Arrow 𝒜) : Prop :=
  ∀ A : 𝒜, Injective (J.obj A).right

/-- The notion of *functorial injective embeddings* for an abelian category `𝒜`: there exists a
functor `J : 𝒜 ⥤ Arrow 𝒜` satisfying the three conditions `IsFunctorialInjectiveEmbeddings₁`,
`IsFunctorialInjectiveEmbeddings₂`, and `IsFunctorialInjectiveEmbeddings₃`. -/
@[stacks 0139]
def HasFunctorialInjectiveEmbeddings : Prop :=
  ∃ J : 𝒜 ⥤ Arrow 𝒜, IsFunctorialInjectiveEmbeddings₁ 𝒜 J ∧ IsFunctorialInjectiveEmbeddings₂ 𝒜 J ∧
    IsFunctorialInjectiveEmbeddings₃ 𝒜 J

set_option linter.unusedSectionVars false in
/-- If `𝒜` has functorial injective embeddings in the sense of Stacks Tag 0139,
then `𝒜` has enough injectives in the standard (non-functorial) Mathlib sense. -/
theorem enoughInjectives_of_hasFunctorialInjectiveEmbeddings
    (h : HasFunctorialInjectiveEmbeddings 𝒜) : EnoughInjectives 𝒜 := by
  obtain ⟨J, h₁, h₂, h₃⟩ := h
  refine ⟨fun A => ⟨?_⟩⟩
  have : Mono (J.obj A).hom := h₂ A
  have : Injective (J.obj A).right := h₃ A
  -- The source of `J(A)` is `(J ⋙ Arrow.leftFunc).obj A = (𝟭 𝒜).obj A = A`, so transporting
  -- the monomorphism `J(A)` along this equality gives an injective embedding `A ↪ t(J(A))`.
  have key : ∀ {B : 𝒜} (e : A = B) (g : B ⟶ (J.obj A).right),
      Mono g → Mono (eqToHom e ≫ g) := by
    intro B e g hg
    subst e
    simpa using hg
  exact
    { J := (J.obj A).right
      injective := h₃ A
      f := eqToHom (Functor.congr_obj h₁ A).symm ≫ (J.obj A).hom
      mono := key (Functor.congr_obj h₁ A).symm (J.obj A).hom (h₂ A) }

end
