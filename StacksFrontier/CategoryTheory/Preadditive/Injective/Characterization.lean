module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic

/-!
# Characterisation of injective objects (Stacks 0136)

For an object `I` of an abelian category `𝒜`, the following are equivalent
(`injective_tfae`):

1. `I` is injective.
2. The functor `B ↦ Hom_𝒜(B, I)` is exact.
3. Every short exact sequence `0 ⟶ I ⟶ A ⟶ B ⟶ 0` is split.
4. `Ext_𝒜(B, I) = 0` for every object `B`.

Condition (2) is stated as: the functor `Hom(-, I) = preadditiveYoneda.obj I : 𝒜ᵒᵖ ⥤ Ab` sends
every short exact sequence of `𝒜` to a short exact sequence of abelian groups (`HomToIsExact`,
the form of Stacks 010N (4)), and also, as the fifth entry of the list, as
`preadditiveYoneda.obj I` commuting with finite limits and finite colimits (Categories,
Definition 0034). Condition (3) is `EverySESStartingAtSplits`. Condition (4) uses Mathlib's
`Abelian.Ext B I 1` for the `HasExt` structure `HasExt.standard 𝒜`, which exists for every
abelian category; it plays the role of the group of extensions of `B` by `I` of Stacks
Section 010I.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- Condition (2) of Stacks 0136: the functor `B ↦ Hom_𝒜(B, I)` is exact, i.e. it sends every
short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜` to a short exact sequence
`0 ⟶ Hom(C, I) ⟶ Hom(B, I) ⟶ Hom(A, I) ⟶ 0` of abelian groups. -/
def HomToIsExact (I : 𝒜) : Prop :=
  ∀ S : ShortComplex 𝒜, S.ShortExact → (S.op.map (preadditiveYoneda.obj I)).ShortExact

/-- (1) → (2): if `I` is injective, the functor `Hom(-, I)` is exact. -/
theorem homToIsExact_of_injective (I : 𝒜) (hI : Injective I) : HomToIsExact I := by
  intro S hS
  have : Epi S.g := hS.epi_g
  have : Mono S.f := hS.mono_f
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff_function_exact]
    intro ψ
    constructor
    · intro hψ
      have h : S.f ≫ ψ = 0 := hψ
      obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel ψ h
      exact ⟨l, hl⟩
    · rintro ⟨l, rfl⟩
      exact (S.zero_assoc (l : S.X₃ ⟶ I)).trans zero_comp
  · rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    exact (cancel_epi S.g).1 hab
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro φ
    have key : ∀ ψ : S.X₁ ⟶ I, ∃ t : S.X₂ ⟶ I, S.f ≫ t = ψ := fun ψ =>
      ⟨Injective.factorThru ψ S.f, Injective.comp_factorThru ψ S.f⟩
    exact key φ

/-- (2) → (1): if the functor `Hom(-, I)` is exact, then `I` is injective. -/
theorem injective_of_homToIsExact (I : 𝒜) (hI : HomToIsExact I) : Injective I := by
  refine ⟨fun {X Y} g m hm => ?_⟩
  let S := ShortComplex.mk m (cokernel.π m) (cokernel.condition m)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  have := (hI S hS).epi_g
  rw [AddCommGrpCat.epi_iff_surjective] at this
  obtain ⟨h, hh⟩ := this g
  exact ⟨h, hh⟩

/-- (4) → (1): if `Ext¹(B, I) = 0` for every object `B`, then `I` is injective. -/
theorem injective_of_subsingleton_ext_one [HasExt 𝒜] (I : 𝒜)
    (hI : ∀ B : 𝒜, Subsingleton (Abelian.Ext B I 1)) : Injective I := by
  refine ⟨fun {X Y} g m hm => ?_⟩
  let S := ShortComplex.mk m (cokernel.π m) (cokernel.condition m)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS I (Abelian.Ext.mk₀ g)
    (by omega : 1 + 0 = 1) (Subsingleton.elim _ _)
  obtain ⟨h, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x₂
  refine ⟨h, (Abelian.Ext.mk₀_bijective _ _).1 ?_⟩
  rw [← hx₂, Abelian.Ext.mk₀_comp_mk₀]

/-- Condition (2) of Stacks 0136 in the form of Categories, Definition 0034: the functor
`Hom(-, I) : 𝒜ᵒᵖ ⥤ Ab` commutes with finite limits and finite colimits. By Stacks 010N (4)
(Mathlib's `Functor.exact_tfae`) this is equivalent to `HomToIsExact I`. -/
theorem homToIsExact_iff_preservesFiniteLimits_and_preservesFiniteColimits (I : 𝒜) :
    HomToIsExact I ↔ PreservesFiniteLimits (preadditiveYoneda.obj I) ∧
      PreservesFiniteColimits (preadditiveYoneda.obj I) := by
  refine Iff.trans ?_ ((Functor.exact_tfae (preadditiveYoneda.obj I)).out 1 4)
  constructor
  · intro h S hS
    exact h S.unop hS.unop
  · intro h S hS
    exact h S.op hS.op

/-- **Characterisation of injective objects.** For an object `I` of an abelian category `𝒜`,
the following are equivalent:
1. `I` is injective;
2. the functor `B ↦ Hom_𝒜(B, I)` is exact, in the form "sends short exact sequences to short
   exact sequences" (`HomToIsExact`), and in the form of Categories, Definition 0034
   "commutes with finite limits and finite colimits" (the last entry of the list);
3. every short exact sequence `0 ⟶ I ⟶ A ⟶ B ⟶ 0` is split (`EverySESStartingAtSplits`);
4. `Ext¹_𝒜(B, I) = 0` for every object `B`, for the `Ext` groups of `HasExt.standard 𝒜`. -/
@[stacks 0136 "Condition (2) appears twice: as `HomToIsExact` (`preadditiveYoneda.obj I` sends
short exact sequences to short exact sequences, Stacks 010N (4)) and, as the fifth entry, as
`preadditiveYoneda.obj I` commuting with finite limits and colimits (Definition 0034); these agree
by Mathlib's `Functor.exact_tfae`. Condition (4) is `Subsingleton (Abelian.Ext B I 1)` for
Mathlib's `HasExt.standard`; (1)⇒(4) is Mathlib's `Abelian.Ext.subsingleton_of_injective`,
(4)⇒(1) uses `Abelian.Ext.contravariant_sequence_exact₁`, (1)⇒(3) is
`ShortComplex.ShortExact.splittingOfInjective`."]
theorem injective_tfae (I : 𝒜) :
    letI := HasExt.standard 𝒜
    List.TFAE [Injective I, HomToIsExact I, EverySESStartingAtSplits I,
      ∀ B : 𝒜, Subsingleton (Abelian.Ext B I 1),
      PreservesFiniteLimits (preadditiveYoneda.obj I) ∧
        PreservesFiniteColimits (preadditiveYoneda.obj I)] := by
  let := HasExt.standard 𝒜
  tfae_have 1 → 2 := homToIsExact_of_injective I
  tfae_have 2 → 1 := injective_of_homToIsExact I
  tfae_have 1 ↔ 3 := injective_iff_everySES_splits I
  tfae_have 1 → 4 := fun h B => subsingleton_ext_one_of_injective I h B
  tfae_have 4 → 1 := injective_of_subsingleton_ext_one I
  tfae_have 2 ↔ 5 := homToIsExact_iff_preservesFiniteLimits_and_preservesFiniteColimits I
  tfae_finish

end
