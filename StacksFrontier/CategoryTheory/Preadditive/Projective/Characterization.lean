module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import StacksFrontier.CategoryTheory.Preadditive.Projective.Basic

/-!
# The characterisation of projective objects (Stacks 013C)

Let `𝒜` be an abelian category and `P` an object of `𝒜`. This file proves the converse
`(2) → (1)` (an exact `Hom(P, -)` makes `P` projective) and assembles the four conditions of
Stacks, Homological Algebra, Section 12.28 (Tag 013C) into `projective_tfae`. The equivalence
`(1) ↔ (3)` is `projective_iff_every_ses_splits`, and `(1) ↔ (4)` is Mathlib's
`CategoryTheory.projective_iff_subsingleton_ext_one`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- If `Hom(P, -)` sends short exact sequences to short exact sequences, then `P` is
projective: apply it to `0 → ker e → E → X → 0` for an epimorphism `e : E ⟶ X`. -/
lemma projective_of_homFunctorExact {P : 𝒜} (h : HomFunctorExact P) : Projective P := by
  refine ⟨fun {E X} f e _ => ?_⟩
  let S : ShortComplex 𝒜 := ShortComplex.mk (kernel.ι e) e (kernel.condition e)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel e
      mono_f := equalizer.ι_mono
      epi_g := inferInstance }
  have hepi : Epi ((homFunctor P).map e) := (h S hS).epi_g
  rw [AddCommGrpCat.epi_iff_surjective] at hepi
  obtain ⟨g, hg⟩ := hepi f
  exact ⟨g, hg⟩

/-- `(1) ↔ (2)`: `P` is projective iff `Hom(P, -)` is exact. -/
theorem projective_iff_homFunctorExact (P : 𝒜) : Projective P ↔ HomFunctorExact P :=
  ⟨homFunctorExact_of_projective, projective_of_homFunctorExact⟩

/-- **Stacks 013C.** Let `𝒜` be an abelian category and `P` an object of `𝒜`. The following
are equivalent:
1. `P` is projective;
2. the functor `B ↦ Hom(P, B)` is exact (it sends short exact sequences of `𝒜` to short exact
   sequences of abelian groups, `HomFunctorExact`);
3. every short exact sequence `0 → A → B → P → 0` splits (`EverySESEndingInPSplits`);
4. `Ext(P, A) = 0` for every `A`, stated as `Subsingleton (Ext P A 1)` for any choice of
   `HasExt` universe.

The Stacks `Ext_𝒜(P, A)` is the (Yoneda) group of extension classes `0 → A → E → P → 0`;
Mathlib's `Abelian.Ext P A 1` (derived category `Ext`) is the standard model of it. The
equivalence `(1) ↔ (4)` is Mathlib's `CategoryTheory.projective_iff_subsingleton_ext_one`. -/
@[stacks 013C "the four conditions as `List.TFAE`; (4) uses Mathlib's `Abelian.Ext P A 1` \
  for the Yoneda `Ext`, via `CategoryTheory.projective_iff_subsingleton_ext_one`"]
theorem projective_tfae [HasExt.{w} 𝒜] (P : 𝒜) :
    List.TFAE [Projective P, HomFunctorExact P, EverySESEndingInPSplits P,
      ∀ A : 𝒜, Subsingleton (Abelian.Ext.{w} P A 1)] := by
  tfae_have 1 ↔ 2 := projective_iff_homFunctorExact P
  tfae_have 1 ↔ 3 := projective_iff_every_ses_splits P
  tfae_have 1 ↔ 4 := projective_iff_subsingleton_ext_one
  tfae_finish

end
