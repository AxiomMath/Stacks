module

public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionAcyclic

/-!
# Bijectivity of the adjunction map on `Ext` into an acyclic object

Let `L ⊣ R` be an adjunction between abelian categories with `L` exact, and let
`Stacks.ExtAdjunction.extMap` be the adjunction map `Ext^n(A, R M) → Ext^n(L A, M)`: apply `L`
and postcompose with the counit. When `R` is exact this map is bijective
(`Stacks.ExtAdjunction.extMap_bijective`). This file proves bijectivity under a weaker
hypothesis, which only asks `R` to be exact on enough injective presentations: if `P` is a class
of objects of the target such that every `M` in `P` sits in a short exact sequence
`0 ⟶ M ⟶ I ⟶ C ⟶ 0` with `I` injective, `C` in `P`, and image under `R` still short exact, then
the adjunction map is bijective in every degree for every `M` in `P`. This is the case of an
`R`-acyclic object (`R^i R M = 0` for `i > 0`), in the form in which the vanishing is checked
in practice.

## Main results

* `Stacks.ExtAdjunction.extMap_bijective_of_presentations`: the bijectivity.

## Implementation notes

The proof is the dimension shift of `Stacks.ExtAdjunction.extMap_bijective`: the two long exact
sequences of `Ext` in the second variable, for the presentation and for its image under `R`, are
compared by the adjunction map, which commutes with the connecting morphisms
(`Stacks.ExtAdjunction.extMap_naturality_extClass_of_shortExact`) and is bijective on the
injective middle term (both sides vanish in positive degree, `R` preserving injectives) and, by
induction, on the quotient.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

universe w w' v v' u u'

namespace Stacks.ExtAdjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [HasExt.{w} C] [HasExt.{w'} D]

attribute [local instance] Ext.subsingleton_of_injective in
/-- **The adjunction map into an object with good injective presentations is bijective**, the
target category having enough injectives: the dimension shift of
`Stacks.ExtAdjunction.extMap_bijective`, with the exactness of `R` replaced by the short
exactness of the image of each presentation. -/
lemma extMap_bijective_of_presentations [EnoughInjectives D] (P : D → Prop)
    (hP : ∀ M, P M → ∃ (S : ShortComplex D) (_ : S.ShortExact) (_ : (S.map R).ShortExact)
      (_ : Injective S.X₂) (_ : P S.X₃), S.X₁ = M)
    (A : C) (n : ℕ) : ∀ M, P M →
      Function.Bijective (extMap adj A M n : Ext.{w} A (R.obj M) n → Ext.{w'} (L.obj A) M n) := by
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  have hinj : ∀ (I : D) [Injective I] (m : ℕ),
      Function.Bijective (extMap adj A I m : Ext.{w} A (R.obj I) m → Ext.{w'} (L.obj A) I m) := by
    intro I _ m
    have : Injective (R.obj I) := R.injective_obj_of_injective inferInstance
    cases m with
    | zero => exact extMap_zero_bijective adj A I
    | succ m =>
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  induction n with
  | zero => exact fun M _ => extMap_zero_bijective adj A M
  | succ n hn =>
    intro M hM
    obtain ⟨S, hS, hRS, hI, hC, rfl⟩ := hP M hM
    have : Injective (S.map R).X₂ := R.injective_obj_of_injective hI
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extMap adj A S.X₂ n) (extMap adj A S.X₃ n) (extMap adj A S.X₁ (n + 1))
      (by ext e; exact (extMap_naturality_mk₀ adj A S.g n e).symm)
      (by ext e; exact (extMap_naturality_extClass_of_shortExact adj A hS hRS n e).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hRS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj A) hS n (n + 1) rfl))
      (hinj S.X₂ n).surjective (hn S.X₃ hC)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hRS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS y₁ (by subsingleton) rfl)

end Stacks.ExtAdjunction

end
