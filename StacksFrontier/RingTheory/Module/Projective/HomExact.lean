module

public import StacksCore.Algebra.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Linear.Yoneda
import StacksCore.Tactic.StacksAttribute

/-!
# Projective modules are those with an exact `Hom` functor

Let `R` be a ring. The Stacks project defines an `R`-module `P` to be *projective* when the
functor `Hom_R(P, -) : Mod_R → Mod_R` is exact (Stacks tag 05CE, Definition 10.77.1). Mathlib
defines `Module.Projective R P` instead by asking that the canonical surjection `(P →₀ R) → P`
split. This file proves that the two notions agree.

Over a commutative ring `R`, `Hom_R(P, -)` is the functor
`(linearCoyoneda R (ModuleCat R)).obj (op (ModuleCat.of R P)) : ModuleCat R ⥤ ModuleCat R`,
and "exact" may be read either as "sends short exact sequences to short exact sequences" or as
"preserves finite limits and finite colimits"; these are equivalent for additive functors
between abelian categories (`CategoryTheory.Functor.exact_tfae`), and both forms are stated.

Since `Hom_R(P, -)` is always left exact (Stacks tag 0582, `LinearMap.exact_iff_homLeft`), the
content of the statement is that `Hom_R(P, N) → Hom_R(P, N'')` is onto whenever `N → N''` is;
this is also recorded elementwise, for an arbitrary (possibly noncommutative) ring, with the
hom-sets regarded as abelian groups.

## Conventions

The modules range over a universe `max u v` containing that of `R`, so that the free module
`P →₀ R` used to test projectivity lives in the same category as `P`.

## Main results

* `Module.projective_iff_homLeft_shortExact`: `P` is projective iff for every short exact
  sequence `0 → N₁ → N₂ → N₃ → 0` the sequence `0 → Hom(P, N₁) → Hom(P, N₂) → Hom(P, N₃) → 0`
  is exact.
* `Module.projective_iff_shortExact_map_linearCoyoneda`: over a commutative ring, `P` is
  projective iff `Hom_R(P, -) : ModuleCat R ⥤ ModuleCat R` preserves short exact sequences.
* `Module.projective_iff_preservesFiniteLimits_and_preservesFiniteColimits_linearCoyoneda`:
  the same with "exact" read as preserving finite limits and finite colimits.

## References

* [Stacks: Tag 05CE](https://stacks.math.columbia.edu/tag/05CE)
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace Module

section Ring

variable {R : Type u} [Ring R] (P : Type (max u v)) [AddCommGroup P] [Module R P]

/-- An `R`-module `P` is projective if and only if `Hom_R(P, -)` carries every short exact
sequence `0 → N₁ → N₂ → N₃ → 0` to a short exact sequence
`0 → Hom(P, N₁) → Hom(P, N₂) → Hom(P, N₃) → 0`. -/
@[stacks 05CE "elementwise form, any ring"]
theorem projective_iff_homLeft_shortExact :
    Module.Projective R P ↔ ∀ (N₁ N₂ N₃ : Type (max u v)) [AddCommGroup N₁] [Module R N₁]
      [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
      (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃), Function.Injective f → Function.Exact f g →
        Function.Surjective g →
        Function.Injective (LinearMap.compRight (M := P) ℕ f) ∧
        Function.Exact (LinearMap.compRight (M := P) ℕ f) (LinearMap.compRight (M := P) ℕ g) ∧
        Function.Surjective (LinearMap.compRight (M := P) ℕ g) := by
  refine ⟨fun _ N₁ N₂ N₃ _ _ _ _ _ _ f g hf hfg hg ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨hinj, hex⟩ := (LinearMap.exact_iff_homLeft f g).1 ⟨hf, hfg⟩ P
    exact ⟨hinj, hex, fun k ↦ projective_lifting_property g k hg⟩
  · have hπ := Finsupp.linearCombination_id_surjective R P
    obtain ⟨-, -, hsurj⟩ := h _ _ _ _ _ (LinearMap.ker _).injective_subtype
      (LinearMap.exact_subtype_ker_map _) hπ
    exact projective_def'.2 (hsurj LinearMap.id)

end Ring

section CommRing

variable {R : Type u} [CommRing R] (P : Type (max u v)) [AddCommGroup P] [Module R P]

/-- An `R`-module `P` is projective if and only if the functor
`Hom_R(P, -) : ModuleCat R ⥤ ModuleCat R` sends short exact sequences to short exact
sequences. -/
@[stacks 05CE]
theorem projective_iff_shortExact_map_linearCoyoneda :
    Module.Projective R P ↔ ∀ S : ShortComplex (ModuleCat.{max u v} R), S.ShortExact →
      (S.map ((linearCoyoneda R (ModuleCat.{max u v} R)).obj
        (op (ModuleCat.of R P)))).ShortExact := by
  refine ⟨fun _ S hS ↦ ?_, fun h ↦ ?_⟩
  · have := hS.mono_f
    refine .mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x₂ hx₂
      change x₂ ≫ S.g = 0 at hx₂
      exact ⟨hS.exact.lift x₂ hx₂, hS.exact.lift_f x₂ hx₂⟩
    · rw [ModuleCat.mono_iff_injective]
      exact fun a b hab ↦ (cancel_mono S.f).1 hab
    · rw [ModuleCat.epi_iff_surjective]
      intro k
      obtain ⟨l, hl⟩ := projective_lifting_property S.g.hom k.hom
        ((ModuleCat.epi_iff_surjective _).1 hS.epi_g)
      exact ⟨ModuleCat.ofHom l, ModuleCat.hom_ext (by
        rw [← hl]
        rfl)⟩
  · have hπ := Finsupp.linearCombination_id_surjective R P
    have hepi := (h _ (LinearMap.shortExact_shortComplexKer hπ)).epi_g
    rw [ModuleCat.epi_iff_surjective] at hepi
    obtain ⟨s, hs⟩ := hepi (𝟙 (ModuleCat.of R P))
    exact projective_def'.2 ⟨s.hom, congrArg ModuleCat.Hom.hom hs⟩

/-- An `R`-module `P` is projective if and only if the functor
`Hom_R(P, -) : ModuleCat R ⥤ ModuleCat R` is exact, in the sense that it preserves finite
limits and finite colimits. -/
@[stacks 05CE "exact functor as preserving finite limits and finite colimits"]
theorem projective_iff_preservesFiniteLimits_and_preservesFiniteColimits_linearCoyoneda :
    Module.Projective R P ↔
      PreservesFiniteLimits ((linearCoyoneda R (ModuleCat.{max u v} R)).obj
        (op (ModuleCat.of R P))) ∧
      PreservesFiniteColimits ((linearCoyoneda R (ModuleCat.{max u v} R)).obj
        (op (ModuleCat.of R P))) :=
  (projective_iff_shortExact_map_linearCoyoneda P).trans ((Functor.exact_tfae _).out 1 4)

end CommRing

end Module
