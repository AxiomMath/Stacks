module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic

/-!
# Dévissage for a cohomological δ-functor

Let `D = {Dⁿ, δ}` be a cohomological δ-functor from an abelian category `A` to a preadditive
category `B` (Stacks 010Q, `CategoryTheory.DeltaFunctor`). Let `P` be a
property of objects of `A` with the following *dévissage property*: every `X` with `P X` fits in
a short exact sequence `0 → X → I → Q → 0` where `I` is killed by all the `Dᵐ⁺¹`, where
`D⁰(I) → D⁰(Q)` is an epimorphism, and where `Q` again satisfies `P`. Then `Dⁿ⁺¹(X) = 0` for
every `n` and every `X` with `P X`.

This is the inductive engine of the proofs of [Stacks, Tag 01EV] and [Stacks, Tag 01EW] — the
step the source states as "and so on and so forth". Only the long exact sequence of the δ-functor
is used, three terms at a time:

* in degree zero, `D⁰(I) → D⁰(Q) --δ--> D¹(X) → D¹(I) = 0` makes `δ` epi while the surjectivity
  of `D⁰(I) → D⁰(Q)` makes it zero, so `D¹(X) = 0`;
* in degree `n + 1`, `Dⁿ⁺¹(Q) --δ--> Dⁿ⁺²(X) → Dⁿ⁺²(I) = 0` makes `δ` epi while the induction
  hypothesis applied to `Q` makes its source zero, so `Dⁿ⁺²(X) = 0`.

## Main results

* `Stacks.CohomologyVanishing.isZero_obj_succ_of_devissage`: the statement above.
* `Stacks.CohomologyVanishing.isZero_obj_succ_of_injective_devissage`: the same with the
  acyclicity of `I` replaced by injectivity of `I` together with the vanishing of the `Dᵐ⁺¹` on
  injective objects — the form in which the two cohomology lemmas use it, since
  `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ` supplies the vanishing.

## Implementation notes

The short exact sequence is handed over as a `CategoryTheory.ShortComplex` together with
`ShortComplex.ShortExact` and an equation `S.X₁ = X`, rather than as an abstract sequence
starting at `X`: the connecting morphism `DeltaFunctor.δ` is indexed by the exactness proof of a
`ShortComplex`, so this is the shape in which it can be applied, and the equation is eliminated
by substitution.

No hypothesis is made on `D` beyond the fields of `CategoryTheory.DeltaFunctor`; in particular
nothing is assumed about `D⁰`, which in the intended application is the global sections functor
over a fixed open.

No tag attribute is attached here: this is one step of the proofs of 01EV and 01EW, not either
tag's statement, and those tags belong to the cohomology chapters.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 01EV](https://stacks.math.columbia.edu/tag/01EV)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
-/

@[expose] public section

universe v v' u u'

namespace Stacks.CohomologyVanishing

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
  [Preadditive B]

/-- **Dévissage for a cohomological δ-functor.** If every object satisfying `P` is the kernel of
a short exact sequence whose middle term is acyclic for `D` in positive degrees, whose degree-zero
part is surjective, and whose third term again satisfies `P`, then `D` vanishes in positive
degrees on every object satisfying `P`. -/
theorem isZero_obj_succ_of_devissage (D : DeltaFunctor A B) (P : A → Prop)
    (step : ∀ X : A, P X → ∃ S : ShortComplex A, S.ShortExact ∧ S.X₁ = X ∧
      (∀ m : ℕ, IsZero ((D.functor (m + 1)).obj S.X₂)) ∧
      Epi ((D.functor 0).map S.g) ∧ P S.X₃) (n : ℕ) :
    ∀ X : A, P X → IsZero ((D.functor (n + 1)).obj X) := by
  have key : ∀ (S : ShortComplex A) (hS : S.ShortExact) (m : ℕ),
      IsZero ((D.functor (m + 1)).obj S.X₂) → D.δ hS m = 0 →
      IsZero ((D.functor (m + 1)).obj S.X₁) := fun S hS m hI h ↦
    have := D.epi_δ_of_map_f_eq_zero hS m (hI.eq_zero_of_tgt _)
    IsZero.of_epi_eq_zero _ h
  induction n with
  | zero =>
    intro X hX
    obtain ⟨S, hS, rfl, hI, hepi, -⟩ := step X hX
    exact key S hS 0 (hI 0)
      ((cancel_epi ((D.functor 0).map S.g)).1 ((D.map_g_δ hS 0).trans comp_zero.symm))
  | succ n ih =>
    intro X hX
    obtain ⟨S, hS, rfl, hI, -, hQ⟩ := step X hX
    exact key S hS (n + 1) (hI _) ((ih S.X₃ hQ).eq_zero_of_src _)

/-- **Dévissage for a cohomological δ-functor, embedding into injectives.** The variant of
`Stacks.CohomologyVanishing.isZero_obj_succ_of_devissage` in which the middle term of the short
exact sequence is injective and the positive-degree parts of `D` are known to vanish on injective
objects. -/
theorem isZero_obj_succ_of_injective_devissage (D : DeltaFunctor A B)
    (hinj : ∀ (m : ℕ) (I : A), Injective I → IsZero ((D.functor (m + 1)).obj I))
    (P : A → Prop)
    (step : ∀ X : A, P X → ∃ S : ShortComplex A, S.ShortExact ∧ S.X₁ = X ∧
      Injective S.X₂ ∧ Epi ((D.functor 0).map S.g) ∧ P S.X₃) (n : ℕ) :
    ∀ X : A, P X → IsZero ((D.functor (n + 1)).obj X) :=
  isZero_obj_succ_of_devissage D P (fun X hX ↦ by
    obtain ⟨S, hS, hX₁, hinj₂, hepi, hQ⟩ := step X hX
    exact ⟨S, hS, hX₁, fun m ↦ hinj m _ hinj₂, hepi, hQ⟩) n

end Stacks.CohomologyVanishing
