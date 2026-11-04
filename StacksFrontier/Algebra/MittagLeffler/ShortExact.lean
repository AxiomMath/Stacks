module

public import StacksFrontier.Algebra.MittagLeffler.TensorProductPi

@[expose] public section

universe u v

/-!
# The Mittag-Leffler property in a universally exact sequence

Let `R` be a commutative ring and let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a universally exact
sequence of `R`-modules, that is, a short exact sequence for which `f₁ ⊗ id_T` is injective for
every `R`-module `T`. This file proves that being Mittag-Leffler passes from `M₂` to `M₁`, and
from `M₁` and `M₃` to `M₂`.

Proposition 059M turns "`M` is Mittag-Leffler" into injectivity of the comparison map
`TensorProduct.piRightHom R R M Q : M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` for every family `Q`, so
both items become statements about the commutative diagram

```
M₁ ⊗ (∀ α, Q α) → M₂ ⊗ (∀ α, Q α) → M₃ ⊗ (∀ α, Q α) → 0
      ↓                 ↓                 ↓
∀ α, M₁ ⊗ Q α  → ∀ α, M₂ ⊗ Q α  → ∀ α, M₃ ⊗ Q α
```

whose squares commute by naturality of the comparison map in its module argument, whose top row is
exact by right exactness of `· ⊗ (∀ α, Q α)` and whose left horizontal maps are injective by
universal injectivity of `f₁`. For the first item, the composite along the top and right of the
left square is injective, hence so is the composite along the left and bottom, hence so is its
first factor `piRightHom M₁`; this needs no exactness and is stated for an arbitrary map. For the
second, an element of `Ker (piRightHom M₂)` dies in `∀ α, M₃ ⊗ Q α`, hence in `M₃ ⊗ (∀ α, Q α)`,
so it is `(f₁ ⊗ id) y`; then `piRightHom M₁ y` dies in `∀ α, M₂ ⊗ Q α` componentwise, so `y = 0`.

## Main results

* `Stacks.MittagLeffler.UniversallyExact.solution`: Stacks 059N, the statement of
  `Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective`.

## Implementation notes

Naturality of `TensorProduct.piRightHom` in its module argument is not in Mathlib. It is the
private lemma `piRightHom_comp_rTensor`, the commutativity of each square above, with its
pointwise form `piRightHom_rTensor_apply`; both hold over a commutative semiring, for modules and
index types in arbitrary universes, and they are the only ingredients beyond Proposition 059M.

The two items are the two private lemmas
`Stacks.MittagLeffler.UniversallyExact.piRightHom_injective_of_rTensor_injective` — for one
universally injective map into a module whose comparison map is injective, the comparison map of
the source is injective — and `Stacks.MittagLeffler.UniversallyExact.piRightHom_injective_of_exact`
— the chase in the diagram above. Both are stated one family `Q` at a time, quantified over
neither the family nor the finitely presented test modules of the Mittag-Leffler condition, so
`Small.{v} R` and the universe constraints of 059M enter only where 059M is used, which is in
`solution` alone.

## References

* [StacksProject 059N](https://stacks.math.columbia.edu/tag/059N)
-/



@[expose] public section

/-! ### Naturality of the comparison map in its module argument -/

section Naturality

open TensorProduct

variable {R : Type*} [CommSemiring R] {M M' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] {A : Type*} (Q : A → Type*) [∀ α, AddCommMonoid (Q α)]
  [∀ α, Module R (Q α)]

/-- The comparison map `M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is natural in `M`: for `R`-linear
`f : M → M'` the square with vertical maps `TensorProduct.piRightHom` and horizontal maps induced
by `f` commutes. -/
private lemma piRightHom_comp_rTensor (f : M →ₗ[R] M') :
    piRightHom R R M' Q ∘ₗ LinearMap.rTensor (∀ α, Q α) f =
      (LinearMap.piMap fun α ↦ LinearMap.rTensor (Q α) f) ∘ₗ piRightHom R R M Q := by
  ext x q
  simp

/-- Naturality of `TensorProduct.piRightHom` in its module argument, componentwise. -/
private lemma piRightHom_rTensor_apply (f : M →ₗ[R] M') (x : M ⊗[R] (∀ α, Q α)) (α : A) :
    piRightHom R R M' Q (LinearMap.rTensor (∀ α, Q α) f x) α
      = LinearMap.rTensor (Q α) f (piRightHom R R M Q x α) :=
  congr_fun (LinearMap.congr_fun (piRightHom_comp_rTensor Q f) x) α

end Naturality

namespace Stacks.MittagLeffler.UniversallyExact

open TensorProduct

/-! ### Injectivity of the comparison map along a universally injective map -/

section Injectivity

variable {R : Type*} [CommSemiring R] {M M' : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] {A : Type*} (Q : A → Type*) [∀ α, AddCommMonoid (Q α)]
  [∀ α, Module R (Q α)]

/-- If `f : M → M'` stays injective after tensoring with `∀ α, Q α` and the comparison map of `M'`
for the family `Q` is injective, then so is the comparison map of `M`: the composite along the top
and right of the naturality square is injective, hence so is the composite along its left and
bottom, hence so is the left factor of that composite. -/
private lemma piRightHom_injective_of_rTensor_injective (f : M →ₗ[R] M')
    (hf : Function.Injective (LinearMap.rTensor (∀ α, Q α) f))
    (h : Function.Injective (piRightHom R R M' Q)) :
    Function.Injective (piRightHom R R M Q) := by
  have hcomp := h.comp hf
  rw [← LinearMap.coe_comp, piRightHom_comp_rTensor, LinearMap.coe_comp] at hcomp
  exact hcomp.of_comp

end Injectivity

/-! ### The chase in the two rows -/

section Exact

variable {R : Type*} [CommRing R] {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] {A : Type*} (Q : A → Type*)
  [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)]

/-- Let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be exact with `f₁ ⊗ id_{Q α}` injective for every `α`, and
let the comparison maps of `M₁` and of `M₃` for the family `Q` be injective. Then so is that of
`M₂`: an element `x` of its kernel dies in every `M₃ ⊗[R] Q α`, hence in `M₃ ⊗[R] (∀ α, Q α)` by
injectivity for `M₃`, hence is `(f₁ ⊗ id) y` by right exactness of `· ⊗ (∀ α, Q α)`; the image of
`y` under the comparison map of `M₁` then dies componentwise in `M₂ ⊗[R] Q α`, so `y = 0`. -/
private lemma piRightHom_injective_of_exact {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (h : Function.Exact f₁ f₂) (h₂ : Function.Surjective f₂)
    (hf₁ : ∀ α, Function.Injective (LinearMap.rTensor (Q α) f₁))
    (h₁ : Function.Injective (piRightHom R R M₁ Q))
    (h₃ : Function.Injective (piRightHom R R M₃ Q)) :
    Function.Injective (piRightHom R R M₂ Q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx₃ : LinearMap.rTensor (∀ α, Q α) f₂ x = 0 :=
    (map_eq_zero_iff _ h₃).mp <| funext fun α => by
      rw [piRightHom_rTensor_apply, hx]; simp
  obtain ⟨y, hy⟩ := (rTensor_exact (∀ α, Q α) h h₂ x).mp hx₃
  have hy₀ : y = 0 := (map_eq_zero_iff _ h₁).mp <| funext fun α =>
    (map_eq_zero_iff _ (hf₁ α)).mp <| by
      rw [← piRightHom_rTensor_apply, hy]; exact congr_fun hx α
  rw [← hy, hy₀, map_zero]

end Exact

/-! ### The main result -/

/-- Let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be exact with `f₁ ⊗ id_T` injective for every `R`-module
`T`. Then (1) if `M₂` is Mittag-Leffler, so is `M₁`, and (2) if `M₁` and `M₃` are Mittag-Leffler,
so is `M₂`. -/
public theorem solution
    {R : Type u} [CommRing R] [Small.{v} R] {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] {f₁ : M₁ →ₗ[R] M₂}
    {f₂ : M₂ →ₗ[R] M₃} (h : Function.Exact f₁ f₂) (h₂ : Function.Surjective f₂)
    (hf₁ : ∀ (T : Type v) [AddCommGroup T] [Module R T], Function.Injective (f₁.rTensor T)) :
    ((∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M₂), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) →
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M₁), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ∧
      ((∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M₁), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
                [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) →
        (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M₃), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
                [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) →
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M₂), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) := by
  refine ⟨fun hM₂ => ?_, fun hM₁ hM₃ => ?_⟩
  · -- (1) `M₂` Mittag-Leffler implies `M₁` Mittag-Leffler.
    rw [Module.mittagLeffler_iff_piRightHom_injective R M₁]
    intro A Q _ _
    exact piRightHom_injective_of_rTensor_injective Q f₁ (hf₁ _)
      ((Module.mittagLeffler_iff_piRightHom_injective R M₂).mp hM₂ A Q)
  · -- (2) `M₁` and `M₃` Mittag-Leffler implies `M₂` Mittag-Leffler.
    rw [Module.mittagLeffler_iff_piRightHom_injective R M₂]
    intro A Q _ _
    exact piRightHom_injective_of_exact Q h h₂ (fun α => hf₁ (Q α))
      ((Module.mittagLeffler_iff_piRightHom_injective R M₁).mp hM₁ A Q)
      ((Module.mittagLeffler_iff_piRightHom_injective R M₃).mp hM₃ A Q)

end Stacks.MittagLeffler.UniversallyExact

end

/-!
# The Mittag-Leffler property in a universally exact sequence

Let `R` be a commutative ring. A map `f₁ : M₁ → M₂` of `R`-modules is *universally injective* when
`f₁ ⊗ id_T` is injective for every `R`-module `T`, and a short exact sequence
`0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` is *universally exact* when `f₁` is universally injective
(Definition 058I). An `R`-module `M` is *Mittag-Leffler* when every map `f : P → M` from a
finitely presented module dominates and is dominated by a map `g : P → Q` into a finitely
presented module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`; this is
condition (1) of Proposition 059E, the one of the five conditions there that mentions only `M`,
and it is Definition 059F.

This file states that the Mittag-Leffler property is stable along a universally exact sequence in
two of the three positions: it passes from the middle term to the sub-object, and from the sub-
and quotient objects to the middle term. Tensoring the sequence with a product `∏ T α` and
comparing with the product of the tensored sequences gives a commutative diagram

```
0 → M₁ ⊗ (∏ T α) → M₂ ⊗ (∏ T α) → M₃ ⊗ (∏ T α) → 0
      ↓                ↓                ↓
0 → ∏ (M₁ ⊗ T α) → ∏ (M₂ ⊗ T α) → ∏ (M₃ ⊗ T α) → 0
```

with exact rows — the top row because `f₁` is universally injective and the tensor product is
right exact, the bottom row because products are exact and each `f₁ ⊗ id_{T α}` is injective — and
Proposition 059M reads the Mittag-Leffler property of `M i` off injectivity of the `i`-th vertical
arrow. Injectivity of the middle vertical arrow together with that of the top-left horizontal
arrow forces injectivity of the left vertical arrow, which is item (1); injectivity of the left and
right verticals forces injectivity of the middle one by a chase in the two rows, which is
item (2).

## Main results

* `Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective`: for a
  universally exact sequence `0 → M₁ → M₂ → M₃ → 0` of `R`-modules, `M₂` Mittag-Leffler implies
  `M₁` Mittag-Leffler, and `M₁` and `M₃` Mittag-Leffler imply `M₂` Mittag-Leffler.

## Implementation notes

Choices of form, none of them weakening the source's statement.

*The Mittag-Leffler property is spelled out.* `Mathlib` has no predicate for a Mittag-Leffler
module: `CategoryTheory.Functor.IsMittagLeffler` is the condition on an inverse system, that is
condition (4) of 059E for the dual systems, and does not apply to a module on its own. So the
condition is written inline in the intrinsic form 059E (1), the spelling of Proposition 059M and of
Lemma 05CQ, and it is the same text five times over, once for each occurrence of
"is Mittag-Leffler" in the two items.

*Universal exactness is exactness plus universal injectivity of `f₁`.* Exactness is carried by the
hypotheses `Function.Exact f₁ f₂` and `Function.Surjective f₂`, as in 058K, 058L and 058M, rather
than by a `ShortComplex.ShortExact` object, so that the statement chains with 058K, whose
hypotheses are literally these. Universal injectivity is spelled out with `LinearMap.rTensor`,
exactly as item (1) of 058K does. `Function.Injective f₁`, the third hypothesis of those
statements, is *not* assumed here: it is the case `T = R` of `hf₁`, so assuming it would be
assuming a consequence of another hypothesis.

*The two items are the two conjuncts of one statement.* They share their hypotheses and their proof.
Item (1) uses only `hf₁`: it holds for any universally injective map `f₁ : M₁ → M₂` with `M₂`
Mittag-Leffler, with no quotient in sight. That more general form is the present statement applied
to `M₃ = M₂ ⧸ LinearMap.range f₁` and `f₂ = (LinearMap.range f₁).mkQ`, whose exactness and
surjectivity are `LinearMap.exact_map_mkQ_range` and `Submodule.mkQ_surjective`, so nothing is lost
by stating item (1) for a sequence, as the source does; `h` and `h₂` are hypotheses of the
conjunction, used by item (2), not decoration on item (1).

*An abstract quotient.* `M₃` is an arbitrary module with `Function.Exact f₁ f₂` and
`Function.Surjective f₂` rather than the concrete cokernel `M₂ ⧸ LinearMap.range f₁`, so that a
user with a sequence in hand need not transport along an isomorphism.

*Universes.* The three modules, the test module `T` of universal injectivity and the modules `P`,
`Q`, `N` of the Mittag-Leffler condition all live in `Type v`, with `R : Type u` assumed
`Small.{v}`, the convention of 058K, 058L, 058M, 059E, 059M and 05CQ. This is not a
weakening: `Small.{v} R` is automatic when `v = max u v`, in particular whenever `R` and the
modules share a universe, so the single-universe form is the instance `v := max u v`. It is also
what makes the `Type v` quantifiers the source's quantifiers over all modules — domination may be
tested on the finitely presented modules of `Type v` alone (Lemma 059C) — and it is carried by
Proposition 059M, through which the proof passes.

Faithfulness. (1) No hypothesis is dead: `hf₁` is used by both conjuncts, and `h` and `h₂` by the
second, where they enter as exactness of the tensored row `M₁ ⊗ T → M₂ ⊗ T → M₃ ⊗ T → 0`, that is as
`rTensor_exact _ h h₂`; `Small.{v} R` is used as described above. (2) The scalars and the base are
the source's: `M₁`, `M₂`, `M₃` and all test modules are `R`-modules, `f₁`, `f₂`, `f` and `g` are
`R`-linear, finite presentation is over `R`, and every tensor product is `⊗[R]`; nothing is
localized or base changed. (3) The maps the source names are pinned, not merely asserted to exist:
`f₁ ⊗ id_T` is `f₁.rTensor T`, built from `f₁` itself, and the maps whose kernels are compared in
the Mittag-Leffler condition are `f.rTensor N` and `g.rTensor N`; only the finitely presented module
`Q` and the map `g` are existentially quantified, as they are in 059E (1). (4) The instantiation is
not degenerate: for `R = ℤ`, `M₁ = M₃ = ℤ`, `M₂ = ℤ × ℤ`, `f₁ = inl` and `f₂ = snd` every hypothesis
holds — the sequence is split, hence universally exact (058J (1)) — and all three modules are
Mittag-Leffler, being finitely presented, so `Q = P` and `g = f` witness the condition. Neither item
is vacuous, because the Mittag-Leffler condition is not automatic: over `R = ℤ` the module `ℚ` fails
it (Example 059I), so the hypothesis of item (1) and the conclusion of item (2) can both fail. `hf₁`
is not idle either: it enters item (1) at the single test module `T = ∀ α, Q α` and item (2) at each
`T = Q α`, and it cannot be dropped in favour of bare exactness, since for a merely exact sequence
the source proves only the weaker Lemma 0EGI — `M₁` finitely generated and `M₂` Mittag-Leffler give
`M₃` Mittag-Leffler — and nothing about `M₁` or `M₂`.

## References

* [StacksProject 059N](https://stacks.math.columbia.edu/tag/059N)
-/



@[expose] public section

/-- Let `0 → M₁ →[f₁] M₂ →[f₂] M₃ → 0` be a universally exact sequence of `R`-modules, that is, a
short exact sequence for which `f₁ ⊗ id_T : M₁ ⊗ T → M₂ ⊗ T` is injective for every `R`-module `T`.
Then (1) if `M₂` is Mittag-Leffler, so is `M₁`, and (2) if `M₁` and `M₃` are Mittag-Leffler, so is
`M₂`. Being Mittag-Leffler is spelled out in the intrinsic form 059E (1): every map `f : P → M`
from a finitely presented module dominates and is dominated by a map `g : P → Q` into a finitely
presented module, domination meaning `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. -/
@[stacks 059N "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M and
05CQ; universal exactness is `h`, `h₂` and injectivity of `f₁ ⊗ id_T` for every `T`, as in
058K (1). The two items are the two conjuncts."]
public theorem Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective
    {R : Type u} [CommRing R] [Small.{v} R] {M₁ M₂ M₃ : Type v} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] {f₁ : M₁ →ₗ[R] M₂}
    {f₂ : M₂ →ₗ[R] M₃} (h : Function.Exact f₁ f₂) (h₂ : Function.Surjective f₂)
    (hf₁ : ∀ (T : Type v) [AddCommGroup T] [Module R T], Function.Injective (f₁.rTensor T)) :
    ((∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M₂), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) →
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M₁), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ∧
      ((∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M₁), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
                [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) →
        (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M₃), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
                [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) →
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M₂), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :=
  Stacks.MittagLeffler.UniversallyExact.solution h h₂ hf₁

end

/-!
# Mittag-Leffler passes to a quotient with finitely generated kernel

Let `R` be a commutative ring, let `M` be a Mittag-Leffler `R`-module and let `l : M → M'` be a
surjective `R`-linear map whose kernel is finitely generated. This file proves that `M'` is again
Mittag-Leffler.

Proposition 059M turns "`M` is Mittag-Leffler" into injectivity of the comparison map
`TensorProduct.piRightHom R R M Q : M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` for every family `Q`, and
Proposition 059J turns "`ker l` is finitely generated" into surjectivity of the same map for
`ker l`. So the statement becomes a chase in the commutative diagram

```
M₁ ⊗ (∀ α, Q α) → M₂ ⊗ (∀ α, Q α) → M₃ ⊗ (∀ α, Q α) → 0
      ↓                 ↓                  ↓
∀ α, M₁ ⊗ Q α  → ∀ α, M₂ ⊗ Q α  → ∀ α, M₃ ⊗ Q α  → 0
```

with `M₁ = ker l`, `M₂ = M` and `M₃ = M'`, whose rows are exact by right exactness of the tensor
product, the bottom one componentwise. Let `x` lie in the kernel of the right vertical map.
Exactness of the top row writes `x = (f₂ ⊗ id) m`; commutativity of the right square then makes
each component of `piRightHom M₂ Q m` die in `M₃ ⊗ Q α`, so exactness of the bottom row produces
`z α ∈ M₁ ⊗ Q α` mapping to it. Surjectivity of the left vertical map — this is where finite
generation of the kernel enters — assembles the `z α` into a single `w ∈ M₁ ⊗ (∀ α, Q α)`, and
commutativity of the left square identifies `piRightHom M₂ Q ((f₁ ⊗ id) w)` with
`piRightHom M₂ Q m`. Injectivity of the middle vertical map — this is where the Mittag-Leffler
property of `M` enters — gives `m = (f₁ ⊗ id) w`, whence `x = ((f₂ ∘ f₁) ⊗ id) w`, which is `0`.

## Main results

* `Stacks.MittagLeffler.FgKernelQuotient.solution`: Stacks 0EGI, the statement of
  `Module.mittagLeffler_of_surjective`.

## Implementation notes

The chase above is the whole content of the proposition and is isolated as the private lemma
`Stacks.MittagLeffler.FgKernelQuotient.piRightHom_injective_of_exact`: it is stated for one exact
sequence `M₁ → M₂ → M₃ → 0` and one family `Q`, since that is all the chase uses, and it asks
exactly for surjectivity of the comparison map of `M₁` and injectivity of that of `M₂`. The
statement is then the two invocations of 059M, one of 059J, and one application of that lemma to
`LinearMap.exact_subtype_ker_map l`, the exact sequence `ker l → M → M'`; the bottom row's
exactness is that same sequence tensored by `rTensor_exact`.

The commutativity of each square above is naturality of `TensorProduct.piRightHom` in its module
argument, which is not in Mathlib: it is the private lemma `piRightHom_comp_rTensor`, with its
pointwise form `piRightHom_rTensor_apply`, both over a commutative semiring for modules in
arbitrary universes.

The source states the hypothesis as an exact sequence `M₁ → M₂ → M₃ → 0` with `M₁` finitely
generated, and uses it only through the finite generation of the kernel of `M₂ → M₃`, which is how
the statement phrases it; the kernel is taken as `LinearMap.ker l` with its `Submodule.subtype`.

## References

* [StacksProject 0EGI](https://stacks.math.columbia.edu/tag/0EGI)
-/



@[expose] public section

namespace Stacks.MittagLeffler.FgKernelQuotient

open TensorProduct

/-! ### The chase in the two rows -/

section Exact

variable {R : Type*} [CommRing R] {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] {A : Type*} (Q : A → Type*)
  [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)]

/-- Let `M₁ →[f₁] M₂ →[f₂] M₃ → 0` be exact and let `Q` be a family of `R`-modules. If the
comparison map of `M₁` for `Q` is surjective and that of `M₂` is injective, then that of `M₃` is
injective: an element of the kernel is `(f₂ ⊗ id) m` by right exactness of `· ⊗ (∀ α, Q α)`, each
component of `piRightHom M₂ Q m` then dies in `M₃ ⊗[R] Q α`, hence comes from some
`z α ∈ M₁ ⊗[R] Q α`; surjectivity for `M₁` assembles the `z α` into one `w`, injectivity for `M₂`
identifies `(f₁ ⊗ id) w` with `m`, and `f₂ ∘ₗ f₁ = 0`. -/
private lemma piRightHom_injective_of_exact {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃}
    (h : Function.Exact f₁ f₂) (h₂ : Function.Surjective f₂)
    (h₁ : Function.Surjective (piRightHom R R M₁ Q))
    (hmid : Function.Injective (piRightHom R R M₂ Q)) :
    Function.Injective (piRightHom R R M₃ Q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := LinearMap.rTensor_surjective (∀ α, Q α) h₂ x
  choose z hz using fun α =>
    (rTensor_exact (Q α) h h₂ _).mp (by rw [← piRightHom_rTensor_apply, hx]; simp)
  obtain ⟨w, hw⟩ := h₁ z
  have hwm : LinearMap.rTensor (∀ α, Q α) f₁ w = m := hmid <| funext fun α => by
    rw [piRightHom_rTensor_apply, hw]; exact hz α
  rw [← hwm, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, h.linearMap_comp_eq_zero]
  simp

end Exact

/-! ### The main result -/

/-- If `M` is Mittag-Leffler and `l : M → M'` is a surjective `R`-linear map with finitely
generated kernel, then `M'` is Mittag-Leffler. -/
public theorem solution {R : Type u} [CommRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M] {M' : Type v} [AddCommGroup M'] [Module R M']
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    (l : M →ₗ[R] M') (hl : Function.Surjective l) (hl' : (LinearMap.ker l).FG) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M'), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  -- 059J for `ker l`: its comparison map is surjective.
  have hker := ((Module.Finite.tfae_piRightHom_surjective R (LinearMap.ker l)).out 1 2).mp
    (Module.Finite.iff_fg.mpr hl')
  -- 059M, twice: Mittag-Leffler is injectivity of the comparison map.
  rw [Module.mittagLeffler_iff_piRightHom_injective R M']
  intro A Q _ _
  exact piRightHom_injective_of_exact Q (LinearMap.exact_subtype_ker_map l) hl (hker A Q)
    ((Module.mittagLeffler_iff_piRightHom_injective R M).mp hML A Q)

end Stacks.MittagLeffler.FgKernelQuotient

end

/-!
# Mittag-Leffler passes to a quotient with finitely generated kernel

An `R`-module `M` is *Mittag-Leffler* (Definition 059F) if the equivalent conditions of
Proposition 059E hold; only condition (1) is intrinsic to `M`, and it is the one written out here,
as in 059M, 05CQ and 0AS6: every map `f : P → M` from a finitely presented `R`-module dominates and
is dominated by a map `g : P → Q` into a finitely presented `R`-module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`.

The property is inherited by a quotient of `M` by a finitely generated submodule. Writing the
quotient map as a surjection `l : M → M'` with finitely generated kernel `K`, and testing against a
family `(Q α)` of `R`-modules, right exactness of the tensor product gives a commutative diagram
with exact rows
`K ⊗ (∀ α, Q α) → M ⊗ (∀ α, Q α) → M' ⊗ (∀ α, Q α) → 0` over
`(∀ α, K ⊗ Q α) → (∀ α, M ⊗ Q α) → (∀ α, M' ⊗ Q α) → 0`,
the bottom row being exact because a product of exact sequences with surjective right-hand maps is
exact. The left vertical arrow is surjective because `K` is finitely generated
(Proposition 059J) and the middle one is injective because `M` is Mittag-Leffler
(Proposition 059M); a diagram chase then makes the right vertical arrow injective, so `M'` is
Mittag-Leffler, again by Proposition 059M.

## Main results

* `Module.mittagLeffler_of_surjective`: if `M` is Mittag-Leffler and `l : M → M'` is a surjective
  `R`-linear map whose kernel is finitely generated, then `M'` is Mittag-Leffler.

## Implementation notes

The source states the hypothesis as an exact sequence `M₁ → M₂ → M₃ → 0` with `M₁` finitely
generated. The module `M₁` is inert in that statement — only the image of `M₁ → M₂`, which is the
kernel of `M₂ → M₃`, enters the proof — so the hypothesis is stated here in the equivalent form of
its Mathlib sibling `Module.finitePresentation_of_surjective`: a surjection `l : M → M'` with
`(LinearMap.ker l).FG`. The two are interchangeable: given the source's exact sequence, `ker l` is
the range of `M₁ → M₂`, hence finitely generated as the image of a finitely generated module, and
conversely `M₁ := ker l` with its inclusion realizes the source's sequence. The name is that
sibling's with `finitePresentation` replaced by `mittagLeffler`.

Mathlib has no predicate for a Mittag-Leffler module — its
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system*,
that is condition (4) of 059E for the system of duals — so the condition is spelled out inline on
both sides of the implication, in the intrinsic form 059E (1) and byte for byte as in the
left-hand side of `Module.mittagLeffler_iff_piRightHom_injective` (059M). Mutual domination is
equality of the kernels of the tensored maps, `f ⊗ id_N` being `f.rTensor N`, as in 059D
(`LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp`).

The test data of the Mittag-Leffler condition — the finitely presented modules `P`, `Q` and the
module `N` — range over `Type v`, the universe of `M` and `M'`, as in 059D, 059E, 059M, 05CQ and
0AS6, and `Small.{v} R` is what puts them there. That hypothesis is load-bearing for the source's
route: both of its steps invoke 059M, which carries it. It is automatic when `R` itself lives in
`Type v`, by `small_self`, and a quotient in a larger universe is reached by applying the statement
to a `ULift` copy.

Faithfulness. (1) No hypothesis is idle: taking `l = LinearMap.id` turns the conclusion back into
`hML`, so `hML` cannot be dropped (else `ℚ` would be Mittag-Leffler over `ℤ`); dropping `hl` allows
`l = 0 : ℤ →ₗ[ℤ] ℚ`, whose kernel `⊤ = ℤ` is finitely generated, with `ℤ` Mittag-Leffler and `ℚ`
not; dropping `hl'` allows the quotient map from the free `ℤ`-module on `ℚ`, which is
Mittag-Leffler by 059P, onto `ℚ`, which is not; and `Small.{v} R` is used as described above.
(2) The scalars and the base are the source's: one commutative ring `R` throughout, `l` is
`R`-linear, `LinearMap.ker l` is an `R`-submodule, every tensor product in the Mittag-Leffler
condition is `⊗[R]` and both occurrences of the condition are over `R`; nothing is localized or
base changed. (3) The map the source leaves implicit in `M₂ → M₃` is pinned: it is the given
`l : M →ₗ[R] M'`, its surjectivity and the finite generation of its kernel are hypotheses on that
very map, and the maps of the Mittag-Leffler condition are pinned to `LinearMap.rTensor N f` and
`LinearMap.rTensor N g` with their kernels compared by equality. (4) The instantiation is not
degenerate: for `R = ℤ`, `M = ℤ`, `M' = ℤ ⧸ 2ℤ` and `l` the quotient map, the kernel `2ℤ` is
finitely generated, `hML` holds since `ℤ` is finitely presented (059E (1) with `Q = P`, `g = f`),
and the conclusion is the Mittag-Leffler condition for `ℤ ⧸ 2ℤ`, which is not vacuous — `P = ℤ`
and `f = mkQ` is a map from a finitely presented module, and the witness is `Q = ℤ ⧸ 2ℤ`, `g = f`.

## References

* [StacksProject 0EGI](https://stacks.math.columbia.edu/tag/0EGI)
-/



@[expose] public section

/-- Let `R` be a commutative ring, let `M` be a Mittag-Leffler `R`-module — every map `f : P → M`
from a finitely presented `R`-module dominates and is dominated by a map `g : P → Q` into a
finitely presented `R`-module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`,
which is condition (1) of Proposition 059E — and let `l : M → M'` be a surjective `R`-linear map
whose kernel is finitely generated. Then `M'` is Mittag-Leffler. -/
@[stacks 0EGI "The exact sequence `M₁ → M₂ → M₃ → 0` with `M₁` finitely generated is stated as a
surjection with finitely generated kernel, as in `Module.finitePresentation_of_surjective`;
Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M, 05CQ and 0AS6, with test
data in the universe of `M`, whence `Small.{v} R`. See the module docstring."]
public theorem Module.mittagLeffler_of_surjective {R : Type u} [CommRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M] {M' : Type v} [AddCommGroup M'] [Module R M']
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    (l : M →ₗ[R] M') (hl : Function.Surjective l) (hl' : (LinearMap.ker l).FG) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M'), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
  Stacks.MittagLeffler.FgKernelQuotient.solution hML l hl hl'

end
