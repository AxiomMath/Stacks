module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic

/-!
# Descending dévissage for a cohomological δ-functor

Let `D = {Dⁿ, δ}` be a cohomological δ-functor from an abelian category `A` to a preadditive
category `B`, and let `P` be a class of objects of `A`. Suppose

* `D` already vanishes on `P` above some degree `e`, and
* every `X` satisfying `P` is a *quotient* in a short exact sequence `0 → X₁ → X₂ → X → 0`
  whose middle term is `D`-acyclic in positive degrees and whose sub-object again satisfies `P`.

Then `D` vanishes on `P` in *every* positive degree. The induction runs downwards from the
bound `e`, reading `Dᵖ(X₂) → Dᵖ(X) → Dᵖ⁺¹(X₁)` off the long exact sequence: the left term
vanishes by acyclicity of `X₂` and the right term by the inductive hypothesis one degree up, so
the middle term vanishes too.

This is the opposite orientation to `Stacks.CohomologyVanishing.isZero_obj_succ_of_devissage`,
which embeds `X` as a *sub*-object of an acyclic object and needs no vanishing bound. Both
shapes occur in the Stacks project, and this one is the shape of the cohomological arguments of
Chapter 30 that start from a finite affine cover:

* [Stacks, Tag 01YS] part (4) and [Stacks, Tag 0B5Q] part (3) — eventual vanishing of the higher
  cohomology of a coherent sheaf under twisting. There `P` is coherence, `e` is again read off a
  finite affine cover, and the short exact sequence is the kernel sequence of a surjection from
  a finite direct sum of twists.

## Main results

* `Stacks.HighTwistDevissage.isZero_obj_of_shortExact_of_isZero`: the one-step long exact
  sequence argument, `Dⁿ(X₂) = 0` and `Dⁿ⁺¹(X₁) = 0` imply `Dⁿ(X₃) = 0`.
* `Stacks.HighTwistDevissage.isZero_obj_of_descending_devissage_of_lt`: the descending induction
  with its decreasing parameter exposed, which is what carries the induction.
* `Stacks.HighTwistDevissage.isZero_obj_of_descending_devissage`: the statement above.
* `Stacks.HighTwistDevissage.exists_isZero_obj_twist_of_descending_devissage`: the *twisted* form,
  in which the conclusion is vanishing on all sufficiently large twists rather than outright
  vanishing. This is the engine of [Stacks, Tag 01YS] part (4) and [Stacks, Tag 0B5Q] part (3),
  and `exists_isZero_obj_twist_of_descending_devissage_of_lt` is the induction behind it.

## Implementation notes

The induction is on an auxiliary natural number `k` measuring how far the degree `p` is allowed
to sit *below* the vanishing bound: the hypothesis is `e < p + k`, so `k = 0` is the already
known range `e < p` and each step buys one more degree downwards. Instantiating at `k = e + 1`
covers every `p ≥ 1`, since `e < p + e + 1` whenever `p ≥ 1`. A direct downward recursion on
`e - p` would need the same bookkeeping and would not be shorter.

The acyclicity hypothesis on the middle term is stated degreewise in every positive degree
rather than for the single degree in play, because the induction consumes it at `p` and at every
degree between `p` and `e`; nothing is gained by indexing it.

**The single class `P` is a real restriction, and [Stacks, Tag 0EBD] does not fit it.** An earlier
version of this note listed 0EBD here, with `P` quasi-coherence and the short exact sequence
`0 → F' → ⊕ⱼ L^{⊗ -dⱼ} → F → 0` coming from global generation after an ample twist. That is
wrong: the sequence exists only when `F` is of *finite type* ([Stacks, Tag 01Q3], clause (8)),
and demanding it for every quasi-coherent `F` is a hypothesis with no instances on a nonempty
scheme — no module of infinite type is a quotient of a finite direct sum of invertible modules.
Meanwhile the sequence's first term, the kernel of a surjection onto a finite-type module, is
quasi-coherent and nothing more, so the class producing the sequence and the class the induction
descends over are genuinely different. 0EBD needs the two-class form,
`Stacks.DevissageColimit.isZero_obj_of_descending_devissage_of_reduction`, whose extra hypothesis
is the colimit reduction ([Stacks, Tag 01PG] with Cohomology, Lemma 20.19.1) that the source uses
to pass from the finite-type modules to all quasi-coherent ones. The 01YS/0B5Q shape above is
unaffected: there `P` is coherence, which the kernel of a surjection onto a coherent sheaf again
satisfies.

No tag attribute is attached: this is an engine for several tags of Chapter 30 and the statement
of none of them.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public section

universe v v' u u'

namespace Stacks.HighTwistDevissage

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B]
  [Preadditive B]

/-- **One step of the long exact sequence.** For a short exact sequence
`0 → X₁ → X₂ → X₃ → 0`, if `Dⁿ(X₂)` and `Dⁿ⁺¹(X₁)` both vanish then so does `Dⁿ(X₃)`: the
connecting morphism `δ : Dⁿ(X₃) ⟶ Dⁿ⁺¹(X₁)` is a monomorphism because the map it follows is
zero, and it is itself zero because its target is. -/
theorem isZero_obj_of_shortExact_of_isZero (D : DeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) (h₂ : IsZero ((D.functor n).obj S.X₂))
    (h₁ : IsZero ((D.functor (n + 1)).obj S.X₁)) :
    IsZero ((D.functor n).obj S.X₃) :=
  haveI : Mono (D.δ hS n) :=
    D.mono_δ_of_map_g_eq_zero hS n (h₂.eq_zero_of_src ((D.functor n).map S.g))
  IsZero.of_mono_eq_zero (D.δ hS n) (h₁.eq_zero_of_tgt (D.δ hS n))

/-- **The descending dévissage induction**, with the parameter `k` that drives it exposed: `D`
vanishes in every degree `p ≥ 1` with `e < p + k`, by induction on `k`.

For `k = 0` this is the hypothesis `hbound`. The induction step uses the short exact sequence
supplied by `step` together with `isZero_obj_of_shortExact_of_isZero`, applying the inductive
hypothesis one degree higher, where the budget `k` suffices. -/
theorem isZero_obj_of_descending_devissage_of_lt (D : DeltaFunctor A B) (P : A → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ X : A, P X → IsZero ((D.functor p).obj X))
    (step : ∀ X : A, P X → ∃ S : ShortComplex A, S.ShortExact ∧ S.X₃ = X ∧ P S.X₁ ∧
      ∀ m : ℕ, 0 < m → IsZero ((D.functor m).obj S.X₂)) :
    ∀ k p : ℕ, 0 < p → e < p + k → ∀ X : A, P X → IsZero ((D.functor p).obj X) := by
  intro k
  induction k with
  | zero =>
    intro p _ hlt X hX
    exact hbound p (by omega) X hX
  | succ k ih =>
    intro p hp hlt X hX
    by_cases hep : e < p
    · exact hbound p hep X hX
    · obtain ⟨S, hS, hX₃, hP₁, hacyc⟩ := step X hX
      subst hX₃
      exact isZero_obj_of_shortExact_of_isZero D hS p (hacyc p hp)
        (ih (p + 1) (by omega) (by omega) S.X₁ hP₁)

/-- **Descending dévissage for a cohomological δ-functor.** If `D` vanishes on the class `P`
above the degree `e`, and every object of `P` is the quotient term of a short exact sequence
whose middle term is `D`-acyclic in positive degrees and whose first term is again in `P`, then
`D` vanishes on `P` in every positive degree. -/
theorem isZero_obj_of_descending_devissage (D : DeltaFunctor A B) (P : A → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ X : A, P X → IsZero ((D.functor p).obj X))
    (step : ∀ X : A, P X → ∃ S : ShortComplex A, S.ShortExact ∧ S.X₃ = X ∧ P S.X₁ ∧
      ∀ m : ℕ, 0 < m → IsZero ((D.functor m).obj S.X₂))
    (p : ℕ) (hp : 0 < p) (X : A) (hX : P X) : IsZero ((D.functor p).obj X) :=
  isZero_obj_of_descending_devissage_of_lt D P e hbound step (e + 1) p hp (by omega) X hX

section Twisted

variable (D : DeltaFunctor A B) (T : ℤ → A ⥤ A) [∀ d : ℤ, (T d).PreservesZeroMorphisms]
  (P : A → Prop) (e : ℕ)

/-- **The twisted descending dévissage induction**, with the parameter `k` that drives it
exposed. See `Stacks.HighTwistDevissage.exists_isZero_obj_twist_of_descending_devissage` for the
statement. -/
theorem exists_isZero_obj_twist_of_descending_devissage_of_lt
    (hbound : ∀ p : ℕ, e < p → ∀ X : A, P X → ∀ d : ℤ, IsZero ((D.functor p).obj ((T d).obj X)))
    (step : ∀ X : A, P X → ∃ S : ShortComplex A, S.X₃ = X ∧ P S.X₁ ∧
      (∀ d : ℤ, (S.map (T d)).ShortExact) ∧
      ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
        IsZero ((D.functor m).obj ((T d).obj S.X₂))) :
    ∀ k p : ℕ, 0 < p → e < p + k → ∀ X : A, P X →
      ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → IsZero ((D.functor p).obj ((T d).obj X)) := by
  intro k
  induction k with
  | zero =>
    intro p _ hlt X hX
    exact ⟨0, fun d _ => hbound p (by omega) X hX d⟩
  | succ k ih =>
    intro p hp hlt X hX
    by_cases hep : e < p
    · exact ⟨0, fun d _ => hbound p hep X hX d⟩
    · obtain ⟨S, hX₃, hP₁, hSE, d₂, hd₂⟩ := step X hX
      subst hX₃
      obtain ⟨d₁, hd₁⟩ := ih (p + 1) (by omega) (by omega) S.X₁ hP₁
      refine ⟨max d₁ d₂, fun d hd => ?_⟩
      exact isZero_obj_of_shortExact_of_isZero D (hSE d) p
        (hd₂ d (le_trans (le_max_right d₁ d₂) hd) p hp)
        (hd₁ d (le_trans (le_max_left d₁ d₂) hd))

/-- **Twisted descending dévissage for a cohomological δ-functor.** Let `T d : A ⥤ A`, `d : ℤ`,
be a family of endofunctors — in the application, twisting by the `d`-th power of an invertible
sheaf. If

* `D` vanishes on every twist of every object of `P` above the degree `e`, and
* every object of `P` is the quotient term of a short exact sequence whose every twist is again
  short exact, whose first term is again in `P`, and whose middle term is `D`-acyclic in positive
  degrees *for all sufficiently large twists*,

then for every object of `P` and every positive degree, `D` vanishes on all sufficiently large
twists.

This is the shape of [Stacks, Tag 01YS] part (4) and [Stacks, Tag 0B5Q] part (3): the dévissage
sequence is the kernel sequence of a surjection from a finite direct sum of twists of the
structure sheaf, the acyclicity of the middle term for large twists is the cohomology
computation on the twists themselves, and `e` is read off a finite affine cover. The eventual
bound is `max` of the one for the middle term and the one the induction returns one degree up. -/
theorem exists_isZero_obj_twist_of_descending_devissage
    (hbound : ∀ p : ℕ, e < p → ∀ X : A, P X → ∀ d : ℤ, IsZero ((D.functor p).obj ((T d).obj X)))
    (step : ∀ X : A, P X → ∃ S : ShortComplex A, S.X₃ = X ∧ P S.X₁ ∧
      (∀ d : ℤ, (S.map (T d)).ShortExact) ∧
      ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
        IsZero ((D.functor m).obj ((T d).obj S.X₂)))
    (p : ℕ) (hp : 0 < p) (X : A) (hX : P X) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → IsZero ((D.functor p).obj ((T d).obj X)) :=
  exists_isZero_obj_twist_of_descending_devissage_of_lt D T P e hbound step (e + 1) p hp
    (by omega) X hX

end Twisted

end Stacks.HighTwistDevissage

end
