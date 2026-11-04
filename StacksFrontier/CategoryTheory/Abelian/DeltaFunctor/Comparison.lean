module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-! # A morphism of δ-functors that is invertible in degree zero

Let `F` and `G` be cohomological δ-functors (`CategoryTheory.DeltaFunctor`, Stacks 010Q) between
abelian categories and let `η : F ⟶ G` be a morphism of δ-functors (Stacks 010R).  Suppose that

* `η` is an isomorphism in degree `0` at every object, and
* every object of the source admits a monomorphism into an object that **both** `F` and `G` kill
  in every positive degree.

Then `η` is an isomorphism in **every** degree at every object.

The effacing object need not be injective, and the source category need not have enough
injectives or any colimits: only the vanishing of `Fⁿ⁺¹` and `Gⁿ⁺¹` on it is assumed. This is the
degree induction in the proof of Stacks 0A37.

## Main definitions

* `DeltaFunctor.ladderδ₁`: the comparison ladder from `Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)` to
  `Gⁿ(X₂) → Gⁿ(X₃) → Gⁿ⁺¹(X₁)`, whose vertical maps are the components of `η`.

## Main results

* `DeltaFunctor.isIso_app_of_isIso_app_zero`: the conclusion, pointwise.
* `DeltaFunctor.isIso_app_of_isIso_app_zero'`: the same as invertibility of the natural
  transformation `η.app n : Fⁿ ⟶ Gⁿ`.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010R](https://stacks.math.columbia.edu/tag/010R)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.DeltaFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {F G : DeltaFunctor A B}

/-- **The comparison ladder of a morphism of δ-functors at the first stretch through `δ`**: the
morphism of short complexes from `Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)` to `Gⁿ(X₂) → Gⁿ(X₃) → Gⁿ⁺¹(X₁)`
whose vertical maps are the components of `η`. -/
@[simps]
def ladderδ₁ (η : F ⟶ G) {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    F.scδ₁ hS n ⟶ G.scδ₁ hS n where
  τ₁ := (η.app n).app S.X₂
  τ₂ := (η.app n).app S.X₃
  τ₃ := (η.app (n + 1)).app S.X₁
  comm₁₂ := ((η.app n).naturality S.g).symm
  comm₂₃ := η.comm hS n

/-- **A morphism of δ-functors invertible in degree zero between two δ-functors effaced by a
common family of monomorphisms is invertible in every degree.**

The hypotheses are: `η` is an isomorphism in degree `0` at every object, and every object `X`
admits a monomorphism `X ⟶ E` with `Fⁿ⁺¹(E) = 0` and `Gⁿ⁺¹(E) = 0` for every `n`. -/
@[sga "4 XII 6.2" "(c)⇒(a), special case", sga "4½ Arcata 4.3.6" "(iii) ⇒ (i)"]
theorem isIso_app_of_isIso_app_zero (η : F ⟶ G)
    (h0 : ∀ X : A, IsIso ((η.app 0).app X))
    (heff : ∀ X : A, ∃ (E : A) (ι : X ⟶ E), Mono ι ∧
      (∀ n : ℕ, IsZero ((F.functor (n + 1)).obj E)) ∧
      (∀ n : ℕ, IsZero ((G.functor (n + 1)).obj E)))
    (n : ℕ) (X : A) : IsIso ((η.app n).app X) := by
  induction n generalizing X with
  | zero => exact h0 X
  | succ n ih =>
    obtain ⟨E, ι, _, hFz, hGz⟩ := heff X
    have hS : (ShortComplex.cokernelSequence ι).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact ι
        mono_f := ‹Mono ι›
        epi_g := inferInstance }
    have hEpi : ∀ (H : DeltaFunctor A B), (∀ n : ℕ, IsZero ((H.functor (n + 1)).obj E)) →
        Epi (H.δ hS n) := fun H hz => H.epi_δ_of_map_f_eq_zero hS n ((hz n).eq_of_tgt _ 0)
    have hEpiF := hEpi F hFz
    have hEpiG := hEpi G hGz
    have := ih (ShortComplex.cokernelSequence ι).X₂
    have := ih (ShortComplex.cokernelSequence ι).X₃
    have hm : Mono ((η.app (n + 1)).app X) :=
      ShortComplex.mono_of_epi_of_epi_of_mono (ladderδ₁ η hS n) (G.scδ₁_exact hS n)
        hEpiF (IsIso.epi_of_iso ((η.app n).app _)) (IsIso.mono_of_iso ((η.app n).app _))
    have he : Epi ((η.app (n + 1)).app X) :=
      @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_comp' inferInstance hEpiG) (η.comm hS n).symm
    exact isIso_of_mono_of_epi _

/-- **The degree-`n` component of such a morphism of δ-functors is an isomorphism of
functors.** -/
theorem isIso_app_of_isIso_app_zero' (η : F ⟶ G)
    (h0 : ∀ X : A, IsIso ((η.app 0).app X))
    (heff : ∀ X : A, ∃ (E : A) (ι : X ⟶ E), Mono ι ∧
      (∀ n : ℕ, IsZero ((F.functor (n + 1)).obj E)) ∧
      (∀ n : ℕ, IsZero ((G.functor (n + 1)).obj E)))
    (n : ℕ) : IsIso (η.app n) :=
  have := isIso_app_of_isIso_app_zero η h0 heff n
  NatIso.isIso_of_isIso_app _

end CategoryTheory.DeltaFunctor

end
