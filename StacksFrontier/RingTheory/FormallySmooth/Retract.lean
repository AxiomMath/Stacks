module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Formal smoothness passes to retracts

An `R`-algebra `A` that is a retract of a formally smooth `R`-algebra `B` — that is, one for
which there are `R`-algebra maps `i : A → B` and `r : B → A` with `r ∘ i = id` — is itself
formally smooth over `R`.

Indeed, to lift an `R`-algebra map `f : A → T/I` along a square-zero surjection `T → T/I`,
lift the composite `f ∘ r : B → T/I` to some `g : B → T` using formal smoothness of `B`, and
take `g ∘ i`.

## Main results

* `Algebra.FormallySmooth.of_retract`: formal smoothness passes from an algebra to any retract
  of it.
-/

@[expose] public section

namespace Algebra.FormallySmooth

/-- Formal smoothness passes to retracts: if `i : A →ₐ[R] B` admits an `R`-algebra retraction
`r : B →ₐ[R] A` and `B` is formally smooth over `R`, then so is `A`. -/
theorem of_retract {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [FormallySmooth R B]
    (i : A →ₐ[R] B) (r : B →ₐ[R] A) (hri : r.comp i = AlgHom.id R A) :
    FormallySmooth R A := by
  apply FormallySmooth.of_comp_surjective
  intro T _ _ I hI f
  obtain ⟨g, hg⟩ := FormallySmooth.comp_surjective R B I hI (f.comp r)
  refine ⟨g.comp i, ?_⟩
  rw [← AlgHom.comp_assoc, hg, AlgHom.comp_assoc, hri, AlgHom.comp_id]

end Algebra.FormallySmooth

end
