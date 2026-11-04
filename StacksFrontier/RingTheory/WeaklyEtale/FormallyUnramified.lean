module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.Smooth.Fiber
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Flat multiplication maps are formally unramified

Let `A → B` be a map of commutative rings. If the multiplication map `B ⊗[A] B → B` is flat,
then `B` is formally unramified over `A`. Adding finiteness hypotheses upgrades this: if the
map is of finite type, then it is unramified; if it is flat and of finite presentation, then it
is étale. Consequently, a weakly étale map of finite presentation is étale.

## Main results

* `formallyUnramified_of_flat_lmul` (Stacks 092M): flatness of the multiplication map implies
  formal unramifiedness.
* `unramified_of_finiteType_and_etale_of_finitePresentation` (Stacks 0CKP): the two
  conclusions for a flat multiplication map, together with the weakly étale consequence.

## Implementation notes

The multiplication map is `Algebra.TensorProduct.lmul' A`. Formal unramifiedness is expressed
by `Algebra.FormallyUnramified A B`, whose defining condition is that the module of Kähler
differentials is subsingleton.

The three assertions of Stacks 0CKP are bundled in one proposition to retain both numbered
conclusions and the concluding weakly étale case of the source lemma.

## References

* [Stacks Project, Tag 092M](https://stacks.math.columbia.edu/tag/092M)
* [Stacks Project, Tag 0CKP](https://stacks.math.columbia.edu/tag/0CKP)
* [Olivier-AF]
* [Ferrand-epi]
-/

open scoped TensorProduct

universe u v

/-- If the multiplication map `B ⊗[A] B → B` is flat, then `B` is formally unramified
over `A`. -/
@[stacks 092M]
theorem formallyUnramified_of_flat_lmul (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    (h : (Algebra.TensorProduct.lmul' A (S := B)).Flat) :
    Algebra.FormallyUnramified A B := by
  let f := Algebra.TensorProduct.lmul' A (S := B)
  let : Algebra (B ⊗[A] B) B := f.toRingHom.toAlgebra
  have hf : Function.Surjective f := fun b => ⟨1 ⊗ₜ[A] b, by simp [f]⟩
  have hflat : Module.Flat (B ⊗[A] B) B := by
    simpa [RingHom.Flat, f] using h
  have hpure : (RingHom.ker f).Pure := Module.Flat.of_linearEquiv
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId (B ⊗[A] B) B) hf).toLinearEquiv
  exact ⟨(Ideal.cotangent_subsingleton_iff _).mpr (Ideal.isIdempotentElem_of_pure _)⟩

/-- If the multiplication map `B ⊗[A] B → B` is flat, finite type implies unramified and
finite presentation together with flatness implies étale. In particular, every weakly étale
algebra of finite presentation is étale. -/
@[stacks 0CKP]
theorem unramified_of_finiteType_and_etale_of_finitePresentation
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    ((Algebra.TensorProduct.lmul' A (S := B)).Flat →
      (Algebra.FiniteType A B → Algebra.Unramified A B) ∧
      (Algebra.FinitePresentation A B → Module.Flat A B → Algebra.Etale A B)) ∧
    (Algebra.WeaklyEtale A B →
      Algebra.FinitePresentation A B → Algebra.Etale A B) := by
  refine ⟨fun hmul => ?_, fun _ _ => ?_⟩
  · have := formallyUnramified_of_flat_lmul A B hmul
    exact ⟨fun hfinite => ⟨this, hfinite⟩, fun _ _ => .of_formallyUnramified_of_flat⟩
  · have := formallyUnramified_of_flat_lmul A B (Algebra.WeaklyEtale.flat_lmul' A B)
    exact .of_formallyUnramified_of_flat
