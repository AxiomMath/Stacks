module

public import Mathlib.RingTheory.Henselian
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# A henselian local ring as a henselian pair

A local ring is henselian exactly when it forms a henselian pair with its maximal ideal. This
file proves the direction that produces the pair, which is the shape in which Gabber's theorem
on finite étale covers takes its hypothesis.

## Main results

* `henselianPair_maximalIdeal` — a henselian local ring and its maximal ideal form a henselian
  pair.

## Implementation notes

The proof uses the étale-lifting characterisation of a henselian pair (`henselianPair_tfae`,
Tag 09XI): a pair `(A, I)` is henselian as soon as every `A`-algebra map from an étale
`A`-algebra to `A ⧸ I` lifts to `A`. For `I` the maximal ideal of a henselian local ring that is
Hensel's lemma for étale algebras, `HenselianLocalRing.existsUnique_algHom_residue_of_etale`.

## References

* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

universe u

open IsLocalRing

/-- A henselian local ring forms a henselian pair with its maximal ideal.

Every `A`-algebra map from an étale `A`-algebra to the residue field is the reduction of an
`A`-algebra map to `A`, which is the étale-lifting criterion for a henselian pair. -/
theorem henselianPair_maximalIdeal (A : Type u) [CommRing A] [HenselianLocalRing A] :
    HenselianPair A (maximalIdeal A) := by
  refine ((henselianPair_tfae.{u, u} A (maximalIdeal A)).out 2 1).mp ?_
  intro A' _ _ _ σ
  obtain ⟨τ, hτ, -⟩ :=
    HenselianLocalRing.existsUnique_algHom_residue_of_etale (R := A) (A := A') (S := A) σ
  exact ⟨τ, AlgHom.ext hτ⟩

end
