module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZero
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Polynomial

/-!
# The augmentation of a graded divided-power polynomial algebra

A Tate resolution carries an algebra map onto the algebra being resolved which agrees with the
prescribed presentation on the coefficients and kills every variable. Such a map is one
application of the mapping property of a graded divided-power polynomial algebra: the target,
regarded as graded in degree zero, receives the coefficient map because its degree-zero piece is
everything, and every variable must go to zero because the piece of its degree is zero.

That the target is concentrated in degree zero also settles the two properties the resolution
asks of the augmentation beyond its values: it kills every element of positive degree, and it is
surjective as soon as the prescribed presentation is.

## Main results

* `DividedPowers.TateResolution.exists_augmentation` — the augmentation onto a prescribed
  quotient of the coefficient algebra.

## Implementation notes

The mapping property is used in its standalone form
`existsUnique_gradedDividedPowerPolynomial_map`, which is available here precisely because the
target is degree-zero: its hypothesis that the coefficient map lands in degree zero is what
makes that form inapplicable to a comparison between two stages of the construction, and it is
free for the augmentation.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

section Augmentation

/-- **The augmentation of a graded divided-power polynomial algebra.** A map of the coefficient
algebra to a commutative algebra extends uniquely to a map of the whole algebra killing every
variable; the extension vanishes in every positive degree, and is surjective whenever the given
map is.

These are the augmentation of a Tate resolution together with its compatibility with the
prescribed presentation, its vanishing in positive degrees and its surjectivity. What it does
*not* give is the vanishing of the augmentation on boundaries, which depends on the variables of
degree one being sent to generators of the kernel of the presentation. -/
public theorem exists_augmentation {R : Type u} {P : Type v} {A : Type w} {S : Type z}
    [CommRing R] [Ring P] [Algebra R P] [Ring A] [Algebra R A] [CommRing S] [Algebra R S]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
    (γ : DividedPowerStructure 𝒜) (ι : P →ₐ[R] A) (h : GradedDividedPowerPolynomial 𝒜 γ ι)
    (φ : P →ₐ[R] S) :
    ∃ g : A →ₐ[R] S,
      (∀ p : P, g (ι p) = φ p) ∧
      (∀ j : Σ n : ℕ, h.indices n, g (h.generator j) = 0) ∧
      (∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → g a = 0) ∧
      (Function.Surjective φ → Function.Surjective g) := by
  obtain ⟨g, ⟨hg1, hg2, hg3, -⟩, -⟩ :=
    existsUnique_gradedDividedPowerPolynomial_map 𝒜 γ ι h (degreeZeroGrade R S)
      (degreeZeroDividedPowers R S) φ (fun p => mem_degreeZeroGrade_zero R S (φ p))
      (fun _ => 0) (fun _ => Submodule.zero_mem _)
  refine ⟨g, hg1, hg2, fun n a hn ha => ?_, fun hφ y => ?_⟩
  · exact eq_zero_of_mem_degreeZeroGrade R S hn.ne' (hg3 n a ha)
  · obtain ⟨p, hp⟩ := hφ y
    exact ⟨ι p, (hg1 p).trans hp⟩

end Augmentation

end DividedPowers.TateResolution

end
