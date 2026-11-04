module

public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.PowerSeriesSurjection
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.CompleteNoetherian

/-!
# The adic completion of a Noetherian ring is Noetherian

Let `R` be a Noetherian commutative ring and let `I ⊆ R` be an ideal. Then the `I`-adic
completion `R^∧ = lim_n R/Iⁿ` is again a Noetherian ring.

The development is split into:

* `NoetherianRing.PowerSeriesSurjection`: the direct proof through the surjection
  `R⟦x i⟧ → R^∧`, and the instance `AdicCompletion.isNoetherianRing` (Stacks 0316);
* `NoetherianRing.AssociatedGraded`: the associated-graded module `grModule S J` and its
  `MvPolynomial (Fin t) (S ⧸ J)`-module structure;
* `NoetherianRing.GradedNoetherian`: Noetherianity of `grModule S J` and the action of
  monomials on homogeneous leading forms;
* `NoetherianRing.CompleteNoetherian`: leading forms of ideals and the completion criterion
  `completion_noetherian` (Stacks 05GH).

## References

* [StackProject 0316](https://stacks.math.columbia.edu/tag/0316)
-/
