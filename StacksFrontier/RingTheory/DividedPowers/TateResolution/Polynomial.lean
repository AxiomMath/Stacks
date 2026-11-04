module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomial

/-!
# Graded divided-power polynomial algebras

A graded divided-power algebra is a *graded divided-power polynomial algebra* over its
coefficient algebra when it is the directed union of finite stages, each obtained from the
previous one by adjoining a single homogeneous variable of positive degree: an exterior
variable in odd degree, a divided-power variable in even degree.

The structure recording that presentation is
`DividedPowers.TateResolution.GradedDividedPowerPolynomial`, declared in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomial` and re-exported here;
its mapping property
`DividedPowers.TateResolution.existsUnique_gradedDividedPowerPolynomial_map` is proved in
`StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedPolynomialMap`.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
-/
