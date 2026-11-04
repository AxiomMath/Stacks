module

public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.ApproximationLevels
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.CompletionLifts
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.ResiduePointLifting
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectVersal.VersalityCriterion

/-!
# Versality at a point and versality of the associated formal object

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be a category fibred in groupoids, `U` a scheme over `S` of
finite type, `x` an object of `𝒳` over `U` and `u₀ ∈ U` a finite type point. Write
`R = 𝒪^∧_{U, u₀}` for the completed local ring of `U` at `u₀`, let `x_R` be the
restriction of `x` to a presentation of `Spec R` and let `ξ` be the formal object of `𝒳`
attached to `x_R` by the approximation functor. Then `x` is versal at `u₀` precisely when
`ξ` is versal, that is, when the formal object of the predeformation category of its closed
fibre determined by `ξ` has smooth associated morphism.

## Main results

* `Deformation.Artin.isVersalAt_iff_isVersal`: **Stacks 0CXK**, versality at a point agrees
  with versality of the formal object attached to the completed local restriction.

## References

* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
-/
