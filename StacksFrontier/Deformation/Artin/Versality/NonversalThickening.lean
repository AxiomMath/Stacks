module

public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening.SmallExtensionStages
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening.ArtinianObjectsOverPoint
public import StacksFrontier.Deformation.Artin.Versality.NonversalThickening.ThickeningWithoutRetraction

/-!
# A one-point thickening witnessing failure of versality

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian
scheme `S`, satisfying (RS*), and let `x` be an object of `𝒳` over an affine scheme `U` of
finite type over `S`. If `x` fails to be versal at a finite type point `u ∈ U`, then there is
a morphism `x ⟶ y` of `𝒳` over a first order thickening `U ⟶ T` whose ideal is the residue
field `κ(u)`, such that `x ⟶ y` admits no retraction over any open neighbourhood of `u` in
`T`: no pair `(W, β)` with `W ⊆ T` open containing `u` and `β : y|_W ⟶ x` makes the
composition `x|_{U ∩ W} ⟶ y|_W ⟶ x` the canonical morphism `x|_{U ∩ W} ⟶ x`.

## Main results

* `Deformation.Artin.exists_firstOrderThickening_without_localRetraction`: **Stacks 0G2J**.

## Implementation notes

The thickening is the affine pushout `T = U ⨿_{Spec A} Spec B` of a small extension
`B ⟶ A` of Artinian local algebras extracted from the failure of versality, obtained as
the spectrum of the fibre product of rings; axiom (RS*) glues `x` and the object over
`Spec B` into the object `y` over `T`. The short exact sequence
`0 ⟶ κ(u) ⟶ 𝒪_T ⟶ 𝒪_U ⟶ 0` is expressed by surjectivity of the structure sheaf map
`𝒪_T ⟶ i_*𝒪_U` together with an isomorphism of its kernel with the direct image of the
structure sheaf of `Spec κ(u)` along the canonical inclusion of the point `u` into `T`,
which is the skyscraper sheaf with value `κ(u)` at `u`.

An open neighbourhood `W` of `u` in `T` is given by an object of the site together with an
open immersion to `T` whose image contains `u`; the restrictions `y|_W` and `x|_{U ∩ W}` are
given by Cartesian arrows, the latter over a fibre-product square, so that the negative
condition quantifies over every choice of those restrictions.

## References

* [Stacks Project, Tag 0G2J](https://stacks.math.columbia.edu/tag/0G2J)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/
