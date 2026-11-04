module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.SquareZeroDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.UniversalEffectiveEpi

/-!
# Fpqc coverings are universal effective epimorphisms

For a family of morphisms of affine schemes `{f i : U i ⟶ X}`, the global sections of every
quasi-coherent module on `X` form the equalizer of the two maps between the products of the
sections over the members and over their pairwise fibre products exactly when the family is a
universal effective epimorphic family in the category of affine schemes.

## Main definitions

* `AlgebraicGeometry.IsQuasicoherentSectionsEqualizer` is the equalizer condition on global
  sections of quasi-coherent modules, stated elementwise.

## Main results

* `AlgebraicGeometry.quasicoherentSectionsEqualizer_iff_isUniversalEffectiveEpiFamily`
  identifies that condition with universal effective epimorphy.

## Implementation notes

The equalizer is stated elementwise: every compatible family of sections has a unique
preimage. Pairwise fibre products are taken in schemes after forgetting affineness; they are
affine and agree canonically with the fibre products formed in affine schemes.

For the forward implication a section of a quasi-coherent module `F` is turned into a
morphism to the affine line out of the relative spectrum of the square-zero extension
`O_X + F`, whose formation is the square-zero extension of rings `TrivSqZeroExt` and whose
base change along a ring map is computed by `trivSqZeroExtBaseChange`.  The reverse
implication is the base-change formula of Stacks 02KG: along an affine morphism `p : Y ⟶ X`
the global sections of a quasi-coherent module on `Y` are the global sections of its direct
image, compatibly with pullback, so the equalizer condition for `X` transfers to `Y`.

## References

* [Stacks Project, Tag 00WP](https://stacks.math.columbia.edu/tag/00WP)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 0EUA](https://stacks.math.columbia.edu/tag/0EUA)
-/
