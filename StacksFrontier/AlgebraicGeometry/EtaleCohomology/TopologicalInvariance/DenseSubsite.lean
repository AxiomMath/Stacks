module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.CoverDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The small étale site of a universal homeomorphism is a dense subsite

Let `f : X ⟶ Y` be a universal homeomorphism of schemes. Two statements about small étale base
change along `f` are used side by side in the étale cohomology of universal homeomorphisms:

* that `Stacks.EtaleCohomology.smallEtaleBaseChange f` is an *equivalence* of small étale
  categories (Stacks Project, Tag 04DZ);
* that it exhibits the small étale site of `Y` as a *dense subsite* of that of `X` (Stacks
  Project, Tag 03SI, part (1)), which is what transports abelian sheaf cohomology.

They are not the same statement, and the second is the weaker one. This file proves the second
outright. By `Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_isCoverDense`
the only input it needs is cover-density, which
`Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff` unfolds to the statement that
every point of every scheme étale over `X` lies in the image of a morphism from a base change
of a scheme étale over `Y` — and that is exactly property (C) for `f`, Stacks Project Tag 04DW,
now available as `Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding`.

Essential surjectivity, the remaining content of Tag 04DZ, is strictly stronger and is *not*
obtained: cover-density only asks that the base changes be jointly surjective onto each scheme
étale over `X`, not that they exhaust it up to isomorphism.

## Main results

* `Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_of_universalHomeomorphism`: small
  étale base change along a universal homeomorphism is cover-dense. This is Tag 04DW read
  through `Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff`.
* `Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`: consequently base change
  along a universal homeomorphism exhibits the small étale site of `Y` as a dense subsite of
  that of `X`. This is Stacks Project Tag 03SI, part (1).
* `Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_essSurj` and
  `Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_isEquivalence`: the same
  conclusion from essential surjectivity, respectively from the equivalence of Tag 04DZ. Both
  are subsumed by the unconditional statement and are kept because they are the shape in which
  the étale cohomology of universal homeomorphisms consumes the hypothesis, and because they
  record which of the two statements implies which.

## Implementation notes

Nothing here carries a tag. Tag 03SI has further parts, and the library's tagging rule puts a tag
only on a covering set for the whole of its content, so part (1) alone earns no attribute; the
tag it does discharge, Tag 04DW, is carried where it is proved.

A universal homeomorphism is integral, universally injective and surjective (Stacks Project
Tag 04DF, `AlgebraicGeometry.universalHomeomorphism_iff_integral_universallyInjective_surjective`)
and is a homeomorphism on points
(`Stacks.EtaleCohomology.isHomeomorph_base_of_universalHomeomorphism`), hence in particular a
homeomorphism onto a closed subset. Those are precisely the hypotheses of Tag 04DW.

Property (C) produces its dominating morphism out of `X ×ₗᵧ V` with the fibre product taken in
the order `pullback f v`, whereas an object of the small étale site of `X` obtained by base
change has underlying scheme `pullback v f`; the two are matched by
`CategoryTheory.Limits.pullbackSymmetry`.

The implication proved here is strict and cannot be run backwards: cover-density does not imply
essential surjectivity, so Tag 04DZ does not follow. That ordering is recorded in
`Stacks.EtaleCohomology.isCoverDense_of_essSurj`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- **Small étale base change along a universal homeomorphism is cover-dense.** For a universal
homeomorphism `f : X ⟶ Y`, every point of every scheme étale over `X` lies in the image of a
morphism to it from the base change along `f` of a scheme étale over `Y`.

This is property (C) for `f`, Stacks Project Tag 04DW
(`Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding`), read through
`Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_iff`: a universal homeomorphism is
integral and is a homeomorphism onto a closed subset, so Tag 04DW applies to it, and the
surjection it produces hits the given point. -/
theorem isCoverDense_smallEtaleBaseChange_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] :
    (smallEtaleBaseChange f).IsCoverDense (smallEtaleTopology X) := by
  have hint : IsIntegralHom f :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).1 ‹_›).1
  have hce : Topology.IsClosedEmbedding f.base :=
    (isHomeomorph_base_of_universalHomeomorphism f).isClosedEmbedding
  refine (isCoverDense_smallEtaleBaseChange_iff f).2 fun U u => ?_
  obtain ⟨V, v, hv, h, hsurj, hcomp⟩ :=
    hasPropertyC_of_isIntegralHom_of_isClosedEmbedding f hce U.hom U.prop
  have := hv
  have := hsurj
  have hm : ((pullbackSymmetry v f).hom ≫ h) ≫ U.hom = pullback.snd v f := by
    rw [Category.assoc, hcomp, pullbackSymmetry_hom_comp_fst]
  refine ⟨Scheme.Etale.mk v, MorphismProperty.Over.homMk _ hm trivial, ?_⟩
  exact (inferInstance : Surjective ((pullbackSymmetry v f).hom ≫ h)).surj u

/-- **Stacks Project, Tag 03SI, part (1).** Base change along a universal homeomorphism of
schemes exhibits the small étale site of the target as a dense subsite of the small étale site
of the source.

Of the four conditions for a dense subsite inclusion, all but cover-density hold for any
universal homeomorphism by
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism_of_isCoverDense`, and
cover-density is
`Stacks.EtaleCohomology.isCoverDense_smallEtaleBaseChange_of_universalHomeomorphism`, i.e.
Tag 04DW. -/
@[sga "4½ Th_finitude 2.7" "partial"]
theorem isDenseSubsite_of_universalHomeomorphism (f : X ⟶ Y) [UniversalHomeomorphism f] :
    (smallEtaleBaseChange f).IsDenseSubsite (smallEtaleTopology Y) (smallEtaleTopology X) :=
  have := isCoverDense_smallEtaleBaseChange_of_universalHomeomorphism f
  isDenseSubsite_of_universalHomeomorphism_of_isCoverDense f

/-- **Essential surjectivity also gives the dense subsite inclusion.** For a universal
homeomorphism `f : X ⟶ Y`, if small étale base change along `f` is essentially surjective then it
exhibits the small étale site of `Y` as a dense subsite of that of `X`.

Full faithfulness is unconditional for a universal homeomorphism, and an essentially surjective
functor is cover-dense for any topology, so no further input is needed. This route is subsumed by
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`, which needs no hypothesis at
all; it is retained because it records that essential surjectivity is the stronger statement. -/
theorem isDenseSubsite_of_universalHomeomorphism_of_essSurj (f : X ⟶ Y)
    [UniversalHomeomorphism f] [(smallEtaleBaseChange f).EssSurj] :
    (smallEtaleBaseChange f).IsDenseSubsite (smallEtaleTopology Y) (smallEtaleTopology X) :=
  have := isCoverDense_of_essSurj f
  isDenseSubsite_of_universalHomeomorphism_of_isCoverDense f

/-- **Tag 03SI part (1) from Tag 04DZ.** For a universal homeomorphism `f : X ⟶ Y`, if small
étale base change along `f` is an equivalence of small étale categories then it exhibits the
small étale site of `Y` as a dense subsite of that of `X`.

This is the shape in which the étale cohomology of universal homeomorphisms consumes the
hypothesis; the conclusion is now available unconditionally as
`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`. -/
theorem isDenseSubsite_of_universalHomeomorphism_of_isEquivalence (f : X ⟶ Y)
    [UniversalHomeomorphism f] [(smallEtaleBaseChange f).IsEquivalence] :
    (smallEtaleBaseChange f).IsDenseSubsite (smallEtaleTopology Y) (smallEtaleTopology X) :=
  isDenseSubsite_of_universalHomeomorphism_of_essSurj f

end Stacks.EtaleCohomology

end
