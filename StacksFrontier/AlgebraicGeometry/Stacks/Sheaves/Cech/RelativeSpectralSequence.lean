module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Resolution
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Abelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.ModuleCech
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence.Modules

/-!
# The relative Čech-to-cohomology spectral sequence

Let `f : 𝒰 ⥤ 𝒳` be a faithful `1`-morphism of categories fibred in groupoids over the big fppf
site of a scheme `S`, with equalizers in `𝒰`, and suppose the image of `f` covers every object
of `𝒳` locally for one of the five topologies `τ`. For an abelian sheaf `𝓕` on `𝒳_τ` there is a
first-quadrant spectral sequence whose first page is the sheaf cohomology of the inverse image
of `𝓕` on the terms of the relative Čech nerve of `f` and which abuts to the sheaf cohomology
of `𝓕` on `𝒳_τ`.

If moreover a `1`-morphism `g : 𝒳 ⥤ 𝒴` is given, the same double complex with the direct image
along `g` in place of global sections produces a first-quadrant spectral sequence of abelian
sheaves on `𝒴_τ` whose first page is the higher direct image along `g` composed with the terms
of the relative Čech nerve, and which abuts to the higher direct images of `𝓕` along `g`.

The same spectral sequence exists for a sheaf of `𝒪_𝒳`-modules on `𝒳_τ`, with all higher
direct images taken in the category of sheaves of modules.

## Main definitions

* `Stacks.RelativeCech.SpectralSequenceData` records the first page, the first-quadrant
  vanishing and the finite abutment of the spectral sequence.
* `Stacks.RelativeCech.PushforwardSpectralSequenceData` records the same data for the relative
  version, with higher direct images along `g` in place of cohomology.
* `Stacks.RelativeCech.moduleRingSheaf` is the sheaf of rings for modules on the site
  associated with a category fibred in groupoids and one of the five topologies.
* `Stacks.RelativeCech.moduleInverseImage` and `Stacks.RelativeCech.moduleDirectImage` are the
  inverse and direct images of sheaves of modules along a `1`-morphism, and
  `Stacks.RelativeCech.moduleInverseDirectImageAdjunction` is the adjunction between them.
* `Stacks.RelativeCech.ModulePushforwardSpectralSequenceData` records the first page, the
  first-quadrant vanishing and the abutment of the spectral sequence of sheaves of modules.

## Main results

* `Stacks.RelativeCech.exists_spectralSequenceData` constructs the spectral sequence.
* `Stacks.RelativeCech.exists_pushforwardSpectralSequenceData` constructs the relative one.
* `Stacks.RelativeCech.exists_modulePushforwardSpectralSequenceData` constructs the relative
  one for sheaves of modules.

## Implementation notes

The spectral sequence is the one attached to the double complex obtained by applying global
sections to an injective resolution of `𝓕` in one direction and the sheafified relative Čech
complex in the other. Exactness of the extended relative Čech complex makes the augmentation of
each term of the injective resolution a resolution, and the terms of the sheafified Čech complex
of an injective sheaf are injective, so the rows of the double complex compute nothing beyond
degree zero and the abutment is the cohomology of `𝓕`. The columns are identified with the
cohomology of the inverse image of `𝓕` on the Čech terms using that each projection of the Čech
nerve is a fibred `1`-morphism, hence continuous and cocontinuous for the inherited topologies,
and that its inverse image preserves injectives. The terms of the Čech nerve are themselves
fibred in groupoids over the base and have equalizers, which is what makes the latter
available.

For sheaves of modules the relative Čech complex is built directly from the inverse and direct
images of modules along the projections of the Čech nerve, with no sheafification: the direct
image of a sheaf of modules is already a sheaf, being a pointwise right Kan extension along a
cocontinuous functor. Its underlying complex of abelian sheaves is the sheafified relative Čech
complex of the underlying abelian sheaf, because both degreewise terms are right Kan extensions
of the same restriction and the comparison between them is compatible with the simplicial
reindexing maps; exactness of the augmented complex therefore descends from the abelian case,
forgetting the module structure being exact and faithful. The terms of the complex of an
injective sheaf of modules are injective by the module forms of the two injectivity statements,
and the columns are identified using that the direct image along a composite is the composite of
the direct images.

## References

* [Stacks Project, Tag 06XF](https://stacks.math.columbia.edu/tag/06XF)
* [Stacks Project, Tag 072D](https://stacks.math.columbia.edu/tag/072D)
* [Stacks Project, Tag 06X8](https://stacks.math.columbia.edu/tag/06X8)
* [Stacks Project, Tag 06XA](https://stacks.math.columbia.edu/tag/06XA)
* [Stacks Project, Tag 06XE](https://stacks.math.columbia.edu/tag/06XE)
* [Stacks Project, Tag 072E](https://stacks.math.columbia.edu/tag/072E)
-/
