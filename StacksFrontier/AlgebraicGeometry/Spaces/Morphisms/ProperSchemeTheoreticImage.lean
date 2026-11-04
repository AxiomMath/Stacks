module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The scheme-theoretic image of a proper algebraic space (Stacks 0AGD)

Let `S` be a scheme contained in a big fppf site `B`, and let

```
X --h--> Y
 \      /
  f    g
   \  /
    T
```

be a commutative triangle of algebraic spaces over `S`, so `h ≫ g = f`. Assume `f` is proper
and `g` is separated and locally of finite type. **Stacks 0AGD** asserts two things about the
scheme-theoretic image `Z` of `h`, which here is
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor` of Stacks 082X: that `Z` is proper
over `T`, and that `X ⟶ Z` is surjective.

Surjectivity comes first, since properness is deduced from it. The morphism `h` is
quasi-compact: `f` is proper hence quasi-compact, and `g` is quasi-separated, being separated
(**Stacks 03KK**), so **Stacks 03KS** cancels `g` off. Therefore the image of `X` is dense in
`Z` by part (4) of **Stacks 082Z**. On the other hand the image of `|X|` in `|Y|` is already
closed, by part (1) of **Stacks 04NX** applied to the universally closed `f` and the separated
`g`. Pulling that closed set back along `|Z| → |Y|`, which is continuous and injective — the
inclusion of a subfunctor is a monomorphism, and a monomorphism is injective on points by
**Stacks 06RV** — produces exactly the image of `|X|` in `|Z|`. So the image of `|X|` in `|Z|`
is both closed and dense, hence all of `|Z|`.

Properness is then **Stacks 08AJ** applied to the surjection `X ⟶ Z` over `T`: `Z ⟶ T` is
separated as the composite of the closed immersion `Z ⟶ Y` (**Stacks 04CH**) with the separated
`g` (**Stacks 03KQ**); it is locally of finite type as the composite of the closed immersion
with the locally-of-finite-type `g` (**Stacks 03XG**); it is quasi-compact because `X ⟶ T` is
and `X ⟶ Z` is surjective (part (2) of **Stacks 040W**); and these together with universal
closedness of `X ⟶ T` are what Stacks 08AJ consumes.

## Main definitions

There are no new definitions: the scheme-theoretic image is
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor` and the morphism to it is
`AlgebraicGeometry.Space.toSchemeTheoreticImage`, both of Stacks 082X.

## Main results

* `AlgebraicGeometry.Space.isSurjective_toSchemeTheoreticImage_of_isProper` is the second
  assertion of **Stacks 0AGD**: the morphism from `X` to the scheme-theoretic image of `h` is
  surjective.
* `AlgebraicGeometry.Space.isProper_schemeTheoreticImageSubfunctor_inclusion_comp` is the first
  assertion of **Stacks 0AGD**: the scheme-theoretic image of `h` is proper over `T`.

## Implementation notes

"`Z` is proper over `T`" is read as properness of the composite of the inclusion of the
scheme-theoretic image into `Y` with `g`, that composite being the structure morphism of `Z`
over `T` which the triangle provides. Surjectivity of `X ⟶ Z` does not need `g` to be locally
of finite type, so that hypothesis is absent from the surjectivity statement; it is needed only
for the finite-type conjunct of properness.

## References

* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03KQ](https://stacks.math.columbia.edu/tag/03KQ)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 0AGD](https://stacks.math.columbia.edu/tag/0AGD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

variable {X Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0AGD, second assertion.** Let `h : X ⟶ Y`, `f : X ⟶ T` and `g : Y ⟶ T` be
morphisms of algebraic spaces over `S` with `h ≫ g = f`. If `f` is proper and `g` is separated,
then the morphism from `X` to the scheme-theoretic image of `h` is surjective.

The image of `|X|` in `|Z|` is dense, by part (4) of Stacks 082Z, `h` being quasi-compact by
Stacks 03KS; and it is closed, being the preimage along the continuous injection `|Z| → |Y|` of
the image of `|X|` in `|Y|`, which is closed by part (1) of Stacks 04NX. -/
@[stacks 0AGD "second assertion: surjectivity onto the scheme-theoretic image"]
theorem isSurjective_toSchemeTheoreticImage_of_isProper
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (h : X ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    (hcomm : h ≫ g = f) (hf : IsProper B S hS f) (hg : IsSeparated B S hS g) :
    IsSurjective B S hS (toSchemeTheoreticImage B S hS h) := by
  have hhqc : IsQuasiCompact B S hS h :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS h g hX hT
      (by rw [hcomm]; exact hf.2.1.2) (isQuasiSeparated_of_isSeparated B S hS hg)
  have hdense : DenseRange (pointsMap B S hS X (toSchemeTheoreticImage B S hS h)) :=
    denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact B S hS h hX hY hhqc
  have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS X h)) :=
    isClosed_range_of_comp_of_isSeparated B S hS hX hY hT h g
      (by rw [hcomm]; exact hf.2.2) hg
  have hmap : pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS h).toFunctor
        (schemeTheoreticImageSubfunctor B S hS h).ι ∘
      pointsMap B S hS X (toSchemeTheoreticImage B S hS h) = pointsMap B S hS X h := by
    rw [← pointsMap_comp, toSchemeTheoreticImage_ι]
  have hinj : Function.Injective
      (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS h).toFunctor
        (schemeTheoreticImageSubfunctor B S hS h).ι) :=
    pointsMap_injective_of_mono B S hS _
  have hrange : Set.range (pointsMap B S hS X (toSchemeTheoreticImage B S hS h)) =
      pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS h).toFunctor
          (schemeTheoreticImageSubfunctor B S hS h).ι ⁻¹'
        Set.range (pointsMap B S hS X h) := by
    rw [← hmap, Set.range_comp, Set.preimage_image_eq _ hinj]
  have hclosed' : _root_.IsClosed
      (Set.range (pointsMap B S hS X (toSchemeTheoreticImage B S hS h))) := by
    rw [hrange]
    exact hclosed.preimage (continuous_pointsMap B S hS _)
  exact Set.range_eq_univ.mp (hclosed'.closure_eq.symm.trans hdense.closure_range)

/-- **Stacks 0AGD, first assertion.** Let `h : X ⟶ Y`, `f : X ⟶ T` and `g : Y ⟶ T` be morphisms
of algebraic spaces over `S` with `h ≫ g = f`. If `f` is proper and `g` is separated and
locally of finite type, then the scheme-theoretic image of `h` is proper over `T`.

The scheme-theoretic image is a closed subspace of `Y` (Stacks 082X), so its structure morphism
over `T` is separated by Stacks 04CH and Stacks 03KQ, and locally of finite type by Stacks 03XG;
it is quasi-compact by part (2) of Stacks 040W, `X ⟶ T` being quasi-compact and `X` surjecting
onto the image by
`AlgebraicGeometry.Space.isSurjective_toSchemeTheoreticImage_of_isProper`. Properness is then
the second assertion of Stacks 08AJ, `f` being universally closed. -/
@[stacks 0AGD "first assertion: the scheme-theoretic image is proper over the base"]
theorem isProper_schemeTheoreticImageSubfunctor_inclusion_comp
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hT : IsAlgebraicSpace B S hS T) (h : X ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    (hcomm : h ≫ g = f) (hf : IsProper B S hS f) (hg : IsSeparated B S hS g)
    (hgft : IsLocallyOfFiniteType B S hS g) :
    IsProper B S hS ((schemeTheoreticImageSubfunctor B S hS h).ι ≫ g) := by
  have hZ : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS h) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS h hY
  have hsurj : IsSurjective B S hS (toSchemeTheoreticImage B S hS h) :=
    isSurjective_toSchemeTheoreticImage_of_isProper B S hS hX hY hT h f g hcomm hf hg
  have hfactor : toSchemeTheoreticImage B S hS h ≫
      (schemeTheoreticImageSubfunctor B S hS h).ι ≫ g = f := by
    rw [← Category.assoc, toSchemeTheoreticImage_ι, hcomm]
  have hsep : IsSeparated B S hS ((schemeTheoreticImageSubfunctor B S hS h).ι ≫ g) :=
    isSeparated_comp B S hS _ g (isSeparated_of_isClosedImmersion B S hS _ hZ.2) hg
  have hlft : IsLocallyOfFiniteType B S hS
      ((schemeTheoreticImageSubfunctor B S hS h).ι ≫ g) :=
    isLocallyOfFiniteType_comp B S hS hZ.1 hY hT _ g
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS _ hZ.2) hgft
  have hqc : IsQuasiCompact B S hS ((schemeTheoreticImageSubfunctor B S hS h).ι ≫ g) :=
    IsQuasiCompact.of_isSurjective_comp B S hS hX hZ.1 hT hfactor hsurj hf.2.1.2
  exact isProper_of_isSurjective B S hS hX hZ.1 hT (toSchemeTheoreticImage B S hS h) f _
    hfactor hsurj hf.2.2 hsep ⟨hlft, hqc⟩

end AlgebraicGeometry.Space

end
