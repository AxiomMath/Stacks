module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure

/-!
# `a^*Ω_{Y/Bb}` restricted to an étale chart of the source, as an associated cotangent sheaf

Let `q : Y ⟶ Bb` and `a : Z ⟶ Y` be morphisms of algebraic spaces over a scheme `S` contained in
a big fppf site `B`, let `A` be an étale scheme chart of `Z`, and suppose the composite
`chartSpace A ⟶ Z ⟶ Y` factors through a commuting square

```
W --k--> V
|        |
w        v
v        v
Y --q--> Bb
```

of étale charts of `q` by objects of the big fppf site, say as `r ≫ w` for a morphism
`r : A ⟶ W` of the site.  This file exhibits the inverse image of `a^*Ω_{Y/Bb}` to the small
étale site of the chart space as the module `Mᵃ` of [Stacks Project, Tag 03DU] (4) of the
*Zariski* cotangent sheaf `r^*Ω_{W/V}` on the chart's scheme, in the spelling
`Stacks.Smooth.pullbackCotangentSheaf`.

Everything is available and nothing is carried beyond the étaleness of the two charts of the square,
which is the hypothesis of [Stacks Project, Tag 04CU]:

* `AlgebraicGeometry.Space.modulePullbackCompIso`, [Stacks Project, Tag 03LU], collapses the two
  inverse images into the inverse image along the composite;
* `AlgebraicGeometry.Space.chartCompositeDifferentialsAssociatedIso` — the composite of
  [Stacks Project, Tag 04CU] and [Stacks Project, Tag 04CS] — identifies that with the associated
  module of `(Scheme.Modules.pullback r).obj (Scheme.Hom.relativeDifferentials k)`;
* `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` changes the inner sheaf from the
  corepresenting construction `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` to the
  sheafified one `Stacks.Smooth.cotangentSheaf`, which is the construction
  `Stacks.Smooth.pullbackCotangentSheaf` — and hence the chart presentation of a lifting
  problem — is written in.

## Why this is wanted

It is the *source* half of the comparison of the two descriptions of the acting sheaf of
[Stacks Project, Tag 061D] on an étale chart, which step (II) of [Stacks Project, Tag 04AM]
needs.  The acting group at a chart,
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, is a linear map out of
`Γ(Stacks.Smooth.pullbackCotangentSheaf …, ⊤)`, so the comparison has to land at that spelling
and not merely at `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`; the two are not
definitionally equal, their inner sheaves being a corepresenting object and a sheafification.

## Main definitions

* `AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso`: **the inverse image of
  `a^*Ω_{Y/Bb}` to the small étale site of a chart space, as the associated module of the Zariski
  cotangent sheaf of the chart square.**

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_pullbackCotangentSheaf_chartSquare`: the Zariski
  module on the right is quasi-coherent, with no hypothesis — which is what the passage from an
  isomorphism of associated modules to a bijection of morphisms,
  `AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap`, asks for.

## Implementation notes

The chart space is written `AlgebraicGeometry.Space.chartSpace`, and its property argument is
handed to `AlgebraicGeometry.Space.representedAssociatedModule` as `(chartSpace … A).2`; this is
the same term as `(schemeSpace ((SmallEtale.toOver … ).obj A)).property` — see
`AlgebraicGeometry.Space.chartSpace_eq_yoneda` — so no comparison of the two readings of the
chart space is needed anywhere below.

The change of the inner sheaf is moved as an *isomorphism*, by two nested
`CategoryTheory.Functor.mapIso`, and never through its components: projecting `hom` out of a
composite of chart comparisons is what the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.AssociatedModuleChartPushTranspose` record as unaffordable.

No `@[stacks]` attribute is claimed: Tags 03LU, 04CS and 04CU are registered at the isomorphisms
composed here, and Tag 01BG at the quasi-coherence of a Zariski pullback.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {Bb Z Y : AlgebraicSpaces B S hS} {W V : BigFppfOver B S hS}

/-- **The inverse image of `a^*Ω_{Y/Bb}` to the small étale site of an étale chart space of the
source, as an associated module.**  For a commuting square `w ≫ q = k ≫ v` of étale charts of
`q : Y ⟶ Bb` by objects of the big fppf site, an étale scheme chart `A` of `Z` and a morphism
`r : A ⟶ W` of the site through which the composite `chartSpace A ⟶ Z ⟶ Y` factors,

`(chartToSpace A)^*a^*Ω_{Y/Bb} ≅ (r^*Ω_{W/V})ᵃ`,

the right-hand side being the associated module of the Zariski cotangent sheaf in the spelling
`Stacks.Smooth.pullbackCotangentSheaf`. -/
def chartDifferentialsAssociatedCotangentIso (q : Y ⟶ Bb) (a : Z ⟶ Y)
    (w : schemeSpace W ⟶ Y) (v : schemeSpace V ⟶ Bb) (k : W ⟶ V)
    (hw : IsEtale B S hS w.hom) (hv : IsEtale B S hS v.hom)
    (hsq : w ≫ q = schemeSpaceMap k ≫ v)
    (A : SmallEtale B S hS Z.1) (r : (SmallEtale.toOver B S hS Z.1).obj A ⟶ W)
    (hc : chartToSpace B S hS Z A ≫ a = schemeSpaceMap r ≫ w) :
    (modulePullback B S hS
          (chartToSpace B S hS Z A :
            schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z)).obj
        ((modulePullback B S hS a).obj (sheafOfDifferentials B S hS q)) ≅
      (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
          (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property).obj
        (Stacks.Smooth.pullbackCotangentSheaf ((BigFppfOver.toScheme B S hS).map k)
          ((BigFppfOver.toScheme B S hS).map r)) :=
  (modulePullbackCompIso B S hS
        (chartToSpace B S hS Z A :
          schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A) ⟶ Z) a).app
      (sheafOfDifferentials B S hS q) ≪≫
    chartCompositeDifferentialsAssociatedIso B S hS q w v k hw hv hsq r
      (chartToSpace B S hS Z A ≫ a) hc ≪≫
    (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS Z.1).obj A)
      (schemeSpace ((SmallEtale.toOver B S hS Z.1).obj A)).property).mapIso
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map r)).mapIso
          (Scheme.Hom.cotangentSheafIso ((BigFppfOver.toScheme B S hS).map k)))

/-- The Zariski cotangent sheaf of a chart square, pulled back along a morphism of the site, is
quasi-coherent.  This is [Stacks Project, Tag 01BG] at the sheaf of differentials, which is
quasi-coherent with no hypothesis on the morphism. -/
theorem isQuasicoherent_pullbackCotangentSheaf_chartSquare (k : W ⟶ V)
    {T : BigFppfOver B S hS} (r : T ⟶ W) :
    (Stacks.Smooth.pullbackCotangentSheaf ((BigFppfOver.toScheme B S hS).map k)
      ((BigFppfOver.toScheme B S hS).map r)).IsQuasicoherent :=
  Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf' _ _

end AlgebraicGeometry.Space

end
