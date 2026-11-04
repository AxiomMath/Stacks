module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap

/-!
# The collapse step of Stacks 073K, part (2): `H^i(X_B, 𝓕_B) = H^i(X, g'_*𝓕_B)`

For the cartesian square of **Stacks 073J**

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `Y = Spec(A)` and `Y' = Spec(B)` affine and `g` flat, the proof of **Stacks 073K**,
part (2) opens with

> Since `g'` is affine the higher direct images `R^i(g')_*𝓕'` are zero, so
> `H^p(X', 𝓕') = H^p(X, g'_*𝓕')`.

This file supplies that step, as a chosen isomorphism, in every degree, with nothing carried.

## Main results

* `AlgebraicGeometry.Space.BaseChangeDiagram.isQuasicoherentOnSite_pulledBack`: the coefficient
  `𝓕' = (g')^*𝓕` of the square is quasi-coherent.
* `AlgebraicGeometry.Space.BaseChangeDiagram.cohomologyPushforwardIso`: **the collapse
  itself** — `H^i(X', 𝓕') ≅ H^i(X, g'_*𝓕')` for every `i`, as `Γ(X, 𝒪_X)`-modules.

## Implementation notes

*Nothing is assumed of `X`.*  In particular `X` is not affine; only the two bases `Y` and `Y'`
are, and only because that is what makes `g`, and hence `g'`, an affine morphism.  The
quasi-compactness and quasi-separatedness of `f` that **Stacks 073K** carries are not needed
for this step — they enter the source's proof only later, at the passage through
**Stacks 073E** — so they are not hypotheses here.

*Why the collapse is available at the small étale seating.*  The identification is
`AlgebraicGeometry.Space.cohomologyPushforwardIsoOfIsFlatOfIsAffineHom`, Stacks 0733 part (1)
for a morphism that is both flat and affine.  Its two inputs are `h03DW`, the vanishing of the
higher direct images along the chart base changes, which for an affine morphism is
unconditional (**Stacks 073H**); and `h072Z`, the acyclicity for global sections on the target
of the direct image of an injective module.  The second is where the hypotheses of the square
are spent twice over: `g'` is affine *and* flat, and for a flat morphism the direct image of an
injective module is itself injective by **Stacks 0730**
(`AlgebraicGeometry.Space.preservesInjectiveObjects_modulePushforward_of_isFlat`), hence acyclic
for every additive functor.  So `h072Z` is obtained without Stacks 072Z, and in particular
without a terminal chart on the target — which is the only thing that would have forced `X` to
be affine, as it does in
`AlgebraicGeometry.Space.acyclicPushforwardOfInjective_of_isAffineSpace`.

Both of the square's hypotheses are therefore genuinely used, and neither is the source's:
affineness of `g'` is **Stacks 03WI** from affineness of `Y` and `Y'`
(`AlgebraicGeometry.Space.BaseChangeDiagram.isAffineHom_g'`), and flatness of `g'` is
**Stacks 03MO** from flatness of `g`
(`AlgebraicGeometry.Space.BaseChangeDiagram.isFlat_g'`), which is the flatness of `A → B`.

*The restriction of scalars on the left.*  The two sides are modules over different rings —
`H^i(X', 𝓕')` over `Γ(X', 𝒪_{X'})` and `H^i(X, g'_*𝓕')` over `Γ(X, 𝒪_X)` — so the comparison is
stated after reading the left hand side over `Γ(X, 𝒪_X)` along the ring map of **Stacks 0732**,
`AlgebraicGeometry.Space.globalSectionsRingHomSite`.  Restriction of scalars does not change
the underlying abelian group, so this is the equality of the source read over a common ring.

*No `@[stacks]` attribute is carried.*  Stacks 073K is claimed, for the pieces of part (2) that
are available, on the declarations of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyPullback.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeMap.lean`, and Stacks 0733
on `AlgebraicGeometry.Space.cohomologyPushforwardIsoOfIsFlatOfIsAffineHom`; this statement is
that one instantiated at the square, so a further claim would double-count both tags.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 0730](https://stacks.math.columbia.edu/tag/0730)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-- **The coefficient `𝓕' = (g')^*𝓕` of the square is quasi-coherent**, the inverse image of a
quasi-coherent module being quasi-coherent. -/
theorem isQuasicoherentOnSite_pulledBack : D.pulledBack.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS D.g' D.F D.isQuasicoherent

/-- **The collapse step of Stacks 073K, part (2).**  For a cartesian square of algebraic spaces
with affine bases `Y` and `Y'` and a flat `g : Y' ⟶ Y`, the cohomology of the pulled back
coefficient on `X'` is the cohomology on `X` of its direct image along `g'`,

`H^i(X', 𝓕') ≅ H^i(X, g'_*𝓕')`,

in every degree `i`, as modules over `Γ(X, 𝒪_X)`.

Nothing is assumed of `X`: this is the step at which the source says that the higher direct
images along the affine morphism `g'` vanish, and it is `Stacks 0733` part (1) for a morphism
that is both affine and flat,
`AlgebraicGeometry.Space.cohomologyPushforwardIsoOfIsFlatOfIsAffineHom`, instantiated at `g'`.
Affineness of `g'` comes from affineness of the two bases and flatness
of `g'` from flatness of `g`, that is from flatness of `A → B`. -/
def cohomologyPushforwardIso (hg : IsFlat B S hS D.g.hom) (hY : IsAffineSpace B S hS D.Y.1)
    (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    ((globalSectionsRestrictScalars B S hS D.g').obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
          i).obj D.pulledBack) ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).rightDerived i).obj
        ((modulePushforward B S hS D.g').obj D.pulledBack)) :=
  cohomologyPushforwardIsoOfIsFlatOfIsAffineHom B S hS D.g' (D.isAffineHom_g' hY hY')
    (D.isFlat_g' hg) D.pulledBack D.isQuasicoherentOnSite_pulledBack i

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end
