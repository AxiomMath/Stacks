module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 08PU in the derived category, at module coefficients

Let `A → B` be a ring map, let `π` and `i` be as in [Stacks, Tag 08PR] and let `𝒪` be the
structure sheaf of the site `C_{B/A}` of polynomial `A`-algebras augmented to `B`. [Stacks, Tag
08PU] identifies the cotangent complex `L_{B/A}` of [Stacks, Tag 08PN] with the derived lower
shriek of the sheaf of `B̲`-modules `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲`, as an object of `D(B)`.

`StacksFrontier/Cotangent/PolynomialAlgebraSiteModuleShriek.lean` carries that identification
*degreewise*, in `CommAlgCat.standardResolutionModuleLeftDerivedCotangentComplexIso`, and its
implementation note records what separates the degreewise statement from the source's
isomorphism in `D(B)`: the derived form of [Stacks, Tag 08PT], a comparison
`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` for a point resolution `U_•`. That comparison is now available, as
`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`, and this file applies it: the
standard resolution is a point resolution of the small model of the footnote-restricted site, and
the cotangent complex *is* the Moore complex of `i^*Ω_{𝒪/A}` evaluated on it, reindexed into
cohomological degrees `≤ 0` by `ComplexShape.embeddingUpIntLE 0`.

## Main results

* `CommAlgCat.standardResolutionCotangentDerivedLowerShriekIso`: **[Stacks, Tag 08PU] in `D(B)`**
  at module coefficients, on the small model of the footnote-restricted site.

## Implementation notes

The two sides are already in place: the left-hand side is `DerivedCategory.Q` of
`CommAlgCat.cotangentComplex` and the right-hand side is
`CommAlgCat.smallPolynomialCotangentDerivedLowerShriek`. The only step added here is that
`CommAlgCat.cotangentComplex` is, by definition, the reindexing along
`ComplexShape.embeddingUpIntLE 0` of the alternating face map complex of
`CommAlgCat.cotangentSimplicialModule`, so that applying the reindexing functor to
`CommAlgCat.standardResolutionCotangentModuleMooreComplexIso` identifies it with the extended
Moore complex that the derived form of [Stacks, Tag 08PT] computes.

The isomorphism is one of objects of `D(B)`; like the comparison it rests on, it is not asserted
to be natural in the coefficient module, a projective resolution of the latter being chosen to
produce it. Tag 08PU is a statement about one sheaf, so nothing is lost.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The cotangent complex is the extended Moore complex of `i^*Ω_{𝒪/A}` evaluated on the
standard resolution.** Both are the alternating face map complex of the simplicial `B`-module of
[Stacks, Tag 08PN], reindexed into cohomological degrees `≤ 0`; the identification of the
simplicial modules is `CommAlgCat.standardResolutionCotangentModuleMooreComplexIso`. -/
def standardResolutionCotangentMooreCochainIso :
    (mooreCochainComplex (standardResolutionSmallCosimplicialObject A B)).obj
        (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) ≅
      cotangentComplex.{u, u} A B :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
    (ModuleCat.{u} (B : Type u))).mapIso
      (standardResolutionCotangentModuleMooreComplexIso A B)

/-- **[Stacks, Tag 08PU] in `D(B)`, at module coefficients and on the small model of the
footnote-restricted site `C_{B/A}`.** The cotangent complex `L_{B/A}` of [Stacks, Tag 08PN] is
derived lower shriek of the sheaf of `B̲`-modules `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲`, as an object of
`D(B)`:

`Q(L_{B/A}) ≅ Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`.

Here `Lπ_!` is `CommAlgCat.smallPolynomialModuleDerivedLowerShriek`, the total left derived
functor of the colimit over the index category of `B̲`-modules, which is the `π_!` of
[Stacks, Tag 08PF].

The proof is the source's. The standard resolution is a point resolution of the small model
(`CommAlgCat.isPointResolution_standardResolutionSmallCosimplicialObject`), so the derived form
of [Stacks, Tag 08PT] at module coefficients
(`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`) computes `Lπ_!` of
`i^*Ω_{𝒪/A}` as the extended Moore complex of its evaluation on that resolution, and that
complex is the cotangent complex. The step `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` of the source is the
flatness of `Ω_{𝒪/A}` over `𝒪`, which is why `i^*Ω_{𝒪/A}` may be used underived. -/
@[stacks 08PU "in D(B), at module coefficients: Q(L_{B/A}) = L pi_!(Omega ⊗ B) for the point \
  morphism of the small model of the footnote-restricted site C_{B/A}, with L pi_! the total \
  left derived functor of the colimit on D(B-underline)"]
def standardResolutionCotangentDerivedLowerShriekIso :
    DerivedCategory.Q.obj (cotangentComplex.{u, u} A B) ≅
      smallPolynomialCotangentDerivedLowerShriek A B (standardResolutionVarCardinal A B) :=
  (DerivedCategory.Q.mapIso (standardResolutionCotangentMooreCochainIso A B)).symm ≪≫
    mooreCochainQIsoDerivedColimit (standardResolutionSmallCosimplicialObject A B)
      (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B))
      (isPointResolution_standardResolutionSmallCosimplicialObject A B)

end Derived

end CommAlgCat

end
