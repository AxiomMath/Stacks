module

public import StacksFrontier.Cotangent.AtiyahClassSmallSiteMoore
public import StacksFrontier.Cotangent.AtiyahClassBigSiteResolution
public import StacksFrontier.Homology.TorAmplitude.CompositionCanonical

/-!
# The cotangent complex as a Moore complex at the site `C_{B/A}` itself

At the site `C_{B/A}` of [Stacks, Tag 08PR] itself, read on its `CategoryTheory.AsSmall` model
`CommAlgCat.atiyahSite`, the sheaf `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` has sections
`ULift B ⊗_{ULift P} Ω[ULift P ⁄ ULift A]` in `Type (u + 1)`, because the morphism of topoi `π`
of [Stacks, Tag 08PF] is formed at a coefficient universe containing the objects of the site.
`CommAlgCat.polynomialCotangentModulePresheaf` is the same mathematical object written at
`Type u`, and `StacksDraft.TorAmplitude.moduleLift` is the universe lift that mediates between
them. This file computes the extended Moore complex of the lifted sheaf on the standard
resolution:

`Moore((i^*Ω_{𝒪/A})(P_•, ε)) = L_{B/A}` and, after tensoring, `L_{B/A} ⊗_B M` degreewise.

The identification of the evaluation of `i^*Ω_{𝒪/A}` on the standard resolution with the simplicial
module of [Stacks, Tag 08PN] is `CommAlgCat.standardResolutionOverDifferentialsIso`, which mentions
no site at all -- it compares `CommAlgCat.overDifferentialsFunctor` restricted along the resolution
with `CommAlgCat.cotangentSimplicialModule`, and the two are the same formula. What this site
contributes is that the terms of the standard resolution are objects of `C_{B/A}` on the nose, no
cardinality bound and so no transport along a model intervening: that is what makes the comparison
below the extension of an isomorphism of simplicial modules and nothing more.

## Main results

* `CommAlgCat.atiyahStandardCotangentMooreCochainIso`: **the extended Moore complex of
  `i^*Ω_{𝒪/A}` on the standard resolution, read at the site `C_{B/A}` itself, is the cotangent
  complex `L_{B/A}` of [Stacks, Tag 08PN]**, at `Type u` coefficients.
* `CommAlgCat.atiyahMooreTensorIso`: the extended Moore complex of `M ⊗_B i^*Ω_{𝒪/A}` at the
  coefficients `ULift B` of the site's own ringed point is `M ⊗ -` applied degreewise to the
  universe lift of `L_{B/A}`.

## References

* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicTopology Opposite

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- `i^*Ω_{𝒪/A}` read on `CommAlgCat.atiyahSite` at `Type u` coefficients: the restriction of
`CommAlgCat.polynomialCotangentModulePresheaf` along the comparison functor of the `AsSmall`
model. -/
abbrev atiyahCotangentModulePresheaf :
    (atiyahSite A B)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u) :=
  atiyahSiteFunctor A B ⋙ polynomialCotangentModulePresheaf A B

/-- **The extended Moore complex of `i^*Ω_{𝒪/A}` on the standard resolution, at the site
`C_{B/A}` itself, is the cotangent complex `L_{B/A}`.** No transport along a model intervenes:
the terms of the standard resolution are objects of `C_{B/A}`, so the evaluation of
`i^*Ω_{𝒪/A}` on the cosimplicial object of the resolution is
`CommAlgCat.overDifferentialsFunctor` restricted along it, which is
`CommAlgCat.cotangentSimplicialModule` by
`CommAlgCat.standardResolutionOverDifferentialsIso`. -/
def atiyahStandardCotangentMooreCochainIso :
    (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex
          (atiyahStandardCosimplicialObject A B) (ModuleCat.{u} (B : Type u))).obj
        (atiyahCotangentModulePresheaf A B) ≅
      cotangentComplex.{u, u} A B :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{u} (B : Type u))).mapIso
    ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).mapIso
      (standardResolutionOverDifferentialsIso A B))

/-- The universe lift of the cotangent complex: `L_{B/A}` read as a complex of `ULift B`-modules
in `Type (u + 1)`, which is the universe of the site's own ringed point
`CommAlgCat.polynomialRingedPoint`. -/
abbrev moduleLiftCotangentComplex :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) ℤ :=
  ((StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)

variable (M : ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))

/-- **The extended Moore complex of `M ⊗_B i^*Ω_{𝒪/A}` on the standard resolution is `M ⊗ -`
applied degreewise to the universe lift of the cotangent complex.** The Moore complex commutes
with an additive functor applied degreewise
(`Stacks.ChaoticSite.GeneralValued.mooreCochainMapHomologicalComplexIso`), used twice: once at
the universe lift `StacksDraft.TorAmplitude.moduleLift` and once at `M ⊗ -`. The case `M = B` is
`CommAlgCat.atiyahStandardCotangentMooreCochainIso`. -/
def atiyahMooreTensorIso :
    (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex
          (atiyahStandardCosimplicialObject A B)
          (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))).obj
        (atiyahCotangentModulePresheaf A B ⋙
          StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u) ⋙
            tensorLeft M) ≅
      ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (moduleLiftCotangentComplex A B) :=
  (Stacks.ChaoticSite.GeneralValued.mooreCochainMapHomologicalComplexIso
      (atiyahStandardCosimplicialObject A B) (tensorLeft M)
      (atiyahCotangentModulePresheaf A B ⋙
        StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u))).symm ≪≫
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((Stacks.ChaoticSite.GeneralValued.mooreCochainMapHomologicalComplexIso
          (atiyahStandardCosimplicialObject A B)
          (StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1} (B : Type u))
          (atiyahCotangentModulePresheaf A B)).symm ≪≫
        ((StacksDraft.TorAmplitude.moduleLift.{u, u, u + 1}
            (B : Type u)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          (atiyahStandardCotangentMooreCochainIso A B))

end CommAlgCat

end
