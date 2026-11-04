module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInjective

/-!
# Cohomology over an object of a simplicial component

Let `S` be a simplicial-site situation (Stacks 09WE) and let
`g_n : Sh(C_n) ⟶ Sh(C_total)` be the morphism of topoi of Stacks 09WG induced by the inclusion
`u : C_n ⥤ C_total` of the degree-`n` component. For an abelian sheaf `F` on the total site and
an object `U` of `C_n`, the cohomology of the restriction `g_n⁻¹F` over `U` is the cohomology of
`F` over `U` viewed as an object of the total site.

The proof is the one the source gives for its general form, Stacks 03YU and Stacks 0DD8:
sections over `U` of a restriction are sections over `u(U)` — on the nose, the underlying
presheaf of a restriction being precomposition with `uᵒᵖ` — and restriction to a component is
exact and preserves injective abelian sheaves, so it carries an injective resolution to an
injective resolution and both sides are computed by the same complex. Preservation of
injectives is Stacks 09WH, which rests on the exactness of lower shriek,
Stacks 09WG (7); the formal step from there to the comparison of derived functors is the
generic `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.additive_componentRestrictionAb`,
  `.preservesFiniteLimits_componentRestrictionAb`,
  `.preservesFiniteColimits_componentRestrictionAb` and
  `.preservesInjectiveObjects_componentRestrictionAb`: restriction of abelian sheaves to a
  simplicial component is an additive exact functor preserving injective objects.
* `CategoryTheory.SimplicialSiteSituation.sections_comp_componentRestrictionAb`: sections over
  `U` of a restricted abelian sheaf are its sections over `u(U)`, by `rfl`.
* `CategoryTheory.SimplicialSiteSituation.componentCohomologyIso`:
  `H^p(U, g_n⁻¹F) ≅ H^p(u(U), F)`, naturally in `F`.
* `CategoryTheory.SimplicialSiteSituation.componentDerivedSectionsIso`: the same comparison at
  the level of `RΓ`, in the injective-resolution model `K^+(Ab)` of `D^+(ℤ)`.

## Implementation notes

`H^p(U, -)` is `Stacks.Cohomology.CompositeRightDerived.cohomology`, the `p`-th right derived
functor of sections over `U`, which is the definition the source makes and the one
Stacks 071E and Stacks 03YU of this repository use.

Restriction is left exact because it is the right adjoint of lower shriek, and right exact
because it is the left adjoint of the direct image of the cocontinuous component inclusion;
both adjunctions exist at the site's own coefficient universe without hypotheses, the component
and the total category being small there. The same universe restriction governs
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentInjective.lean`, whose statement this
file consumes.

### Relation to Stacks 0DBZ

Stacks 0DBZ is this comparison for an abelian sheaf, and it is formalized as
`Stacks.Cohomology.SimplicialComponent.cohomologyObj_iso_component`
(`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentSumNaturality/ComponentCohomology.lean`)
in a *different carrier*: Mathlib's `Ext`-based `CategoryTheory.Sheaf.H'`, with restriction
spelled as `CategoryTheory.Functor.sheafPullbackCocontinuous`. That declaration is not reused
here, for two reasons recorded so that the overlap is not mistaken for duplication.

First, it is not canonical. It transports
`Stacks.Cohomology.CompositeRightDerived.statement2_cohomology`, which asserts `Nonempty` of an
isomorphism, along two further existence statements relating `Sheaf.H'` to right-derived
sections; the implementation notes of
`StacksFrontier/Cotangent/CohomologyPresheaf/BiggerSiteObjectwise.lean` say that the isomorphism
there is a choice, as is each of the two transports. Building the module-coefficient statement
on it would mean choosing data out of an existence statement. The comparison constructed here
goes through the canonical
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` instead, so it is pinned by
the injective resolutions it is computed from and involves no choice.

Second, the carrier has to be right-derived sections for the module-coefficient statement to be
definitional on sections: restriction of sheaves of modules to a component has the identity
structure map, so on underlying abelian sheaves it is
`CategoryTheory.Functor.sheafPushforwardContinuous` on the nose, and sections over `U` of that
are sections over `u(U)` by `rfl`. Nothing in this repository identifies `Sheaf.H'` with
right-derived sections canonically.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 0DBZ](https://stacks.math.columbia.edu/tag/0DBZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.CompositeRightDerived

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- **`Γ(U, g_n⁻¹(-)) = Γ(u(U), -)`.** The underlying presheaf of a restriction along the
component inclusion is precomposition with the opposite of that inclusion, so sections over `U`
of a restricted abelian sheaf are sections over `U` viewed as an object of the total site. -/
theorem sections_comp_componentRestrictionAb (U : S.component n) :
    S.restrictAb n ⋙ sections (S.componentTopology n) U =
      sections S.totalTopology ((componentFunctor S n).obj U) :=
  rfl

/-- **`H^p(U, g_n⁻¹F) ≅ H^p(u(U), F)`**, naturally in the abelian sheaf `F` on the total site:
for an object `U` of the degree-`n` component, cohomology over `U` of the restriction of an
abelian sheaf is its cohomology over `U` viewed as an object of the total site. -/
noncomputable def componentCohomologyIso (U : S.component n) (p : ℕ) :
    S.restrictAb n ⋙ cohomology (S.componentTopology n) U p ≅
      cohomology S.totalTopology ((componentFunctor S n).obj U) p :=
  (compRightDerivedNatIso (S.restrictAb n) (sections (S.componentTopology n) U) p).symm ≪≫
    rightDerivedNatIso (eqToIso (sections_comp_componentRestrictionAb S n U)) p

/-- **`RΓ(U, g_n⁻¹F) ≅ RΓ(u(U), F)`**, naturally in `F`: the comparison of
`componentCohomologyIso` at the level of the bounded-below derived category, modelled by the
homotopy category of bounded-below cochain complexes of abelian groups. -/
noncomputable def componentDerivedSectionsIso (U : S.component n) :
    S.restrictAb n ⋙ RGamma (S.componentTopology n) U ≅
      RGamma S.totalTopology ((componentFunctor S n).obj U) :=
  (compRightDerivedToHomotopyCategoryNatIso ((componentFunctor S n).sheafPushforwardContinuous
      Ab.{u} (S.componentTopology n) S.totalTopology)
      (sections (S.componentTopology n) U)).symm ≪≫
    rightDerivedToHomotopyCategoryNatIso (eqToIso (sections_comp_componentRestrictionAb S n U))

end CategoryTheory.SimplicialSiteSituation

end
