module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmallOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 08PS in the derived category: `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)` and in `D(B)`

Let `A → B` be a ring map and let `ε : P_• ⟶ B` be a resolution of `B` over `A` in the sense of
Tag 08QI — each `P_n` a polynomial algebra over `A` and `ε` a trivial Kan fibration on underlying
simplicial sets — whose terms are polynomial algebras on at most `κ` variables. The conclusion of
Tag 08PS is

`Lπ_!(ℱ) = ℱ(P_•, ε)`

in `D(Ab)`, resp. `D(B)`, functorially in `ℱ` in `Ab(C_{B/A})`, resp. `Mod(B̲)`. This file proves
both halves **as isomorphisms in the derived category**, natural in `ℱ`, read at the small model of
the footnote-restricted site `C_{B/A}` of `StacksFrontier/Cotangent/PolynomialAlgebraSiteSmall.lean`.

What was already available is the *degreewise* form:
`CommAlgCat.smallResolutionLeftDerivedLowerShriekNatIso` and
`CommAlgCat.smallResolutionModuleLeftDerivedLowerShriekNatIso` identify the degree `n` functor
`(Lπ_!)_n` with `H_n` of the Moore complex of `ℱ(P_•, ε)`, for every `n`.
That is strictly weaker than the source's conclusion: a complex is not determined by its
cohomology, and a consumer transporting a morphism of coefficients — an augmentation `𝒪 ⟶ B̲`,
or the comparison of two resolutions of the same ring map — across the identification needs the
isomorphism in `D(Ab)`, resp. `D(B)`.

## Main results

* `CommAlgCat.smallResolutionDerivedColimitNatIso`: the conclusion of Tag 08PS in `D(Ab)` at the
  small model — the extended Moore complex of `ℱ(P_•, ε)` is `Lπ_!(ℱ)` in `D(Ab)`, as an
  isomorphism of functors of the abelian sheaf `ℱ`.
* `CommAlgCat.smallResolutionModuleDerivedColimitNatIso`: the same for a sheaf of `B`-modules
  `ℱ`, in `D(B)`.
* `CommAlgCat.standardResolutionDerivedColimitNatIso` and
  `CommAlgCat.standardResolutionModuleDerivedColimitNatIso`: **Tag 08PT** in `D(Ab)` and in
  `D(B)`, the same two statements for the standard resolution of `B` over `A`, whose hypotheses
  are discharged by Tag 08QI.

## Implementation notes

**Where the mathematics is.** Nothing is reproved here. The hypothesis the criterion of Tag 08Q9
asks of the cosimplicial object of the resolution is Tag 08PS's own content,
`CommAlgCat.isPointResolution_smallResolutionCosimplicialObject`, and it does not mention the
coefficients. The criterion itself, in its derived-category form and natural in the coefficient
object, is
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit` at abelian coefficients and
`Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit` at linear coefficients; both
are proved by comparing the two filtrations of the double complex obtained by evaluating a
projective resolution of `ℱ` on the cosimplicial object, the naturality coming from the fact that
the resolutions of Tag 0646 are degreewise epimorphic so that a morphism of coefficients lifts
(Tag 0649). The four declarations below are those criteria applied to the resolution.

**`ℱ(P_•, ε)` is the extended Moore complex.** The right-hand side of the source is the simplicial
abelian group, resp. simplicial `B`-module, `n ↦ ℱ(P_n, ε_n)`, read as an object of the derived
category. The reindexing used is `ComplexShape.embeddingUpIntLE 0`, which puts the simplicial
degree `n` in cohomological degree `-n`; this is the same reindexing by which
`CommAlgCat.standardResolutionModuleLeftDerivedCotangentComplexIso` compares the Moore complex
with the cotangent complex, so the statements below compose with it.

**`Lπ_!` is the total left derived colimit.** On a chaotic site `π_!` is the colimit over the
index category (Tag 08PF, `Stacks.ChaoticSite.lowerShriek_pointSections_colimitIso`), and `Lπ_!`
below is accordingly `Stacks.CategoryHomology.totalDerivedColimit`, the total left derived functor
of that colimit — the same functor out of which Tag 09CZ's `Lπ_! : D(𝒪) ⟶ D(B)` is built
(`Stacks.ChaoticSite.derivedColimitWithCoefficients`). Coefficients are abelian *presheaves* on
the small model, which for the chaotic topology are its abelian sheaves
(`Stacks.ChaoticSite.sheafToPresheafTrivial_isEquivalence`), and linear coefficients are diagrams
of `B`-modules, which are the `B̲`-modules
(`Stacks.ChaoticSite.constantModulePresheafEquivalence`). The degreewise statements cited above
are stated instead with `Stacks.ChaoticSite.abelianPointLowerShriek`, resp.
`Stacks.ChaoticSite.ModuleValued.modulePointLowerShriek`, followed by the sections at the point,
the passage between the two being the transport of `CategoryTheory.Functor.leftDerived` of
`Stacks.ChaoticSite.leftDerivedPointLowerShriekNatIso`; the corresponding transport of a *total*
left derived functor along those equivalences is not in the library, so the statements below are
read at the colimit presentation of `π_!`.

**The small model, and why these are not the tag.** These statements are read at the small model
of the footnote-restricted site, so their coefficients are the abelian sheaves, resp. the
`B̲`-modules, of a *full subcategory* of `C_{B/A}` -- the augmentations whose set of variables has
cardinality at most `κ`. Both `Ab(-)` and `Lπ_!` change when one restricts to a full subcategory,
so neither statement is Tag 08PS, and neither carries the attribute. Tag 08PS at the site of
Tag 08PR itself is proved in
`StacksFrontier/Cotangent/ResolutionPointCriterionPolynomialSite.lean`, the criterion of Tag 08Q9
with its smallness hypothesis removed being
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge`. What these statements
still supply is the conclusion at a coefficient universe equal to that of the site's morphisms,
which the general version does not: there the coefficients are forced up to the universe of the
site's objects. See the second implementation note of
`StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean` for why the cardinal bound is carried
as a parameter `κ` rather than fixed at `#B`.

## References

* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryHomology

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

section Bounded

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, functorially in `ℱ`, for a resolution of `B` over `A`.**
Let `ε : P_• ⟶ B` be a resolution of `B` over `A` — each `P_n` a polynomial algebra over `A`, `ε`
a trivial Kan fibration on underlying simplicial sets — whose terms are polynomial algebras on at
most `κ` variables. Then the extended Moore complex of the simplicial abelian group `ℱ(P_•, ε)` is
`Lπ_!(ℱ)` in `D(Ab)`, as an **isomorphism of functors** of the abelian sheaf `ℱ` on the small
model of the restricted site `C_{B/A}`.

This is the abelian half of the conclusion of Tag 08PS read at the small model, in the derived
category rather than degreewise: the hypothesis of the criterion of Tag 08Q9 holds for the
cosimplicial object of the resolution by
`CommAlgCat.isPointResolution_smallResolutionCosimplicialObject`, and
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit` is that criterion in its
derived form, natural in the coefficient presheaf. The degreewise form
`CommAlgCat.smallResolutionLeftDerivedLowerShriekNatIso` does not give this: it determines only
the cohomology of the two sides.

It carries no 08PS attribute: the footnote-restricted site is a full subcategory of `C_{B/A}`, so
this is the tag's conclusion for a smaller category of coefficients. Tag 08PS itself, at
`CommAlgCat.polynomialSite`, is
`CommAlgCat.polynomialSiteResolutionDerivedColimitNatIso`. -/
def smallResolutionDerivedColimitNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.AbelianValued.mooreCochainComplex
          (smallResolutionCosimplicialObject ε κ hPκ) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ AddCommGrpCat.{u})
          (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙
          totalDerivedColimit (smallBoundedPolynomialSite A B κ) AddCommGrpCat.{u} :=
  Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit _
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε)

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)`, functorially in `ℱ`, for a resolution of `B` over `A`.**
Let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial algebras on at most
`κ` variables. Then the extended Moore complex of the simplicial `B`-module `ℱ(P_•, ε)` is
`Lπ_!(ℱ)` in `D(B)`, as an **isomorphism of functors** of the sheaf of `B`-modules `ℱ` on the
small model of the restricted site `C_{B/A}`.

This is the module half of the conclusion of Tag 08PS, in the derived category rather than
degreewise, beside the abelian half `CommAlgCat.smallResolutionDerivedColimitNatIso`: the same
hypothesis `CommAlgCat.isPointResolution_smallResolutionCosimplicialObject` — which does not
mention the coefficients — is fed to
`Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit`, the criterion of Tag 08Q9 in
its derived form at linear coefficients, natural in the coefficient module. The degreewise form
`CommAlgCat.smallResolutionModuleLeftDerivedLowerShriekNatIso` does not give this.

As for the abelian half it carries no 08PS attribute, being the tag's conclusion for the
coefficients of a full subcategory of `C_{B/A}`; Tag 08PS in `D(B)` is
`CommAlgCat.polynomialSiteResolutionModuleDerivedColimitNatIso`. -/
def smallResolutionModuleDerivedColimitNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.ModuleValued.mooreCochainComplex (B := (B : Type u))
          (smallResolutionCosimplicialObject ε κ hPκ) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single
          ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} (B : Type u))
          (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙
          totalDerivedColimit (smallBoundedPolynomialSite A B κ) (ModuleCat.{u} (B : Type u)) :=
  Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit _
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε)

end Bounded

/-! ### The standard resolution -/

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)` for the standard resolution**, functorially in the abelian
sheaf `ℱ` on the small model of the site restricted to polynomial algebras on at most
`CommAlgCat.standardResolutionVarCardinal A B` variables.

This is the abelian half of the conclusion of Tag 08PT in the derived category. The two
hypotheses of Tag 08PS hold for the standard resolution by Tag 08QI — its terms are polynomial
algebras and its augmentation is a trivial Kan fibration — and its terms are boundedly many
variables wide by `CommAlgCat.standardResolution_isPolynomialAlgebraBelow`, so nothing is
assumed. -/
@[stacks 08PT "the conclusion `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)` functorially in `ℱ` in \
  `Ab(C_{B/A})`, for the standard resolution, as an isomorphism in the derived category rather \
  than degreewise, read at the small model of the footnote-restricted site — for the reason \
  recorded at Tag 08PS in this file"]
def standardResolutionDerivedColimitNatIso :
    Stacks.ChaoticSite.AbelianValued.mooreCochainComplex
          (smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom
            (standardResolutionVarCardinal A B)
            (standardResolution_isPolynomialAlgebraBelow A B)) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            AddCommGrpCat.{u})
          (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙
          totalDerivedColimit (smallBoundedPolynomialSite A B
            (standardResolutionVarCardinal A B)) AddCommGrpCat.{u} :=
  smallResolutionDerivedColimitNatIso (standardResolution.{u, u} A B).hom
    (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)` for the standard resolution**, functorially in the sheaf of
`B`-modules `ℱ` on the small model of the site restricted to polynomial algebras on at most
`CommAlgCat.standardResolutionVarCardinal A B` variables.

This is the module half of the conclusion of Tag 08PT in the derived category, beside the abelian
half `CommAlgCat.standardResolutionDerivedColimitNatIso`; as there, the hypotheses of Tag 08PS are
discharged for the standard resolution by Tag 08QI. -/
@[stacks 08PT "the conclusion `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)` functorially in `ℱ` in `Mod(B̲)`, \
  for the standard resolution, as an isomorphism in the derived category rather than degreewise, \
  read at the small model of the footnote-restricted site — for the reason recorded at Tag 08PS \
  in this file"]
def standardResolutionModuleDerivedColimitNatIso :
    Stacks.ChaoticSite.ModuleValued.mooreCochainComplex (B := (B : Type u))
          (smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom
            (standardResolutionVarCardinal A B)
            (standardResolution_isPolynomialAlgebraBelow A B)) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u))
          (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙
          totalDerivedColimit (smallBoundedPolynomialSite A B
            (standardResolutionVarCardinal A B)) (ModuleCat.{u} (B : Type u)) :=
  smallResolutionModuleDerivedColimitNatIso (standardResolution.{u, u} A B).hom
    (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration

end CommAlgCat

end
