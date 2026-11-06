module

public import StacksFrontier.Cotangent.AtiyahClass
public import StacksFrontier.Cotangent.PolynomialAlgebraSitePointValuesLargeSite
public import StacksFrontier.Cotangent.ResolutionPointCriterionPolynomialSite
import StacksCore.Tactic.StacksAttribute

/-!
# The site `C_{B/A}` itself: its point resolutions and `Lπ_!π^{-1} = id`

The Atiyah triangle of [Stacks, Tag 09DD] is formed, in
`StacksFrontier/Cotangent/AtiyahClass.lean`, on `CommAlgCat.atiyahSite`, which is
`CategoryTheory.AsSmall` of the site `C_{B/A}` of [Stacks, Tag 08PR] itself. Passing to
`AsSmall` is not a change of site: it is an equivalence of categories, so the categories of
abelian sheaves agree and so do the two `Lπ_!`
(`Stacks.ChaoticSite.totalDerivedColimitEquivalenceIso`). What it buys is that
`Stacks.ChaoticSite.derivedColimitWithCoefficients`, the `Lπ_! : D(𝒪) ⟶ D(B)` of
[Stacks, Tag 09CZ], is stated for a site whose objects and morphisms live in one universe, while
the objects of `C_{B/A}` live in `Type (u + 1)` and its morphisms in `Type u`.

This file supplies, at that site, the two inputs the endpoints of the Atiyah triangle need:

* the cosimplicial object of a resolution `ε : P_• ⟶ B` is a point resolution, which is the
  hypothesis of the criterion of [Stacks, Tag 08Q9];
* `Lπ_!(π^{-1}M) = M`, which is [Stacks, Tag 08QE].

Both are read off statements about `CommAlgCat.polynomialSite` -- nothing is reproved. The first
is `CommAlgCat.isPointResolution_resolutionCosimplicialObject` carried along the equivalence by
`Stacks.ChaoticSite.isPointResolution_asSmall`, and the second is
`Stacks.ChaoticSite.derivedConstCompColimitIso`, whose only hypothesis is that the site have a
terminal (or an initial) object -- here the augmentation `A → B`, by
`CommAlgCat.isTerminal_polynomialBaseObj`.

## Main definitions

* `CommAlgCat.atiyahBaseObj`: the augmentation `A → B` as an object of `CommAlgCat.atiyahSite`.
* `CommAlgCat.atiyahCosimplicialObject`: the cosimplicial object of a resolution
  `ε : P_• ⟶ B`, read in `CommAlgCat.atiyahSite`, and
  `CommAlgCat.atiyahStandardCosimplicialObject` for the standard resolution.

## Main results

* `CommAlgCat.isTerminal_atiyahBaseObj` and `CommAlgCat.hasTerminal_atiyahSite`: the
  augmentation `A → B` is a terminal object of `CommAlgCat.atiyahSite`.
* `CommAlgCat.isPointResolution_atiyahCosimplicialObject` and
  `CommAlgCat.isPointResolution_atiyahStandardCosimplicialObject`: a resolution of `B` over `A`
  gives a point resolution of `CommAlgCat.atiyahSite`.
* `CommAlgCat.atiyahModuleDerivedInverseImageCompLowerShriekIso`: **[Stacks, Tag 08QE] at the
  site `C_{B/A}` itself**, `Lπ_!(π^{-1}M) = M` in `D(B)` naturally in `M`, at the coefficient
  ring `ULift B` of the site's own ringed point `CommAlgCat.polynomialRingedPoint`.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08Q7](https://stacks.math.columbia.edu/tag/08Q7)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QE](https://stacks.math.columbia.edu/tag/08QE)
* [Stacks Project, Tag 09DD](https://stacks.math.columbia.edu/tag/09DD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryHomology

universe u

namespace CommAlgCat

/-! ### The terminal object of `CommAlgCat.atiyahSite` -/

section Terminal

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- The augmentation `A → B`, read as an object of `CommAlgCat.atiyahSite`. -/
def atiyahBaseObj : atiyahSite A B := AsSmall.up.obj (polynomialBaseObj A B)

/-- **The augmentation `A → B` is a terminal object of `CommAlgCat.atiyahSite`.** It is one of
`CommAlgCat.polynomialSite` by `CommAlgCat.isTerminal_polynomialBaseObj`, and the morphisms of
`CategoryTheory.AsSmall` of a category are the universe lifts of its morphisms, so both halves of
the universal property are read off there. -/
def isTerminal_atiyahBaseObj : IsTerminal (atiyahBaseObj A B) :=
  IsTerminal.ofUniqueHom
    (fun Y => ULift.up ((isTerminal_polynomialBaseObj A B).from (AsSmall.down.obj Y)))
    fun _ _ => ULift.ext ((isTerminal_polynomialBaseObj A B).hom_ext _ _)

/-- The category `CommAlgCat.atiyahSite A B` has a terminal object. -/
instance hasTerminal_atiyahSite : HasTerminal (atiyahSite A B) :=
  (isTerminal_atiyahBaseObj A B).hasTerminal

end Terminal

/-! ### Point resolutions of `CommAlgCat.atiyahSite` -/

section PointResolution

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))

/-- The augmentation `ε : P_• ⟶ B`, read as a cosimplicial object of
`CommAlgCat.atiyahSite`. -/
def atiyahCosimplicialObject : CosimplicialObject (atiyahSite A B) :=
  resolutionCosimplicialObject ε hP ⋙ AsSmall.up

/-- **The cosimplicial object of a resolution is a point resolution of
`CommAlgCat.atiyahSite`.** The hypothesis holds at `CommAlgCat.polynomialSite` by
`CommAlgCat.isPointResolution_resolutionCosimplicialObject`, and it speaks only of the simplicial
sets of morphisms, whose sections the passage to `CategoryTheory.AsSmall` merely lifts in
universe: that is `Stacks.ChaoticSite.isPointResolution_asSmall`. -/
theorem isPointResolution_atiyahCosimplicialObject
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.IsPointResolution (atiyahCosimplicialObject ε hP) :=
  Stacks.ChaoticSite.isPointResolution_asSmall (polynomialSite A B)
    (isPointResolution_resolutionCosimplicialObject ε hP hε)

end PointResolution

section Standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- The standard resolution of `B` over `A`, read as a cosimplicial object of
`CommAlgCat.atiyahSite`: the cosimplicial object
`CommAlgCat.standardResolutionPolynomialSiteCosimplicialObject` of `CommAlgCat.polynomialSite`,
carried along `CategoryTheory.AsSmall.up`. -/
abbrev atiyahStandardCosimplicialObject : CosimplicialObject (atiyahSite A B) :=
  standardResolutionPolynomialSiteCosimplicialObject A B ⋙ AsSmall.up

/-- **The standard resolution is a point resolution of `CommAlgCat.atiyahSite`.** It is one of
`CommAlgCat.polynomialSite` by
`CommAlgCat.isPointResolution_standardResolutionPolynomialSiteCosimplicialObject`, and the
hypothesis speaks only of the simplicial sets of morphisms, whose sections the passage to
`CategoryTheory.AsSmall` merely lifts in universe. -/
theorem isPointResolution_atiyahStandardCosimplicialObject :
    Stacks.ChaoticSite.IsPointResolution (atiyahStandardCosimplicialObject A B) :=
  Stacks.ChaoticSite.isPointResolution_asSmall (polynomialSite A B)
    (isPointResolution_standardResolutionPolynomialSiteCosimplicialObject A B)

end Standard

/-! ### Tag 08QE at the site `C_{B/A}` itself -/

section Tag08QE

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **[Stacks, Tag 08QE] at the site `C_{B/A}` itself.** Derived lower shriek of the inverse
image of a `B`-module is that module: `Lπ_!(π^{-1}M) = M` in `D(B)`, naturally in `M`. Here
`π^{-1}` is the constant diagram and `Lπ_!` the total left derived functor of the colimit over
the index category, which is the `π_!` of [Stacks, Tag 08PF]; the coefficient ring is
`ULift B`, the ring of the site's own ringed point `CommAlgCat.polynomialRingedPoint`.

The proof is the source's: the augmentation `A → B` is a terminal object of the site
(`CommAlgCat.isTerminal_atiyahBaseObj`), so `π^{-1}` has the exact right adjoint "sections over
`A → B`" and `Stacks.ChaoticSite.derivedConstCompColimitIso` applies with no hypothesis on the
existence of the derived functor. The statement at the footnote-restricted site is
`CommAlgCat.smallPolynomialModuleDerivedInverseImageCompLowerShriekIso`; that is a statement
about different coefficients, the restriction to a full subcategory changing both `Mod(B̲)` and
`Lπ_!`. -/
@[stacks 08QE "in D(B), at module coefficients: Lπ_!(π^{-1}M) = M at `CommAlgCat.polynomialSite` \
  -- the site of Tag 08PR itself, not a restriction of it, read on its `AsSmall` model -- with \
  Lπ_! the total left derived functor of the colimit on D(B̲), π^{-1} the constant diagram, and \
  the coefficient ring read as `ULift.{u+1} B` exactly as the site's own ringed point \
  `CommAlgCat.polynomialRingedPoint` reads it"]
def atiyahModuleDerivedInverseImageCompLowerShriekIso :
    (Functor.const (atiyahSite A B)ᵒᵖ :
          ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)) ⥤ _).mapDerivedCategory ⋙
        totalDerivedColimit (atiyahSite A B)
          (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) ≅ 𝟭 _ :=
  Stacks.ChaoticSite.derivedConstCompColimitIso _ _ (Or.inr inferInstance)

end Tag08QE

end CommAlgCat

end
