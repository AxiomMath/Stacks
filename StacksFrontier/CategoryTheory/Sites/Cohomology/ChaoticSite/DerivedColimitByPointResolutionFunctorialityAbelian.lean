module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek under a functor with a common cosimplicial resolution

Let `f : C' ⥤ C` be a functor between small categories carrying their chaotic topologies and let
`g^{-1}` be the induced inverse image on abelian presheaves, that is, restriction along `f`. Let
`U_•` be a cosimplicial object of `C'` such that both `U_•` and its image `f(U_•)` are point
resolutions. Then

`Lπ'_! ∘ g^{-1} = Lπ_!`

in the derived category `D(Ab)`: both sides are the extended Moore complex of one and the same
simplicial abelian group, because evaluating the restriction of an abelian presheaf on `U_•` is
evaluating the presheaf itself on `f(U_•)`.

## Main results

* `Stacks.ChaoticSite.AbelianValued.presheafRestriction_comp_mooreCochainComplex`: restriction
  along `f` followed by the extended Moore complex on `U_•` is the extended Moore complex on
  `f(U_•)`.
* `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionNatIso`: the derived lower
  shriek on `C'` of the restriction of an abelian presheaf `ℱ` on `C` is the derived lower shriek
  of `ℱ` on `C`, as an isomorphism of functors into `D(Ab)`.

## Implementation notes

Both sites and the coefficients live in one universe `u`. The domain of the isomorphism is the
category of abelian presheaves on `C`, not the derived category `D(C)`; the same identification
for a bounded above complex of abelian presheaves is
`Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionComplexNatIso`.

For an unbounded complex `K` the total complex of the double complex of `K` on `U_•` does not
compute `Lπ_!(K)`. There the canonical map `Lπ'_!(g^{-1}K) ⟶ Lπ_!(K)` is the `Lπ'_!`-adjunct of
`g^{-1}` applied to the unit of `Stacks.CategoryHomology.totalDerivedColimitAdjunction`, and it is
an isomorphism once it is one on a set of compact generators of `D(C)` and their shifts.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite.AbelianValued

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']

/-- Restriction of abelian presheaves along `f` followed by the extended Moore complex over `ℤ` on
`U_•` is the extended Moore complex on `f(U_•)`, as an equality of functors. -/
lemma presheafRestriction_comp_mooreCochainComplex (f : C' ⥤ C) (U : CosimplicialObject C') :
    Stacks.CategoryHomology.presheafRestriction.{u, u, u} f ⋙ mooreCochainComplex U =
      mooreCochainComplex (U ⋙ f) :=
  rfl

/-- Let `f : C' ⥤ C` be a functor between small categories with their chaotic topologies, let
`g^{-1}` be restriction of abelian presheaves along `f`, and let `U_•` be a cosimplicial object of
`C'` such that both `U_•` and `f(U_•)` are point resolutions. Then the derived lower shriek on
`C'` of the restriction of an abelian presheaf `ℱ` on `C` is the derived lower shriek of `ℱ` on
`C`, as an isomorphism of functors into `D(Ab)` and naturally in `ℱ`: that is,
`Lπ'_! ∘ g^{-1} = Lπ_!`. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(Ab)`, at abelian \
  coefficients, as an isomorphism of functors whose domain is the category of abelian presheaves \
  on `C` — the heart. The same identification for an arbitrary bounded above COMPLEX of abelian \
  presheaves, which is what the source's `D(C) ⥤ D(Ab)` says, is \
  `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionComplexNatIso`; the \
  unbounded case is open and the implementation note says what it needs"]
def derivedColimitPresheafRestrictionNatIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    Stacks.CategoryHomology.presheafRestriction.{u, u, u} f ⋙
        HomologicalComplex.single (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0 ⋙
          DerivedCategory.Q ⋙ totalDerivedColimit C' AddCommGrpCat.{u} ≅
      HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft (Stacks.CategoryHomology.presheafRestriction.{u, u, u} f)
      (mooreCochainNatIsoDerivedColimit U hU).symm ≪≫
    (Functor.associator (Stacks.CategoryHomology.presheafRestriction.{u, u, u} f)
        (mooreCochainComplex U) DerivedCategory.Q).symm ≪≫
    eqToIso (congrArg (· ⋙ DerivedCategory.Q)
      (presheafRestriction_comp_mooreCochainComplex f U)) ≪≫
    mooreCochainNatIsoDerivedColimit (U ⋙ f) hfU

end Stacks.ChaoticSite.AbelianValued

end
