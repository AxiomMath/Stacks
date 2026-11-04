module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
public import StacksCore.Tactic.StacksAttribute

/-!
# Homology of a category is unchanged under a functor with a common cosimplicial resolution

Let `f : C' ⥤ C` be a functor between small categories carrying their chaotic topologies and let
`g^{-1}` be the induced inverse image on abelian presheaves, that is, restriction along `f`. Let
`U_•` be a cosimplicial object of `C'` such that both `U_•` and its image `f(U_•)` are point
resolutions, so that the criterion of Tag 08Q9 applies on both sites. Then

`L_nπ'_! ∘ g^{-1} = L_nπ_!`

for every degree `n`: both sides compute the homology of the Moore complex of one and the same
simplicial abelian group, because evaluating the restriction of an abelian presheaf on `U_•` is
evaluating the presheaf itself on `f(U_•)`.

## Main results

* `Stacks.ChaoticSite.presheafRestriction_comp_cosimplicialMooreComplex`: restriction along `f`
  followed by evaluation on `U_•` is evaluation on `f(U_•)`, on the nose. This is the content of
  the source's remark that `g^{-1}` is given by precomposing with `f`.
* `Stacks.ChaoticSite.leftDerivedColimitPresheafRestrictionNatIso`: **Tag 08QA** for the left
  derived functors of the colimit over the index category — the homology of `C'` with
  coefficients the restriction of an abelian presheaf `ℱ` on `C` is the homology of `C` with
  coefficients `ℱ`, naturally in `ℱ`.

## Implementation notes

Both sites and the coefficients live in one universe `u`, the universe convention of
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution`: the criterion
of Tag 08Q9 is stated for a small site with coefficients in `AddCommGrpCat.{u}`, and the
restriction functor of Tag 08PH is read at that convention by taking all three of its universe
parameters to be `u`.

The identification of the two Moore complexes is an equality of functors rather than an
isomorphism: restriction along `f.op` and evaluation on `U_•` are both precomposition, and
precomposition with `U_•.op ⋙ f.op` is precomposition with `(U_• ⋙ f).op`.

This is the statement for the left derived functors of `colim`; the passage to the genuine
sheaf-theoretic `π_!`, as in
`Stacks.ChaoticSite.leftDerivedPointLowerShriekNatIso`, needs the inverse image of the induced
morphism of topoi on abelian sheaves and is not developed here.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ChaoticSite

universe u

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']

/-- **Restriction along `f` followed by evaluation on `U_•` is evaluation on `f(U_•)`.** Both
functors are precomposition of an abelian presheaf with `U_•.op ⋙ f.op = (U_• ⋙ f).op`, so the
Moore complexes agree on the nose. -/
lemma presheafRestriction_comp_cosimplicialMooreComplex (f : C' ⥤ C) (U : CosimplicialObject C') :
    Stacks.CategoryHomology.presheafRestriction.{u, u, u} f ⋙ cosimplicialMooreComplex U =
      cosimplicialMooreComplex (U ⋙ f) :=
  rfl

/-- **Stacks 08QA.** Let `f : C' ⥤ C` be a functor between small categories and let `U_•` be a
cosimplicial object of `C'` such that both `U_•` and `f(U_•)` are point resolutions. Then the
homology of `C'` with coefficients the restriction of an abelian presheaf `ℱ` on `C` along `f` is
the homology of `C` with coefficients `ℱ`, in every degree and naturally in `ℱ`: that is,
`L_nπ'_! ∘ g^{-1} = L_nπ_!`. -/
@[stacks 08QA "the identification `L_nπ'_! ∘ g^{-1} = L_nπ_!` degreewise, for the left derived \
  functors of `colim` at abelian coefficients. The derived-category forms at a single module of \
  coefficients are `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionNatIso` \
  and `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageNatIso`, and at an arbitrary \
  bounded above COMPLEX of coefficients — the form the source states — \
  `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionComplexNatIso` and \
  `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageComplexNatIso`"]
def leftDerivedColimitPresheafRestrictionNatIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) (n : ℕ) :
    Stacks.CategoryHomology.presheafRestriction.{u, u, u} f ⋙
        (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n :=
  Functor.isoWhiskerLeft (Stacks.CategoryHomology.presheafRestriction.{u, u, u} f)
      (leftDerivedColimitNatIso U hU n) ≪≫
    (Functor.associator (Stacks.CategoryHomology.presheafRestriction.{u, u, u} f)
        (cosimplicialMooreComplex U)
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n)).symm ≪≫
    eqToIso (congrArg
      (· ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n)
      (presheafRestriction_comp_cosimplicialMooreComplex f U)) ≪≫
    (leftDerivedColimitNatIso (U ⋙ f) hfU n).symm

end Stacks.ChaoticSite

end
