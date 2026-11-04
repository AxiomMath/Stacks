module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.ConstantRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfAResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek is unchanged under a functor with a common cosimplicial resolution

Let `f : C' ⥤ C` be a functor between small categories carrying their chaotic topologies, let
`g : Sh(C') ⟶ Sh(C)` be the induced morphism of topoi, so that `g^{-1}` is restriction along `f`
on abelian sheaves, and let `U_•` be a cosimplicial object of `C'` such that both `U_•` and its
image `f(U_•)` are point resolutions. Then

`L_nπ'_!(g^{-1}ℱ) = L_nπ_!(ℱ)`

for every degree `n` and every abelian sheaf `ℱ` on `C`, naturally in `ℱ`.

This is the statement of
`Stacks.ChaoticSite.leftDerivedColimitPresheafRestrictionNatIso` — Tag 08QA for the left derived
functors of `colim` over the index category of abelian presheaves — read for the genuine
sheaf-theoretic `π_!` of Tag 08PF.

## Main results

* `Stacks.ChaoticSite.leftDerivedPointLowerShriekPresheafRestrictionNatIso`: **Tag 08QA for
  `Lπ_!`.**

## Implementation notes

Nothing is reproved. Both sides are identified with the homology of the Moore complex of one and
the same simplicial abelian group by
`Stacks.ChaoticSite.leftDerivedPointLowerShriekNatIso`, applied at `C'` to `U_•` and at `C` to
`f(U_•)`; what makes the two Moore complexes agree is the equality
`Stacks.ChaoticSite.presheafRestriction_comp_cosimplicialMooreComplex`, and what makes `g^{-1}`
on sheaves agree with restriction on presheaves is
`CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso`, which is the identity.
Both are definitional, so the composite is a composite of exactly two isomorphisms.

The chaotic topologies make every functor continuous, by
`Stacks.ChaoticSite.isContinuous_trivial`, so the inverse image is available with no hypothesis
on `f`.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ChaoticSite

universe u

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']

/-- **Tag 08QA for `Lπ_!`.** Let `f : C' ⥤ C` be a functor between small categories with their
chaotic topologies and let `U_•` be a cosimplicial object of `C'` such that both `U_•` and
`f(U_•)` are point resolutions. Then the sections at the point of `L_nπ'_!` applied to the
inverse image of an abelian sheaf `ℱ` on `C` are the sections at the point of `L_nπ_!(ℱ)`, in
every degree and naturally in `ℱ`: that is, `L_nπ'_! ∘ g^{-1} = L_nπ_!`. -/
@[stacks 08QA "the identification `L_nπ'_! ∘ g^{-1} = L_nπ_!` for the sheaf-theoretic lower \
  shriek along the point morphism, read through the sections at the point"]
def leftDerivedPointLowerShriekPresheafRestrictionNatIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) (n : ℕ) :
    f.sheafPushforwardContinuous AddCommGrpCat.{u} (GrothendieckTopology.trivial C')
          (GrothendieckTopology.trivial C) ⋙
        (abelianPointLowerShriek C').leftDerived n ⋙
          pointSections.{u, u + 1, u} AddCommGrpCat.{u} ≅
      (abelianPointLowerShriek C).leftDerived n ⋙
        pointSections.{u, u + 1, u} AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft
      (f.sheafPushforwardContinuous AddCommGrpCat.{u} (GrothendieckTopology.trivial C')
        (GrothendieckTopology.trivial C))
      (leftDerivedPointLowerShriekNatIso C' U hU n) ≪≫
    (leftDerivedPointLowerShriekNatIso C (U ⋙ f) hfU n).symm

end Stacks.ChaoticSite

end
