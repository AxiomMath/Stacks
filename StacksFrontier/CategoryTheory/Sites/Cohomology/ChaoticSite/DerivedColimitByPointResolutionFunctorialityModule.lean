module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitOfComplexesByPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekAlongAFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek of modules is unchanged under a functor with a common resolution

Let `f : C' ⥤ C` be a functor between small categories carrying their chaotic topologies, let `B`
be a ring, so that a `B̲`-module is a diagram of `B`-modules on the opposite category, and let
`g^{-1} = Stacks.ChaoticSite.inverseImageAlongAFunctor` be the inverse image of the induced
morphism of ringed topoi, that is, restriction along `f`. Let `U_•` be a cosimplicial object of
`C'` such that both `U_•` and its image `f(U_•)` are point resolutions. Then

`Lπ'_! ∘ g^{-1} = Lπ_!`

**in the derived category** `D(B)`: both sides are the extended Moore complex of one and the same
simplicial `B`-module, because evaluating the restriction of a diagram on `U_•` is evaluating the
diagram itself on `f(U_•)`.

## Main results

* `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageNatIso`: the derived lower shriek on
  `C'` of the inverse image of a `B̲`-module `ℱ` on `C` is the derived lower shriek of `ℱ` on
  `C`, as an isomorphism of functors into `D(B)`.

## Implementation notes

The two sites and the module sections live in one universe `u`;
`Stacks.ChaoticSite.inverseImageAlongAFunctor` is read at that convention by taking both of its
universe parameters to be `u`.

The domain of the isomorphism is the category of `B̲`-modules on `C`, not the derived category
`D(C, B̲)`. The statement for an arbitrary bounded above complex of `B̲`-modules is
`Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageComplexNatIso`.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite.ModuleValued

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] {B : Type u} [Ring B]

/-- Inverse image along `f` followed by the extended Moore complex on `U_•` is the extended Moore
complex on `f(U_•)`. -/
lemma inverseImageAlongAFunctor_comp_mooreCochainComplex (f : C' ⥤ C)
    (U : CosimplicialObject C') :
    inverseImageAlongAFunctor C C' f B ⋙ mooreCochainComplex U =
      mooreCochainComplex (B := B) (U ⋙ f) :=
  rfl

/-- Let `f : C' ⥤ C` be a functor between small categories with their chaotic topologies, let `B`
be a ring, let `g^{-1}` be the inverse image of the induced morphism of ringed topoi — restriction
of diagrams of `B`-modules along `f` — and let `U_•` be a cosimplicial object of `C'` such that
both `U_•` and `f(U_•)` are point resolutions. Then the derived lower shriek on `C'` of the
inverse image of a `B̲`-module `ℱ` on `C` is the derived lower shriek of `ℱ` on `C`, as an
isomorphism of functors into `D(B)` and naturally in `ℱ`: that is, `Lπ'_! ∘ g^{-1} = Lπ_!`. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(B)`, at module \
  coefficients, as an isomorphism of functors whose domain is the category of `B̲`-modules on \
  `C` — the heart. The same identification for an arbitrary bounded above COMPLEX of \
  `B̲`-modules, which is what the source's `D(C, B̲) ⥤ D(B)` says, is \
  `Stacks.ChaoticSite.ModuleValued.derivedColimitInverseImageComplexNatIso`; the unbounded case \
  is open and the implementation note says what it needs"]
def derivedColimitInverseImageNatIso (f : C' ⥤ C) (U : CosimplicialObject C')
    (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    inverseImageAlongAFunctor C C' f B ⋙
        HomologicalComplex.single (C'ᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0 ⋙
          DerivedCategory.Q ⋙ totalDerivedColimit C' (ModuleCat.{u} B) ≅
      HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C (ModuleCat.{u} B) :=
  Functor.isoWhiskerLeft (inverseImageAlongAFunctor C C' f B)
      (mooreCochainNatIsoDerivedColimit U hU).symm ≪≫
    (Functor.associator (inverseImageAlongAFunctor C C' f B)
        (mooreCochainComplex U) DerivedCategory.Q).symm ≪≫
    eqToIso (congrArg (· ⋙ DerivedCategory.Q)
      (inverseImageAlongAFunctor_comp_mooreCochainComplex (B := B) f U)) ≪≫
    mooreCochainNatIsoDerivedColimit (U ⋙ f) hfU

end Stacks.ChaoticSite.ModuleValued

end
