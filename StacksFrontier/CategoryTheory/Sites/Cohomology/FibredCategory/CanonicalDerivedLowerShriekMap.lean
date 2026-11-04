module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.MorphismSourceSituation
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Stacks 08PD for every situation of Stacks 08PA

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, with the three induced morphisms of topoi
`π : Sh(C) ⟶ Sh(D)`, `π' : Sh(C') ⟶ Sh(D)` and `g : Sh(C') ⟶ Sh(C)`. The identification
`Lπ'_! = Lπ_! ∘ Lg_!` and the canonical map `Lπ'_!(F') ⟶ Lπ_!(F)` of Stacks 08PD are constructed in
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFunctoriality` from
the acyclicity statement of Stacks 07AC for each of the three lower-shriek functors. All three
statements hold: for the two projections it is
`Stacks.Sites.FibredCategory.FibredCategorySituation.abelianLowerShriekAcyclic`, and for the
1-morphism it is `Stacks.Sites.FibredCategory.MorphismSituation.abelianLowerShriekAcyclic`. This
file supplies them, so that the three derived lower-shriek functors exist as instances and the
two constructions of Stacks 08PD take nothing beyond the situation.

## Main definitions

All in the namespace `Stacks.Sites.FibredCategory.MorphismSituation`:

* `derivedAbelianLowerShriekCompIso'`: **the identification `Lπ'_! = Lπ_! ∘ Lg_!` of
  Stacks 08PD**, for every situation of Stacks 08PA.
* `canonicalDerivedLowerShriekMap'`: **the canonical map `Lπ'_!(F') ⟶ Lπ_!(F)` of
  Stacks 08PD**, for every situation of Stacks 08PA.

## Main results

* `hasPointwiseLeftDerivedFunctor_totalAbelianLowerShriekOnHomotopy` and
  `hasPointwiseLeftDerivedFunctor_sourceAbelianLowerShriekOnHomotopy`: Stacks 07AC for `π_!` and
  `π'_!`, existence of the unbounded left derived functors with no hypothesis; the same for `g_!`
  is `hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy`, of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.MorphismLowerShriekAcyclic`.
* `conjugateEquiv_derivedAbelianLowerShriekCompIso'_inv`: the identification is the mate of the
  factorization of restriction.

## Implementation notes

`derivedAbelianLowerShriekCompIso'` and `canonicalDerivedLowerShriekMap'` are
`derivedAbelianLowerShriekCompIso` and `canonicalDerivedLowerShriekMap` at the three discharged
acyclicity statements. The latter two take those statements as arguments because the module that
constructs them is imported by the one that discharges the statement for the 1-morphism.

## References

* [Stacks Project, Tag 08PD](https://stacks.math.columbia.edu/tag/08PD)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

universe u₀ u₁ u₂ v₀ v₁ v₂ w

namespace MorphismSituation

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC for `π_!`**, existence with no hypothesis: the acyclicity statement for the
target's projection is the one of its fibred category. -/
instance hasPointwiseLeftDerivedFunctor_totalAbelianLowerShriekOnHomotopy :
    (S.totalAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ)) :=
  S.hasPointwiseLeftDerivedTotalAbelianLowerShriek (totalSituation S).abelianLowerShriekAcyclic

/-- **Stacks 07AC for `π'_!`**, existence with no hypothesis: the acyclicity statement for the
source's projection is the one of its fibred category. -/
instance hasPointwiseLeftDerivedFunctor_sourceAbelianLowerShriekOnHomotopy :
    (S.sourceAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ)) :=
  S.hasPointwiseLeftDerivedSourceAbelianLowerShriek (sourceSituation S).abelianLowerShriekAcyclic

/-- **Stacks 08PD, the identification `Lπ'_! = Lπ_! ∘ Lg_!`**, for every situation of
Stacks 08PA. The three derived lower-shriek functors are left adjoint to the three derived
restrictions, by Stacks 07AC at the three discharged acyclicity statements, and restriction to the
source fibred category is restriction to the target followed by restriction along the
1-morphism; so this is uniqueness of left adjoints applied to
`derivedAbelianInverseImageCompIso`. -/
@[stacks 08PD "the identification Lπ'_! = Lπ_! ∘ Lg_!"]
def derivedAbelianLowerShriekCompIso' :
    S.derivedAbelianLowerShriek ⋙ S.derivedTotalAbelianLowerShriek ≅
      S.derivedSourceAbelianLowerShriek :=
  S.derivedAbelianLowerShriekCompIso (abelianLowerShriekAcyclic S)
    (totalSituation S).abelianLowerShriekAcyclic (sourceSituation S).abelianLowerShriekAcyclic

/-- **The identification `Lπ'_! = Lπ_! ∘ Lg_!` is the mate of the factorization of restriction.**
This characterises `derivedAbelianLowerShriekCompIso'`: a natural transformation between left
adjoints is determined by the transformation of right adjoints it is conjugate to. -/
theorem conjugateEquiv_derivedAbelianLowerShriekCompIso'_inv :
    conjugateEquiv
      ((S.derivedAbelianLowerShriekAdjunction (abelianLowerShriekAcyclic S)).comp
        (S.derivedTotalAbelianLowerShriekAdjunction
          (totalSituation S).abelianLowerShriekAcyclic))
      (S.derivedSourceAbelianLowerShriekAdjunction
        (sourceSituation S).abelianLowerShriekAcyclic)
      S.derivedAbelianLowerShriekCompIso'.inv =
    S.derivedAbelianInverseImageCompIso.hom :=
  S.conjugateEquiv_derivedAbelianLowerShriekCompIso_inv _ _ _

/-- **Stacks 08PD, the canonical map**, for every situation of Stacks 08PA. Let `F` be an abelian
sheaf on `C`, let `F'` be an abelian sheaf on `C'` and let `t : F' ⟶ g⁻¹F` be a map of abelian
sheaves. The canonical map `Lπ'_!(F') ⟶ Lπ_!(F)` is the identification `Lπ'_! = Lπ_! ∘ Lg_!`
followed by `Lπ_!` applied to the composite of the comparison `Lg_!(F') ⟶ g_!F'` with the adjoint
`g_!F' ⟶ F` of `t`. -/
@[stacks 08PD "canonical map"]
def canonicalDerivedLowerShriekMap'
    (F : Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
    (t : F' ⟶ S.abelianInverseImage.obj F) :
    S.derivedSourceAbelianLowerShriek.obj ((DerivedCategory.singleFunctor
        (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj F') ⟶
      S.derivedTotalAbelianLowerShriek.obj ((DerivedCategory.singleFunctor
        (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj F) :=
  S.canonicalDerivedLowerShriekMap (abelianLowerShriekAcyclic S)
    (totalSituation S).abelianLowerShriekAcyclic (sourceSituation S).abelianLowerShriekAcyclic
    F F' t

end MorphismSituation

end Stacks.Sites.FibredCategory

end
