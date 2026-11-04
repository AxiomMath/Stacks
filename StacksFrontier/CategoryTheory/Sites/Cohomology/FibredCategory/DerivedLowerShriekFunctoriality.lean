module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of derived lower shriek for a morphism of fibred categories

Let `u : C' ⥤ C` be a 1-morphism of fibred categories over a ringed site `(D, O_D)`, as in the
standing data of Stacks 08PA, and give `C` and `C'` the topologies they inherit from `D`. The three
induced morphisms of topoi `π : Sh(C) ⟶ Sh(D)`, `π' : Sh(C') ⟶ Sh(D)` and `g : Sh(C') ⟶ Sh(C)` have
inverse images `π⁻¹ = p_s`, `(π')⁻¹ = p'_s` and `g⁻¹ = u_s`, restriction along the three functors.
On abelian sheaves each of those restrictions has a left adjoint — `π_!`, `π'_!` and `g_!` — and
each left adjoint has an unbounded left derived functor as soon as the acyclicity statement of
Stacks 07AC holds for it.

This file produces the canonical map of Stacks 08PD. Because `p' = u ⋙ p`, restriction factors as
`(π')⁻¹ = g⁻¹ ∘ π⁻¹`, and on the unbounded derived categories, where all three restrictions are
induced degreewise by exactness, the same factorization holds; uniqueness of left adjoints turns it
into the identification `Lπ'_! = Lπ_! ∘ Lg_!`. Given an abelian sheaf `F` on `C`, an abelian sheaf
`F'` on `C'` and a map `t : F' ⟶ g⁻¹F`, the canonical map `Lπ'_!(F') ⟶ Lπ_!(F)` is that
identification followed by `Lπ_!` applied to the composite of the comparison `Lg_!(F') ⟶ g_!F'`
with the adjoint `g_!F' ⟶ F` of `t`.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.totalAbelianLowerShriek` and
  `sourceAbelianLowerShriek`: `π_! : Ab(C) ⥤ Ab(D)` and `π'_! : Ab(C') ⥤ Ab(D)`, the lower-shriek
  functors of the two projections, alongside the already available `abelianLowerShriek`, which is
  `g_! : Ab(C') ⥤ Ab(C)`.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedTotalAbelianLowerShriek`,
  `derivedSourceAbelianLowerShriek` and `derivedAbelianLowerShriek`: `Lπ_!`, `Lπ'_!` and `Lg_!` on
  the unbounded derived categories, with their derived adjunctions
  `derivedTotalAbelianLowerShriekAdjunction`, `derivedSourceAbelianLowerShriekAdjunction` and
  `derivedAbelianLowerShriekAdjunction`.
* `Stacks.Sites.FibredCategory.MorphismSituation.AbelianLowerShriekAcyclic`,
  `TotalAbelianLowerShriekAcyclic` and `SourceAbelianLowerShriekAcyclic`: the acyclicity statement
  of Stacks 07AC for each of the three lower-shriek functors.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedAbelianLowerShriekSingleComparison`: the
  comparison `Lg_!(F') ⟶ g_!F'` at an abelian sheaf placed in degree zero.
* `Stacks.Sites.FibredCategory.MorphismSituation.canonicalDerivedLowerShriekMap`: **the canonical
  map `Lπ'_!(F') ⟶ Lπ_!(F)` of Stacks 08PD.**

## Main results

* `Stacks.Sites.FibredCategory.MorphismSituation.abelianInverseImageCompIso`: restriction of
  abelian sheaves to `C'` is restriction to `C` followed by restriction along `u`.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedAbelianInverseImageCompIso`: the same
  factorization on the unbounded derived categories.
* `Stacks.Sites.FibredCategory.MorphismSituation.derivedAbelianLowerShriekCompIso`: **the
  identification `Lπ'_! = Lπ_! ∘ Lg_!` of Stacks 08PD**, characterised by
  `conjugateEquiv_derivedAbelianLowerShriekCompIso_inv` as the mate of
  `derivedAbelianInverseImageCompIso`.

## Implementation notes

**The acyclicity hypotheses.** The existence of `Lπ_!`, `Lπ'_!` and `Lg_!` is Stacks 07AC, whose
proof reduces to one statement that is not formal: that the lower-shriek functor carries a bounded
above acyclic complex whose terms are direct sums of the free abelian sheaves `j_{U!} ℤ_U` to an
acyclic complex. Lower shriek is not exact for a general fibred category, so that statement is not
discharged here. The three derived functors therefore carry the resulting pointwise left derived
functor as an instance hypothesis, and every statement that needs a *derived adjunction* carries
the acyclicity statement itself. Stacks 08PD presupposes all three derived functors, so carrying
these hypotheses is part of its standing data and not a weakening of its conclusion.

**The universes, and why the instances are seated by name.** The sections are taken in
`AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}`, the universe in which Stacks 08PA forms the three
morphisms of topoi and in which Stacks 08PC states the lower-shriek functors. The generic machinery
of `StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean` is stated
with coefficients `AddCommGrpCat.{max v w'}` for a free `w'`, and is applied here with
`w' := max w u₀ u₁ u₂ v₀ v₁ v₂`. Solving `max v ?w' =?= max w u₀ u₁ u₂ v₀ v₁ v₂` is beyond Lean's
level unifier, so instance search does not find those instances on its own: every application below
writes its universes explicitly, and the side conditions they need — sheafification on the three
sites, Grothendieck abelianness of abelian sheaves on `C` and on `D`, smallness of the two fibred
categories, the right-adjointness of the three restrictions, and their additivity and exactness —
are recorded here as named instances rather than left to search.
-/

/-!
## References

* [Stacks Project, Tag 08PD](https://stacks.math.columbia.edu/tag/08PD)
* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

universe u₀ u₁ u₂ v₀ v₁ v₂ w u v t

namespace MorphismSituation

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-! ### Sheafification, Grothendieck abelianness and smallness -/

/-- Abelian sheaves for the inherited topology on the source fibred category can be sheafified in
the universe in which the three morphisms of topoi are formed. -/
instance hasSheafifySourceTopology :
    HasSheafify S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  hasSheafify_addCommGrpCat.{u₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology

/-- Abelian sheaves for the inherited topology on the target fibred category can be sheafified in
the universe in which the three morphisms of topoi are formed. -/
instance hasSheafifyTotalTopology :
    HasSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  hasSheafify_addCommGrpCat.{u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalTopology

/-- Abelian sheaves on the base site can be sheafified in the universe in which the three morphisms
of topoi are formed. -/
instance hasSheafifyBaseTopology :
    HasSheafify S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  hasSheafify_addCommGrpCat.{u₀, v₀, max w u₀ u₁ u₂ v₀ v₁ v₂} S.base.J

/-- The weak form of sheafification on the target fibred category. -/
instance hasWeakSheafifyTotalTopology :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.hasSheafifyTotalTopology.isRightAdjoint

/-- The weak form of sheafification on the base site. -/
instance hasWeakSheafifyBaseTopology :
    HasWeakSheafify S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.hasSheafifyBaseTopology.isRightAdjoint

/-- Abelian sheaves on the target fibred category form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_totalSheaves :
    IsGrothendieckAbelian.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  isGrothendieckAbelian_sheaf_addCommGrpCat.{u₁, v₁, max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalTopology

/-- Abelian sheaves on the base site form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_baseSheaves :
    IsGrothendieckAbelian.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  isGrothendieckAbelian_sheaf_addCommGrpCat.{u₀, v₀, max w u₀ u₁ u₂ v₀ v₁ v₂} S.base.J

/-- The source fibred category is small in the universe of the sections, its objects lying in a
universe contained in that one. -/
instance small_source : Small.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.source :=
  small_max.{max w u₀ u₁ v₀ v₁ v₂, u₂} _

/-- The target fibred category is small in the universe of the sections, its objects lying in a
universe contained in that one. -/
instance small_total : Small.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.total :=
  small_max.{max w u₀ u₂ v₀ v₁ v₂, u₁} _

/-! ### The three restrictions and their left adjoints -/

/-- Restriction of abelian sheaves along `u` admits a left adjoint. -/
instance uInverseImage_isRightAdjoint :
    (S.u.sheafPushforwardContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.sourceTopology S.totalTopology).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous S.u
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology S.totalTopology).isRightAdjoint

/-- Restriction of abelian sheaves along `p` admits a left adjoint. -/
instance pInverseImage_isRightAdjoint :
    (S.p.sheafPushforwardContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.totalTopology S.base.J).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous S.p
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalTopology S.base.J).isRightAdjoint

/-- Restriction of abelian sheaves along `p'` admits a left adjoint. -/
instance p'InverseImage_isRightAdjoint :
    (S.p'.sheafPushforwardContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}
      S.sourceTopology S.base.J).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous S.p'
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology S.base.J).isRightAdjoint

/-- `π⁻¹ : Ab(D) ⥤ Ab(C)`, the inverse image of abelian sheaves along the morphism of topoi induced
by the target's projection: restriction along `p`. -/
abbrev totalAbelianInverseImage :
    Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.p.sheafPushforwardContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalTopology S.base.J

/-- `(π')⁻¹ : Ab(D) ⥤ Ab(C')`, the inverse image of abelian sheaves along the morphism of topoi
induced by the source's projection: restriction along `p'`. -/
abbrev sourceAbelianInverseImage :
    Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.p'.sheafPushforwardContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology S.base.J

/-- `π_! : Ab(C) ⥤ Ab(D)`, the lower-shriek functor on abelian sheaves for the target's projection:
the chosen left adjoint of `π⁻¹`. -/
abbrev totalAbelianLowerShriek :
    Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.p.sheafPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalTopology S.base.J

/-- `π'_! : Ab(C') ⥤ Ab(D)`, the lower-shriek functor on abelian sheaves for the source's
projection: the chosen left adjoint of `(π')⁻¹`. -/
abbrev sourceAbelianLowerShriek :
    Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} ⥤
      Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  S.p'.sheafPullback AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology S.base.J

/-- The adjunction `π_! ⊣ π⁻¹` on abelian sheaves. -/
abbrev totalAbelianLowerShriekAdjunction :
    S.totalAbelianLowerShriek ⊣ S.totalAbelianInverseImage :=
  S.p.sheafAdjunctionContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.totalTopology S.base.J

/-- The adjunction `π'_! ⊣ (π')⁻¹` on abelian sheaves. -/
abbrev sourceAbelianLowerShriekAdjunction :
    S.sourceAbelianLowerShriek ⊣ S.sourceAbelianInverseImage :=
  S.p'.sheafAdjunctionContinuous AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology S.base.J

/-- `π_!` is additive, being a left adjoint between additive categories. -/
instance totalAbelianLowerShriek_additive : S.totalAbelianLowerShriek.Additive :=
  Cohomology.DerivedLowerShriek.additive_abelianLowerShriek.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- `π'_!` is additive, being a left adjoint between additive categories. -/
instance sourceAbelianLowerShriek_additive : S.sourceAbelianLowerShriek.Additive :=
  Cohomology.DerivedLowerShriek.additive_abelianLowerShriek.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

/-- `g⁻¹` preserves finite colimits, being exact. -/
instance abelianInverseImage_preservesFiniteColimits' :
    PreservesFiniteColimits S.abelianInverseImage :=
  Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u

/-- `π⁻¹` is additive, being exact. -/
instance totalAbelianInverseImage_additive : S.totalAbelianInverseImage.Additive :=
  Cohomology.DerivedLowerShriek.additive_abelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- `π⁻¹` preserves finite colimits. -/
instance totalAbelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits S.totalAbelianInverseImage :=
  Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- `π⁻¹` preserves finite limits, being a right adjoint. -/
instance totalAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits S.totalAbelianInverseImage := inferInstance

/-- `(π')⁻¹` is additive, being exact. -/
instance sourceAbelianInverseImage_additive : S.sourceAbelianInverseImage.Additive :=
  Cohomology.DerivedLowerShriek.additive_abelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

/-- `(π')⁻¹` preserves finite colimits. -/
instance sourceAbelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits S.sourceAbelianInverseImage :=
  Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianRestriction.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

/-- `(π')⁻¹` preserves finite limits, being a right adjoint. -/
instance sourceAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits S.sourceAbelianInverseImage := inferInstance

/-! ### Restriction factors through the target fibred category -/

/-- **Restriction of abelian sheaves to the source fibred category factors through the target**:
`(π')⁻¹ = g⁻¹ ∘ π⁻¹`, because `p' = u ⋙ p`. -/
def abelianInverseImageCompIso :
    S.totalAbelianInverseImage ⋙ S.abelianInverseImage ≅ S.sourceAbelianInverseImage :=
  Functor.sheafPushforwardContinuousComp' (eqToIso S.isFibredOneMorphism.comp_eq)
    AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂} S.sourceTopology S.totalTopology S.base.J

/-! ### The acyclicity statements of Stacks 07AC -/

/-- **The acyclicity statement of Stacks 07AC for `g_!`.** Lower shriek along the 1-morphism
carries a bounded above acyclic complex whose terms are direct sums of the free abelian sheaves
`j_{U!} ℤ_U` on objects of the source fibred category to an acyclic complex. -/
abbrev AbelianLowerShriekAcyclic : Prop :=
  Cohomology.DerivedLowerShriek.AbelianLowerShriekAcyclic.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u

/-- **The acyclicity statement of Stacks 07AC for `π_!`**, for the free abelian sheaves on objects
of the target fibred category. -/
abbrev TotalAbelianLowerShriekAcyclic : Prop :=
  Cohomology.DerivedLowerShriek.AbelianLowerShriekAcyclic.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- **The acyclicity statement of Stacks 07AC for `π'_!`**, for the free abelian sheaves on objects
of the source fibred category. -/
abbrev SourceAbelianLowerShriekAcyclic : Prop :=
  Cohomology.DerivedLowerShriek.AbelianLowerShriekAcyclic.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

/-- `g_!` applied degreewise to unbounded complexes of abelian sheaves, read on the homotopy
categories. -/
abbrev abelianLowerShriekOnHomotopy :
    HomotopyCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ) :=
  Cohomology.DerivedLowerShriek.abelianLowerShriekOnHomotopy.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u

/-- `π_!` applied degreewise to unbounded complexes of abelian sheaves, read on the homotopy
categories. -/
abbrev totalAbelianLowerShriekOnHomotopy :
    HomotopyCategory (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ) :=
  Cohomology.DerivedLowerShriek.abelianLowerShriekOnHomotopy.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- `π'_!` applied degreewise to unbounded complexes of abelian sheaves, read on the homotopy
categories. -/
abbrev sourceAbelianLowerShriekOnHomotopy :
    HomotopyCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ) :=
  Cohomology.DerivedLowerShriek.abelianLowerShriekOnHomotopy.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC for `g_!`**, existence: the acyclicity statement produces the pointwise left
derived functor of degreewise `g_!` on the unbounded homotopy category. -/
theorem hasPointwiseLeftDerivedAbelianLowerShriek (h : S.AbelianLowerShriekAcyclic) :
    (S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ)) :=
  Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u h

/-- **Stacks 07AC for `π_!`**, existence. -/
theorem hasPointwiseLeftDerivedTotalAbelianLowerShriek (h : S.TotalAbelianLowerShriekAcyclic) :
    (S.totalAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ)) :=
  Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p h

/-- **Stacks 07AC for `π'_!`**, existence. -/
theorem hasPointwiseLeftDerivedSourceAbelianLowerShriek (h : S.SourceAbelianLowerShriekAcyclic) :
    (S.sourceAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
        (ComplexShape.up ℤ)) :=
  Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p' h

/-- `g⁻¹ : D(Ab(C)) ⥤ D(Ab(C'))` on the unbounded derived categories, induced degreewise because
restriction of abelian sheaves along a continuous and cocontinuous functor of sites is exact. -/
abbrev derivedAbelianInverseImage :
    DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u

/-- `π⁻¹ : D(Ab(D)) ⥤ D(Ab(C))` on the unbounded derived categories. -/
abbrev derivedTotalAbelianInverseImage :
    DerivedCategory (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- `(π')⁻¹ : D(Ab(D)) ⥤ D(Ab(C'))` on the unbounded derived categories. -/
abbrev derivedSourceAbelianInverseImage :
    DerivedCategory (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

/-- **The factorization `(π')⁻¹ = g⁻¹ ∘ π⁻¹` on the unbounded derived categories.** -/
def derivedAbelianInverseImageCompIso :
    S.derivedTotalAbelianInverseImage ⋙ S.derivedAbelianInverseImage ≅
      S.derivedSourceAbelianInverseImage :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso
      (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) (ComplexShape.up ℤ))
    ((S.totalAbelianInverseImage.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q) ⋙ S.derivedAbelianInverseImage)
    (S.sourceAbelianInverseImage.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    _ _
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ S.abelianInverseImage.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso S.abelianInverseImageCompIso (ComplexShape.up ℤ))
        DerivedCategory.Q)

variable [(S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
      (ComplexShape.up ℤ))]
  [(S.totalAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
      (ComplexShape.up ℤ))]
  [(S.sourceAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
      (ComplexShape.up ℤ))]

/-- `Lg_! : D(Ab(C')) ⥤ D(Ab(C))`, the unbounded left derived functor of lower shriek along the
1-morphism of fibred categories. -/
abbrev derivedAbelianLowerShriek :
    DerivedCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u

/-- `Lπ_! : D(Ab(C)) ⥤ D(Ab(D))`, the unbounded left derived functor of `π_!`. -/
abbrev derivedTotalAbelianLowerShriek :
    DerivedCategory (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- `Lπ'_! : D(Ab(C')) ⥤ D(Ab(D))`, the unbounded left derived functor of `π'_!`. -/
abbrev derivedSourceAbelianLowerShriek :
    DerivedCategory (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ⥤
      DerivedCategory (Sheaf S.base.J AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :=
  Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{max w u₀ u₁ u₂ v₀ v₁ v₂,
    v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

/-- The comparison `Lg_! ⟶ g_!` on the homotopy category: the counit exhibiting `Lg_!` as a left
derived functor of degreewise `g_!`. -/
abbrev derivedAbelianLowerShriekComparison :
    DerivedCategory.Qh ⋙ S.derivedAbelianLowerShriek ⟶
      S.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh :=
  Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u

/-- **Stacks 07AC for `g_!`**, the derived adjunction: `Lg_!` is left adjoint to derived
restriction along `u`. -/
def derivedAbelianLowerShriekAdjunction (h : S.AbelianLowerShriekAcyclic) :
    S.derivedAbelianLowerShriek ⊣ S.derivedAbelianInverseImage :=
  have := Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u h DerivedCategory.Qh
    S.derivedAbelianLowerShriek S.derivedAbelianLowerShriekComparison S.derivedAbelianInverseImage
  Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u

/-- **Stacks 07AC for `π_!`**, the derived adjunction: `Lπ_!` is left adjoint to derived
restriction along `p`. -/
def derivedTotalAbelianLowerShriekAdjunction (h : S.TotalAbelianLowerShriekAcyclic) :
    S.derivedTotalAbelianLowerShriek ⊣ S.derivedTotalAbelianInverseImage :=
  have := Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p h DerivedCategory.Qh
    S.derivedTotalAbelianLowerShriek
    (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p)
    S.derivedTotalAbelianInverseImage
  Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p

/-- **Stacks 07AC for `π'_!`**, the derived adjunction: `Lπ'_!` is left adjoint to derived
restriction along `p'`. -/
def derivedSourceAbelianLowerShriekAdjunction (h : S.SourceAbelianLowerShriekAcyclic) :
    S.derivedSourceAbelianLowerShriek ⊣ S.derivedSourceAbelianInverseImage :=
  have := Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p' h DerivedCategory.Qh
    S.derivedSourceAbelianLowerShriek
    (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p')
    S.derivedSourceAbelianInverseImage
  Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{max w
    u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p'

/-- **The identification `Lπ'_! = Lπ_! ∘ Lg_!`**, the isomorphism of left adjoints induced by
`derivedAbelianInverseImageCompIso`. -/
@[stacks 08PD "the identification Lπ'_! = Lπ_! ∘ Lg_!"]
def derivedAbelianLowerShriekCompIso (h : S.AbelianLowerShriekAcyclic)
    (hp : S.TotalAbelianLowerShriekAcyclic) (hp' : S.SourceAbelianLowerShriekAcyclic) :
    S.derivedAbelianLowerShriek ⋙ S.derivedTotalAbelianLowerShriek ≅
      S.derivedSourceAbelianLowerShriek :=
  Adjunction.leftAdjointCompIso (S.derivedAbelianLowerShriekAdjunction h)
    (S.derivedTotalAbelianLowerShriekAdjunction hp)
    (S.derivedSourceAbelianLowerShriekAdjunction hp')
    S.derivedAbelianInverseImageCompIso

/-- **The identification `Lπ'_! = Lπ_! ∘ Lg_!` is the mate of the factorization of restriction.**
This characterises `derivedAbelianLowerShriekCompIso`: a natural transformation between left
adjoints is determined by the transformation of right adjoints it is conjugate to. -/
theorem conjugateEquiv_derivedAbelianLowerShriekCompIso_inv (h : S.AbelianLowerShriekAcyclic)
    (hp : S.TotalAbelianLowerShriekAcyclic) (hp' : S.SourceAbelianLowerShriekAcyclic) :
    conjugateEquiv
      ((S.derivedAbelianLowerShriekAdjunction h).comp
        (S.derivedTotalAbelianLowerShriekAdjunction hp))
      (S.derivedSourceAbelianLowerShriekAdjunction hp')
      (S.derivedAbelianLowerShriekCompIso h hp hp').inv =
    S.derivedAbelianInverseImageCompIso.hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- **The comparison `Lg_!(F') ⟶ g_!F'`** at an abelian sheaf `F'` on `C'` placed in degree zero:
the counit exhibiting `Lg_!` as a left derived functor, read between the two spellings of a sheaf
as an object of the derived category. -/
def derivedAbelianLowerShriekSingleComparison
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) :
    S.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor
        (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj F') ⟶
      (DerivedCategory.singleFunctor
        (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj
          (S.abelianLowerShriek.obj F') :=
  S.derivedAbelianLowerShriek.map
      ((DerivedCategory.singleFunctorIsoCompQh
        (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).hom.app F') ≫
    S.derivedAbelianLowerShriekComparison.app ((HomotopyCategory.singleFunctor
      (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj F') ≫
    DerivedCategory.Qh.map
      ((S.abelianLowerShriek.mapHomotopyCategorySingleFunctor 0).hom.app F') ≫
    (DerivedCategory.singleFunctorIsoCompQh
      (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).inv.app
        (S.abelianLowerShriek.obj F')

/-- **The canonical map.** Let `F` be an abelian sheaf on `C`, let `F'` be an abelian sheaf on `C'`
and let `t : F' ⟶ g⁻¹F` be a map of abelian sheaves. The canonical map `Lπ'_!(F') ⟶ Lπ_!(F)` is the
identification `Lπ'_! = Lπ_! ∘ Lg_!` followed by `Lπ_!` applied to the composite of the comparison
`Lg_!(F') ⟶ g_!F'` with the adjoint `g_!F' ⟶ F` of `t`. -/
@[stacks 08PD "canonical map"]
def canonicalDerivedLowerShriekMap (h : S.AbelianLowerShriekAcyclic)
    (hp : S.TotalAbelianLowerShriekAcyclic) (hp' : S.SourceAbelianLowerShriekAcyclic)
    (F : Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
    (t : F' ⟶ S.abelianInverseImage.obj F) :
    S.derivedSourceAbelianLowerShriek.obj ((DerivedCategory.singleFunctor
        (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj F') ⟶
      S.derivedTotalAbelianLowerShriek.obj ((DerivedCategory.singleFunctor
        (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).obj F) :=
  (S.derivedAbelianLowerShriekCompIso h hp hp').inv.app _ ≫
    S.derivedTotalAbelianLowerShriek.map
      (S.derivedAbelianLowerShriekSingleComparison F' ≫
        (DerivedCategory.singleFunctor
          (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) 0).map
            ((S.abelianLowerShriekAdjunction.homEquiv F' F).symm t))

end Derived

end MorphismSituation

end Stacks.Sites.FibredCategory

end
