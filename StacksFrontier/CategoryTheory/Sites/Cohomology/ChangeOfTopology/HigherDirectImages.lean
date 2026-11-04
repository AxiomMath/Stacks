module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Homology.RightDerivedCoEdge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonClass
import StacksCore.Tactic.StacksAttribute

/-! # Higher direct images under a change of topology

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in Stacks 0EZ3, write
`ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology morphism, and let `f : X ⟶ Y` be a morphism
of `C`. The square of topoi of Stacks 0EZ2 gives the strict identity

`ε_{X,*} ⋙ f_{τ',*} = f_{τ,*} ⋙ ε_{Y,*}`

of direct images on abelian sheaves over the localized sites — the two composites are the same
functor, because none of the four changes the underlying presheaf of a sheaf. Stacks 0EZA
compares the two ways of deriving it in degree `i`, asserting that

`R^i f_{τ',*} ε_{X,*} ℱ = ε_{Y,*} R^i f_{τ,*} ℱ`

for `f` in the distinguished class, `ℱ` in `𝒜_X` and `i ≤ n`, under the vanishing hypothesis
`(V_n)`.

The canonical map which the tag asserts to be invertible is
`Stacks.ComparingTopologies.higherDirectImageComparison`. It is the composite of the two edge
morphisms of the Grothendieck spectral sequence of the square: the edge `E₂^{i,0} ⟶ H^i` for the
pair `(ε_{X,*}, f_{τ',*})`, followed by the edge `H^i ⟶ E₂^{0,i}` for the pair
`(f_{τ,*}, ε_{Y,*})`, the common middle term being `R^i` of the one composite functor. The map
is defined for every abelian sheaf on the finer localized site over `X`.

## Main definitions

* `Stacks.ComparingTopologies.abelianComparisonAdjunction`: the change-of-topology inverse image
  is left adjoint to the change-of-topology direct image.
* `Stacks.ComparingTopologies.higherDirectImageComparison`: the canonical degree-`i` comparison
  `ε_{X,*} ⋙ R^i f_{τ',*} ⟶ R^i f_{τ,*} ⋙ ε_{Y,*}`.

## Main results

* `Stacks.Cohomology.Localization.overPushforward_preservesInjectiveObjects` and
  `Stacks.Cohomology.Localization.overPullback_preservesInjectiveObjects`: both the direct and
  the inverse image between localized sites preserve injective objects.
* `Stacks.ComparingTopologies.abelianComparisonPushforward_preservesInjectiveObjects`: the
  change-of-topology direct image preserves injective objects.
* `Stacks.ComparingTopologies.abelianComparisonPushforward_square`: the square of topoi of
  Stacks 0EZ2 on abelian sheaves, as a strict identity of functors.
* `Stacks.ComparingTopologies.isIso_abelianComparisonAdjunction_unit_of_weakSerre`: the unit
  `ℱ ⟶ ε_{X,*} ε_X^{-1} ℱ` is invertible for `ℱ` in `𝒜'_X`.

## References

* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
* [Stacks Project, Tag 0EZ2](https://stacks.math.columbia.edu/tag/0EZ2)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- Inverse image between localized sites is left exact. -/
instance overPullback_preservesFiniteLimits (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteLimits (overPullback J f) := by
  have adj : (Over.map f).sheafPullback Ab.{max u v} (J.over X) (J.over Y) ⊣
      overPullback J f :=
    (Over.map f).sheafAdjunctionContinuous Ab.{max u v} (J.over X) (J.over Y)
  exact (adj.rightAdjoint_preservesLimits.{max u v, max u v}).preservesFiniteLimits

/-- Inverse image between localized sites is right exact. -/
instance overPullback_preservesFiniteColimits (J : GrothendieckTopology C) {X Y : C}
    (f : X ⟶ Y) : PreservesFiniteColimits (overPullback J f) := by
  have adj : overPullback J f ⊣ overPushforward J f :=
    (Over.map f).sheafAdjunctionCocontinuous Ab.{max u v} (J.over X) (J.over Y)
  exact (adj.leftAdjoint_preservesColimits.{max u v, max u v}).preservesFiniteColimits

/-- Inverse image between localized sites preserves monomorphisms. -/
instance overPullback_preservesMonomorphisms (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) :
    (overPullback J f).PreservesMonomorphisms :=
  inferInstance

/-- Direct image between localized sites preserves injective objects. -/
instance overPushforward_preservesInjectiveObjects (J : GrothendieckTopology C) {X Y : C}
    (f : X ⟶ Y) : (overPushforward J f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.map f).sheafAdjunctionCocontinuous Ab.{max u v} (J.over X) (J.over Y))

/-- Inverse image between localized sites preserves injective objects. -/
@[sga "4 V 2.2" "special case"]
instance overPullback_preservesInjectiveObjects (J : GrothendieckTopology C) {X Y : C}
    (f : X ⟶ Y) [∀ U : C, HasSheafify (J.over U) Ab.{max u v}] :
    (overPullback J f).PreservesInjectiveObjects := by
  have : PreservesFiniteLimits
      ((Over.map f).sheafPullback Ab.{max u v} (J.over X) (J.over Y)) :=
    overMapSheafPullback_preservesFiniteLimits J f
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.map f).sheafAdjunctionContinuous Ab.{max u v} (J.over X) (J.over Y))

end Stacks.Cohomology.Localization

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- **Change of topology is an adjunction on abelian sheaves.** Sheafification for the finer
localized topology is left adjoint to the change-of-topology direct image. -/
def abelianComparisonAdjunction (K K' : Precoverage C) (h : K' ≤ K) (X : C) :
    abelianComparisonPullback K K' X ⊣ abelianComparisonPushforward K K' h X :=
  (sheafificationAdjunction (K.toGrothendieck.over X) Ab.{max u v}).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (sheafToPresheaf (K'.toGrothendieck.over X) Ab.{max u v}))
    (Functor.FullyFaithful.ofFullyFaithful (𝟭 (Sheaf (K.toGrothendieck.over X) Ab.{max u v})))
    (Iso.refl _) (Iso.refl _)

/-- The change-of-topology direct image is left exact. -/
instance abelianComparisonPushforward_preservesFiniteLimits (K K' : Precoverage C) (h : K' ≤ K)
    (X : C) : PreservesFiniteLimits (abelianComparisonPushforward K K' h X) :=
  ((abelianComparisonAdjunction K K' h X).rightAdjoint_preservesLimits.{u, u}).preservesFiniteLimits

/-- The change-of-topology inverse image is left exact. -/
@[sga "4 III 1.7" "partial"]
instance abelianComparisonPullback_preservesFiniteLimits (K K' : Precoverage C) (X : C) :
    PreservesFiniteLimits (abelianComparisonPullback K K' X) := by
  dsimp [abelianComparisonPullback]
  exact Limits.comp_preservesFiniteLimits _ _

/-- The change-of-topology inverse image is right exact. -/
instance abelianComparisonPullback_preservesFiniteColimits (S : CohomologyComparison C) (X : C) :
    PreservesFiniteColimits (abelianComparisonPullback S.fineCoverage S.coarseCoverage X) := by
  have := (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
    S.coarse_le_fine X).isLeftAdjoint
  infer_instance

/-- The change-of-topology inverse image preserves monomorphisms. -/
instance abelianComparisonPullback_preservesMonomorphisms (K K' : Precoverage C) (X : C) :
    (abelianComparisonPullback K K' X).PreservesMonomorphisms :=
  inferInstance

/-- The change-of-topology direct image is full. -/
instance abelianComparisonPushforward_full (K K' : Precoverage C) (h : K' ≤ K) (X : C) :
    (abelianComparisonPushforward K K' h X).Full := by
  dsimp [abelianComparisonPushforward]
  infer_instance

/-- The change-of-topology direct image is faithful. -/
instance abelianComparisonPushforward_faithful (K K' : Precoverage C) (h : K' ≤ K) (X : C) :
    (abelianComparisonPushforward K K' h X).Faithful := by
  dsimp [abelianComparisonPushforward]
  infer_instance

/-- The change-of-topology inverse image is additive. -/
instance abelianComparisonPullback_additive (S : CohomologyComparison C) (X : C) :
    (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).Additive :=
  (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
    S.coarse_le_fine X).left_adjoint_additive

/-- **The sheaf-condition assumption of Stacks 0EZ3, in adjunction form.** For an abelian sheaf
`F` of the weak Serre class `𝒜'_X` on the coarser localized site, the unit
`F ⟶ ε_{X,*} ε_X^{-1} F` of the change-of-topology adjunction is an isomorphism. -/
theorem isIso_abelianComparisonAdjunction_unit_of_weakSerre (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}) (hF : S.weakSerre X F) :
    IsIso ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).unit.app F) :=
  (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
    S.coarse_le_fine X).isIso_unit_app_of_iso
      (show F ≅ (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).obj ⟨F.obj, S.weakSerre_isSheaf_fine X F hF⟩ from Iso.refl _)

/-- The change-of-topology direct image preserves injective objects. -/
instance abelianComparisonPushforward_preservesInjectiveObjects (K K' : Precoverage C)
    (h : K' ≤ K) (X : C) :
    (abelianComparisonPushforward K K' h X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (abelianComparisonAdjunction K K' h X)

/-- **The square of topoi of Stacks 0EZ2, on abelian sheaves over the localized sites.**
Change-of-topology direct image followed by direct image along `f` for the coarser topology is
direct image along `f` for the finer topology followed by change-of-topology direct image, as
one and the same functor. -/
theorem abelianComparisonPushforward_square (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) :
    abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X ⋙
        overPushforward S.coarseCoverage.toGrothendieck f =
      overPushforward S.fineCoverage.toGrothendieck f ⋙
        abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine Y :=
  rfl

/-- **The comparison transformation.** The canonical degree-`i` map from the coarse
higher direct image of the change-of-topology direct image to the change-of-topology direct
image of the fine higher direct image,

`R^i f_{τ',*} ε_{X,*} ℱ ⟶ ε_{Y,*} R^i f_{τ,*} ℱ`,

natural in the abelian sheaf `ℱ` on the finer localized site over `X`.

It is the composite of the two edge morphisms of the Grothendieck spectral sequence of the
square of topoi `abelianComparisonPushforward_square`: the edge `E₂^{i,0} ⟶ H^i` for the pair
`(ε_{X,*}, f_{τ',*})`, followed by the edge `H^i ⟶ E₂^{0,i}` for the pair `(f_{τ,*}, ε_{Y,*})`. -/
@[stacks 0EZA "canonical comparison transformation"]
def higherDirectImageComparison (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y) (i : ℕ) :
    abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X ⋙
        (overPushforward S.coarseCoverage.toGrothendieck f).rightDerived i ⟶
      (overPushforward S.fineCoverage.toGrothendieck f).rightDerived i ⋙
        abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine Y :=
  Stacks.Cohomology.RightDerivedEdge.edge
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X)
      (overPushforward S.coarseCoverage.toGrothendieck f) i ≫
    Stacks.Cohomology.RightDerivedCoEdge.secondEdge
      (overPushforward S.fineCoverage.toGrothendieck f)
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine Y) i

end Stacks.ComparingTopologies

end
