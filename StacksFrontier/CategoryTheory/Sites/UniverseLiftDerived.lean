module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportEtaleZariski
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftSeparator

/-!
# The universe lift of abelian sheaves commutes with right derived functors

Let `L : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf J AddCommGrpCat.{max t s}` be the universe lift of
abelian sheaves on a site. It is exact and, by
`Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator`, it
carries injective abelian sheaves to injective abelian sheaves. So for an additive functor `G`
out of abelian sheaves in the smaller universe and its counterpart `G'` in the larger universe,
related by `G ⋙ L' ≅ L ⋙ G'` for an exact `L'` on the targets, the right derived functors are
related in the same way: `Rᵠ G ⋙ L' ≅ L ⋙ Rᵠ G'`. Computing `Rᵠ G'` on the lift of an injective
resolution, which is an injective resolution, proves it.

The functors for which this is recorded are those built from the sites alone: direct image
along a continuous functor of sites, which on the small étale site is `j_*` and restriction to
an object `U`, and the global sections vanishing on a subobject, which on the small étale site
is `Γ_Z` for a closed subset `Z`.

## Main results

* `CategoryTheory.Functor.rightDerivedIsoOfSquare` — right derived functors along a square whose
  source side is exact and preserves injective objects and whose target side is exact.
* `Stacks.Sheaves.UniverseLift.sheafPushforwardContinuousULiftIso` — direct image commutes with
  the universe lift.
* `Stacks.Sheaves.UniverseLift.rightDerivedSheafPushforwardContinuousULiftIso` — the higher
  direct images commute with the universe lift.
* `Stacks.Sheaves.UniverseLift.rightDerivedSectionsVanishingOutsideULiftIso` — cohomology with
  support commutes with the universe lift.
* `Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_smallEtale` — on the
  small étale site of a scheme the universe lift from `u` to `u + 1` preserves injectives.

## Implementation notes

The square is stated with the lift on the *target* of `G` as an arbitrary exact functor `L'`,
so that a functor to abelian groups such as `Γ_Z` and a functor between sheaf categories such
as `j_*` are covered by one statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe z s t v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Functor

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasInjectiveResolutions A] [HasInjectiveResolutions A']
  (L : A ⥤ A') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L.PreservesInjectiveObjects]
  (G : A ⥤ B) [G.Additive] (G' : A' ⥤ B') [G'.Additive]
  (L' : B ⥤ B') [L'.Additive] [L'.PreservesHomology]

/-- **Right derived functors along a square.** For an exact functor `L : A ⥤ A'` preserving
injective objects, an exact functor `L' : B ⥤ B'` and additive functors `G : A ⥤ B`,
`G' : A' ⥤ B'` with `G ⋙ L' ≅ L ⋙ G'`, the right derived functors satisfy
`Rᵠ G ⋙ L' ≅ L ⋙ Rᵠ G'`. -/
def rightDerivedIsoOfSquare (sq : G ⋙ L' ≅ L ⋙ G') (q : ℕ) :
    G.rightDerived q ⋙ L' ≅ L ⋙ G'.rightDerived q :=
  (G.rightDerivedCompIso L' q).symm ≪≫ rightDerivedIsoOfNatIso sq q ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G' q

end CategoryTheory.Functor

namespace Stacks.Sheaves.UniverseLift

section Exactness

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- The universe lift of abelian sheaves is additive. -/
instance uliftSheafFunctor_additive : (uliftSheafFunctor.{s, t} J).Additive where
  map_add {_ _ _ _} := Sheaf.hom_ext (by ext; rfl)

variable [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]

/-- The universe lift of abelian sheaves is left exact: it is so on presheaves, where it acts
objectwise, and the forgetful functor from sheaves reflects the limits it preserves. -/
instance uliftSheafFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (uliftSheafFunctor.{s, t} J) := by
  have : PreservesFiniteLimits
      (uliftSheafFunctor.{s, t} J ⋙ sheafToPresheaf J AddCommGrpCat.{max t s}) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf J AddCommGrpCat.{t} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{s, t}))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J _)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]

/-- The universe lift of abelian sheaves is right exact, preserving all colimits of size `t`. -/
instance uliftSheafFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (uliftSheafFunctor.{s, t} J) :=
  have := sheafCompose_uliftFunctor_preservesColimits.{u₁, v₁, t, s} (J := J)
  PreservesColimitsOfSize.preservesFiniteColimits _

end Exactness

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D) [F.IsContinuous J K]

/-- **Direct image along a continuous functor of sites commutes with the universe lift**: both
composites send an abelian sheaf `𝒢` to `U ↦ ULift (𝒢 (F U))`. -/
def sheafPushforwardContinuousULiftIso :
    F.sheafPushforwardContinuous AddCommGrpCat.{t} J K ⋙ uliftSheafFunctor.{s, t} J ≅
      uliftSheafFunctor.{s, t} K ⋙ F.sheafPushforwardContinuous AddCommGrpCat.{max t s} J K :=
  Iso.refl _

variable [HasSheafify K AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{max t s}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{t}] [K.WEqualsLocallyBijective AddCommGrpCat.{max t s}]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{t})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{max t s})]
  [(uliftSheafFunctor.{s, t} K).PreservesInjectiveObjects]

/-- **The higher direct images along a continuous functor of sites commute with the universe
lift**: `Rᵠ F_*` of the lift of an abelian sheaf is the lift of `Rᵠ F_*`. -/
def rightDerivedSheafPushforwardContinuousULiftIso (q : ℕ) :
    (F.sheafPushforwardContinuous AddCommGrpCat.{t} J K).rightDerived q ⋙
        uliftSheafFunctor.{s, t} J ≅
      uliftSheafFunctor.{s, t} K ⋙
        (F.sheafPushforwardContinuous AddCommGrpCat.{max t s} J K).rightDerived q :=
  have : (uliftSheafFunctor.{s, t} J).PreservesHomology := Functor.preservesHomologyOfExact _
  Functor.rightDerivedIsoOfSquare (uliftSheafFunctor.{s, t} K)
    (F.sheafPushforwardContinuous AddCommGrpCat.{t} J K)
    (F.sheafPushforwardContinuous AddCommGrpCat.{max t s} J K) (uliftSheafFunctor.{s, t} J)
    (sheafPushforwardContinuousULiftIso J K F) q

end Pushforward

section SectionsVanishingOutside

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {V T : C} (f : V ⟶ T)

/-- The sections over `T` of the lift of an abelian sheaf are the lift of its sections over
`T`, naturally in the sheaf. -/
def sheafSectionsULiftIso (T : C) :
    (sheafSections J AddCommGrpCat.{t}).obj (op T) ⋙ AddCommGrpCat.uliftFunctor.{s, t} ≅
      uliftSheafFunctor.{s, t} J ⋙ (sheafSections J AddCommGrpCat.{max t s}).obj (op T) :=
  Iso.refl _

/-- **Sections vanishing outside a subobject commute with the universe lift**: lifting the
universe preserves the kernel of the restriction map. -/
def sectionsVanishingOutsideULiftIso :
    Stacks.Sites.SupportedSections.sectionsVanishingOutside.{t} J f ⋙
        AddCommGrpCat.uliftFunctor.{s, t} ≅
      uliftSheafFunctor.{s, t} J ⋙
        Stacks.Sites.SupportedSections.sectionsVanishingOutside.{max t s} J f :=
  (PreservesKernel.iso ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{s, t})
      (Stacks.Sites.SupportedSections.sectionsRestriction.{t} J f)) ≪≫
    (PreservesKernel.iso ((Functor.whiskeringLeft _ _ _).obj (uliftSheafFunctor.{s, t} J))
      (Stacks.Sites.SupportedSections.sectionsRestriction.{max t s} J f)).symm

variable [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{t})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max t s})]
  [(uliftSheafFunctor.{s, t} J).PreservesInjectiveObjects]

/-- **Cohomology with support commutes with the universe lift**: the derived functors of the
sections vanishing outside a subobject, at the lift of an abelian sheaf, are the lifts of
those at the sheaf. -/
def rightDerivedSectionsVanishingOutsideULiftIso (q : ℕ) :
    (Stacks.Sites.SupportedSections.sectionsVanishingOutside.{t} J f).rightDerived q ⋙
        AddCommGrpCat.uliftFunctor.{s, t} ≅
      uliftSheafFunctor.{s, t} J ⋙
        (Stacks.Sites.SupportedSections.sectionsVanishingOutside.{max t s} J f).rightDerived q :=
  have : AddCommGrpCat.uliftFunctor.{s, t}.PreservesHomology := Functor.preservesHomologyOfExact _
  Functor.rightDerivedIsoOfSquare (uliftSheafFunctor.{s, t} J)
    (Stacks.Sites.SupportedSections.sectionsVanishingOutside.{t} J f)
    (Stacks.Sites.SupportedSections.sectionsVanishingOutside.{max t s} J f)
    AddCommGrpCat.uliftFunctor.{s, t} (sectionsVanishingOutsideULiftIso J f) q

end SectionsVanishingOutside

section SmallEtale

variable (X : AlgebraicGeometry.Scheme.{u})

/-- **On the small étale site of a scheme, the universe lift of abelian sheaves from `u` to
`u + 1` preserves injective objects.** -/
instance preservesInjectiveObjects_uliftSheafFunctor_smallEtale :
    (uliftSheafFunctor.{u + 1, u} X.smallEtaleTopology).PreservesInjectiveObjects :=
  have : HasSeparator (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.hasSeparator.{u} _ _ _
      (AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X
        AddCommGrpCat.{u})
  have := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{u + 1, u + 1, u} _

end SmallEtale

end Stacks.Sheaves.UniverseLift
