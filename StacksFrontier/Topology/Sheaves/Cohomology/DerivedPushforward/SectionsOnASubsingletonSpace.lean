module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOnAPoint
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections on a ringed space with at most one point

Let `(Z, 𝒪_Z)` be a ringed space whose underlying space has at most one point. Such a space is
indiscrete and its only opens are `⊥` and `⊤`, so the sheaf condition for a presheaf of
`𝒪_Z`-modules is exactly that its sections on `⊥` vanish — which is automatic, the structure
sheaf having the zero ring there. Forgetting the sheaf condition is therefore an equivalence,
sections over an open are computed in presheaves of modules, and in particular

`Γ(U, -) : Mod(𝒪_Z) ⥤ Mod(Γ(U, 𝒪_Z))`

is exact. Combined with the second half of this file — that derived sections agree with sections
whenever sections are exact — this gives `RΓ(U, -) ≅ Γ(U, -)` on any such space.

`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedSectionsIso` is this statement for the
one-point ringed space `({*}, R)` of `Stacks.AssociatedSheaf.coefficientPoint`, whose structure
sheaf is a skyscraper by construction. The point of this file is to have it for a space that is
*given* as having one point rather than built that way — in particular for the closed subset `{x}`
of a ringed space with its restricted structure sheaf, which is not of the form
`coefficientPoint R`.

## Main definitions

* `Stacks.Cohomology.SubsingletonSections.subsingletonForgetEquivalence`: on a space with at most
  one point, forgetting the sheaf condition is an equivalence between sheaves and presheaves of
  `𝒪_Z`-modules; its unit and counit are identities.
* `Stacks.Cohomology.SubsingletonSections.derivedSectionsOverOpenIso`: `RΓ(U, -) ≅ Γ(U, -)` for
  an open `U` of a ringed space on which sections over `U` are exact.
* `Stacks.Cohomology.SubsingletonSections.derivedPreimageSectionsIso`: the same for sections over
  the inverse image of an open along a morphism of ringed spaces, with the scalars restricted
  along that morphism that the Leray isomorphism of Tag 0D5W produces.

## Main results

* `Stacks.Cohomology.SubsingletonSections.isSheaf_of_presheafOfModules_of_subsingleton`: every
  presheaf of `𝒪_Z`-modules on such a space is a sheaf.
* `Stacks.Cohomology.SubsingletonSections.preservesFiniteColimits_sectionsOverOpen`: sections
  over an open of such a space preserve finite colimits, hence are exact.

## Implementation notes

The sheafhood argument is the one of
`Stacks.AssociatedSheaf.isSheaf_of_presheafOfModules_coefficientPoint` with the two inputs
replaced by their general forms: the topology of a space with at most one point is `⊤` by
`Subsingleton.elim`, which is what `TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete` asks
(the `PUnit` specialisation `isSheaf_on_punit_of_isTerminal` used there is strictly weaker); and
the sections of the structure sheaf on `⊥` form the zero ring because a sheaf's sections on `⊥`
are terminal (`TopCat.Sheaf.isTerminalOfEmpty`) and a terminal commutative ring is trivial
(`CommRingCat.subsingleton_of_isTerminal`) — rather than because the structure sheaf is a
skyscraper, which only `coefficientPoint` is.

Exactness of sections is then formal: `SheafOfModules.evaluation` *is*
`SheafOfModules.forget ⋙ PresheafOfModules.evaluation` (by `rfl`), the first factor is half of an
equivalence and the second preserves colimits because colimits of presheaves of modules are
computed open by open. Left exactness needs none of this and holds on any ringed space.

The derived statement is the recipe of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedSectionsComparison` with exactness
carried as instance arguments instead of being supplied by the one-point equivalence: an exact
functor's termwise extension to derived categories is already a right derived functor
(`Stacks.DerivedFunctor.HigherDerivedOfExact.everywhere_defined`), so the comparison out of
`RΓ(U, -)` that the universal property produces is invertible.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedSectionsLeray

universe v u

namespace Stacks.Cohomology.SubsingletonSections

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction of scalars is exact -/

/-- **Restriction of scalars along a homomorphism of rings preserves finite limits.** Mathlib has
this for commutative rings only, through the exactness criterion of
`ModuleCat.restrictScalars_map_exact`; over arbitrary rings it follows from
`ModuleCat.preservesLimit_restrictScalars`, the underlying abelian group being unchanged. -/
@[sga "4 IV 11.1.6" "special case"]
public instance preservesFiniteLimits_restrictScalars {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) := by
  constructor; intro J _ _; constructor; intro K; infer_instance

/-- **Restriction of scalars along a homomorphism of rings preserves finite colimits**, by
`ModuleCat.preservesColimit_restrictScalars`; see
`Stacks.Cohomology.SubsingletonSections.preservesFiniteLimits_restrictScalars` for why this is
stated over arbitrary rings. -/
@[sga "4 IV 11.1.6" "special case"]
public instance preservesFiniteColimits_restrictScalars {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) : PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  constructor; intro J _ _; constructor; intro K; infer_instance

/-! ### Presheaves of modules on a space with at most one point are sheaves -/

section Sheafhood

variable (Z : RingedSpace.{u, u}) [Subsingleton Z.carrier]

omit [Subsingleton Z.carrier] in
/-- **The structure sheaf of a ringed space has the zero ring on the empty open.** Sections of a
sheaf on `⊥` are a terminal object, and a terminal commutative ring is trivial. -/
public theorem subsingleton_structureSheafRing_bot :
    Subsingleton ((structureSheafRing Z).obj.obj (op (⊥ : Opens Z.carrier))) :=
  CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf)

/-- **A presheaf of modules on a ringed space with at most one point is a sheaf.** Its sections on
`⊥` are zero, the scalars there being the zero ring, and on an indiscrete space that is the whole
of the sheaf condition. -/
public theorem isSheaf_of_presheafOfModules_of_subsingleton
    (N : PresheafOfModules.{u} (structureSheafRing Z).obj) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Z.carrier) N.presheaf := by
  have hring := subsingleton_structureSheafRing_bot Z
  have h : Subsingleton (N.obj (op (⊥ : Opens Z.carrier))) :=
    subsingleton_of_subsingleton_ring
      (S := (structureSheafRing Z).obj.obj (op (⊥ : Opens Z.carrier)))
  exact TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete (Subsingleton.elim _ _) N.presheaf
    (@AddCommGrpCat.isZero_of_subsingleton (N.presheaf.obj (op ⊥)) h).isTerminal

/-- A presheaf of modules on a ringed space with at most one point, regarded as a sheaf. -/
public def subsingletonSheafOfModules :
    PresheafOfModules.{u} (structureSheafRing Z).obj ⥤
      SheafOfModules.{u} (structureSheafRing Z) where
  obj N := ⟨N, isSheaf_of_presheafOfModules_of_subsingleton Z N⟩
  map f := ⟨f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **On a ringed space with at most one point, forgetting the sheaf condition is an
equivalence** between sheaves of `𝒪_Z`-modules and presheaves of `𝒪_Z`-modules; its unit and
counit are identities. -/
public def subsingletonForgetEquivalence :
    SheafOfModules.{u} (structureSheafRing Z) ≌
      PresheafOfModules.{u} (structureSheafRing Z).obj where
  functor := SheafOfModules.forget _
  inverse := subsingletonSheafOfModules Z
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- **Sections over an open of a ringed space with at most one point preserve finite
colimits.** Sections are the composite of forgetting the sheaf condition, an equivalence here,
with evaluation on presheaves of modules, which is computed open by open. -/
public instance preservesFiniteColimits_sectionsOverOpen (U : Opens Z.carrier) :
    PreservesFiniteColimits (sectionsOverOpen Z U) := by
  have _ : (subsingletonForgetEquivalence Z).functor.IsEquivalence :=
    (subsingletonForgetEquivalence Z).isEquivalence_functor
  change PreservesFiniteColimits
    ((subsingletonForgetEquivalence Z).functor ⋙ PresheafOfModules.evaluation _ (op U))
  infer_instance

end Sheafhood

/-! ### Derived sections are sections when sections are exact -/

section Derived

variable (Z : RingedSpace.{u, u}) (U : Opens Z.carrier)
  [PreservesFiniteColimits (sectionsOverOpen Z U)]

/-- The comparison `RΓ(U, -) ⟶ Γ(U, -)` from derived sections over `U` to the functor induced
termwise by sections, given by the universal property of the right derived functor. -/
public def derivedSectionsOverOpenComparison :
    derivedSectionsOverOpen Z U ⟶ (sectionsOverOpen Z U).mapDerivedCategory :=
  (derivedSectionsOverOpen Z U).rightDerivedDesc
    (derivedSectionsOverOpenUnit Z U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
      (ComplexShape.up ℤ)) _
    (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical (sectionsOverOpen Z U))

/-- **Derived sections over an open on which sections are exact are sections.** An exact functor's
termwise extension to derived categories is already a right derived functor, so the comparison out
of `RΓ(U, -)` is invertible. -/
public instance isIso_derivedSectionsOverOpenComparison :
    IsIso (derivedSectionsOverOpenComparison Z U) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      (derivedSectionsOverOpenUnit Z U) _ _
      (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
        (sectionsOverOpen Z U))).1
    (Stacks.DerivedFunctor.HigherDerivedOfExact.everywhere_defined
      (sectionsOverOpen Z U)).2

/-- The natural isomorphism `RΓ(U, -) ≅ Γ(U, -)` on an open whose sections are exact. -/
public def derivedSectionsOverOpenIso :
    derivedSectionsOverOpen Z U ≅ (sectionsOverOpen Z U).mapDerivedCategory :=
  asIso (derivedSectionsOverOpenComparison Z U)

end Derived

/-! ### The same for sections over an inverse image -/

section DerivedPreimage

variable {Z Y : RingedSpace.{u, u}} (f : Z ⟶ Y) (V : Opens Y.carrier)
  [PreservesFiniteLimits (preimageSections f V)]
  [PreservesFiniteColimits (preimageSections f V)]

/-- The comparison `RΓ(f⁻¹ V, -) ⟶ Γ(f⁻¹ V, -)`, with scalars restricted along `f^♯`, from
derived sections over the inverse image to the functor induced termwise by sections. -/
public def derivedPreimageSectionsComparison :
    derivedPreimageSections f V ⟶ (preimageSections f V).mapDerivedCategory :=
  (derivedPreimageSections f V).rightDerivedDesc
    (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z))
      (ComplexShape.up ℤ)) _
    (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical (preimageSections f V))

/-- **Derived sections over an inverse image on which sections are exact are sections.** -/
public instance isIso_derivedPreimageSectionsComparison :
    IsIso (derivedPreimageSectionsComparison f V) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      (derivedPreimageSectionsUnit f V) _ _
      (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
        (preimageSections f V))).1
    (Stacks.DerivedFunctor.HigherDerivedOfExact.everywhere_defined
      (preimageSections f V)).2

/-- The natural isomorphism `RΓ(f⁻¹ V, -) ≅ Γ(f⁻¹ V, -)` when those sections are exact. -/
public def derivedPreimageSectionsIso :
    derivedPreimageSections f V ≅ (preimageSections f V).mapDerivedCategory :=
  asIso (derivedPreimageSectionsComparison f V)

end DerivedPreimage

end Stacks.Cohomology.SubsingletonSections

end
