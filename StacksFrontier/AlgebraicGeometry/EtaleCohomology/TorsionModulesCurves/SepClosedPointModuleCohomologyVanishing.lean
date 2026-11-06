module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpen
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Positive-degree étale cohomology of `Λ`-modules vanishes over a separably closed field

Let `Λ` be a ring, let `Ω` be a separably closed field, and let `A` be a sheaf of `Λ`-modules on
the small étale site of `Spec Ω`. This file shows `H^{n+1}_étale(Spec Ω, A) = 0` for every `n`.

The identity lift of the canonical point of `Spec Ω` is an initial object among the étale
neighbourhoods of that point, so the stalk there is evaluation at the final object of the site,
that is global sections. This is the argument of `Stacks.EtaleCohomology.sheafFiberIdIsoGamma`,
which is stated for sheaves of sets, carried to coefficients in `ModuleCat Λ` through
`CategoryTheory.GrothendieckTopology.Point.ulift`, which moves the fibre of the point to the
universe at which `ModuleCat Λ` lives. The stalk functor is exact — it preserves finite limits
because filtered colimits of modules are exact, and finite colimits because it is a left adjoint
— so global sections on `Spec Ω` is exact, and an exact functor has no higher right derived
functors (`CategoryTheory.Functor.isZero_rightDerived_of_exact`).

## Main definitions

* `Stacks.EtaleCohomology.TorsionModules.sheafFiberIdIsoGammaModule` — the stalk of a sheaf of
  `Λ`-modules at the canonical point of `Spec Ω` is its module of global sections.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.preservesFiniteLimits_moduleSheafΓ_sepClosedField` and
  `Stacks.EtaleCohomology.TorsionModules.preservesFiniteColimits_moduleSheafΓ_sepClosedField` —
  global sections of sheaves of `Λ`-modules on the small étale site of `Spec Ω` is exact.
* `Stacks.EtaleCohomology.TorsionModules.isZero_moduleEtaleCohomology_succ_sepClosedField` —
  `H^{n+1}_étale(Spec Ω, A) = 0`.

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology

universe u r

namespace Stacks.EtaleCohomology.TorsionModules

variable (Λ : Type r) [CommRing Λ] (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- **The identity lift of the canonical point, raised to the module-coefficient universe, is
still an initial étale neighbourhood of that point.** This is
`Stacks.EtaleCohomology.isInitialPointSmallEtaleIdElement` on `ULift`-wrapped data. -/
def isInitial_ulift_pointSmallEtaleIdElement :
    IsInitial (show (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r})).fiber.Elements
      from (Functor.Elements.mk (obj := Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (ULift.up (pointSmallEtaleIdElement Ω)))) := by
  apply IsInitial.ofUniqueHom
    (fun U : (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r})).fiber.Elements ↦
      Functor.Elements.homMk
      (MorphismProperty.Over.homMk U.val.down.left (CategoryTheory.Over.w U.val.down)) ?_)
    (fun U morphism ↦ ?_)
  · apply ULift.ext
    apply CategoryTheory.Over.OverMorphism.ext
    exact Category.id_comp U.val.down.left
  · apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    have h : 𝟙 (Spec (.of Ω)) ≫ morphism.hom.left = U.val.down.left :=
      congrArg (fun b ↦ b.left) (congrArg ULift.down morphism.map_val)
    exact (Category.id_comp morphism.hom.left).symm.trans h

/-- The germ at the identity lift of the canonical point, raised to the module-coefficient
universe, of a section of a presheaf of `Λ`-modules over the final object. -/
def sectionsToPresheafFiberIdModule :
    (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ⟶
      (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r})).presheafFiber :=
  (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r})).toPresheafFiberNatTrans
    (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) (ULift.up (pointSmallEtaleIdElement Ω))

/-- **The fibre of a presheaf of `Λ`-modules at the canonical point of `Spec Ω` is evaluation at
the final object of the site**: the module-coefficient analogue of
`Stacks.EtaleCohomology.presheafFiberIdIsoSections`. -/
def presheafFiberIdIsoSectionsModule :
    (evaluation (Spec (.of Ω)).Etaleᵒᵖ (ModuleCat.{max (u + 1) r} Λ)).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≅
      (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r})).presheafFiber := by
  letI : ∀ P, IsIso ((sectionsToPresheafFiberIdModule Λ Ω).app P) := fun P ↦
    ((((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r})).isColimitPresheafFiberCocone
        P).isIso_ι_app_of_isTerminal
      (op (Functor.Elements.mk (obj := Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (ULift.up (pointSmallEtaleIdElement Ω))))
      (isInitial_ulift_pointSmallEtaleIdElement Ω).op
  letI := NatIso.isIso_of_isIso_app (sectionsToPresheafFiberIdModule Λ Ω)
  exact asIso (sectionsToPresheafFiberIdModule Λ Ω)

/-- **The stalk of a sheaf of `Λ`-modules at the canonical point of `Spec Ω` is its module of
global sections.** The module-coefficient analogue of
`Stacks.EtaleCohomology.sheafFiberIdIsoGamma`. -/
def sheafFiberIdIsoGammaModule :
    (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) r})).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ) ≅
      Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{max (u + 1) r} Λ) :=
  (Functor.isoWhiskerLeft
      (sheafToPresheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{max (u + 1) r} Λ))
      (presheafFiberIdIsoSectionsModule Λ Ω)).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{max (u + 1) r} Λ)
      (isTerminalEtaleMkId (Spec (.of Ω)))).symm

/-- **Global sections of sheaves of `Λ`-modules on the small étale site of `Spec Ω` preserves
finite limits**, `Ω` a separably closed field: it is isomorphic to the stalk at the canonical
point, which is left exact because filtered colimits of `Λ`-modules are exact. -/
instance preservesFiniteLimits_moduleSheafΓ_sepClosedField :
    PreservesFiniteLimits
      (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{max (u + 1) r} Λ)) :=
  preservesFiniteLimits_of_natIso (sheafFiberIdIsoGammaModule Λ Ω)

/-- **Global sections of sheaves of `Λ`-modules on the small étale site of `Spec Ω` preserves
finite colimits**, `Ω` a separably closed field: it is isomorphic to the stalk at the canonical
point, which is right exact, being a left adjoint. -/
instance preservesFiniteColimits_moduleSheafΓ_sepClosedField :
    PreservesFiniteColimits
      (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{max (u + 1) r} Λ)) :=
  preservesFiniteColimits_of_natIso (sheafFiberIdIsoGammaModule Λ Ω)

/-- **Positive-degree étale cohomology of a sheaf of `Λ`-modules vanishes over a separably
closed field.** No finiteness, torsion or constructibility hypothesis is needed on the sheaf:
global sections on `Spec Ω` is exact, so its right derived functors vanish in positive degree at
every object. -/
@[sga "4 VIII 2.4" "more general"]
theorem isZero_moduleEtaleCohomology_succ_sepClosedField
    (A : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{max (u + 1) r} Λ)) (n : ℕ) :
    IsZero ((moduleEtaleCohomology.{u, r, r} Λ (Spec (.of Ω)) (n + 1)).obj A) :=
  Functor.isZero_rightDerived_of_exact _ A (n + 1) n.succ_pos

end Stacks.EtaleCohomology.TorsionModules

end
