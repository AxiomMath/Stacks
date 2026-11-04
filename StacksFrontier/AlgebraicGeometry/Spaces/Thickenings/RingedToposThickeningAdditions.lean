module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickening
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafTransport
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickenings

/-!
# Additions to `StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickening`

Declarations extending
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/RingedToposThickening.lean`,
kept in a separate module so that the base file is unchanged.
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z Z' : AlgebraicSpaces B S hS}

/-- **The direct image of the morphism of small étale topoi of a surjective closed immersion is
an equivalence.** For a closed immersion `i : Z ⟶ Z'` of algebraic spaces over `S` which is
surjective, the direct image of the morphism of small étale topoi of Stacks 03G8 is an
equivalence of the topoi of sheaves of sets.

For a representable morphism that direct image is base change of étale scheme charts
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable`), and base change along a
surjective closed immersion is a dense subsite inclusion
(`AlgebraicGeometry.Space.smallBaseChange_isDenseSubsite_of_surjective`), so restriction along
it is an equivalence on sheaves. The shapes of the right Kan extension computing the inverse
are essentially `u`-small, which is what supplies the limits at `Type u`; see the
implementation notes. -/
theorem isEquivalence_pushforward_smallEtaleRingedToposHom (i : Z ⟶ Z')
    (hci : IsClosedImmersion B S hS i.hom)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) :
    (smallEtaleRingedToposHom B S hS i).toToposHom.pushforward.IsEquivalence := by
  let _ := (smallBaseChange_isMorphismOfSites B S hS i hci.rep).toIsContinuous
  let _ := smallBaseChange_isDenseSubsite_of_surjective B S hS i hci hsurj
  let _ : ∀ Y : (SmallEtale B S hS Z.1)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow Y (smallBaseChange B S hS i hci.rep).op) (Type u) :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  exact Functor.isEquivalence_of_iso
    (smallEtaleRingedToposHom_representable B S hS i hci.rep).symm

end AlgebraicGeometry.Space

end

