module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCommRingSheafULift
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackULift

/-!
# The inverse image along a morphism of algebraic spaces at the two universes of sets

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of universe `u`. The small
étale sites of `X` and `Y` have their objects in `Type (u + 1)`, and the morphism of small étale
topoi of Stacks 03G2, part (3) is available both for sheaves of sets valued in `Type (u + 1)`,
as `AlgebraicGeometry.Space.smallToposMorphism`, and for sheaves of sets valued in the universe
`u` of the structure rings, as `AlgebraicGeometry.Space.smallToposMorphismTypeU`. The two
inverse images agree after raising the universe:

`ULift (f_small⁻¹ F) ≅ f_small⁻¹ (ULift F)`,

naturally in the sheaf of sets `F` on `Y_étale` valued in `Type u`.

## Main definitions

* `AlgebraicGeometry.Space.smallToposMorphismInverseImageULiftIso`: the comparison, as an
  isomorphism of functors from sheaves of sets valued in `Type u` on `Y_étale` to sheaves of sets
  valued in `Type (u + 1)` on `X_étale`.
* `AlgebraicGeometry.Space.smallEtaleInverseImageRingULiftIso`: the same comparison for sheaves
  of commutative rings, `ULift (f_small⁻¹𝒪) ≅ f_small⁻¹ (ULift 𝒪)`, the universe lift of
  sheaves of commutative rings being `AlgebraicGeometry.SheafOfModules.sheafULift`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.preservesSheafification_uliftFunctor` and
  `AlgebraicGeometry.Space.SpacesEtale.preservesSheafification_uliftFunctor`: raising the
  universe preserves sheafification on the small and on the spaces-étale site.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Raising the universe preserves sheafification on the small étale site of an algebraic space:
on that site the local isomorphisms of presheaves of sets are the locally bijective morphisms in
both universes. -/
instance SmallEtale.preservesSheafification_uliftFunctor (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (SmallEtale.topology B S hS F).PreservesSheafification uliftFunctor.{u + 1, u} :=
  GrothendieckTopology.preservesSheafification_uliftFunctor_of_wEqualsLocallyBijective.{u, u + 1}
    _

/-- Raising the universe preserves sheafification on the spaces-étale site of an algebraic
space, transported from the small étale site along the dense subsite of Stacks 03G1. -/
instance SpacesEtale.preservesSheafification_uliftFunctor (X : AlgebraicSpaces B S hS) :
    (SpacesEtale.topology B S hS X).PreservesSheafification uliftFunctor.{u + 1, u} :=
  haveI := comparisonFunctor_full B S hS X
  haveI := Functor.IsDenseSubsite.isCoverDense (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
  GrothendieckTopology.PreservesSheafification.transport (A := Type u)
    (SpacesEtale.topology B S hS X) (SmallEtale.topology B S hS X.1)
    (comparisonFunctor B S hS X) (Type (u + 1)) uliftFunctor.{u + 1, u}

variable {B S hS}

/-- Restriction along the comparison functor of Stacks 03G1 commutes with raising the universe,
on the nose: both act on the underlying presheaf by composition. -/
noncomputable def comparisonRestrictionULiftIso (X : AlgebraicSpaces B S hS) :
    (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) ⋙
      sheafCompose (SmallEtale.topology B S hS X.1) uliftFunctor.{u + 1, u} ≅
    sheafCompose (SpacesEtale.topology B S hS X) uliftFunctor.{u + 1, u} ⋙
      (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The inverse image of `AlgebraicGeometry.Space.smallToposMorphismTypeU` is the inverse image
along base change of étale charts followed by restriction to the étale charts of `X`: both are
left adjoint to the same direct image. -/
noncomputable def smallToposMorphismTypeU_inverseImageChartIso :
    (smallToposMorphismTypeU B S hS f).inverseImage ≅
      (spacesEtaleChartBaseChange B S hS f).sheafPullback (Type u)
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type u)
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  Adjunction.leftAdjointUniq (smallToposMorphismTypeU B S hS f).adj
    (((spacesEtaleChartBaseChange B S hS f).sheafAdjunctionContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X)).comp
      (smallEtaleToposEquivTypeU B S hS X).toAdjunction)

/-- The inverse image of `AlgebraicGeometry.Space.smallToposMorphism` is the inverse image along
base change of étale charts followed by restriction to the étale charts of `X`: both are left
adjoint to the same direct image. -/
noncomputable def smallToposMorphism_inverseImageChartIso :
    (smallToposMorphism B S hS f).inverseImage ≅
      (spacesEtaleChartBaseChange B S hS f).sheafPullback (Type (u + 1))
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X) ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  Adjunction.leftAdjointUniq (smallToposMorphism B S hS f).adj
    (((spacesEtaleChartBaseChange B S hS f).sheafAdjunctionContinuous (Type (u + 1))
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X)).comp
      (smallEtaleToposEquiv B S hS X).toAdjunction)

/-- **The inverse image along a morphism of algebraic spaces commutes with raising the universe
of sheaves of sets.** For `f : X ⟶ Y`, lifting the universe of `f_small⁻¹F`, computed for
sheaves of sets valued in `Type u`, is `f_small⁻¹` of the lift of `F`, computed for sheaves of
sets valued in `Type (u + 1)`. -/
noncomputable def smallToposMorphismInverseImageULiftIso :
    (smallToposMorphismTypeU B S hS f).inverseImage ⋙
        sheafCompose (SmallEtale.topology B S hS X.1) uliftFunctor.{u + 1, u} ≅
      sheafCompose (SmallEtale.topology B S hS Y.1) uliftFunctor.{u + 1, u} ⋙
        (smallToposMorphism B S hS f).inverseImage :=
  Functor.isoWhiskerRight (smallToposMorphismTypeU_inverseImageChartIso f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (comparisonRestrictionULiftIso X) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPullbackULiftIso.{u, u + 1} (spacesEtaleChartBaseChange B S hS f)
        (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS X)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallToposMorphism_inverseImageChartIso f).symm

open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

/-- The inverse image of sheaves of commutative rings along `f_small` at the universe of the
structure rings, followed by the lift of sections, read as transport along the lift of sheaves
of sets: `ULift (f⁻¹𝒪)` is `f⁻¹𝒪` with its ring operations transported along `ULift`. -/
noncomputable def smallEtaleInverseImageRingULiftIsoAux₁ :
    smallEtaleInverseImageRing B S hS f ⋙
        SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1) ≅
      pullbackCommRingSheafFunctor.{u + 1, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS X.1)
        ((smallToposMorphismTypeU B S hS f).inverseImage ⋙
          sheafCompose (SmallEtale.topology B S hS X.1) uliftFunctor.{u + 1, u}) :=
  Functor.isoWhiskerLeft _
      (pullbackCommRingSheafULiftIso.{u, u, u + 1} (SmallEtale.topology B S hS X.1)).symm ≪≫
    pullbackCommRingSheafIterateIso (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS X.1) (smallToposMorphismTypeU B S hS f).inverseImage
      (sheafCompose (SmallEtale.topology B S hS X.1) uliftFunctor.{u + 1, u})

/-- The lift of sections followed by the inverse image of sheaves of commutative rings along
`f_small` at the universe of the small étale sites, read as transport along the lift of sheaves
of sets followed by the inverse image. -/
noncomputable def smallEtaleInverseImageRingULiftIsoAux₂ :
    pullbackCommRingSheafFunctor.{u + 1, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS X.1)
        (sheafCompose (SmallEtale.topology B S hS Y.1) uliftFunctor.{u + 1, u} ⋙
          (smallToposMorphism B S hS f).inverseImage) ≅
      SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS Y.1) ⋙
        inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS f) :=
  (pullbackCommRingSheafIterateIso (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1)
      (sheafCompose (SmallEtale.topology B S hS Y.1) uliftFunctor.{u + 1, u})
      (smallToposMorphism B S hS f).inverseImage).symm ≪≫
    Functor.isoWhiskerRight
      (pullbackCommRingSheafULiftIso.{u, u, u + 1} (SmallEtale.topology B S hS Y.1)) _

/-- **The inverse image of sheaves of commutative rings along a morphism of algebraic spaces
commutes with raising the universe of sections.** For `f : X ⟶ Y`, the universe lift of
`f_small⁻¹𝒪`, computed at the universe `u` of the structure rings, is `f_small⁻¹` of the lift of
`𝒪`, computed at the universe `u + 1` of the small étale sites. On underlying sheaves of sets it
is `AlgebraicGeometry.Space.smallToposMorphismInverseImageULiftIso`; the two universe lifts of
sheaves of commutative rings are compared by
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafULiftIso`. -/
noncomputable def smallEtaleInverseImageRingULiftIso :
    smallEtaleInverseImageRing B S hS f ⋙
        SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS X.1) ≅
      SheafOfModules.sheafULift.{u, u + 1, u} (SmallEtale.topology B S hS Y.1) ⋙
        inverseImageCommRingFunctor.{u + 1, u + 1, u, u + 1, u, u + 1}
          (smallToposMorphism B S hS f) :=
  smallEtaleInverseImageRingULiftIsoAux₁ f ≪≫
    pullbackCommRingSheafFunctorIsoOfNatIso (SmallEtale.topology B S hS X.1)
      (Φ := (smallToposMorphismTypeU B S hS f).inverseImage ⋙
        sheafCompose (SmallEtale.topology B S hS X.1) uliftFunctor.{u + 1, u})
      (Φ' := sheafCompose (SmallEtale.topology B S hS Y.1) uliftFunctor.{u + 1, u} ⋙
        (smallToposMorphism B S hS f).inverseImage)
      (smallToposMorphismInverseImageULiftIso f) ≪≫
    smallEtaleInverseImageRingULiftIsoAux₂ f

end AlgebraicGeometry.Space

end
