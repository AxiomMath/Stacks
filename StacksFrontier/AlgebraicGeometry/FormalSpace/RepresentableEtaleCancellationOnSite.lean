module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSection

/-!
# Representable étale morphisms from relative étaleness on the site

A morphism of fppf sheaves over `S` which is étale after every base change to a represented sheaf
is representable étale.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_relative_etaleOnSite`: a morphism which
  is étale after every represented base change is representable étale.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves which is étale after every represented base change is
representable étale. -/
theorem isRepresentableEtale_of_relative_etaleOnSite {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hrel : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) f.hom) :
    IsRepresentableEtale B S hS f := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS))
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  refine ⟨fun U ξ => ?_, fun U ξ => ?_⟩
  · obtain ⟨W, ρ, w, hpb⟩ := hrel.rep ξ
    exact Space.isAlgebraicSpaceULift_of_iso B S hS hpb.flip.isoPullback
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS W)
  · exact fun _ φ hφ => MorphismProperty.comp_mem _ _ _ hφ
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback ξ f.hom).flip hrel)

end AlgebraicGeometry.FormalSpace

end
