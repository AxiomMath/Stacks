module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsTFAE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.DenseSubsiteRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged

/-!
# The derived category of an algebraic space on the equi-universe model of its small étale site
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 04KH on the equi-universe model**: the model of the small étale ringed site of an
algebraic space is a locally ringed site, being the restriction of a locally ringed site to a
dense subsite. -/
theorem smallEtaleModelRingedSite_isLocallyRinged :
    RingedSite.IsLocallyRinged (smallEtaleModelRingedSite B S hS F hF) :=
  have : (smallEtaleModelEquivalence B S hS F).functor.IsDenseSubsite
      (smallEtaleModelTopology B S hS F) (smallEtaleRingedSite B S hS F hF).J :=
    smallEtaleModelEquivalence_functor_isDenseSubsite B S hS F
  RingedSite.isLocallyRinged_denseRestrict (smallEtaleModelTopology B S hS F)
    (smallEtaleRingedSite B S hS F hF) (smallEtaleModelEquivalence B S hS F).functor
    (smallEtaleRingedSite_isLocallyRinged B S hS F hF)

end AlgebraicGeometry.Space
