module
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetsToAbelianBaseChangeBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SetBaseChangeAbelianTransfer

/-!
# BoundedSetBaseChangeTransferUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer`,
stated as separate declarations beside the ones there: over more general coefficient universes,
or with inputs that are carried there as hypotheses discharged, together with the new results
built on them.

For a commutative square of a big étale site, the base change map of sheaves of sets on the
bounded small étale sites is an isomorphism whenever the corresponding base change map on
Mathlib's small étale sites is one, at the coefficient universe `u + 1` of the site.

## Main results

* `isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange_general`:
  the base change map on the bounded small étale sites is invertible if the one on Mathlib's
  small étale sites is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u})
variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **The base change map of sheaves of sets on the bounded small étale sites is invertible if the
one on Mathlib's small étale sites is.** For a commutative square `g' ≫ f = f' ≫ g` of a big étale
site, if `Stacks.EtaleCohomology.smallEtaleSetBaseChange` is an isomorphism at the coefficient
universe `u + 1` of the site, so is `AlgebraicGeometry.smallEtaleBaseChangeNatTransUniv`. -/
public theorem isIso_smallEtaleBaseChangeNatTrans_of_isIso_smallEtaleSetBaseChange_general
    (h : g' ≫ f = f' ≫ g)
    (hset : IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} (B.inclusion.map g')
      (B.inclusion.map f') (B.inclusion.map f) (B.inclusion.map g)
      (by rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, h]))) :
    IsIso (smallEtaleBaseChangeNatTransUniv.{u, 0} B g' f' f g h) := by
  let adjUg := Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction.{u, 0} (B.inclusion.map g)
  let adjUg' :=
    Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction.{u, 0} (B.inclusion.map g')
  have hun : IsIso ((mateEquiv adjUg' adjUg).symm
      (unboundedBaseChangeMate B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm)).natTrans := by
    rwa [Stacks.EtaleCohomology.smallEtaleSetBaseChange_eq_mateEquiv_symm_univ.{u, 0}
      (B.inclusion.map f) (B.inclusion.map g) (B.inclusion.map g') (B.inclusion.map f') _
      (B.inclusion.map (g' ≫ f)) (B.inclusion.map_comp g' f)
      ((congrArg B.inclusion.map h).trans (B.inclusion.map_comp f' g))] at hset
  have hEq : ((toEtaleSite B X.obj X.property).sheafPushforwardContinuous (Type (u + 1))
      (topology B X.obj X.property) X.obj.smallEtaleTopology).EssSurj :=
    (sheafEquiv B X.obj X.property (Type (u + 1))).isEquivalence_inverse.essSurj
  have := isIso_restrictionPullbackBaseChange B (Type (u + 1)) g' adjUg'
    (B.smallPullbackAdjunction g' (Type (u + 1)))
  have := isIso_restrictionPullbackBaseChange B (Type (u + 1)) g adjUg
    (B.smallPullbackAdjunction g (Type (u + 1)))
  have hb := _root_.Stacks.EtaleCohomology.isIso_mateEquiv_symm_of_essSurj
    adjUg' adjUg (B.smallPullbackAdjunction g' (Type (u + 1)))
    (B.smallPullbackAdjunction g (Type (u + 1)))
    (restrictionPullbackBaseChange B (Type (u + 1)) g' adjUg' _)
    (restrictionPullbackBaseChange B (Type (u + 1)) g adjUg _)
    (toEtaleSitePushforwardBaseChangeIso B f (Type (u + 1))).hom
    (toEtaleSitePushforwardBaseChangeIso B f' (Type (u + 1))).inv
    (unboundedBaseChangeMate B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm)
    (boundedBaseChangeMate B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm)
    (baseChangeMate_cube_eq B (Type (u + 1)) f g g' f' (g' ≫ f) rfl h.symm adjUg _ adjUg' _)
  rwa [← smallEtaleBaseChangeMate_eq_boundedBaseChangeMate_univ.{u, 0} B f g g' f' h (g' ≫ f) rfl
    h.symm] at hb

end AlgebraicGeometry.SmallEtale

end
