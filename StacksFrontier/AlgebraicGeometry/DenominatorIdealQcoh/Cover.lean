module

public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local

/-!
# Quasi-coherence from localization on the basic opens of a cover

A module on a scheme `X` is quasi-coherent as soon as, for each member `U` of a cover of `X` by
affine opens, its sections over each basic open of `U` are the localization of its sections over
`U`.

## Main results

* `Stacks.DenominatorIdealQcoh.isQuasicoherent_of_isLocalizedModule_cover`: a module whose
  sections over each basic open of each member of a cover by affine opens are the localization
  of its sections over that member is quasi-coherent.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace Stacks.DenominatorIdealQcoh

variable {X : Scheme.{u}}

/-- **Quasi-coherence is detected by localization on the basic opens of a cover.**  If `X` is
covered by affine opens `U i` and, for each `i` and each section `a` of the structure sheaf over
`U i`, the sections of `N` over `X.basicOpen a` are the localization of its sections over `U i`
away from `a`, then `N` is quasi-coherent. -/
theorem isQuasicoherent_of_isLocalizedModule_cover (N : X.Modules) {I : Type u}
    (U : I → X.Opens) (hcov : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ (i : I) (a : Γ(X, U i)),
      letI := moduleOfLE N (X.basicOpen_le a)
      IsLocalizedModule.Away a (restrictₗ N (X.basicOpen_le a))) :
    N.IsQuasicoherent := by
  refine isQuasicoherent_of_presentations N U hcov fun i ↦ ?_
  have := isQuasicoherent_restrict_fromSpec N (hU i) (h i)
  have h₂ : ((N.restrict (hU i).fromSpec).restrict (hU i).isoSpec.hom).IsQuasicoherent :=
    inferInstance
  have : (N.restrict (U i).ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
      (((Scheme.Modules.restrictFunctorComp (hU i).isoSpec.hom (hU i).fromSpec).app N).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (hU i).isoSpec_hom_fromSpec).app N) h₂
  exact (nonempty_presentation_of_isoSpec (hU i).isoSpec _).some

end Stacks.DenominatorIdealQcoh

end
