module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom

/-!
# The sections of the internal Hom of modules on an algebraic space, at the module universe `u`

`AlgebraicGeometry.Space.smallEtaleInternalHomSmall M N` is the internal Hom `𝓗om_{𝒪_F}(M, N)`
read at the module universe of the schemes.  Its sections over an étale chart `U` are the
morphisms `M|_U ⟶ N|_U` of the restrictions to the slice of the small étale site at `U`; this file
records that identification, its behaviour under postcomposition (functoriality of the internal
Hom in its second variable) and under the action of the sections of `𝒪_F` over `U`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomSmallSectionsEquiv`: the sections over `U` of
  `𝓗om(M, N)` are the morphisms `M|_U ⟶ N|_U`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleInternalHomSmallSectionsEquiv_map`: postcomposition.
* `AlgebraicGeometry.Space.smallEtaleInternalHomSmallSectionsEquiv_smul`: the module structure.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M N P : Modules.{u, u} B S hS F hF)

/-- The sections of the small internal Hom over a chart are the morphisms of the restrictions
to the slice at the chart. -/
def smallEtaleInternalHomSmallSectionsEquiv (U : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ) :
    (smallEtaleInternalHomSmall B S hS F hF M N).val.obj U ≃ (M.over U.unop ⟶ N.over U.unop) :=
  (equivShrink.{u} ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F hF) M N).val.obj
    U)).symm.trans
  { toFun := fun s => ⟨s⟩
    invFun := fun φ => φ.val
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Under `smallEtaleInternalHomSmallSectionsEquiv`, the map `𝓗om(M, N) ⟶ 𝓗om(M, P)` induced by
`g : N ⟶ P` is postcomposition with the restriction of `g` to the slice at `U`. -/
theorem smallEtaleInternalHomSmallSectionsEquiv_map (g : N ⟶ P)
    (U : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ)
    (x : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj U) :
    smallEtaleInternalHomSmallSectionsEquiv B S hS F hF M P U
        (((RingedSite.internalHomSheafSmallFunctor (smallEtaleRingedSite B S hS F hF) M).map
          g).val.app U x) =
      smallEtaleInternalHomSmallSectionsEquiv B S hS F hF M N U x ≫ g.over U.unop := by
  have h := congrArg (fun k => (k.val.app U) (ULift.up x))
    (RingedSite.moduleULift_map_internalHomSheafSmallFunctor_map
      (smallEtaleRingedSite B S hS F hF) M g)
  have h' : ((RingedSite.internalHomSheafSmallFunctor (smallEtaleRingedSite B S hS F hF) M).map
        g).val.app U x =
      equivShrink.{u}
          ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F hF) M P).val.obj U)
        ((RingedSite.internalHomPost (smallEtaleRingedSite B S hS F hF) g).val.app U
          ((equivShrink.{u} ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F hF) M
            N).val.obj U)).symm x)) :=
    congrArg ULift.down h
  have h'' : (equivShrink.{u} ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F hF) M
      P).val.obj U)).symm
        (((RingedSite.internalHomSheafSmallFunctor (smallEtaleRingedSite B S hS F hF) M).map
          g).val.app U x) =
      (RingedSite.internalHomPost (smallEtaleRingedSite B S hS F hF) g).val.app U
          ((equivShrink.{u} ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F hF) M
            N).val.obj U)).symm x) := by
    rw [h', Equiv.symm_apply_apply]
  exact congrArg (fun s => (⟨s⟩ : M.over U.unop ⟶ P.over U.unop)) h''

/-- Under `smallEtaleInternalHomSmallSectionsEquiv`, multiplying a section of `𝓗om(M, N)` over
`U` by a section `r` of the structure sheaf over `U` multiplies its value on each section `y` of
`M` over `V ⟶ U` by the restriction of `r` to `V`. -/
theorem smallEtaleInternalHomSmallSectionsEquiv_smul
    (U : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj U)
    (x : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj U) (V : Over U.unop)
    (y : (M.over U.unop).val.obj (op V)) :
    ((smallEtaleInternalHomSmallSectionsEquiv B S hS F hF M N U (r • x)).val.app (op V)).hom y =
      (show ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over
          U.unop).obj.obj (op V) from
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.map
          V.hom.op r) •
        ((smallEtaleInternalHomSmallSectionsEquiv B S hS F hF M N U x).val.app (op V)).hom y := by
  have key : (equivShrink.{u} ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F
      hF) M N).val.obj U)).symm (r • x) = r • (equivShrink.{u} ((RingedSite.internalHomSheaf
      (smallEtaleRingedSite B S hS F hF) M N).val.obj U)).symm x :=
    equivShrink_symm_smul (α := ((RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS F
      hF) M N).val.obj U)) r x
  exact (congrArg (fun s => ((⟨s⟩ : M.over U.unop ⟶ N.over U.unop).val.app (op V)).hom y)
    key).trans rfl

end AlgebraicGeometry.Space
