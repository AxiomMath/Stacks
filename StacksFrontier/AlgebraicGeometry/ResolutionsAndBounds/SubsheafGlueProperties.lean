module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictLocality
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubsheafRange

/-!
# The submodule glued across a two-element open cover is of finite type and quasi-coherent

Let `F` be an `𝒪_X`-module and let `X = W ∪ V` be a cover by two opens. Let `B` and `C` be
submodules of `F` in the sense of `SheafOfModules.Submodule` such that `B` is contained in `C`
over `W` and `C` is contained in `B` over `V`. Their sectionwise intersection `inter B C` then
agrees with `B` over `W` and with `C` over `V`, so its restriction to `W` is isomorphic to that
of `B` and its restriction to `V` is isomorphic to that of `C`. Since being of finite type and
being quasi-coherent are local on an open cover, `inter B C` inherits each of those properties
from `B` over `W` and `C` over `V`.

This is the step of the proof of [Stacks, Tag 01PF] in which a finite type quasi-coherent
submodule given on a quasi-compact open and one given on an affine open are combined into one
over the union; `inter B C` is what the source writes as the glued submodule.

## Main results

* `Stacks.AlgebraicGeometry.Subsheaf.isFiniteType_inter`: the glued submodule is of finite type.
* `Stacks.AlgebraicGeometry.Subsheaf.isQuasicoherent_inter`: the glued submodule is
  quasi-coherent.

## Implementation notes

The two hypotheses are one-sided on purpose. In the intended application `C` is the push
`Stacks.AlgebraicGeometry.Subsheaf.push V N` of a submodule `N` of `F.restrict V.ι`, which
constrains a section only over `V` and is therefore *not* contained in `B` away from `V`; and
`B` is a quasi-coherent extension of the given submodule from `W`, which agrees with `C` only
over `W ⊓ V` and hence, `C` being a push, over all of `W`.

The two-element cover is indexed by `Bool` so that the cover-locality statements, which take a
family of opens, apply directly.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Subsheaf

variable {X : Scheme.{u}} {F : X.Modules}

/-- The restriction to `W` of the inclusion of the glued submodule into `B` is an isomorphism. -/
lemma isIso_restrict_inclusion_inf_left {W : X.Opens} (B C : SheafOfModules.Submodule F)
    (h1 : ∀ T : X.Opens, T ≤ W → B.obj (op T) ≤ C.obj (op T)) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map
      (inclusion (N := inter B C) (N' := B) (fun _ => inf_le_left))) :=
  isIso_restrict_inclusion W _ fun _ hT => (inter_obj_of_le_left W B C h1 hT).ge

/-- The restriction to `V` of the inclusion of the glued submodule into `C` is an
isomorphism. -/
lemma isIso_restrict_inclusion_inf_right {V : X.Opens} (B C : SheafOfModules.Submodule F)
    (h2 : ∀ T : X.Opens, T ≤ V → C.obj (op T) ≤ B.obj (op T)) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (inclusion (N := inter B C) (N' := C) (fun _ => inf_le_right))) :=
  isIso_restrict_inclusion V _ fun _ hT => (inter_obj_of_le_right V B C h2 hT).ge

/-- The two-element family `W, V` indexed by `Bool` covers `X` when `W ⊔ V = ⊤`. -/
private theorem iSup_bool_ite_eq_top {W V : X.Opens} (hWV : W ⊔ V = ⊤) :
    (⨆ b : Bool, if b then W else V) = ⊤ := by
  rw [iSup_bool_eq]
  simpa using hWV

/-- **The glued submodule is of finite type.** If `W ⊔ V = ⊤`, if `B` is contained in `C` over
`W` and `C` is contained in `B` over `V`, and if the restriction of `B` to `W` and the
restriction of `C` to `V` are of finite type, then the sectionwise intersection of `B` and `C` is
of finite type. -/
theorem isFiniteType_inter {W V : X.Opens} (hWV : W ⊔ V = ⊤)
    (B C : SheafOfModules.Submodule F)
    (h1 : ∀ T : X.Opens, T ≤ W → B.obj (op T) ≤ C.obj (op T))
    (h2 : ∀ T : X.Opens, T ≤ V → C.obj (op T) ≤ B.obj (op T))
    (hB : ((mod B).restrict W.ι).IsFiniteType)
    (hC : ((mod C).restrict V.ι).IsFiniteType) :
    (mod (inter B C)).IsFiniteType := by
  have := isIso_restrict_inclusion_inf_left B C h1
  have := isIso_restrict_inclusion_inf_right B C h2
  refine AlgebraicGeometry.isFiniteType_of_iSup_eq_top _
    (fun b : Bool => if b then W else V) (iSup_bool_ite_eq_top hWV) fun b => ?_
  cases b
  · exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (asIso ((Scheme.Modules.restrictFunctor V.ι).map
        (inclusion (N := inter B C) (N' := C) (fun _ => inf_le_right)))).symm
  · exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      (asIso ((Scheme.Modules.restrictFunctor W.ι).map
        (inclusion (N := inter B C) (N' := B) (fun _ => inf_le_left)))).symm

/-- **The glued submodule is quasi-coherent.** If `W ⊔ V = ⊤`, if `B` is contained in `C` over
`W` and `C` is contained in `B` over `V`, and if the restriction of `B` to `W` and the
restriction of `C` to `V` are quasi-coherent, then the sectionwise intersection of `B` and `C` is
quasi-coherent. -/
theorem isQuasicoherent_inter {W V : X.Opens} (hWV : W ⊔ V = ⊤)
    (B C : SheafOfModules.Submodule F)
    (h1 : ∀ T : X.Opens, T ≤ W → B.obj (op T) ≤ C.obj (op T))
    (h2 : ∀ T : X.Opens, T ≤ V → C.obj (op T) ≤ B.obj (op T))
    (hB : ((mod B).restrict W.ι).IsQuasicoherent)
    (hC : ((mod C).restrict V.ι).IsQuasicoherent) :
    (mod (inter B C)).IsQuasicoherent := by
  have := isIso_restrict_inclusion_inf_left B C h1
  have := isIso_restrict_inclusion_inf_right B C h2
  refine AlgebraicGeometry.isQuasicoherent_of_iSup_eq_top _
    (fun b : Bool => if b then W else V) (iSup_bool_ite_eq_top hWV) fun b => ?_
  cases b
  · exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      (asIso ((Scheme.Modules.restrictFunctor V.ι).map
        (inclusion (N := inter B C) (N' := C) (fun _ => inf_le_right)))).symm hC
  · exact (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (asIso ((Scheme.Modules.restrictFunctor W.ι).map
        (inclusion (N := inter B C) (N' := B) (fun _ => inf_le_left)))).symm hB

end Stacks.AlgebraicGeometry.Subsheaf
