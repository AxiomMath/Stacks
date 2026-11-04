module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFullness

/-!
# The sheaf condition for the module `Mᵃ` on the slice at a chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `X` be
an étale chart of `F`. For a quasi-coherent module `M` on the scheme of `X`, the presheaf of
pullback sections of `M` on the slice of the small étale site at `X` is a sheaf, so the module
`Mᵃ` of [Stacks, Tag 03DU], `AlgebraicGeometry.Space.SmallEtale.sliceAssociatedModule`, is
defined for every such `M`. This file records this and the two consequences for free modules
and for full faithfulness at an affine chart.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent`: the
  presheaf of pullback sections of a quasi-coherent module on the chart's scheme is a sheaf on
  the slice at the chart.
* `AlgebraicGeometry.Space.SmallEtale.exists_sliceAssociatedModule_iso_free_unconditional`: a
  free module on the slice at an affine chart is isomorphic to `Mᵃ` for a quasi-coherent module
  `M` on the chart's scheme.
* `AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice_unconditional`: the
  functor `M ↦ Mᵃ` is fully faithful on quasi-coherent modules at an affine chart.

## References

* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (X : SmallEtale B S hS F)

/-- The presheaf of pullback sections of a quasi-coherent module `M` on the chart's scheme is a
sheaf on the slice of the small étale site at the chart. -/
theorem isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent (M : (chartScheme X).Modules)
    [M.IsQuasicoherent] :
    Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X)) :=
  Stacks.Sites.isSheaf_associatedPresheaf_of_isContinuous _ M _ _
    (quasiCoherentPresheaf_isSheaf_fpqc' (chartScheme X) M)

include hF in
/-- A free module on the slice of the small étale site at an affine chart is isomorphic to the
module `Mᵃ` of [Stacks, Tag 03DU] attached to some quasi-coherent module `M` on the chart's
scheme. -/
theorem exists_sliceAssociatedModule_iso_free_unconditional
    (hX : IsAffine (chartScheme X)) (I : Type u) :
    ∃ (M : (chartScheme X).Modules) (_ : M.IsQuasicoherent)
      (hM : Presheaf.IsSheaf ((topology B S hS F).over X)
        (Stacks.Sites.associatedPresheaf (chartScheme X) M (sliceToOver B S hS F X))),
      Nonempty (SheafOfModules.free (R := sliceRingSheaf B S hS F hF X) I ≅
        sliceAssociatedModule B S hS F hF X M hM) :=
  exists_sliceAssociatedModule_iso_free B S hS F hF X hX I
    fun M hM => @isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent B S hS F X M hM

include hF in
/-- At an affine chart, the map `φ ↦ φᵃ` from morphisms `M ⟶ N` of quasi-coherent modules on the
chart's scheme to morphisms `Mᵃ ⟶ Nᵃ` on the slice of the small étale site is bijective. -/
theorem bijective_associatedModuleMap_slice_unconditional [IsAffine (chartScheme X)]
    {M N : (chartScheme X).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective fun φ : M ⟶ N =>
      Stacks.Sites.associatedModuleMap (chartScheme X) (sliceToOver B S hS F X) φ :=
  bijective_associatedModuleMap_slice B S hS F hF X
    (isSheaf_sliceAssociatedPresheaf_of_isQuasicoherent B S hS F X N)

end AlgebraicGeometry.Space.SmallEtale

end
