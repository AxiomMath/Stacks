module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage

/-!
# Coherence of a direct image of a structure sheaf depends only on the image

Two open immersions into the same scheme with the same image have isomorphic sources over that
scheme, and the direct images of their structure sheaves are therefore isomorphic. This file
records that comparison and the consequence the induction of [Stacks, Tag 0BK1] consumes: for a
nested pair of opens `V' ≤ P` of a scheme `X`, the composite `(P.ι ⁻¹ᵁ V').ι ≫ P.ι` and the
inclusion `V'.ι` have the same image, so coherence of the direct image may be transferred from
one to the other.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pushforwardUnitIsoOfIsIso`: the direct image of the structure
  sheaf along an isomorphism of schemes is the structure sheaf.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_opensRange_eq`: coherence of
  `j_*𝒪` depends on the open immersion `j` only through its image.

## Implementation notes

The comparison of the two direct images is assembled from Mathlib's
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` and
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` together with
`AlgebraicGeometry.isIso_structureSheafToPushforward_of_isIso`, which says that the canonical
comparison map `𝒪_Y ⟶ f_*𝒪_X` is invertible when `f` is. No bookkeeping on sections is needed:
the isomorphism of the sources over `X` is `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`,
whose defining factorization is exactly the hypothesis `pushforwardCongr` wants.

## References

* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The direct image of the structure sheaf along an isomorphism of schemes is the structure
sheaf.** The canonical comparison map `𝒪_Y ⟶ f_*𝒪_X` of
`AlgebraicGeometry.structureSheafToPushforward` is invertible as soon as `f` is, because on
sections it is `f.app U` pushed along the forgetful functor to abelian groups. -/
noncomputable def pushforwardUnitIsoOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    SheafOfModules.unit.{u} Y.ringCatSheaf ≅
      (pushforward f).obj (SheafOfModules.unit.{u} X.ringCatSheaf) :=
  @asIso _ _ _ _ (structureSheafToPushforward f)
    (isIso_structureSheafToPushforward_of_isIso f)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.LocalCohomology

/-- **The direct images of the structure sheaves of two open immersions with the same image are
isomorphic.** If `j₁ : W₁ ⟶ X` and `j₂ : W₂ ⟶ X` are open immersions with
`j₁.opensRange = j₂.opensRange`, then `(j₂)_*𝒪_{W₂} ≅ (j₁)_*𝒪_{W₁}`.

`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` is the isomorphism `e : W₂ ≅ W₁` over `X`, so
`(j₂)_*` and `(e.hom ≫ j₁)_*` agree by `AlgebraicGeometry.Scheme.Modules.pushforwardCongr`, the
latter splits as `(j₁)_* ∘ (e.hom)_*` by
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`, and `(e.hom)_*𝒪_{W₂} ≅ 𝒪_{W₁}` by
`AlgebraicGeometry.Scheme.Modules.pushforwardUnitIsoOfIsIso`. -/
noncomputable def pushforwardStructureSheafIsoOfOpensRangeEq {X W₁ W₂ : Scheme.{u}}
    (j₁ : W₁ ⟶ X) [IsOpenImmersion j₁] (j₂ : W₂ ⟶ X) [IsOpenImmersion j₂]
    (hr : j₁.opensRange = j₂.opensRange) :
    (Scheme.Modules.pushforward j₂).obj (SheafOfModules.unit.{u} W₂.ringCatSheaf) ≅
      (Scheme.Modules.pushforward j₁).obj (SheafOfModules.unit.{u} W₁.ringCatSheaf) := by
  have hcoe := (congrArg (fun U : X.Opens => (U : Set X)) hr).symm
  refine (Scheme.Modules.pushforwardCongr
      (IsOpenImmersion.isoOfRangeEq_hom_fac j₂ j₁ (by simpa using hcoe)).symm).app _ ≪≫
    ((Scheme.Modules.pushforwardComp
      (IsOpenImmersion.isoOfRangeEq j₂ j₁ (by simpa using hcoe)).hom j₁).app _).symm ≪≫
    (Scheme.Modules.pushforward j₁).mapIso
      (Scheme.Modules.pushforwardUnitIsoOfIsIso
        (IsOpenImmersion.isoOfRangeEq j₂ j₁ (by simpa using hcoe)).hom).symm

/-- **Coherence of the direct image of a structure sheaf along an open immersion depends only on
the image of that immersion.**

This is the identification the induction of [Stacks, Tag 0BK1] needs in order to pass between a
nested pair of opens `V' ≤ P` of a scheme `X` read two ways: as `V'.ι : V' ⟶ X`, and as the
composite `(P.ι ⁻¹ᵁ V').ι ≫ P.ι` through the intermediate open `P` on which the inductive step
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_basicOpen_le` is stated. The two
have the same image, and coherence transports along
`pushforwardStructureSheafIsoOfOpensRangeEq`. -/
theorem isCoherent_pushforward_structureSheaf_of_opensRange_eq {X W₁ W₂ : Scheme.{u}}
    (j₁ : W₁ ⟶ X) [IsOpenImmersion j₁] (j₂ : W₂ ⟶ X) [IsOpenImmersion j₂]
    (hr : j₁.opensRange = j₂.opensRange)
    (h : ((Scheme.Modules.pushforward j₁).obj
      (SheafOfModules.unit.{u} W₁.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward j₂).obj
      (SheafOfModules.unit.{u} W₂.ringCatSheaf)).IsCoherent :=
  have := h
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (pushforwardStructureSheafIsoOfOpensRangeEq j₁ j₂ hr)

end Stacks.LocalCohomology

end
