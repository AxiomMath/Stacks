module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Pullback preserves local projectivity

The pullback of a locally projective quasi-coherent module along a morphism of schemes is
locally projective.

## Main results

* `AlgebraicGeometry.projective_sections_pullback_of_le`: over an affine open of the source
  mapping into an affine open of the target, the sections of a pullback are the base change of
  the sections upstairs, hence projective as soon as those are.
* `AlgebraicGeometry.pullback_isLocallyProjective`: local projectivity of a quasi-coherent
  module is preserved by pullback.

## Implementation notes

An affine open of the source need not map into an affine open of the target, so the sections
of the pullback over an arbitrary affine open are not a single base change. The affine opens
that do map into an affine open of the target cover the source, and their spectra form a
Zariski, hence fpqc, covering; local projectivity then follows from its fpqc descent, Tag 05JZ.
Over the spectrum of the ring of functions on such an affine open, every affine open is
contained in the whole space, so the base-change comparison applies a second time there.

## References

* [Stacks Project, Tag 060M](https://stacks.math.columbia.edu/tag/060M)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Sections of a pullback over an affine open of the source are projective over the ring of
functions on it, as soon as the sections over an affine open of the target containing their
image are projective. -/
lemma projective_sections_pullback_of_le {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hproj : Module.Projective Γ(X, U) Γ(F, U)) :
    Module.Projective Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V) := by
  let : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hVU).hom.toAlgebra
  have : Module.Projective Γ(X, U) Γ(F, U) := hproj
  have hbc : Module.Projective Γ(Y, V) (Γ(Y, V) ⊗[Γ(X, U)] Γ(F, U)) := by
    have : Module.Projective Γ(Y, V) Γ(Y, V) := inferInstance
    exact Module.Projective.tensorProduct
  have : Module.Projective Γ(Y, V) ((ModuleCat.extendScalars (f.appLE U V hVU).hom).obj
      (ModuleCat.of Γ(X, U) Γ(F, U))) := hbc
  exact Module.Projective.of_equiv'
    (affinePullbackSectionsBaseChangeIso f F hU hV hVU).toLinearEquiv

/-- **Stacks Project, Tag 060M.** The pullback of a locally projective quasi-coherent module
along a morphism of schemes is locally projective. -/
@[stacks 060M]
theorem pullback_isLocallyProjective {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
    [G.IsQuasicoherent] (hG : Scheme.Modules.IsLocallyProjective G) :
    Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pullback f).obj G) := by
  have hFqc : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent X.toRingedSpace Y.toRingedSpace
      f.toLRSHom.toShHom G (show G.IsQuasicoherent from inferInstance)
  refine isLocallyProjective_of_pullback_fpqc _ hFqc
    (I := {p : X.Opens × Y.Opens // IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.1 ≤ f ⁻¹ᵁ p.2})
    (fun i => Spec Γ(X, i.1.1)) (fun i => i.2.1.fromSpec) ?_ ?_
  · refine Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ ?_
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => i.2.1.isOpenImmersion_fromSpec⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (a := f x) (TopologicalSpace.Opens.mem_top _) (TopologicalSpace.Opens.isOpen ⊤)
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) hxW (TopologicalSpace.Opens.isOpen (f ⁻¹ᵁ W))
    obtain ⟨y, hy⟩ : x ∈ Set.range hV.fromSpec.base := hV.range_fromSpec ▸ hxV
    exact ⟨⟨(V, W), hV, hW, hVW⟩, y, hy⟩
  · rintro ⟨⟨V, W⟩, hV, hW, hVW⟩ U' hU'
    refine projective_sections_pullback_of_le hV.fromSpec _ hV hU' ?_
      (projective_sections_pullback_of_le f G hW hV hVW (hG W hW))
    rw [hV.fromSpec_preimage_self]
    exact le_top

end AlgebraicGeometry

end
