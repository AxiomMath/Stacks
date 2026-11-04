module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeMorphism
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Morphisms of modules on `U(ψ)` are determined over the pieces `U(ψ')`

For the data of [Stacks, Tag 01O8], a morphism of sheaves of modules on `U(ψ)` is determined by
its inverse images along the inclusions `U(ψ') ⟶ U(ψ)` of the opens attached to the induced data
over the affine opens `V` of the base (`…GradedPowerMap.affineDatumInclusion`). Each inclusion is
an isomorphism onto the part of `U(ψ)` over `V`, followed by that open immersion; inverse image
along an isomorphism is faithful, along an open immersion it is restriction, and the parts of
`U(ψ)` over the affine opens of the base cover it.

This is the uniqueness step through which clause (3) of [Stacks, Tag 01O9] pins `θ`.

## Main results

* `…GradedPowerMap.hom_ext_of_pullback_affineDatumInclusion`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

/-- Two functors isomorphic to each other identify the same pairs of morphisms. -/
theorem map_eq_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    {X Y : C} {φ ψ : X ⟶ Y} (h : F.map φ = F.map ψ) : G.map φ = G.map ψ := by
  have hφ := e.inv.naturality φ
  have hψ := e.inv.naturality ψ
  exact (cancel_mono (e.inv.app Y)).mp (hφ.trans ((congrArg (e.inv.app X ≫ ·) h).trans hψ.symm))

/-- **Equality of morphisms of modules is local, tested along isomorphisms onto the members of an
open cover.** -/
theorem hom_ext_of_pullback_cover {X : Scheme.{u}} {M N : X.Modules} {φ ψ : M ⟶ N}
    {ι : Type*} (W : ι → X.Opens) (hW : ∀ x : X, ∃ a, x ∈ W a) {Z : ι → Scheme.{u}}
    (e : ∀ a, Z a ⟶ (W a).toScheme) [∀ a, IsIso (e a)] (g : ∀ a, Z a ⟶ X)
    (hg : ∀ a, g a = e a ≫ (W a).ι)
    (h : ∀ a, (Scheme.Modules.pullback (g a)).map φ = (Scheme.Modules.pullback (g a)).map ψ) :
    φ = ψ := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover W hW fun a => ?_
  have h1 := h a
  rw [hg a] at h1
  have h2 := map_eq_of_iso (Scheme.Modules.pullbackComp (e a) (W a).ι).symm h1
  have h3 : (Scheme.Modules.pullback (W a).ι).map φ = (Scheme.Modules.pullback (W a).ι).map ψ :=
    (Scheme.Modules.pullback (e a)).map_injective h2
  exact map_eq_of_iso (Scheme.Modules.restrictFunctorIsoPullback (W a).ι).symm h3

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- **A morphism of modules on `U(ψ)` is determined by its inverse images along the inclusions
`U(ψ') ⟶ U(ψ)` over the affine opens of the base.** -/
theorem hom_ext_of_pullback_affineDatumInclusion {M N : P.coveringOpen.toScheme.Modules}
    {φ ψ : M ⟶ N}
    (h : ∀ V : S.affineOpens, (Scheme.Modules.pullback (P.affineDatumInclusion V)).map φ =
      (Scheme.Modules.pullback (P.affineDatumInclusion V)).map ψ) : φ = ψ := by
  refine hom_ext_of_pullback_cover (fun V : S.affineOpens => P.toBase ⁻¹ᵁ V.1) (fun x => ?_)
    (fun V => (P.pieceIso V.1 V.2).inv) (fun V => P.affineDatumInclusion V) (fun V => rfl) h
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (P.toBase.base x))
  exact ⟨⟨V, hV⟩, hxV⟩

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
