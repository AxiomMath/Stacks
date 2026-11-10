module

public import StacksFrontier.AlgebraicGeometry.ContractionComparison.Basic

/-!
# A morphism factors through a contraction identifying an ample module

Let `d : X ⟶ Y₀` be surjective with `𝒪_{Y₀} = d_*𝒪_X` and `Y₀` reduced, and let `c : X ⟶ Y` be
any morphism to a separated scheme `Y`. If `L₀`, `L` are invertible on `Y₀`, `Y` with `L` ample
and `d^*L₀ ≅ c^*L`, then `c` factors through `d`. This is
`Stacks.ContractionComparison.exists_comp_eq_of_isAmple` without its hypothesis
`𝒪_Y = c_*𝒪_X`, which the chart-by-chart argument there never uses: the sections of powers of
`L` are pulled back along `c` and descended along `d`, so only `𝒪_{Y₀} = d_*𝒪_X` is needed.

## Main results

* `Stacks.ContractionComparison.exists_comp_eq_of_isAmple_of_isIso_unitToPushforwardObjUnit_left`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ContractionComparison

open Stacks.SheafOfModules.Invertible (tensorPower)
open Opposite

variable {X Y₀ Y : Scheme.{u}} (d : X ⟶ Y₀) (c : X ⟶ Y)

/-- **A morphism factors through a contraction identifying an ample module**: let `d : X ⟶ Y₀`
be surjective with `𝒪_{Y₀} = d_*𝒪_X` and `Y₀` reduced, `c : X ⟶ Y` with `Y` separated, and let
`L₀`, `L` be invertible on `Y₀`, `Y` with `L` ample and `d^*L₀ ≅ c^*L`. Then `c` factors through
`d`: each affine `Y_s`, `s ∈ Γ(Y, L^{⊗ n})`, has `c⁻¹Y_s = d⁻¹(Y₀)_{s₀}` for some `s₀`, and these
charts glue (`exists_comp_eq`). No condition on `c_*𝒪_X` is needed. -/
theorem exists_comp_eq_of_isAmple_of_isIso_unitToPushforwardObjUnit_left [Surjective d]
    [IsReduced Y₀] [Y.IsSeparated]
    (hd : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom))
    (L₀ : Y₀.Modules) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y₀.toRingedSpace.presheaf
      (structureSheafRing Y₀.toRingedSpace).property L₀]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    (φ : (Scheme.Modules.pullback d).obj L₀ ≅ (Scheme.Modules.pullback c).obj L)
    (hL : Scheme.Modules.IsAmple Y L) : ∃ e : Y₀ ⟶ Y, d ≫ e = c := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback d).obj L₀) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback d.toLRSHom.toShHom L₀
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback c).obj L) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback c.toLRSHom.toShHom L
  have key := fun (n : ℕ) (s : (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).sections) =>
    exists_preimage_nonvanishingOpen_eq c d hd L L₀ φ.symm n s
  let ι := Σ n : ℕ, {s : (tensorPower Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L (n : ℤ)).sections //
    IsAffineOpen (Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace) _ s)}
  let V : ι → Y.Opens := fun i =>
    Stacks.SheafOfModules.nonvanishingOpen (X := Y.toRingedSpace) _ i.2.1
  let V₀ : ι → Y₀.Opens := fun i =>
    Stacks.SheafOfModules.nonvanishingOpen (X := Y₀.toRingedSpace) _ (key i.1 i.2.1).choose
  have hV₀ : ∀ i, d ⁻¹ᵁ V₀ i = c ⁻¹ᵁ V i := fun i => (key i.1 i.2.1).choose_spec.symm
  refine exists_comp_eq d c V₀ V (fun i => i.2.2) (fun i => (hV₀ i).le) (fun i => ?_) ?_
  · have hO : IsIso (C := Y₀.Modules)
        (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom) := hd
    let e := ((Scheme.Modules.toPresheaf Y₀).mapIso (@asIso _ _ _ _ _ hO)).app (op (V₀ i))
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (ConcreteCategory.bijective_of_isIso e.hom)
  · refine IsOpenCover.mk (eq_top_iff.2 fun y₀ _ => ?_)
    obtain ⟨x, rfl⟩ := d.surjective y₀
    obtain ⟨n, -, s, hxs, haff⟩ := hL.exists_affine_nonvanishingLocus (c x)
    refine Opens.mem_iSup.2 ⟨⟨n, s, haff⟩, ?_⟩
    change x ∈ d ⁻¹ᵁ V₀ ⟨n, s, haff⟩
    rw [hV₀]
    exact hxs

end Stacks.ContractionComparison

end
