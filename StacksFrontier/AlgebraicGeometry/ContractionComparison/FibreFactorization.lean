module

public import StacksFrontier.AlgebraicGeometry.ContractionComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.IsolatedPoints

/-!
# Factoring through a contraction which contracts the fibres

Let `d : W ⟶ Y` be a surjective closed morphism onto a reduced scheme with `𝒪_Y = d_*𝒪_W`, and
let `c : W ⟶ X` be a morphism to a separated scheme which is constant on every fibre of `d`. Then
`c` factors through `d`. Around `y ∈ Y`, choose an affine open `V ⊆ X` containing the image of
the fibre over `y`; the complement `V₀` of the image under `d` of `W ∖ c⁻¹V` is an open
neighbourhood of `y` with `d⁻¹V₀ ⊆ c⁻¹V`, and
`Stacks.ContractionComparison.exists_comp_eq` glues the resulting charts. This is how the
morphisms of models in the proof of [Stacks, Tag 0E97] are produced from their special fibres.

## Main results

* `Stacks.ContractionComparison.exists_comp_eq_of_forall_fiber`: the factorization.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ContractionComparison

/-- **A morphism constant on the fibres of a contraction factors through it.** Let `d : W ⟶ Y`
be surjective and universally closed with `Y` reduced and `𝒪_Y = d_*𝒪_W`, and let `c : W ⟶ X`
with `X` separated be such that every fibre of `d` is mapped by `c` to a single point. Then
`c = d ≫ a` for some `a : Y ⟶ X`. -/
theorem exists_comp_eq_of_forall_fiber {W Y X : Scheme.{u}} (d : W ⟶ Y) (c : W ⟶ X)
    [Surjective d] [UniversallyClosed d] [IsReduced Y] [X.IsSeparated]
    (hd : IsIso (SheafOfModules.unitToPushforwardObjUnit d.toRingCatSheafHom))
    (hfib : ∀ y : Y, ∃ x : X, ∀ w : W, d w = y → c w = x) : ∃ a : Y ⟶ X, d ≫ a = c := by
  choose x hx using hfib
  choose V hVaff hxV _ using fun y : Y =>
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x y) (by simp)
  let V₀ : Y → Y.Opens := fun y =>
    ⟨(d.base '' (c ⁻¹ᵁ V y : Set W)ᶜ)ᶜ,
      (d.isClosedMap _ (c ⁻¹ᵁ V y).isOpen.isClosed_compl).isOpen_compl⟩
  have hle : ∀ y, d ⁻¹ᵁ V₀ y ≤ c ⁻¹ᵁ V y := fun _ w hw =>
    Classical.byContradiction fun h => hw ⟨w, h, rfl⟩
  have hmem : ∀ y, y ∈ V₀ y := fun y => by
    rintro ⟨w, hw, rfl⟩
    refine hw ?_
    change c w ∈ V (d w)
    rw [hx _ w rfl]
    exact hxV _
  exact exists_comp_eq d c V₀ V hVaff hle (fun y =>
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit d hd _)
    (IsOpenCover.mk (eq_top_iff.mpr fun y _ => Opens.mem_iSup.mpr ⟨y, hmem y⟩))

end Stacks.ContractionComparison

end
