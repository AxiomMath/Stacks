module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapEtaleAtlasDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwistGlue

/-!
# A morphism glued from a chart is surjective or bijective when the chart is

Let `χ : M ⟶ N` be a morphism of modules on an algebraic space `X` whose inverse image along the
atlas of a presentation of `X`, followed by a chart identification `e_N`, is `κ_M ≫ θ` with `κ_M`
an isomorphism (`AlgebraicGeometry.Space.Presentation.IsAtlasMapComp`). Then `χ` is an
epimorphism, resp. an isomorphism, exactly when `θ` is, by the étale locality of these properties
(`StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapEtaleAtlasDescent`).

## Main results

* `AlgebraicGeometry.Space.Presentation.IsAtlasMapComp.epi_iff` and `….isIso_iff`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.Presentation.IsAtlasMapComp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : Presentation B S hS X.1 X.2}
  {M N : Modules.{u, u} B S hS X.1 X.2}
  {C D : Modules.{u, u} B S hS (yoneda.obj P.U) (isAlgebraicSpace_yoneda B S hS P.U)}
  {eN : Iso.{u + 1} ((modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).obj N) D}
  {κM : (modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).obj M ⟶ C}
  {θ : C ⟶ D} {χ : M ⟶ N}

/-- The inverse image of `χ` along the atlas, written through the chart identifications. -/
theorem modulePullback_map_eq (h : P.IsAtlasMapComp eN κM θ χ) :
    (modulePullback B S hS (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩)
      P.atlas).map χ = κM ≫ θ ≫ eN.inv := by
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A morphism glued from a chart is an epimorphism exactly when the chart morphism is.** -/
theorem epi_iff (h : P.IsAtlasMapComp eN κM θ χ) [IsIso κM] : Epi χ ↔ Epi θ := by
  have hiff : Epi ((modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).map χ) ↔ Epi χ :=
    epi_modulePullback_map_iff_of_isEtale_of_isSurjective B S hS
      (Z' := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas
      P.isEtale_atlas P.isSurjective_atlas χ
  rw [← hiff, h.modulePullback_map_eq, epi_comp_iff_of_epi, epi_comp_iff_of_isIso]

/-- **A morphism glued from a chart is an isomorphism exactly when the chart morphism is.** -/
theorem isIso_iff (h : P.IsAtlasMapComp eN κM θ χ) [IsIso κM] : IsIso χ ↔ IsIso θ := by
  have hiff : IsIso ((modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).map χ) ↔ IsIso χ :=
    isIso_modulePullback_map_iff_of_isEtale_of_isSurjective B S hS
      (Z' := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas
      P.isEtale_atlas P.isSurjective_atlas χ
  rw [← hiff, h.modulePullback_map_eq, isIso_comp_left_iff, isIso_comp_right_iff]

end AlgebraicGeometry.Space.Presentation.IsAtlasMapComp

end
