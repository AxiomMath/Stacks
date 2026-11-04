module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact

/-!
# The sheaf `W ↦ ℱ(W ∩ U)` attached to an open `U`

For an open `U` of a topological space `X` and a sheaf `ℱ` on `X`, the presheaf `W ↦ ℱ(W ∩ U)` is
again a sheaf on `X`: it is `j_* j⁻¹ ℱ` for the inclusion `j : U ⟶ X`. Restriction of sections
gives a natural map `ℱ ⟶ j_* j⁻¹ ℱ`.

Both are defined on the site of opens by precomposition with the continuous functor
`Stacks.Cohomology.RestrictionCover.openIntersection U : W ↦ j(j⁻¹ W)` of opens of `X`, so the
sections over `W` are `ℱ(j(j⁻¹ W))`.

## Main definitions

* `TopologicalSpace.Opens.restrictExtend`: the functor `ℱ ↦ (W ↦ ℱ(j(j⁻¹ W)))` on sheaves.
* `TopologicalSpace.Opens.toRestrictExtend`: the restriction map `ℱ ⟶ restrictExtend U ℱ`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Topology

universe w v u

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X)

open Stacks.Cohomology.RestrictionCover in
/-- The open `j(j⁻¹ W)` is contained in `W`. -/
theorem openIntersection_obj_le (W : Opens X) : (openIntersection U).obj W ≤ W := by
  show U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W) ≤ W
  rw [Opens.functor_map_eq_inf]; exact inf_le_left

open Stacks.Cohomology.RestrictionCover in
/-- The open `j(j⁻¹ W)` is contained in `U`. -/
theorem openIntersection_obj_le_right (W : Opens X) : (openIntersection U).obj W ≤ U := by
  show U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W) ≤ U
  rw [Opens.functor_map_eq_inf]; exact inf_le_right

variable (A : Type w) [Category.{v} A]

/-- **The sheaf `W ↦ ℱ(W ∩ U)`**, that is `j_* j⁻¹ ℱ` for the inclusion `j` of `U`, as a functor
on sheaves; its sections over `W` are `ℱ(j(j⁻¹ W))`. -/
abbrev restrictExtend :
    Sheaf (Opens.grothendieckTopology X) A ⥤ Sheaf (Opens.grothendieckTopology X) A :=
  (Stacks.Cohomology.RestrictionCover.openIntersection U).sheafPushforwardContinuous A _ _

/-- The restriction maps `ℱ(W) ⟶ ℱ(W ∩ U)`, as a natural transformation
`ℱ ⟶ restrictExtend U ℱ`. -/
def toRestrictExtend : 𝟭 (Sheaf (Opens.grothendieckTopology X) A) ⟶ restrictExtend U A where
  app F := ⟨{
    app W := F.obj.map (homOfLE (openIntersection_obj_le U W.unop)).op
    naturality W W' i := by
      change F.obj.map i ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      rfl }⟩
  naturality F G φ := by
    ext W
    exact (φ.hom.naturality _).symm

/-- The component of `toRestrictExtend U A` at `F` over `W` is the restriction map of `F`. -/
@[simp]
theorem toRestrictExtend_app_hom_app (F : Sheaf (Opens.grothendieckTopology X) A)
    (W : (Opens X)ᵒᵖ) :
    ((toRestrictExtend U A).app F).hom.app W =
      F.obj.map (homOfLE (openIntersection_obj_le U W.unop)).op := rfl

/-- The image of `φ` under `restrictExtend U A` has, over `W`, the component of `φ` over
`j(j⁻¹ W)`. -/
@[simp]
theorem restrictExtend_map_hom_app {F G : Sheaf (Opens.grothendieckTopology X) A} (φ : F ⟶ G)
    (W : (Opens X)ᵒᵖ) :
    ((restrictExtend U A).map φ).hom.app W =
      φ.hom.app (op ((Stacks.Cohomology.RestrictionCover.openIntersection U).obj W.unop)) :=
  rfl

end TopologicalSpace.Opens

end
