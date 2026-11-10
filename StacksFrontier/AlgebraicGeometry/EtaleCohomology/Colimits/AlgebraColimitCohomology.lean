module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeColimitSheafH
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 03Q6: étale cohomology of `X ×_{Spec A} Spec(colim B_i)`

Let `A` be a ring, `(B_i)` a directed system of `A`-algebras with colimit `B`, `f : X ⟶ Spec A`
quasi-compact and quasi-separated, and `F` an abelian sheaf on `X_étale`. Put
`Y_i = Spec B_i ×_{Spec A} X`, `Y = Spec B ×_{Spec A} X`, and let `G_i`, `G` be the inverse images
of `F`. Then `H^p(Y, G) = colim_i H^p(Y_i, G_i)` for every `p`
(`Stacks.EtaleCohomology.ColimitBaseChange.isIso_colimitDesc_algebraCohomologyCocone`): the
restriction maps along `Y ⟶ Y_i` form a colimit cocone on the diagram of restriction maps along
`Y_j ⟶ Y_i`.

The `A`-algebras are objects of `Under A`; `Y = lim_i Y_i` is derived here: `Spec` carries the
colimit `B` to a limit of affine schemes over `Spec A`
(`Stacks.EtaleCohomology.ColimitBaseChange.isLimitSpecCone`), and base change along `f` preserves
it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology.ColimitBaseChange

universe u

open Stacks.EtaleCohomology.BaseChangeAlgebraSystem

/-- Sheafification of abelian groups at the object universe of the small étale site. -/
local instance hasSheafify_smallEtale_objectUniverse''' (Y : Scheme.{u}) :
    HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Scheme.hasSheafify_smallEtaleTopology.{u, u + 1} Y

variable {I : Type u} [Preorder I] (A : CommRingCat.{u}) (B : I ⥤ Under A)

/-- The system `i ↦ Spec B_i` of affine schemes over `Spec A`. -/
def specDiagram : Iᵒᵖ ⥤ Over (Spec A) where
  obj i := Over.mk (Spec.map (B.obj i.unop).hom)
  map g := Over.homMk (Spec.map (B.map g.unop).right) (by
    change Spec.map (B.map g.unop).right ≫ Spec.map (B.obj _).hom = Spec.map (B.obj _).hom
    rw [← Spec.map_comp, Under.w])
  map_id i := by
    ext1
    simp
  map_comp g g' := by
    ext1
    simp [← Spec.map_comp]

variable (cB : Cocone B)

/-- The cone `Spec B ⟶ Spec B_i` over `Spec A`. -/
def specCone : Cone (specDiagram A B) where
  pt := Over.mk (Spec.map cB.pt.hom)
  π :=
    { app i := Over.homMk (Spec.map (cB.ι.app i.unop).right) (by
        change Spec.map (cB.ι.app i.unop).right ≫ Spec.map (B.obj _).hom = Spec.map cB.pt.hom
        rw [← Spec.map_comp, Under.w]
        rfl)
      naturality i j g := by
        ext1
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Over.comp_left]
        change Spec.map (cB.ι.app j.unop).right = Spec.map (cB.ι.app i.unop).right ≫
          Spec.map (B.map g.unop).right
        rw [← Spec.map_comp, ← Under.comp_right, cB.w] }

/-- **`Spec` of the colimit is the limit of the `Spec B_i` over `Spec A`.** -/
def isLimitSpecCone [Nonempty I] [IsDirected I (· ≤ ·)] (hcB : IsColimit cB) :
    IsLimit (specCone A B cB) := by
  haveI : IsFiltered I := isFiltered_of_directed_le_nonempty I
  haveI : IsConnected I := IsFiltered.isConnected I
  haveI : IsConnected Iᵒᵖ := isConnected_op
  have h1 : IsColimit ((Under.forget A).mapCocone cB) := isColimitOfPreserves (Under.forget A) hcB
  have h2 := isLimitOfPreserves Scheme.Spec h1.op
  have h3 : IsLimit ((Over.forget (Spec A)).mapCone (specCone A B cB)) := h2
  exact isLimitOfReflects (Over.forget (Spec A)) h3

variable {X : Scheme.{u}} (f : X ⟶ Spec A) (F : Sheaf X.smallEtaleTopology Ab.{u + 1})

/-- `Y_i = Spec B_i ×_{Spec A} X`. -/
abbrev algebraLevel (i : I) : Scheme.{u} := pullback (Spec.map (B.obj i).hom) f

/-- `Y = Spec B ×_{Spec A} X` for the colimit `B` of the `B_i`. -/
abbrev algebraLimit : Scheme.{u} := pullback (Spec.map cB.pt.hom) f

/-- `G_i`, the inverse image of `F` to `Y_i`. -/
abbrev algebraLevelSheaf (i : I) : Sheaf (algebraLevel A B f i).smallEtaleTopology Ab.{u + 1} :=
  (smallEtalePullbackAb (pullback.snd (Spec.map (B.obj i).hom) f)).obj F

/-- `G`, the inverse image of `F` to `Y`. -/
abbrev algebraLimitSheaf : Sheaf (algebraLimit A B cB f).smallEtaleTopology Ab.{u + 1} :=
  (smallEtalePullbackAb (pullback.snd (Spec.map cB.pt.hom) f)).obj F

/-- The transition `Y_j ⟶ Y_i` for `i ⟶ j`, the base change of `Spec B_j ⟶ Spec B_i`. -/
abbrev algebraTransition {i j : I} (g : i ⟶ j) : algebraLevel A B f j ⟶ algebraLevel A B f i :=
  (baseChange (Spec A) (Over.mk f) (specDiagram A B)).map g.op

/-- The cone of the `Y ⟶ Y_i`, the base change of `specCone`. -/
abbrev algebraLimitCone : Cone (baseChange (Spec A) (Over.mk f) (specDiagram A B)) :=
  baseChangeCone (Spec A) (Over.mk f) (specDiagram A B) (specCone A B cB)

/-- The leg `Y ⟶ Y_i`. -/
abbrev algebraLeg (i : I) : algebraLimit A B cB f ⟶ algebraLevel A B f i :=
  (algebraLimitCone A B cB f).π.app (op i)

/-- The projection `Y ⟶ X` is the leg `Y ⟶ Y_i` followed by the projection `Y_i ⟶ X`. -/
theorem algebraLimit_proj (i : Iᵒᵖ) :
    pullback.snd (Spec.map cB.pt.hom) f =
      (algebraLimitCone A B cB f).π.app i ≫ levelProj (Spec A) (Over.mk f) (specDiagram A B) i :=
  (Over.w ((Over.pullback f).map ((specCone A B cB).π.app i))).symm

/-- **The diagram `i ↦ H^p(Y_i, G_i)`**, with the restriction maps along `Y_j ⟶ Y_i`. -/
def algebraCohomologyDiagram (n : ℕ) : I ⥤ Ab.{u + 1} :=
  (opOpEquivalence I).inverse ⋙ cohomologyDiagram (Spec A) (Over.mk f) (specDiagram A B) F n

/-- The value of `algebraCohomologyDiagram` at `i` is `H^p(Y_i, G_i)`. -/
theorem algebraCohomologyDiagram_obj (n : ℕ) (i : I) :
    (algebraCohomologyDiagram A B f F n).obj i =
      AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} (algebraLevelSheaf A B f F i) n) := rfl

/-- The map of `algebraCohomologyDiagram` along `i ⟶ j` is restriction along `Y_j ⟶ Y_i`. -/
theorem algebraCohomologyDiagram_map (n : ℕ) {i j : I} (g : i ⟶ j) :
    (algebraCohomologyDiagram A B f F n).map g = AddCommGrpCat.ofHom (sheafHRestriction
      (algebraTransition A B f g) ((smallEtalePullbackAbCompIso' (algebraTransition A B f g)
        (pullback.snd (Spec.map (B.obj i).hom) f) (pullback.snd (Spec.map (B.obj j).hom) f)
        (levelProj_transition (Spec A) (Over.mk f) (specDiagram A B) g.op)).hom.app F) n) := rfl

/-- **The cocone of restrictions `H^p(Y_i, G_i) ⟶ H^p(Y, G)`** along the legs `Y ⟶ Y_i`. -/
def algebraCohomologyCocone (n : ℕ) : Cocone (algebraCohomologyDiagram A B f F n) :=
  (cohomologyCocone (Spec A) (Over.mk f) (specDiagram A B) F (algebraLimitCone A B cB f)
    (pullback.snd (Spec.map cB.pt.hom) f) (algebraLimit_proj A B cB f) n).whisker
      (opOpEquivalence I).inverse

/-- The cocone point of `algebraCohomologyCocone` is `H^p(Y, G)`. -/
theorem algebraCohomologyCocone_pt (n : ℕ) :
    (algebraCohomologyCocone A B cB f F n).pt =
      AddCommGrpCat.of (Sheaf.H.{u + 1, u + 1} (algebraLimitSheaf A B cB f F) n) := rfl

/-- The leg of `algebraCohomologyCocone` at `i` is restriction along `Y ⟶ Y_i`. -/
theorem algebraCohomologyCocone_ι_app (n : ℕ) (i : I) :
    (algebraCohomologyCocone A B cB f F n).ι.app i = AddCommGrpCat.ofHom (sheafHRestriction
      (algebraLeg A B cB f i) ((smallEtalePullbackAbCompIso' (algebraLeg A B cB f i)
        (pullback.snd (Spec.map (B.obj i).hom) f) (pullback.snd (Spec.map cB.pt.hom) f)
        (algebraLimit_proj A B cB f (op i))).hom.app F) n) := rfl

/-- Each `Spec B_i` in `specDiagram` is affine. -/
instance isAffine_specDiagram_obj (i : Iᵒᵖ) : IsAffine ((specDiagram A B).obj i).left :=
  inferInstanceAs (IsAffine (Spec (B.obj i.unop).right))

/-- Let `A` be a ring, `(B_i)` a directed system of `A`-algebras with colimit `B`, `f : X ⟶ Spec A`
quasi-compact and quasi-separated, and `F` an abelian sheaf on `X_étale`. With
`Y_i = Spec B_i ×_{Spec A} X`, `Y = Spec B ×_{Spec A} X` and `G_i`, `G` the inverse images of `F`,
the restriction maps exhibit `H^p(Y, G)` as `colim_i H^p(Y_i, G_i)`, for every `p`. -/
@[stacks 03Q6]
theorem isIso_colimitDesc_algebraCohomologyCocone [Nonempty I] [IsDirected I (· ≤ ·)]
    (hcB : IsColimit cB) [QuasiCompact f] [QuasiSeparated f] (n : ℕ) :
    IsIso (colimit.desc (algebraCohomologyDiagram A B f F n)
      (algebraCohomologyCocone A B cB f F n)) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  have hcY : IsLimit (algebraLimitCone A B cB f) :=
    isLimitOfPreserves (Over.forget X)
      (isLimitOfPreserves (Over.pullback f) (isLimitSpecCone A B cB hcB))
  have : QuasiCompact (Over.mk f).hom := ‹QuasiCompact f›
  have : QuasiSeparated (Over.mk f).hom := ‹QuasiSeparated f›
  have h := isIso_colimitDesc_cohomologyCocone (Spec A) (Over.mk f) (specDiagram A B) F
    (algebraLimitCone A B cB f) (pullback.snd (Spec.map cB.pt.hom) f) (algebraLimit_proj A B cB f)
    hcY n
  obtain ⟨hc⟩ := (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).1 h
  exact (Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff _).2
    ⟨hc.whiskerEquivalence (opOpEquivalence I).symm⟩

end Stacks.EtaleCohomology.ColimitBaseChange

end
