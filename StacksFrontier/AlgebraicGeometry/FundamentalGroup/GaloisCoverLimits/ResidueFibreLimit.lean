module

public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ResidueField
public import StacksFrontier.AlgebraicGeometry.Limits.FibreProductLimit
public import Mathlib.CategoryTheory.Limits.Opposites
public import StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.LimitDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.NormalApproximation

/-!
# The fibre of a limit of schemes at a point is the limit of the fibres

Let `B : J ⥤ Scheme` be a cofiltered diagram with affine transition morphisms, `cB` a limit cone
and `s` a point of its vertex, with images `s_j ∈ B_j`. The residue fields `κ(s_j)` form a filtered
diagram whose colimit is `κ(s)` ([Stacks, Tag 0CUG], `AlgebraicGeometry.residueField_isColimit`),
so `Spec κ(s)` is the limit of the `Spec κ(s_j)`. If `φ : A ⟶ B` is a morphism of diagrams and
`cA` a limit cone over `A` with a compatible `p : cA.pt ⟶ cB.pt`, the fibres
`A_j ×_{B_j} Spec κ(s_j)` then have limit `cA.pt ×_{cB.pt} Spec κ(s)`, the fibre of `p` at `s`:
limits commute with fibre products (`AlgebraicGeometry.FibreProductLimit.isLimit`).

This is the descent setting of the generic fibre in the proof of [Stacks, Tag 0EZJ].

## Main definitions

* `AlgebraicGeometry.GaloisCoverLimits.ptResidueSpecDiagram`, `ptResidueSpecCone` — the diagram
  `j ↦ Spec κ(s_j)` and the cone on it with vertex `Spec κ(s)`.
* `AlgebraicGeometry.GaloisCoverLimits.ptResidueSpecι` — the canonical morphisms
  `Spec κ(s_j) ⟶ B_j`, as a natural transformation.
* `AlgebraicGeometry.GaloisCoverLimits.ptFiberDiagram`, `ptFiberCone` — the diagram of fibres and
  the cone on it with vertex the fibre of `p` at `s`.

## Main results

* `AlgebraicGeometry.GaloisCoverLimits.isLimitPtResidueSpecCone` and
  `AlgebraicGeometry.GaloisCoverLimits.isLimitPtFiberCone` — the two limits.

## References

* [Stacks Project, Tag 0CUG](https://stacks.math.columbia.edu/tag/0CUG)
* [Stacks Project, Tag 0EZJ](https://stacks.math.columbia.edu/tag/0EZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GaloisCoverLimits

section Residue

variable {J : Type u} [Category.{u} J] (B : J ⥤ Scheme.{u}) (cB : Cone B) (s : cB.pt)

/-- The image under a transition morphism of the image of `s` at an earlier stage is its image at
the later stage. -/
lemma map_π_app_apply {i j : J} (g : i ⟶ j) : B.map g (cB.π.app i s) = cB.π.app j s := by
  rw [← cB.w g]
  rfl

/-- The map `κ(s_j) ⟶ κ(s_i)` of residue fields along a transition `g : i ⟶ j`. -/
def ptResidueTransition {i j : J} (g : i ⟶ j) :
    (B.obj j).residueField (cB.π.app j s) ⟶ (B.obj i).residueField (cB.π.app i s) :=
  ((B.obj j).residueFieldCongr (map_π_app_apply B cB s g).symm).hom ≫
    (B.map g).residueFieldMap (cB.π.app i s)

/-- The transition maps of residue fields are compatible with the maps to `κ(s)`. -/
lemma ptResidueTransition_residueFieldMap {i j : J} (g : i ⟶ j) :
    ptResidueTransition B cB s g ≫ (cB.π.app i).residueFieldMap s =
      (cB.π.app j).residueFieldMap s := by
  rw [ptResidueTransition, Category.assoc, ← Scheme.residueFieldMap_comp]
  exact (Scheme.Hom.residueFieldMap_congr (cB.w g).symm s).symm

/-- The diagram of the residue fields `κ(s_j)`. -/
@[simps]
def ptResidueDiagram : Jᵒᵖ ⥤ CommRingCat.{u} where
  obj i := (B.obj i.unop).residueField (cB.π.app i.unop s)
  map g := ptResidueTransition B cB s g.unop
  map_id i := by
    have : Mono ((cB.π.app i.unop).residueFieldMap s) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    rw [← cancel_mono ((cB.π.app i.unop).residueFieldMap s), unop_id,
      ptResidueTransition_residueFieldMap, Category.id_comp]
  map_comp {i j k} g h := by
    have : Mono ((cB.π.app k.unop).residueFieldMap s) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    rw [← cancel_mono ((cB.π.app k.unop).residueFieldMap s), unop_comp, Category.assoc,
      ptResidueTransition_residueFieldMap, ptResidueTransition_residueFieldMap,
      ptResidueTransition_residueFieldMap]

/-- The cocone on the residue fields `κ(s_j)` with vertex `κ(s)`. -/
@[simps]
def ptResidueCocone : Cocone (ptResidueDiagram B cB s) where
  pt := cB.pt.residueField s
  ι :=
    { app := fun i ↦ (cB.π.app i.unop).residueFieldMap s
      naturality := fun _ _ g ↦
        (ptResidueTransition_residueFieldMap B cB s g.unop).trans (Category.comp_id _).symm }

/-- **The residue field at a point of the limit is the colimit of the residue fields at its
images** ([Stacks, Tag 0CUG]). -/
def isColimitPtResidueCocone [IsCofiltered J] [∀ {i j : J} (g : i ⟶ j), IsAffineHom (B.map g)]
    (hB : IsLimit cB) : IsColimit (ptResidueCocone B cB s) := by
  have H := residueField_isColimit B cB hB s (ptResidueDiagram B cB s) (fun _ ↦ Iso.refl _)
    (fun f ↦ by
      simp only [ptResidueDiagram_map, Quiver.Hom.unop_op, ptResidueTransition, Iso.refl_hom,
        Iso.refl_inv]
      rfl)
  exact
    { desc := fun t ↦ (H t.pt (fun i ↦ t.ι.app (op i)) (fun g ↦ t.w g.op)).choose
      fac := fun t i ↦ by
        have h := (H t.pt (fun i ↦ t.ι.app (op i)) (fun g ↦ t.w g.op)).choose_spec.1 i.unop
        simp only [Iso.refl_hom] at h
        exact h
      uniq := fun t m hm ↦
        (H t.pt (fun i ↦ t.ι.app (op i)) (fun g ↦ t.w g.op)).choose_spec.2 m
          fun i ↦ by
            simp only [Iso.refl_hom]
            exact hm (op i) }

/-- The diagram of the spectra `Spec κ(s_j)`, written with its objects and maps on the nose. -/
abbrev ptResidueSpecDiagram : J ⥤ Scheme.{u} where
  obj j := Spec ((B.obj j).residueField (cB.π.app j s))
  map g := Spec.map (ptResidueTransition B cB s g)
  map_id j := by
    rw [← Spec.map_id]
    congr 1
    exact (ptResidueDiagram B cB s).map_id (op j)
  map_comp g h := by
    rw [← Spec.map_comp]
    congr 1
    exact (ptResidueDiagram B cB s).map_comp h.op g.op

/-- The cone on the spectra `Spec κ(s_j)` with vertex `Spec κ(s)`, written with its vertex and
legs on the nose. -/
@[simps pt]
def ptResidueSpecCone : Cone (ptResidueSpecDiagram B cB s) where
  pt := Spec (cB.pt.residueField s)
  π :=
    { app := fun j ↦ Spec.map ((cB.π.app j).residueFieldMap s)
      naturality := fun i j g ↦ by
        change 𝟙 _ ≫ Spec.map ((cB.π.app j).residueFieldMap s) =
          Spec.map ((cB.π.app i).residueFieldMap s) ≫ Spec.map (ptResidueTransition B cB s g)
        rw [Category.id_comp, ← Spec.map_comp, ptResidueTransition_residueFieldMap] }

/-- **`Spec κ(s)` is the limit of the `Spec κ(s_j)`.** -/
def isLimitPtResidueSpecCone [IsCofiltered J] [∀ {i j : J} (g : i ⟶ j), IsAffineHom (B.map g)]
    (hB : IsLimit cB) : IsLimit (ptResidueSpecCone B cB s) :=
  (IsLimit.postcomposeHomEquiv (Iso.refl _ : (ptResidueDiagram B cB s).rightOp ⋙ Scheme.Spec ≅
      ptResidueSpecDiagram B cB s) _).symm
    (IsLimit.ofIsoLimit (isLimitOfPreserves Scheme.Spec
      (isLimitConeRightOpOfCocone _ (isColimitPtResidueCocone B cB s hB)))
      (Cone.ext (Iso.refl _) fun _ ↦ by simp))

/-- The object of `ptResidueSpecDiagram` at `j` is `Spec κ(s_j)`. -/
lemma ptResidueSpecDiagram_obj (j : J) :
    (ptResidueSpecDiagram B cB s).obj j = Spec ((B.obj j).residueField (cB.π.app j s)) := rfl

/-- The map of `ptResidueSpecDiagram` along `g` is `Spec` of the transition of residue fields. -/
lemma ptResidueSpecDiagram_map {i j : J} (g : i ⟶ j) :
    (ptResidueSpecDiagram B cB s).map g = Spec.map (ptResidueTransition B cB s g) := rfl

/-- The leg of `ptResidueSpecCone` at `j` is `Spec` of the map `κ(s_j) ⟶ κ(s)`. -/
lemma ptResidueSpecCone_π_app (j : J) :
    (ptResidueSpecCone B cB s).π.app j = Spec.map ((cB.π.app j).residueFieldMap s) := rfl

/-- The projection `Spec κ(s) ⟶ Spec κ(s_j)`, with its source and target written on the nose. -/
abbrev ptResidueSpecProj (j : J) :
    Spec (cB.pt.residueField s) ⟶ Spec ((B.obj j).residueField (cB.π.app j s)) :=
  Spec.map ((cB.π.app j).residueFieldMap s)

/-- The leg of `ptResidueSpecCone` at `j` is `ptResidueSpecProj`. -/
lemma ptResidueSpecCone_π_app_eq_proj (j : J) :
    (ptResidueSpecCone B cB s).π.app j = ptResidueSpecProj B cB s j := rfl

/-- The square formed by `Spec κ(s) ⟶ Spec κ(s_j)`, the canonical morphisms to `cB.pt` and `B_j`,
and the leg `cB.pt ⟶ B_j` commutes. -/
lemma ptResidueSpecProj_comp (j : J) :
    ptResidueSpecProj B cB s j ≫ (B.obj j).fromSpecResidueField (cB.π.app j s) =
      cB.pt.fromSpecResidueField s ≫ cB.π.app j :=
  Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ s

/-- The projections `Spec κ(s) ⟶ Spec κ(s_j)` commute with the transitions. -/
lemma ptResidueSpecProj_naturality {i j : J} (g : i ⟶ j) :
    ptResidueSpecProj B cB s i ≫ Spec.map (ptResidueTransition B cB s g) =
      ptResidueSpecProj B cB s j := by
  rw [ptResidueSpecProj, ptResidueSpecProj, ← Spec.map_comp, ptResidueTransition_residueFieldMap]

/-- The canonical morphisms `Spec κ(s_j) ⟶ B_j` commute with the transitions. -/
lemma specMap_ptResidueTransition_fromSpecResidueField {i j : J} (g : i ⟶ j) :
    Spec.map (ptResidueTransition B cB s g) ≫ (B.obj j).fromSpecResidueField (cB.π.app j s) =
      (B.obj i).fromSpecResidueField (cB.π.app i s) ≫ B.map g := by
  rw [ptResidueTransition, Spec.map_comp, Category.assoc,
    Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- The canonical morphisms `Spec κ(s_j) ⟶ B_j`, as a natural transformation. -/
@[simps]
abbrev ptResidueSpecι : ptResidueSpecDiagram B cB s ⟶ B where
  app j := (B.obj j).fromSpecResidueField (cB.π.app j s)
  naturality _ _ g := specMap_ptResidueTransition_fromSpecResidueField B cB s g

/-- The legs of the cone of residue spectra lie over the legs of `cB`. -/
lemma ptResidueSpecCone_π_app_comp (j : J) :
    (ptResidueSpecCone B cB s).π.app j ≫ (ptResidueSpecι B cB s).app j =
      cB.pt.fromSpecResidueField s ≫ cB.π.app j :=
  Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ s

/-- The legs `Spec κ(s) ⟶ Spec κ(s_j)` of `ptResidueSpecCone` are flat. -/
instance flat_ptResidueSpecCone_π_app (j : J) : Flat ((ptResidueSpecCone B cB s).π.app j) := by
  change Flat (Spec.map ((cB.π.app j).residueFieldMap s))
  rw [Flat.SpecMap_iff]
  let := ((cB.π.app j).residueFieldMap s).hom.toAlgebra
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The legs `Spec κ(s) ⟶ Spec κ(s_j)` of `ptResidueSpecCone` are surjective. -/
instance surjective_ptResidueSpecCone_π_app (j : J) :
    Surjective ((ptResidueSpecCone B cB s).π.app j) := by
  change Surjective (Spec.map ((cB.π.app j).residueFieldMap s))
  exact ⟨fun _ ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩

/-- The legs `Spec κ(s) ⟶ Spec κ(s_j)` of `ptResidueSpecCone` are quasi-compact. -/
instance quasiCompact_ptResidueSpecCone_π_app (j : J) :
    QuasiCompact ((ptResidueSpecCone B cB s).π.app j) := by
  change QuasiCompact (Spec.map ((cB.π.app j).residueFieldMap s))
  infer_instance

/-- The transition morphisms of `ptResidueSpecDiagram` are affine. -/
instance {i j : J} (g : i ⟶ j) : IsAffineHom ((ptResidueSpecDiagram B cB s).map g) := by
  change IsAffineHom (Spec.map (ptResidueTransition B cB s g))
  infer_instance

/-- Each `Spec κ(s_j)` is compact. -/
instance (j : J) : CompactSpace ((ptResidueSpecDiagram B cB s).obj j) := by
  change CompactSpace (Spec ((B.obj j).residueField (cB.π.app j s)))
  infer_instance

/-- Each `Spec κ(s_j)` is quasi-separated. -/
instance (j : J) : QuasiSeparatedSpace ((ptResidueSpecDiagram B cB s).obj j) := by
  change QuasiSeparatedSpace (Spec ((B.obj j).residueField (cB.π.app j s)))
  infer_instance

/-- The projection `Spec κ(s) ⟶ Spec κ(s_j)` is flat. -/
instance (j : J) : Flat (ptResidueSpecProj B cB s j) := flat_ptResidueSpecCone_π_app B cB s j

/-- The projection `Spec κ(s) ⟶ Spec κ(s_j)` is surjective. -/
instance (j : J) : Surjective (ptResidueSpecProj B cB s j) :=
  surjective_ptResidueSpecCone_π_app B cB s j

/-- The projection `Spec κ(s) ⟶ Spec κ(s_j)` is quasi-compact. -/
instance (j : J) : QuasiCompact (ptResidueSpecProj B cB s j) :=
  quasiCompact_ptResidueSpecCone_π_app B cB s j

end Residue

section Fibre

variable {J : Type u} [Category.{u} J] {A B : J ⥤ Scheme.{u}} (φ : A ⟶ B) (cB : Cone B)
  (s : cB.pt) (cA : Cone A) (p : cA.pt ⟶ cB.pt)
  (hp : ∀ j, cA.π.app j ≫ φ.app j = p ≫ cB.π.app j)

/-- The diagram of the fibres `A_j ×_{B_j} Spec κ(s_j)`. -/
abbrev ptFiberDiagram : J ⥤ Scheme.{u} :=
  FibreProductLimit.diagram φ (ptResidueSpecι B cB s)

/-- The projection from the fibre `cA.pt ×_{cB.pt} Spec κ(s)` of `p` at `s` to the fibre of the
stage `j`. -/
def ptFiberConeMap (j : J) :
    pullback p (cB.pt.fromSpecResidueField s) ⟶
      pullback (φ.app j) ((ptResidueSpecι B cB s).app j) :=
  pullback.map _ _ _ _ (cA.π.app j) (ptResidueSpecProj B cB s j) (cB.π.app j)
    (hp j).symm (ptResidueSpecProj_comp B cB s j).symm

/-- The first projection of `ptFiberConeMap` is the leg `cA.pt ⟶ A_j` after the first projection
of the fibre of `p`. -/
@[reassoc (attr := simp)]
lemma ptFiberConeMap_fst (j : J) :
    ptFiberConeMap φ cB s cA p hp j ≫ pullback.fst (φ.app j) ((ptResidueSpecι B cB s).app j) =
      pullback.fst p (cB.pt.fromSpecResidueField s) ≫ cA.π.app j :=
  pullback.lift_fst _ _ _

/-- The second projection of `ptFiberConeMap` is `Spec κ(s) ⟶ Spec κ(s_j)` after the second
projection of the fibre of `p`. -/
@[reassoc (attr := simp)]
lemma ptFiberConeMap_snd (j : J) :
    ptFiberConeMap φ cB s cA p hp j ≫ pullback.snd (φ.app j) ((ptResidueSpecι B cB s).app j) =
      pullback.snd p (cB.pt.fromSpecResidueField s) ≫ ptResidueSpecProj B cB s j :=
  pullback.lift_snd _ _ _

/-- The transitions of `ptFiberDiagram` lie over the transitions of `A` along the first
projections. -/
@[reassoc (attr := simp)]
lemma ptFiberDiagram_map_fst {i j : J} (g : i ⟶ j) :
    (ptFiberDiagram φ cB s).map g ≫ pullback.fst (φ.app j) ((ptResidueSpecι B cB s).app j) =
      pullback.fst (φ.app i) ((ptResidueSpecι B cB s).app i) ≫ A.map g :=
  FibreProductLimit.diagram_map_fst _ _ g

/-- The transitions of `ptFiberDiagram` lie over the transitions of `ptResidueSpecDiagram` along
the second projections. -/
@[reassoc (attr := simp)]
lemma ptFiberDiagram_map_snd {i j : J} (g : i ⟶ j) :
    (ptFiberDiagram φ cB s).map g ≫ pullback.snd (φ.app j) ((ptResidueSpecι B cB s).app j) =
      pullback.snd (φ.app i) ((ptResidueSpecι B cB s).app i) ≫
        (ptResidueSpecDiagram B cB s).map g :=
  FibreProductLimit.diagram_map_snd _ _ g

/-- The projections of the fibre of the limit commute with the transitions of the fibres. -/
lemma ptFiberConeMap_naturality {i j : J} (g : i ⟶ j) :
    ptFiberConeMap φ cB s cA p hp i ≫ (ptFiberDiagram φ cB s).map g =
      ptFiberConeMap φ cB s cA p hp j := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ptFiberDiagram_map_fst, ptFiberConeMap_fst_assoc, ptFiberConeMap_fst,
      cA.w g]
  · rw [Category.assoc, ptFiberDiagram_map_snd, ptFiberConeMap_snd_assoc, ptFiberConeMap_snd]
    exact congrArg (pullback.snd p (cB.pt.fromSpecResidueField s) ≫ ·)
      (ptResidueSpecProj_naturality B cB s g)

/-- The cone on the diagram of fibres with vertex the fibre `cA.pt ×_{cB.pt} Spec κ(s)` of `p`
at `s`. -/
@[simps pt]
def ptFiberCone : Cone (ptFiberDiagram φ cB s) where
  pt := pullback p (cB.pt.fromSpecResidueField s)
  π :=
    { app := ptFiberConeMap φ cB s cA p hp
      naturality := fun i j g ↦ by
        change 𝟙 _ ≫ ptFiberConeMap φ cB s cA p hp j = _
        rw [Category.id_comp, ptFiberConeMap_naturality] }

/-- The leg of `ptFiberCone` at `j` is `ptFiberConeMap`. -/
lemma ptFiberCone_π_app (j : J) :
    (ptFiberCone φ cB s cA p hp).π.app j = ptFiberConeMap φ cB s cA p hp j := rfl

/-- **The fibre of the limit is the limit of the fibres.** -/
def isLimitPtFiberCone [IsCofiltered J] [∀ {i j : J} (g : i ⟶ j), IsAffineHom (B.map g)]
    (hA : IsLimit cA) (hB : IsLimit cB) : IsLimit (ptFiberCone φ cB s cA p hp) :=
  IsLimit.ofIsoLimit
    (FibreProductLimit.isLimit (cA := cA) (cB := ptResidueSpecCone B cB s) (cC := cB) φ
      (ptResidueSpecι B cB s) p (cB.pt.fromSpecResidueField s) hp
      (ptResidueSpecCone_π_app_comp B cB s) hA (isLimitPtResidueSpecCone B cB s hB) hB)
    (Cone.ext (Iso.refl _) fun _ ↦ (Category.id_comp _).symm)

end Fibre

end AlgebraicGeometry.GaloisCoverLimits

end
