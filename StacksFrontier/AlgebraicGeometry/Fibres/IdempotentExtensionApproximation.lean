module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ResidueField
public import StacksFrontier.AlgebraicGeometry.Limits.ProperLimitOfFiniteTypeOverZ

/-!
# Noetherian approximation for the extension of an idempotent from a fibre

[Stacks, Tag 0G7X] asserts that for a proper morphism `f : X ⟶ S` and a point `s : S` every
idempotent of `Γ(X_s, 𝒪)` extends to a section of `𝒪_X` over `f ⁻¹ᵁ U` for some open
neighbourhood `U` of `s`.  The Stacks proof settles the case of a locally Noetherian base by the
theorem on formal functions and reduces the general case to it by the limit argument of
[Stacks, Tag 0A0P].  That reduction is carried out here, and the tag follows from it because
its locally Noetherian case is
`Stacks.FormalFunctions.extendsOverNeighbourhood_of_isLocallyNoetherian`.

## Main results

* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`: **Stacks Tag 0G7X**.
* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_noetherianCase`: Tag 0G7X over an
  arbitrary base, granted Tag 0G7X over a locally Noetherian base.
* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isPullback`: the conclusion of
  Tag 0G7X is local on the base.
* `Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_commSq`: a commuting square
  carries the conclusion of Tag 0G7X from the bottom morphism to the top one.
* `Stacks.AlgebraicGeometry.Fibres.isAffineHom_pullback_map`: the map induced on pullbacks by a
  morphism of cospans with affine components is affine, the base being allowed to vary.

## Implementation notes

The base is first replaced by an affine open neighbourhood of `s`
(`extendsOverNeighbourhood_of_isPullback`), which is legitimate because a section over the
inverse image of an open of that neighbourhood is a section over the inverse image of an open of
`S`.  The base is then quasi-compact and quasi-separated, so [Stacks, Tag 0A0P] writes `f` as the
limit of proper morphisms `fᵢ : Xᵢ ⟶ Sᵢ` with `Sᵢ` of finite type over `Spec ℤ`, hence locally
Noetherian.  The components of that limit of arrows are limits of the sources and of the targets
(`isLimitLeftFuncMapCone`, `isLimitRightFuncMapCone`), proved by hand because the arrow category
of schemes has no limits of the relevant shape to inherit.

The heart of the matter is that the fibre of the limit is the limit of the fibres:
`fiberConeIsLimit`.  Its proof pastes two limits — that of the `Xᵢ` and that of the `Spec κ(sᵢ)`,
the latter from the residue field colimit of [Stacks, Tag 0CUG] read in the opposite category —
against the pullback square defining `X_s`.  The transition morphisms of the fibre diagram are
affine, which is `isAffineHom_pullback_map`: the comparison of a pullback with the pullback over
a larger base is a base change of the diagonal of the map of bases, and that diagonal is a closed
immersion because an affine morphism is separated.  The stages are quasi-compact and
quasi-separated because the `fᵢ` are proper, so the global sections of the fibre are the filtered
colimit of the global sections of the stagewise fibres (`nonempty_isColimit_Γ_mapCocone`); an
idempotent therefore comes from a stage and is idempotent at a later stage.  The hypothesis is
applied to `fᵢ` there, and the resulting section is pulled back along the commuting square
(`extendsOverNeighbourhood_of_commSq`).

The morphisms `stageIncl`, `stageRes`, `limIncl`, `limRes` and their universal properties repeat
the projections of the fibres with their types phrased through the diagrams of which they are
values.  This is not cosmetic: a term whose type mentions the fibre both as a `pullback` and as a
value of the diagram is not type-correct at `implicit` transparency, and no rewriting is possible
inside it.  For the same reason the proofs of `fiberConeSquare` and `fiberConeIsLimit` are terms
rather than rewriting scripts.

## References

* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
* [Stacks Project, Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P)
* [Stacks Project, Tag 0CUG](https://stacks.math.columbia.edu/tag/0CUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.AlgebraicGeometry.Fibres


/-! ### Affineness of the comparison map of two pullbacks -/


/-- **The map induced on pullbacks by a morphism of cospans is affine** as soon as its three
components are.  The base is allowed to vary:  the comparison of the pullback with the pullback
over the target base is a base change of the diagonal of the map of bases, and that diagonal is a
closed immersion because an affine morphism is separated. -/
lemma isAffineHom_pullback_map {X Y S X' Y' S' : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [IsAffineHom i₁] [IsAffineHom i₂] [IsAffineHom i₃] :
    IsAffineHom (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) := by
  let : MorphismProperty.IsStableUnderComposition (@IsAffineHom.{u}) :=
    ⟨fun _ _ hf hg => by let := hf; let := hg; infer_instance⟩
  have key : pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
      pullback.map f g (f ≫ i₃) (g ≫ i₃) (𝟙 X) (𝟙 Y) i₃ (by simp) (by simp) ≫
        pullback.map (f ≫ i₃) (g ≫ i₃) f' g' i₁ i₂ (𝟙 S')
          (by simp [e₁]) (by simp [e₂]) := by
    apply pullback.hom_ext <;>
      simp
  have h₁ : IsAffineHom (pullback.map f g (f ≫ i₃) (g ≫ i₃) (𝟙 X) (𝟙 Y) i₃
      (by simp) (by simp)) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom.{u})
      (pullback_map_diagonal_isPullback f g i₃) inferInstance
  have h₂ : IsAffineHom (pullback.map (f ≫ i₃) (g ≫ i₃) f' g' i₁ i₂ (𝟙 S')
      (by simp [e₁]) (by simp [e₂])) :=
    MorphismProperty.pullbackMap (P := @IsAffineHom.{u}) ‹IsAffineHom i₁› ‹IsAffineHom i₂› e₁ e₂
  rw [key]
  infer_instance

/-! ### The components of a limit cone of arrows -/

section ArrowCone

/-- The commuting square of a morphism of arrows, precomposed with a map into its source. -/
private lemma comp_arrow_w {C : Type*} [Category C] {A B : Arrow C} (φ : A ⟶ B) {T : C}
    (a : T ⟶ A.left) : (a ≫ φ.left) ≫ B.hom = (a ≫ A.hom) ≫ φ.right := by
  rw [Category.assoc, Arrow.w, Category.assoc]

variable {J : Type*} [Category J] (D : J ⥤ Arrow Scheme.{u})

/-- The cone of arrows attached to a cone on the diagram of sources, with the identity of its
apex as the apex arrow. -/
private def leftAuxCone (t : Cone (D ⋙ Arrow.leftFunc)) : Cone D where
  pt := Arrow.mk (𝟙 t.pt)
  π :=
    { app := fun j =>
        { left := t.π.app j
          right := t.π.app j ≫ (D.obj j).hom
          w := (Category.id_comp _).symm }
      naturality := fun i j g => by
        have hl : t.π.app i ≫ (D.map g).left = t.π.app j := t.w g
        refine CommaMorphism.ext ?_ ?_
        · change 𝟙 t.pt ≫ t.π.app j = t.π.app i ≫ (D.map g).left
          rw [Category.id_comp]
          exact hl.symm
        · exact (Category.id_comp _).trans
            ((congrArg (fun z => z ≫ (D.obj j).hom) hl).symm.trans
              (comp_arrow_w (D.map g) (t.π.app i))) }

/-- The cone of arrows attached to a cone on the diagram of targets, with the initial scheme as
the source of the apex arrow. -/
private def rightAuxCone (t : Cone (D ⋙ Arrow.rightFunc)) : Cone D where
  pt := Arrow.mk (initial.to t.pt)
  π :=
    { app := fun j =>
        { left := initial.to (D.obj j).left
          right := t.π.app j
          w := initialIsInitial.hom_ext _ _ }
      naturality := fun i j g => by
        have hr : t.π.app i ≫ (D.map g).right = t.π.app j := t.w g
        refine CommaMorphism.ext (initialIsInitial.hom_ext _ _) ?_
        change 𝟙 t.pt ≫ t.π.app j = t.π.app i ≫ (D.map g).right
        rw [Category.id_comp]
        exact hr.symm }

/-- **The sources of a limit cone of arrows form a limit cone.** -/
private def isLimitLeftFuncMapCone (c : Cone D) (hc : IsLimit c) :
    IsLimit (Arrow.leftFunc.mapCone c) where
  lift t := (hc.lift (leftAuxCone D t)).left
  fac t j := congrArg CommaMorphism.left (hc.fac (leftAuxCone D t) j)
  uniq t m hm := by
    let M : Arrow.mk (𝟙 t.pt) ⟶ c.pt :=
      Arrow.homMk m (m ≫ c.pt.hom) (Category.id_comp _).symm
    have hM : ∀ j, M ≫ c.π.app j = (leftAuxCone D t).π.app j := by
      intro j
      have hmj : m ≫ (c.π.app j).left = t.π.app j := hm j
      refine CommaMorphism.ext hmj ?_
      change (m ≫ c.pt.hom) ≫ (c.π.app j).right = t.π.app j ≫ (D.obj j).hom
      exact (comp_arrow_w (c.π.app j) m).symm.trans
        (congrArg (fun z => z ≫ (D.obj j).hom) hmj)
    exact congrArg CommaMorphism.left (hc.uniq (leftAuxCone D t) M hM)

/-- **The targets of a limit cone of arrows form a limit cone.** -/
private def isLimitRightFuncMapCone (c : Cone D) (hc : IsLimit c) :
    IsLimit (Arrow.rightFunc.mapCone c) where
  lift t := (hc.lift (rightAuxCone D t)).right
  fac t j := congrArg CommaMorphism.right (hc.fac (rightAuxCone D t) j)
  uniq t m hm := by
    let M : Arrow.mk (initial.to t.pt) ⟶ c.pt :=
      Arrow.homMk (initial.to c.pt.left) m (initialIsInitial.hom_ext _ _)
    have hM : ∀ j, M ≫ c.π.app j = (rightAuxCone D t).π.app j := fun j =>
      CommaMorphism.ext (initialIsInitial.hom_ext _ _) (hm j)
    exact congrArg CommaMorphism.right (hc.uniq (rightAuxCone D t) M hM)

end ArrowCone

/-! ### A colimit of rings as a limit in the opposite category -/

section LeftOp

variable {K : Type*} [Category K] (G : Kᵒᵖ ⥤ CommRingCat.{u})

/-- The cocone on a diagram of rings read as a cone on the opposite diagram. -/
private def coconeRightOp (d : Cocone G) : Cone G.rightOp where
  pt := op d.pt
  π :=
    { app := fun k => (d.ι.app (op k)).op
      naturality := fun i j g => by
        have h : G.map g.op ≫ d.ι.app (op i) = d.ι.app (op j) := d.w g.op
        simp only [Functor.const_obj_map, Functor.rightOp_map, ← op_comp, h]
        exact Category.id_comp _ }

/-- The cone on the opposite of a diagram of rings read as a cocone on the diagram. -/
private def coneUnop (t : Cone G.rightOp) : Cocone G where
  pt := t.pt.unop
  ι :=
    { app := fun k => (t.π.app k.unop).unop
      naturality := fun i j g => by
        simpa using congrArg Quiver.Hom.unop (t.w g.unop) }

/-- **A colimit of rings is a limit in the opposite category.** -/
private def coconeRightOpIsLimit {d : Cocone G} (hd : IsColimit d) :
    IsLimit (coconeRightOp G d) where
  lift t := (hd.desc (coneUnop G t)).op
  fac t k := Quiver.Hom.unop_inj (by simp [coconeRightOp, coneUnop])
  uniq t m hm := Quiver.Hom.unop_inj
    (hd.uniq (coneUnop G t) m.unop fun k => congrArg Quiver.Hom.unop (hm k.unop))

end LeftOp

/-! ### The residue fields of the images of a point of a limit -/

section Residue

variable {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u}) (c : Cone D) (s : c.pt)

/-- The transition map `κ(sⱼ) ⟶ κ(sᵢ)` between the residue fields at the images of a point of
the limit. -/
private def residueTransition {i j : J} (g : i ⟶ j) :
    (D.obj j).residueField (c.π.app j s) ⟶ (D.obj i).residueField (c.π.app i s) :=
  ((D.obj j).residueFieldCongr (by
    symm
    change (c.π.app i ≫ D.map g) s = _
    rw [c.w g])).hom ≫ (D.map g).residueFieldMap (c.π.app i s)

private lemma residueTransition_comp {i j : J} (g : i ⟶ j) :
    residueTransition D c s g ≫ (c.π.app i).residueFieldMap s =
      (c.π.app j).residueFieldMap s := by
  unfold residueTransition
  rw [Category.assoc, ← Scheme.residueFieldMap_comp]
  exact (Scheme.Hom.residueFieldMap_congr (c.w g).symm s).symm

/-- The diagram of the residue fields at the images of a point of the limit. -/
private def residueDiagram : Jᵒᵖ ⥤ CommRingCat.{u} where
  obj i := (D.obj i.unop).residueField (c.π.app i.unop s)
  map g := residueTransition D c s g.unop
  map_id i := by
    have : Mono ((c.π.app i.unop).residueFieldMap s) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    apply (cancel_mono ((c.π.app i.unop).residueFieldMap s)).mp
    rw [residueTransition_comp, Category.id_comp]
  map_comp {i j k} g h := by
    have : Mono ((c.π.app k.unop).residueFieldMap s) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    apply (cancel_mono ((c.π.app k.unop).residueFieldMap s)).mp
    rw [Category.assoc, residueTransition_comp, residueTransition_comp, residueTransition_comp]

/-- The cocone of the residue fields at the images of a point, with apex the residue field at
that point. -/
private def residueCocone : Cocone (residueDiagram D c s) where
  pt := c.pt.residueField s
  ι :=
    { app := fun i => (c.π.app i.unop).residueFieldMap s
      naturality := fun _ _ g => by
        change residueTransition D c s g.unop ≫ _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact residueTransition_comp D c s g.unop }

/-- **[Stacks, Tag 0CUG]:  the residue field at a point of the limit is the filtered colimit of
the residue fields at its images.** -/
private def residueCoconeIsColimit [IsCofiltered J]
    [∀ {i j : J} (g : i ⟶ j), IsAffineHom (D.map g)] (hc : IsLimit c) :
    IsColimit (residueCocone D c s) := by
  have H := AlgebraicGeometry.residueField_isColimit D c hc s (residueDiagram D c s)
    (fun _ => Iso.refl _) (by intros; simp [residueDiagram, residueTransition])
  refine { desc := ?_, fac := ?_, uniq := ?_ }
  · intro t
    exact (H t.pt (fun i => t.ι.app (op i)) (fun g => t.w g.op)).choose
  · intro t i
    exact (H t.pt (fun i => t.ι.app (op i)) (fun g => t.w g.op)).choose_spec.1 i.unop
  · intro t m hm
    refine (H t.pt (fun i => t.ι.app (op i)) (fun g => t.w g.op)).choose_spec.2 m fun i => ?_
    simp only [Iso.refl_hom]
    exact hm (op i)

/-- The diagram of the spectra of the residue fields at the images of a point of the limit. -/
private def residueSpecDiagram : J ⥤ Scheme.{u} :=
  (residueDiagram D c s).rightOp ⋙ Scheme.Spec

/-- The cone of the spectra of the residue fields at the images of a point of the limit, with
apex the spectrum of the residue field at that point. -/
private def residueSpecCone : Cone (residueSpecDiagram D c s) :=
  Scheme.Spec.mapCone (coconeRightOp (residueDiagram D c s) (residueCocone D c s))

/-- **The spectrum of the residue field at a point of the limit is the limit of the spectra of
the residue fields at its images.** -/
private def residueSpecConeIsLimit [IsCofiltered J]
    [∀ {i j : J} (g : i ⟶ j), IsAffineHom (D.map g)] (hc : IsLimit c) :
    IsLimit (residueSpecCone D c s) :=
  isLimitOfPreserves Scheme.Spec
    (coconeRightOpIsLimit (residueDiagram D c s) (residueCoconeIsColimit D c s hc))

private lemma residueTransition_id (j : J) : residueTransition D c s (𝟙 j) = 𝟙 _ :=
  (residueDiagram D c s).map_id (op j)

private lemma residueTransition_comp_comp {i j k : J} (g : i ⟶ j) (h : j ⟶ k) :
    residueTransition D c s (g ≫ h) =
      residueTransition D c s h ≫ residueTransition D c s g :=
  (residueDiagram D c s).map_comp h.op g.op

private lemma specMap_residueTransition {i j : J} (g : i ⟶ j) :
    Spec.map (residueTransition D c s g) ≫
        (D.obj j).fromSpecResidueField (c.π.app j s) =
      (D.obj i).fromSpecResidueField (c.π.app i s) ≫ D.map g := by
  simp only [residueTransition, Spec.map_comp, Category.assoc,
    Scheme.residueFieldCongr_fromSpecResidueField,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

end Residue

/-! ### The fibre of a limit is the limit of the fibres -/

section Fiber

variable {J : Type u} [Category.{u} J] {A B : J ⥤ Scheme.{u}}

/-- The scheme-theoretic fibre of the stage `j` at the image of `s`. -/
private abbrev fiberObj (φ : A ⟶ B) (cB : Cone B) (s : cB.pt) (j : J) : Scheme.{u} :=
  pullback (φ.app j) ((B.obj j).fromSpecResidueField (cB.π.app j s))

variable (φ : A ⟶ B) (cB : Cone B) (s : cB.pt)

/-- The inclusion of the fibre of the stage `j` into the source. -/
private abbrev fiberIncl (j : J) : fiberObj φ cB s j ⟶ A.obj j := pullback.fst _ _

/-- The structural morphism of the fibre of the stage `j` over its residue field. -/
private abbrev fiberToRes (j : J) :
    fiberObj φ cB s j ⟶ Spec ((B.obj j).residueField (cB.π.app j s)) := pullback.snd _ _

/-- The transition morphism of the diagram of fibres. -/
private def fiberMap {i j : J} (g : i ⟶ j) : fiberObj φ cB s i ⟶ fiberObj φ cB s j :=
  pullback.map _ _ _ _ (A.map g) (Spec.map (residueTransition B cB s g)) (B.map g)
    (φ.naturality g).symm (specMap_residueTransition B cB s g).symm

private lemma fiberMap_fst {i j : J} (g : i ⟶ j) :
    fiberMap φ cB s g ≫ fiberIncl φ cB s j = fiberIncl φ cB s i ≫ A.map g :=
  pullback.lift_fst _ _ _

private lemma fiberMap_snd {i j : J} (g : i ⟶ j) :
    fiberMap φ cB s g ≫ fiberToRes φ cB s j =
      fiberToRes φ cB s i ≫ Spec.map (residueTransition B cB s g) :=
  pullback.lift_snd _ _ _

private lemma fiberMap_id (j : J) : fiberMap φ cB s (𝟙 j) = 𝟙 (fiberObj φ cB s j) := by
  refine pullback.hom_ext ?_ ?_
  · rw [fiberMap_fst, Category.id_comp, A.map_id, Category.comp_id]
  · rw [fiberMap_snd, Category.id_comp, residueTransition_id B cB s, Spec.map_id,
      Category.comp_id]

private lemma fiberMap_comp {i j k : J} (g : i ⟶ j) (h : j ⟶ k) :
    fiberMap φ cB s (g ≫ h) = fiberMap φ cB s g ≫ fiberMap φ cB s h := by
  refine pullback.hom_ext ?_ ?_
  · rw [fiberMap_fst, Category.assoc, fiberMap_fst, ← Category.assoc, fiberMap_fst,
      Category.assoc, A.map_comp]
  · rw [fiberMap_snd, Category.assoc, fiberMap_snd, ← Category.assoc, fiberMap_snd,
      Category.assoc, residueTransition_comp_comp B cB s, Spec.map_comp]

/-- The diagram of the scheme-theoretic fibres of the stages at the images of `s`. -/
private abbrev fiberDiagram : J ⥤ Scheme.{u} :=
  { obj := fiberObj φ cB s
    map := fiberMap φ cB s
    map_id := fiberMap_id φ cB s
    map_comp := fiberMap_comp φ cB s }

/-!
The morphisms below repeat `fiberIncl`, `fiberToRes` and the universal property of the fibres,
with their types phrased through `fiberDiagram` and `residueSpecDiagram`.  This is what makes the
cones over those diagrams rewritable:  a term whose type mentions the fibre both as a pullback
and as a value of the diagram is not type-correct at `implicit` transparency.
-/

/-- The inclusion of the fibre of the stage `j`, as a morphism out of the diagram. -/
private abbrev stageIncl (j : J) : (fiberDiagram φ cB s).obj j ⟶ A.obj j := pullback.fst _ _

/-- The structural morphism over the residue field, as a morphism of the diagrams. -/
private abbrev stageRes (j : J) :
    (fiberDiagram φ cB s).obj j ⟶ (residueSpecDiagram B cB s).obj j := pullback.snd _ _

/-- The morphism from the spectrum of the residue field at the image of `s` in the stage `j`, as
a morphism out of the diagram. -/
private abbrev stageFromSpec (j : J) : (residueSpecDiagram B cB s).obj j ⟶ B.obj j :=
  (B.obj j).fromSpecResidueField (cB.π.app j s)

private lemma stage_condition (j : J) :
    stageIncl φ cB s j ≫ φ.app j = stageRes φ cB s j ≫ stageFromSpec cB s j :=
  pullback.condition

private lemma stage_hom_ext {V : Scheme.{u}} {j : J} {k l : V ⟶ (fiberDiagram φ cB s).obj j}
    (h₁ : k ≫ stageIncl φ cB s j = l ≫ stageIncl φ cB s j)
    (h₂ : k ≫ stageRes φ cB s j = l ≫ stageRes φ cB s j) : k = l :=
  pullback.hom_ext h₁ h₂

/-- The morphism into the fibre of the stage `j` given by its universal property. -/
private def stageLift {V : Scheme.{u}} {j : J} (a : V ⟶ A.obj j)
    (b : V ⟶ (residueSpecDiagram B cB s).obj j)
    (w : a ≫ φ.app j = b ≫ stageFromSpec cB s j) : V ⟶ (fiberDiagram φ cB s).obj j :=
  pullback.lift a b w

private lemma stageLift_incl {V : Scheme.{u}} {j : J} (a : V ⟶ A.obj j)
    (b : V ⟶ (residueSpecDiagram B cB s).obj j)
    (w : a ≫ φ.app j = b ≫ stageFromSpec cB s j) :
    stageLift φ cB s a b w ≫ stageIncl φ cB s j = a :=
  pullback.lift_fst _ _ _

private lemma stageLift_res {V : Scheme.{u}} {j : J} (a : V ⟶ A.obj j)
    (b : V ⟶ (residueSpecDiagram B cB s).obj j)
    (w : a ≫ φ.app j = b ≫ stageFromSpec cB s j) :
    stageLift φ cB s a b w ≫ stageRes φ cB s j = b :=
  pullback.lift_snd _ _ _

private lemma stageMap_incl {i j : J} (g : i ⟶ j) :
    (fiberDiagram φ cB s).map g ≫ stageIncl φ cB s j = stageIncl φ cB s i ≫ A.map g :=
  pullback.lift_fst _ _ _

private lemma stageMap_res {i j : J} (g : i ⟶ j) :
    (fiberDiagram φ cB s).map g ≫ stageRes φ cB s j =
      stageRes φ cB s i ≫ (residueSpecDiagram B cB s).map g :=
  pullback.lift_snd _ _ _

/-- The morphism from the spectrum of the residue field at `s`, as a morphism out of the apex of
the cone of residue fields. -/
private abbrev resApexHom : (residueSpecCone B cB s).pt ⟶ cB.pt :=
  cB.pt.fromSpecResidueField s

private lemma resApexHom_comp (j : J) :
    resApexHom cB s ≫ cB.π.app j =
      (residueSpecCone B cB s).π.app j ≫ stageFromSpec cB s j :=
  ((cB.π.app j).SpecMap_residueFieldMap_fromSpecResidueField s).symm

variable (cA : Cone A) (p : cA.pt ⟶ cB.pt)

/-- The scheme-theoretic fibre of the morphism `p` into the apex of the cone. -/
private abbrev limFiberObj : Scheme.{u} := pullback p (resApexHom cB s)

/-- The inclusion of the fibre of `p`. -/
private abbrev limIncl : limFiberObj cB s cA p ⟶ cA.pt := pullback.fst _ _

/-- The structural morphism of the fibre of `p` over the residue field at `s`. -/
private abbrev limRes : limFiberObj cB s cA p ⟶ (residueSpecCone B cB s).pt := pullback.snd _ _

private lemma lim_condition : limIncl cB s cA p ≫ p = limRes cB s cA p ≫ resApexHom cB s :=
  pullback.condition

private lemma lim_hom_ext {V : Scheme.{u}} {k l : V ⟶ limFiberObj cB s cA p}
    (h₁ : k ≫ limIncl cB s cA p = l ≫ limIncl cB s cA p)
    (h₂ : k ≫ limRes cB s cA p = l ≫ limRes cB s cA p) : k = l :=
  pullback.hom_ext h₁ h₂

/-- The morphism into the fibre of `p` given by its universal property. -/
private def limLift {V : Scheme.{u}} (a : V ⟶ cA.pt) (b : V ⟶ (residueSpecCone B cB s).pt)
    (w : a ≫ p = b ≫ resApexHom cB s) : V ⟶ limFiberObj cB s cA p :=
  pullback.lift a b w

private lemma limLift_incl {V : Scheme.{u}} (a : V ⟶ cA.pt)
    (b : V ⟶ (residueSpecCone B cB s).pt) (w : a ≫ p = b ≫ resApexHom cB s) :
    limLift cB s cA p a b w ≫ limIncl cB s cA p = a :=
  pullback.lift_fst _ _ _

private lemma limLift_res {V : Scheme.{u}} (a : V ⟶ cA.pt)
    (b : V ⟶ (residueSpecCone B cB s).pt) (w : a ≫ p = b ≫ resApexHom cB s) :
    limLift cB s cA p a b w ≫ limRes cB s cA p = b :=
  pullback.lift_snd _ _ _

section ConeData

variable (hp : ∀ j, cA.π.app j ≫ φ.app j = p ≫ cB.π.app j)

include hp

/-- The morphism from the fibre of the limit to the fibre of the stage `j`. -/
private def fiberConeMap (j : J) :
    limFiberObj cB s cA p ⟶ (fiberDiagram φ cB s).obj j :=
  stageLift φ cB s (limIncl cB s cA p ≫ cA.π.app j)
    (limRes cB s cA p ≫ (residueSpecCone B cB s).π.app j) (by
      rw [Category.assoc, hp j, ← Category.assoc, lim_condition, Category.assoc,
        resApexHom_comp, ← Category.assoc])

private lemma fiberConeMap_incl (j : J) :
    fiberConeMap φ cB s cA p hp j ≫ stageIncl φ cB s j = limIncl cB s cA p ≫ cA.π.app j :=
  stageLift_incl _ _ _ _ _ _

private lemma fiberConeMap_res (j : J) :
    fiberConeMap φ cB s cA p hp j ≫ stageRes φ cB s j =
      limRes cB s cA p ≫ (residueSpecCone B cB s).π.app j :=
  stageLift_res _ _ _ _ _ _

private lemma fiberConeMap_naturality {i j : J} (g : i ⟶ j) :
    fiberConeMap φ cB s cA p hp i ≫ (fiberDiagram φ cB s).map g =
      fiberConeMap φ cB s cA p hp j := by
  refine stage_hom_ext φ cB s ?_ ?_
  · rw [Category.assoc, stageMap_incl, ← Category.assoc, fiberConeMap_incl, fiberConeMap_incl,
      Category.assoc, cA.w g]
  · rw [Category.assoc, stageMap_res, ← Category.assoc, fiberConeMap_res, fiberConeMap_res,
      Category.assoc, (residueSpecCone B cB s).w g]

/-- The cone of the fibres of the stages, with apex the fibre of the limit. -/
private def fiberCone : Cone (fiberDiagram φ cB s) where
  pt := limFiberObj cB s cA p
  π :=
    { app := fiberConeMap φ cB s cA p hp
      naturality := fun _ _ g =>
        (Category.id_comp _).trans (fiberConeMap_naturality φ cB s cA p hp g).symm }

private lemma fiberCone_π (j : J) :
    (fiberCone φ cB s cA p hp).π.app j = fiberConeMap φ cB s cA p hp j := rfl

omit hp

/-- The cone on the diagram of sources attached to a cone on the diagram of fibres. -/
private def fiberConeLeft (t : Cone (fiberDiagram φ cB s)) : Cone A where
  pt := t.pt
  π :=
    { app := fun j => t.π.app j ≫ stageIncl φ cB s j
      naturality := fun i j g => by
        have h : t.π.app i ≫ (fiberDiagram φ cB s).map g = t.π.app j := t.w g
        refine (Category.id_comp _).trans ?_
        rw [← h, Category.assoc, stageMap_incl, Category.assoc] }

private lemma fiberConeLeft_π (t : Cone (fiberDiagram φ cB s)) (j : J) :
    (fiberConeLeft φ cB s t).π.app j = t.π.app j ≫ stageIncl φ cB s j := rfl

/-- The cone on the diagram of spectra of residue fields attached to a cone on the diagram of
fibres. -/
private def fiberConeRes (t : Cone (fiberDiagram φ cB s)) :
    Cone (residueSpecDiagram B cB s) where
  pt := t.pt
  π :=
    { app := fun j => t.π.app j ≫ stageRes φ cB s j
      naturality := fun i j g => by
        have h : t.π.app i ≫ (fiberDiagram φ cB s).map g = t.π.app j := t.w g
        refine (Category.id_comp _).trans ?_
        rw [← h, Category.assoc, stageMap_res, Category.assoc] }

private lemma fiberConeRes_π (t : Cone (fiberDiagram φ cB s)) (j : J) :
    (fiberConeRes φ cB s t).π.app j = t.π.app j ≫ stageRes φ cB s j := rfl

include hp in
private lemma fiberConeSquare (hA : IsLimit cA) (hB : IsLimit cB)
    (hR : IsLimit (residueSpecCone B cB s)) (t : Cone (fiberDiagram φ cB s)) :
    hA.lift (fiberConeLeft φ cB s t) ≫ p =
      hR.lift (fiberConeRes φ cB s t) ≫ resApexHom cB s := by
  refine hB.hom_ext fun j => ?_
  have hl : (hA.lift (fiberConeLeft φ cB s t) ≫ p) ≫ cB.π.app j =
      t.π.app j ≫ stageRes φ cB s j ≫ stageFromSpec cB s j :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => hA.lift (fiberConeLeft φ cB s t) ≫ z) (hp j).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ φ.app j)
              ((hA.fac (fiberConeLeft φ cB s t) j).trans (fiberConeLeft_π φ cB s t j))).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun z => t.π.app j ≫ z) (stage_condition φ cB s j))))))
  have hr : (hR.lift (fiberConeRes φ cB s t) ≫ resApexHom cB s) ≫ cB.π.app j =
      t.π.app j ≫ stageRes φ cB s j ≫ stageFromSpec cB s j :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => hR.lift (fiberConeRes φ cB s t) ≫ z) (resApexHom_comp cB s j)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ stageFromSpec cB s j)
              ((hR.fac (fiberConeRes φ cB s t) j).trans (fiberConeRes_π φ cB s t j))).trans
            (Category.assoc _ _ _))))
  exact hl.trans hr.symm

include hp in
/-- **The fibre of a limit is the limit of the fibres.**  The fibre of the morphism `p` induced
on the apexes is the limit of the fibres of the stages, at the images of the point `s`. -/
private def fiberConeIsLimit (hA : IsLimit cA) (hB : IsLimit cB)
    (hR : IsLimit (residueSpecCone B cB s)) : IsLimit (fiberCone φ cB s cA p hp) where
  lift t := limLift cB s cA p (hA.lift (fiberConeLeft φ cB s t))
    (hR.lift (fiberConeRes φ cB s t)) (fiberConeSquare φ cB s cA p hp hA hB hR t)
  fac t j := by
    refine stage_hom_ext φ cB s ?_ ?_
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => limLift cB s cA p (hA.lift (fiberConeLeft φ cB s t))
              (hR.lift (fiberConeRes φ cB s t))
              (fiberConeSquare φ cB s cA p hp hA hB hR t) ≫ z)
            (fiberConeMap_incl φ cB s cA p hp j)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ cA.π.app j)
                (limLift_incl cB s cA p _ _
                  (fiberConeSquare φ cB s cA p hp hA hB hR t))).trans
              ((hA.fac (fiberConeLeft φ cB s t) j).trans (fiberConeLeft_π φ cB s t j)))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => limLift cB s cA p (hA.lift (fiberConeLeft φ cB s t))
              (hR.lift (fiberConeRes φ cB s t))
              (fiberConeSquare φ cB s cA p hp hA hB hR t) ≫ z)
            (fiberConeMap_res φ cB s cA p hp j)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ (residueSpecCone B cB s).π.app j)
                (limLift_res cB s cA p _ _
                  (fiberConeSquare φ cB s cA p hp hA hB hR t))).trans
              ((hR.fac (fiberConeRes φ cB s t) j).trans (fiberConeRes_π φ cB s t j)))))
  uniq t m hm := by
    refine lim_hom_ext cB s cA p ?_ ?_
    · refine Eq.trans (hA.uniq (fiberConeLeft φ cB s t) (m ≫ limIncl cB s cA p) fun j => ?_)
        (limLift_incl cB s cA p _ _ (fiberConeSquare φ cB s cA p hp hA hB hR t)).symm
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => m ≫ z) (fiberConeMap_incl φ cB s cA p hp j).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ stageIncl φ cB s j) (hm j)).trans
              (fiberConeLeft_π φ cB s t j).symm)))
    · refine Eq.trans (hR.uniq (fiberConeRes φ cB s t) (m ≫ limRes cB s cA p) fun j => ?_)
        (limLift_res cB s cA p _ _ (fiberConeSquare φ cB s cA p hp hA hB hR t)).symm
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => m ≫ z) (fiberConeMap_res φ cB s cA p hp j).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ stageRes φ cB s j) (hm j)).trans
              (fiberConeRes_π φ cB s t j).symm)))

end ConeData

end Fiber

/-! ### Descending an idempotent to a stage -/

/-- **An idempotent of a filtered colimit of rings comes from an idempotent at a stage.**  Some
stage carries a preimage, and it is idempotent at a later stage because the difference of its
square and itself dies in the colimit. -/
private lemma exists_idempotent_of_isColimit {K : Type u} [Category.{u} K] [IsFiltered K]
    (G : K ⥤ CommRingCat.{u}) {d : Cocone G} (hd : IsColimit d) (e : d.pt)
    (he : IsIdempotentElem e) :
    ∃ (k : K) (a : G.obj k), IsIdempotentElem a ∧ d.ι.app k a = e := by
  obtain ⟨i, a, ha⟩ := Concrete.isColimit_exists_rep G hd e
  have ha' : d.ι.app i (a * a) = d.ι.app i a := by
    rw [map_mul, ha]
    exact he
  obtain ⟨j, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget _) hd)
      (a * a) a).mp ha'
  refine ⟨j, G.map g a, ?_, (ConcreteCategory.congr_hom (d.w g) a).trans ha⟩
  change G.map g a * G.map g a = G.map g a
  change G.map g (a * a) = G.map g a at hg
  simpa only [map_mul] using hg

/-- **An idempotent global function on a cofiltered limit of schemes with affine transition
morphisms comes from an idempotent at a stage.** -/
private lemma exists_idempotent_appTop_of_isLimit {K : Type u} [Category.{u} K] [IsCofiltered K]
    (E : K ⥤ Scheme.{u}) (d : Cone E) (hd : IsLimit d)
    [∀ {i j : K} (g : i ⟶ j), IsAffineHom (E.map g)]
    [∀ k, CompactSpace (E.obj k)] [∀ k, QuasiSeparatedSpace (E.obj k)]
    (e : Γ(d.pt, ⊤)) (he : IsIdempotentElem e) :
    ∃ (k : K) (a : Γ(E.obj k, ⊤)), IsIdempotentElem a ∧ (d.π.app k).appTop a = e := by
  obtain ⟨h⟩ := nonempty_isColimit_Γ_mapCocone E d hd
  obtain ⟨k, a, ha, heq⟩ := exists_idempotent_of_isColimit _ h e he
  exact ⟨k.unop, a, ha, heq⟩

/-! ### Transferring an extension along a commuting square -/

private lemma appLE_congr {C D : Scheme.{u}} {q r : C ⟶ D} (hqr : q = r) (V : D.Opens)
    (W : C.Opens) (hq : W ≤ q ⁻¹ᵁ V) (hr : W ≤ r ⁻¹ᵁ V) :
    q.appLE V W hq = r.appLE V W hr := by
  subst hqr
  rfl

/-- A section on `Y` over `U` restricts to the fibre `G` along `ι'`, and its image under `k` is its
restriction to `F` through `X` when `k ≫ ι' = ι ≫ a` and the fibres lie over the opens. -/
private lemma appTop_appLE_comm_of_fiber {X Y F G : Scheme.{u}} (ι : F ⟶ X) (ι' : G ⟶ Y)
    (a : X ⟶ Y) (k : F ⟶ G) (hk : k ≫ ι' = ι ≫ a) (U : Y.Opens) (W : X.Opens) (hV : W ≤ a ⁻¹ᵁ U)
    (hW : ι ⁻¹ᵁ W = ⊤) (hU : ι' ⁻¹ᵁ U = ⊤) (v : Γ(Y, U)) :
    k.appTop (ι'.appLE U ⊤ hU.ge v) = ι.appLE W ⊤ hW.ge (a.appLE U W hV v) := by
  have H₁ := Scheme.Hom.appLE_comp_appLE ι a U W ⊤ hV hW.ge
  have H₂ := Scheme.Hom.appLE_comp_appLE k ι' U ⊤ ⊤ hU.ge le_top
  have Htop : k.appLE ⊤ ⊤ le_top = k.appTop := k.appLE_eq_app
  rw [Htop, appLE_congr hk] at H₂
  · exact (ConcreteCategory.congr_hom H₂ v).trans (ConcreteCategory.congr_hom H₁ v).symm
  · exact hW.ge.trans (by rw [Scheme.Hom.comp_preimage]; exact ι.preimage_mono hV)

/-- **A commuting square carries the extension property from the bottom morphism to the top
one.**  A section over `g ⁻¹ᵁ U` pulls back to a section over `f ⁻¹ᵁ (b ⁻¹ᵁ U)`, and the fibre
comparison `k` carries the function on the fibre of `g` to the function on the fibre of `f`. -/
public theorem extendsOverNeighbourhood_of_commSq {X S Y T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ T)
    (a : X ⟶ Y) (b : S ⟶ T) (h : a ≫ g = f ≫ b) (s : S)
    (k : f.fiber s ⟶ g.fiber (b s)) (hk : k ≫ g.fiberι (b s) = f.fiberι s ≫ a)
    (e : Γ(g.fiber (b s), ⊤)) (hext : ExtendsOverNeighbourhood g (b s) e) :
    ExtendsOverNeighbourhood f s (k.appTop e) := by
  obtain ⟨U, hsU, v, hv⟩ := hext
  have hV : f ⁻¹ᵁ (b ⁻¹ᵁ U) ≤ a ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage a g, h, Scheme.Hom.comp_preimage]
  have hbs : s ∈ b ⁻¹ᵁ U := hsU
  refine ⟨b ⁻¹ᵁ U, hbs, a.appLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ (b ⁻¹ᵁ U)) hV v, ?_⟩
  rw [← hv]
  exact (appTop_appLE_comm_of_fiber (f.fiberι s) (g.fiberι (b s)) a k hk _ _ hV
    (fiberι_preimage_preimage_eq_top f hbs) (fiberι_preimage_preimage_eq_top g hsU) v).symm

/-! ### Reduction to an affine base -/

private lemma appLE_surjective_of_eq {C D : Scheme.{u}} (q : C ⟶ D) (V V' : D.Opens)
    (W : C.Opens) (hVV' : V = V') (hV : W ≤ q ⁻¹ᵁ V) (hV' : W ≤ q ⁻¹ᵁ V')
    (hs : Function.Surjective (q.appLE V W hV)) : Function.Surjective (q.appLE V' W hV') := by
  subst hVV'
  exact hs

/-- **The extension property is local on the base.**  If the square is a pullback whose vertical
maps are open immersions, then an idempotent on a fibre of `f` extends over a neighbourhood as
soon as every idempotent on the corresponding fibre of `g` does:  the open of `T` produced for
`g` has an open image in `S`, and the section over `g ⁻¹ᵁ V` is a section over its image by the
isomorphism of sections along an open immersion. -/
public theorem extendsOverNeighbourhood_of_isPullback {X S Y T : Scheme.{u}} {f : X ⟶ S}
    {g : Y ⟶ T} {a : Y ⟶ X} {b : T ⟶ S} [IsOpenImmersion a] [IsOpenImmersion b]
    (H : IsPullback g a b f) (t : T) (e : Γ(f.fiber (b t), ⊤)) (he : IsIdempotentElem e)
    (hg : ∀ e' : Γ(g.fiber t, ⊤), IsIdempotentElem e' → ExtendsOverNeighbourhood g t e') :
    ExtendsOverNeighbourhood f (b t) e := by
  let k : g.fiber t ⟶ f.fiber (b t) :=
    pullback.map g (T.fromSpecResidueField t) f (S.fromSpecResidueField (b t)) a
      (Spec.map (b.residueFieldMap t)) b H.w
      (b.SpecMap_residueFieldMap_fromSpecResidueField t).symm
  have hk : k ≫ f.fiberι (b t) = g.fiberι t ≫ a := pullback.lift_fst _ _ _
  have : IsIso k :=
    (isPullback_fiberToSpecResidueField_of_isPullback H.flip t).isIso_fst_of_isIso
  obtain ⟨V, ht, z, hz⟩ := hg (k.appTop e) (he.map _)
  have hsU : b t ∈ b ''ᵁ V := ⟨t, ht, rfl⟩
  have hOpen : a ''ᵁ (g ⁻¹ᵁ V) = f ⁻¹ᵁ (b ''ᵁ V) :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H V
  have hle : g ⁻¹ᵁ V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ (b ''ᵁ V)) := by
    intro x hx
    change f (a x) ∈ b ''ᵁ V
    rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
    exact ⟨g x, hx, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Γ(X, f ⁻¹ᵁ (b ''ᵁ V)),
      a.appLE (f ⁻¹ᵁ (b ''ᵁ V)) (g ⁻¹ᵁ V) hle w = z := by
    refine appLE_surjective_of_eq a (a ''ᵁ (g ⁻¹ᵁ V)) (f ⁻¹ᵁ (b ''ᵁ V)) (g ⁻¹ᵁ V) hOpen
      (a.preimage_image_eq _).ge hle ?_ z
    have hh := (ConcreteCategory.bijective_of_isIso (a.appIso (g ⁻¹ᵁ V)).hom).2
    rwa [Scheme.Hom.appIso_hom'] at hh
  refine ⟨b ''ᵁ V, hsU, w, ?_⟩
  have : IsIso k.appTop := inferInstanceAs (IsIso (Scheme.Γ.map k.op))
  apply (ConcreteCategory.bijective_of_isIso k.appTop).1
  rw [← hz, ← hw]
  exact appTop_appLE_comm_of_fiber (g.fiberι t) (f.fiberι (b t)) a k hk _ _ hle
    (fiberι_preimage_preimage_eq_top g ht) (fiberι_preimage_preimage_eq_top f hsU) w

/-! ### The reduction of [Stacks, Tag 0G7X] to the locally Noetherian case -/

/-- **[Stacks, Tag 0G7X] over a quasi-compact and quasi-separated base, granted the locally
Noetherian case.**  [Stacks, Tag 0A0P] writes `f` as the limit of proper morphisms whose targets
are of finite type over `Spec ℤ`, hence locally Noetherian;  the fibre of `f` is the limit of the
fibres of those morphisms, so the idempotent comes from one of them. -/
private theorem extendsOverNeighbourhood_of_noetherianCase_of_qcqs
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S] (s : S)
    (hNoe : ∀ {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g] [IsLocallyNoetherian W] (t : W)
      (c : Γ(g.fiber t, ⊤)), IsIdempotentElem c → ExtendsOverNeighbourhood g t c)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ExtendsOverNeighbourhood f s e := by
  obtain ⟨I, hI, hne, hdir, D, c, hproper, hftype, haff, ⟨hc⟩, ⟨iso⟩⟩ :=
    AlgebraicGeometry.exists_isLimit_isProper_finiteType_arrow f
  let := hI
  let := hne
  let := hdir
  have : IsCofilteredOrEmpty Iᵒᵖ := AlgebraicGeometry.isCofilteredOrEmpty_opposite_of_isDirected
  have : Nonempty Iᵒᵖ := Nonempty.map op hne
  have : IsCofiltered Iᵒᵖ := ⟨⟩
  have haffl : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom ((D ⋙ Arrow.leftFunc).map g) :=
    fun g => (haff g).1
  have haffr : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom ((D ⋙ Arrow.rightFunc).map g) :=
    fun g => (haff g).2
  -- the same limit, with the arrow `f` itself as its apex
  let c' : Cone D :=
    { pt := Arrow.mk f
      π :=
        { app := fun j => iso.inv ≫ c.π.app j
          naturality := fun i j g =>
            (Category.id_comp _).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun z => iso.inv ≫ z) (c.w g))).symm } }
  have hc' : IsLimit c' := hc.ofIsoLimit (Cone.ext iso fun j => by simp [c'])
  let φ : (D ⋙ Arrow.leftFunc) ⟶ (D ⋙ Arrow.rightFunc) :=
    { app := fun j => (D.obj j).hom
      naturality := fun _ _ g => (D.map g).w }
  have hp : ∀ j, (Arrow.leftFunc.mapCone c').π.app j ≫ φ.app j =
      f ≫ (Arrow.rightFunc.mapCone c').π.app j := fun j => (c'.π.app j).w
  have hA := isLimitLeftFuncMapCone D c' hc'
  have hB := isLimitRightFuncMapCone D c' hc'
  have hR := residueSpecConeIsLimit (D ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone c') s hB
  have hFib := fiberConeIsLimit φ (Arrow.rightFunc.mapCone c') s
    (Arrow.leftFunc.mapCone c') f hp hA hB hR
  -- the stages of the diagram of fibres are quasi-compact, quasi-separated, and its transition
  -- morphisms are affine
  have hpr : ∀ j, IsProper (D.obj j).hom := hproper
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j),
      IsAffineHom ((fiberDiagram φ (Arrow.rightFunc.mapCone c') s).map g) := fun g =>
    isAffineHom_pullback_map _ _ _ _ ((D ⋙ Arrow.leftFunc).map g)
      (Spec.map (residueTransition (D ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone c') s g))
      ((D ⋙ Arrow.rightFunc).map g) (φ.naturality g).symm
      (specMap_residueTransition (D ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone c') s g).symm
  have : ∀ j, CompactSpace ((fiberDiagram φ (Arrow.rightFunc.mapCone c') s).obj j) := by
    intro j
    exact (quasiCompact_iff_compactSpace (pullback.snd (D.obj j).hom
      ((D.obj j).right.fromSpecResidueField ((c'.π.app j).right s)))).mp inferInstance
  have : ∀ j, QuasiSeparatedSpace ((fiberDiagram φ (Arrow.rightFunc.mapCone c') s).obj j) := by
    intro j
    have hqs : QuasiSeparated (pullback.snd (D.obj j).hom
        ((D.obj j).right.fromSpecResidueField ((c'.π.app j).right s))) :=
      MorphismProperty.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback _ _) inferInstance
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd (D.obj j).hom
      ((D.obj j).right.fromSpecResidueField ((c'.π.app j).right s))) inferInstance hqs
  -- the idempotent comes from a stage
  obtain ⟨j, a, ha, heq⟩ := exists_idempotent_appTop_of_isLimit
    (fiberDiagram φ (Arrow.rightFunc.mapCone c') s)
    (fiberCone φ (Arrow.rightFunc.mapCone c') s (Arrow.leftFunc.mapCone c') f hp) hFib e he
  -- the stage is proper over a locally Noetherian base, so the hypothesis applies there
  have : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
    have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
    exact LocallyOfFiniteType.isLocallyNoetherian
      (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal).hom
  have : LocallyOfFiniteType (terminal.from (D.obj j).right) := (hftype j).1
  have : IsLocallyNoetherian ((D.obj j).right) :=
    LocallyOfFiniteType.isLocallyNoetherian (terminal.from (D.obj j).right)
  have hk : fiberConeMap φ (Arrow.rightFunc.mapCone c') s (Arrow.leftFunc.mapCone c') f hp j ≫
      (D.obj j).hom.fiberι ((c'.π.app j).right s) = f.fiberι s ≫ (c'.π.app j).left :=
    fiberConeMap_incl φ (Arrow.rightFunc.mapCone c') s (Arrow.leftFunc.mapCone c') f hp j
  have hfinal := extendsOverNeighbourhood_of_commSq f (D.obj j).hom (c'.π.app j).left
    (c'.π.app j).right (c'.π.app j).w s _ hk a (hNoe (D.obj j).hom ((c'.π.app j).right s) a ha)
  rw [← heq]
  exact hfinal

/-- **[Stacks, Tag 0G7X] granted its locally Noetherian case.**  An idempotent global function on
a fibre of a proper morphism is the restriction of a section of the structure sheaf over the
inverse image of an open neighbourhood of the base point, provided the same holds over every
locally Noetherian base.  The base is replaced by an affine open neighbourhood of the point,
which is legitimate because the conclusion is local on the base, and then
[Stacks, Tag 0A0P] applies. -/
public theorem extendsOverNeighbourhood_of_noetherianCase
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S)
    (hNoe : ∀ {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g] [IsLocallyNoetherian W] (t : W)
      (c : Γ(g.fiber t, ⊤)), IsIdempotentElem c → ExtendsOverNeighbourhood g t c)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ExtendsOverNeighbourhood f s e := by
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top s)
  have : IsAffine (U : Scheme.{u}) := hU
  have H : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := isPullback_morphismRestrict f U
  have : IsProper (f ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsProper) H.flip inferInstance
  exact extendsOverNeighbourhood_of_isPullback H ⟨s, hs⟩ e he fun e' he' =>
    extendsOverNeighbourhood_of_noetherianCase_of_qcqs (f ∣_ U) ⟨s, hs⟩ hNoe e' he'

/-- **[Stacks, Tag 0G7X].**  An idempotent global function on a fibre of a proper morphism is the
restriction of a section of the structure sheaf over the inverse image of an open neighbourhood
of the base point;  equivalently, it lies in the image of the stalk `(f_* 𝒪_X)_s`.  Nothing is
assumed on the base:  its locally Noetherian case is
`Stacks.FormalFunctions.extendsOverNeighbourhood_of_isLocallyNoetherian`, and the general case
follows from it by the approximation argument above. -/
@[stacks 0G7X]
public theorem extendsOverNeighbourhood_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (s : S) (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ExtendsOverNeighbourhood f s e := by
  refine extendsOverNeighbourhood_of_noetherianCase f s ?_ e he
  intro V W g _ _ t c hc
  exact Stacks.FormalFunctions.extendsOverNeighbourhood_of_isLocallyNoetherian g t c hc

end Stacks.AlgebraicGeometry.Fibres

end
