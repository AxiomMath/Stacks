module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageWitnessPoints
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceProper
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitWitnessHom
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitWitnessHomRestriction
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessOfProper
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement

/-!
# A witness of a limit element descended to a finite stage

In the proof of Stacks 0GI5 (surjectivity, "descending a witness"), an element
`ξ = (Z, u', x̂)` of `F(V)` over a limit `V = lim V_k` of Noetherian affine schemes, with witness
`p : V' ⟶ V`, `x'`, is descended to a stage: a closed `Z_k ⊆ |V_k|` with inverse image `Z`, a
proper `q_k : V'_k ⟶ V_k` with base change `V'`, an isomorphism over `V_k ∖ Z_k`, and
`x'_k : V'_k ⟶ X'` restricting to `x'`, which carries `|q_k|⁻¹ Z_k` exactly onto the inverse
image of `T'`, so that it restricts to a morphism `u'_k : V_k ∖ Z_k ⟶ U'` lifting `u'`.

This is all of the data of the stage element except its formal component; with a formal
component `x̂_k` satisfying the compatibility `x̂_k ∘ q_{k,/Z_k} = g ∘ x'_{k,/Z_k}`, the data is a
witness of an element of `F(V_k)` by
`AlgebraicGeometry.Artin.ContractionSituation.nonempty_compatibilityWitness_of_isProper`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.StageWitness`: the descended data at a stage, with
  its base change `AlgebraicGeometry.Artin.ContractionSituation.StageWitness.baseChange` to later
  stages and the morphism `u'_j` (`AlgebraicGeometry.Artin.ContractionSituation.StageWitness.u`,
  restricting to `u'` by `AlgebraicGeometry.Artin.ContractionSituation.StageWitness.restrict_u`).
* `AlgebraicGeometry.Artin.ContractionSituation.exists_stageWitness`: a stage witness exists.
* `AlgebraicGeometry.Artin.ContractionSituation.StageWitness.exists_mapTriple_eq`: a stage witness
  with a compatible adic formal component restricting to `x̂` gives an element of `F(V_j)`
  restricting to `ξ`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_stage_of_stageWitness`: the surjectivity
  of the limit preservation from the formal component at a stage.
* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.preimage_p_eq_preimage_x'`:
  for a witness, `|p|⁻¹ Z = |x'|⁻¹ T'`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An isomorphism over the complement of `Z` is stable under base change** along a morphism
of the site: if `q : Y ⟶ V_j` is an isomorphism over `V_j ∖ Z`, then `V_k ×_{V_j} Y ⟶ V_k` is an
isomorphism over the complement of the inverse image of `Z`. -/
theorem isIso_pullback_snd_ι_pullback_fst {Vj Vk : BigFppfOver B S hS} (g : Vk ⟶ Vj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y ⟶ yoneda.obj Vj)
    {Z : Set (points B S hS (yoneda.obj Vj))}
    (h : IsIso (pullback.snd q (openSubspaceOfPoints B S hS (yoneda.obj Vj) Zᶜ).ι)) :
    IsIso (pullback.snd (pullback.fst (yoneda.map g) q)
      (openSubspaceOfPoints B S hS (yoneda.obj Vk)
        (pointsMap B S hS _ (yoneda.map g) ⁻¹' Z)ᶜ).ι) := by
  rw [isIso_pullback_snd_ι_iff_existsUnique] at h ⊢
  intro W w
  let r := openSubspaceOfPointsRestrict B S hS (yoneda.map g)
    (pointsMap B S hS _ (yoneda.map g) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz)
  obtain ⟨y₀, hy₀, hu₀⟩ := h W (w ≫ r)
  refine ⟨pullback.lift (w ≫ (openSubspaceOfPoints B S hS (yoneda.obj Vk)
      (pointsMap B S hS _ (yoneda.map g) ⁻¹' Z)ᶜ).ι) y₀ (by
        rw [hy₀, Category.assoc, Category.assoc]; rfl),
    pullback.lift_fst _ _ _, fun y' hy' => ?_⟩
  refine pullback.hom_ext (by rwa [pullback.lift_fst]) ?_
  rw [pullback.lift_snd]
  refine hu₀ _ ?_
  beta_reduce
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hy', Category.assoc,
    Category.assoc]
  rfl

/-- An isomorphism over a subfunctor transports along an isomorphism of the sources over the
base. -/
theorem isIso_pullback_snd_ι_of_iso {V : BigFppfOver B S hS}
    {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y ⟶ yoneda.obj V) (e : Y' ≅ Y)
    (q' : Y' ⟶ yoneda.obj V) (hq : e.hom ≫ q = q')
    (U : Subfunctor (yoneda.obj V)) (h : IsIso (pullback.snd q U.ι)) :
    IsIso (pullback.snd q' U.ι) := by
  subst hq
  rw [isIso_pullback_snd_ι_iff_existsUnique] at h ⊢
  intro W w
  obtain ⟨y₀, hy₀, hu₀⟩ := h W w
  refine ⟨y₀ ≫ e.inv, by beta_reduce; rw [Category.assoc, e.inv_hom_id_assoc, hy₀],
    fun y' hy' => ?_⟩
  beta_reduce at hy'
  rw [← hu₀ (y' ≫ e.hom) (by beta_reduce; rw [Category.assoc, hy']), Category.assoc,
    e.hom_inv_id, Category.comp_id]

/-- A proper morphism to a locally Noetherian scheme is locally of finite presentation. -/
private theorem isLocallyOfFinitePresentation_of_isProper_yoneda {V : LocallyNoetherianOver B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {q : Y ⟶ yoneda.obj V.obj} (hq : IsProper B S hS q) :
    IsLocallyOfFinitePresentation B S hS q :=
  isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hY
    (isAlgebraicSpace_yoneda B S hS _) q
    (hasEtaleLocalProperty_of_representable B S hS _
      (fun T : Scheme.{u} => AlgebraicGeometry.IsLocallyNoetherian T) _ (Iso.refl _)
      V.property) hq.2.1.1

variable (B S hS) in
/-- The terminal sheaf is limit preserving. -/
private theorem limitPreserving_terminal : LimitPreserving.{u, u, u, u, u + 1, u}
    (BigFppfOver.toScheme B S hS) (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  (isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS
    (isAlgebraicSpace_terminal B S hS)).1 (by
      rw [show terminal.from (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) = 𝟙 _ from
        terminal.hom_ext _ _]
      exact isLocallyOfFinitePresentation_id B S hS (isAlgebraicSpace_terminal B S hS))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {c : ContractionSituation B S hS}

/-- **For a witness of compatibility, `|p|⁻¹ Z = |x'|⁻¹ T'`.** A point of `V'` over `Z` is
carried into `T'` by `x'` (it lies in `V'_{/Z}`, which `x̂'` maps to `X'_{/T'}`), and a point of
`V'` outside the inverse image of `Z` comes from `V ∖ Z`, on which `x'` is `u' : V ∖ Z ⟶ U'`. -/
theorem CompatibilityWitness.preimage_p_eq_preimage_x' {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))}
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    (w : CompatibilityWitness c V Z u xhat) :
    Space.pointsMap B S hS w.V' w.p ⁻¹' Z = Space.pointsMap B S hS w.V' w.x' ⁻¹' c.T' := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · induction y using Quot.ind with | _ q => ?_
    rw [Set.mem_preimage, Space.pointsMap_class] at hy ⊢
    exact w.class_map_witnessMap_mem_closedSubset _ hy
  · by_contra hz
    obtain ⟨o, ho⟩ : Space.pointsMap B S hS w.V' w.p y ∈
        Set.range (Space.pointsMap B S hS _
          (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι) := by
      rwa [Space.range_pointsMap_ι_openSubspaceOfPoints]
    obtain ⟨o', -, ho'⟩ := Space.exists_points_of_isPullback B S hS w.isPullback_j o y ho
    have hT : Space.pointsMap B S hS w.V' w.x' y ∈
        Set.range (Space.pointsMap B S hS c.U'.toFunctor c.U'.ι) := by
      rw [← ho', ← Space.pointsMap_comp_apply, w.restrict_x', Space.pointsMap_comp_apply]
      exact ⟨_, rfl⟩
    rw [range_pointsMap_ι_U'] at hT
    exact hT hy

/-! ### Descended models of a witness -/

section Model

variable (c) {I : Type u} [Category.{u} I] {D : I ⥤ LocallyNoetherianOver B S hS} (κ : Cone D)
  (ξ : Triple c κ.pt.obj) (w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat)

/-- A **model at the stage `j`** of the witness `w` of an element `ξ` over the limit of `κ`: a
closed `Z_j ⊆ |V_j|` with inverse image `Z`, and a proper `q : Y ⟶ V_j` whose base change to the
limit is `p : V' ⟶ V`, with second projection `a : V' ⟶ Y`. -/
structure StageModel (j : I) where
  /-- The closed subset `Z_j ⊆ |V_j|`. -/
  Z : Set (Space.points B S hS (yoneda.obj (D.obj j).obj))
  /-- `Z_j` is closed. -/
  isClosed_Z : IsClosed Z
  /-- The inverse image of `Z_j` in `|V|` is `Z`. -/
  preimage_Z : Space.pointsMap B S hS _ (yoneda.map (κ.π.app j).hom) ⁻¹' Z = ξ.Z
  /-- The algebraic space `Y = V'_j`. -/
  Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `Y` is an algebraic space. -/
  isAlgebraicSpace_Y : IsAlgebraicSpace B S hS Y
  /-- The morphism `q : Y ⟶ V_j`. -/
  q : Y ⟶ yoneda.obj (D.obj j).obj
  /-- `q` is proper. -/
  isProper_q : Space.IsProper B S hS q
  /-- The projection `a : V' ⟶ Y`. -/
  a : w.V' ⟶ Y
  /-- `V' = V ×_{V_j} Y`. -/
  isPullback_a : IsPullback w.p a (yoneda.map (κ.π.app j).hom) q

variable {c κ ξ w}

/-- `Z` is contained in the inverse image of `Z_j` in `|V|`. -/
theorem StageModel.subset_preimage_Z {j : I} (M : StageModel c κ ξ w j) :
    ξ.Z ⊆ Space.pointsMap B S hS _ (yoneda.map (κ.π.app j).hom) ⁻¹' M.Z :=
  M.preimage_Z.symm.subset

/-- The complement of `Z` is contained in the inverse image of `|V_j| ∖ Z_j` in `|V|`. -/
theorem StageModel.compl_subset_preimage_compl_Z {j : I} (M : StageModel c κ ξ w j) :
    ξ.Zᶜ ⊆ Space.pointsMap B S hS _ (yoneda.map (κ.π.app j).hom) ⁻¹' M.Zᶜ :=
  (congrArg compl M.preimage_Z).symm.subset

/-- The projections of the cone `κ` commute with the transition morphism `V_k ⟶ V_j`. -/
theorem cone_π_hom_comp {j k : I} (g : k ⟶ j) :
    (κ.π.app k).hom ≫ (D.map g).hom = (κ.π.app j).hom :=
  congrArg (fun φ => φ.hom) (κ.w g)

/-- If `Z ⊆ |V_j|` has inverse image `ξ.Z` in `|V|`, then so does its inverse image in `|V_k|`. -/
theorem preimage_preimage_Z {j k : I} (g : k ⟶ j)
    {Z : Set (Space.points B S hS (yoneda.obj (D.obj j).obj))}
    (hZ : Space.pointsMap B S hS _ (yoneda.map (κ.π.app j).hom) ⁻¹' Z = ξ.Z) :
    Space.pointsMap B S hS _ (yoneda.map (κ.π.app k).hom) ⁻¹'
      (Space.pointsMap B S hS _ (yoneda.map (D.map g).hom) ⁻¹' Z) = ξ.Z := by
  rwa [← Set.preimage_comp, ← Space.pointsMap_comp, ← Functor.map_comp, cone_π_hom_comp]

/-- The base change `V_k ×_{V_j} Y` of a model `Y` of `V'` over `V_j` is a model over `V_k`. -/
theorem isPullback_lift_pullback {j k : I} (g : k ⟶ j) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {q : Y ⟶ yoneda.obj (D.obj j).obj} {a : w.V' ⟶ Y}
    (h : IsPullback w.p a (yoneda.map (κ.π.app j).hom) q) :
    IsPullback w.p (pullback.lift (w.p ≫ yoneda.map (κ.π.app k).hom) a (by
        rw [Category.assoc, ← Functor.map_comp, cone_π_hom_comp]
        exact h.w))
      (yoneda.map (κ.π.app k).hom) (pullback.fst (yoneda.map (D.map g).hom) q) :=
  IsPullback.of_bot (by
      rwa [pullback.lift_snd, ← Functor.map_comp, cone_π_hom_comp])
    (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)

/-- The base change `V_k ×_{V_j} Y ⟶ V_k` of a proper morphism `q : Y ⟶ V_j` is proper. -/
theorem isProper_pullback_fst_yoneda {Vj Vk : BigFppfOver B S hS} (g : Vk ⟶ Vj)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {q : Y ⟶ yoneda.obj Vj} (hq : Space.IsProper B S hS q) :
    Space.IsProper B S hS (pullback.fst (yoneda.map g) q) :=
  Space.isProper_of_isPullback B S hS
    (isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _) hY
      (isAlgebraicSpace_yoneda B S hS _)) hY
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (IsPullback.of_hasPullback _ _).flip hq

/-- The **base change** of a model along a morphism `g : k ⟶ j` of the index category:
`Y_k = V_k ×_{V_j} Y` with the inverse image of `Z_j`. -/
noncomputable def StageModel.baseChange {j k : I} (M : StageModel c κ ξ w j) (g : k ⟶ j) :
    StageModel c κ ξ w k where
  Z := Space.pointsMap B S hS _ (yoneda.map (D.map g).hom) ⁻¹' M.Z
  isClosed_Z := M.isClosed_Z.preimage (Space.continuous_pointsMap B S hS _)
  preimage_Z := preimage_preimage_Z g M.preimage_Z
  Y := pullback (yoneda.map (D.map g).hom) M.q
  isAlgebraicSpace_Y := isAlgebraicSpace_pullback B S hS _ _ (isAlgebraicSpace_yoneda B S hS _)
    M.isAlgebraicSpace_Y (isAlgebraicSpace_yoneda B S hS _)
  q := pullback.fst _ _
  isProper_q := isProper_pullback_fst_yoneda _ M.isAlgebraicSpace_Y M.isProper_q
  a := _
  isPullback_a := isPullback_lift_pullback g M.isPullback_a

/-- The closed subset of the base change is the inverse image of `Z_j` in `|V_k|`. -/
theorem StageModel.baseChange_Z {j k : I} (M : StageModel c κ ξ w j) (g : k ⟶ j) :
    (M.baseChange g).Z = Space.pointsMap B S hS _ (yoneda.map (D.map g).hom) ⁻¹' M.Z := rfl

/-- The projection `Y_k = V_k ×_{V_j} Y ⟶ Y` of the base change. -/
noncomputable def StageModel.baseChangeHom {j k : I} (M : StageModel c κ ξ w j) (g : k ⟶ j) :
    (M.baseChange g).Y ⟶ M.Y :=
  pullback.snd (yoneda.map (D.map g).hom) M.q

/-- The projection `V' ⟶ Y_k` of the base change, followed by `Y_k ⟶ Y`, is `a`. -/
theorem StageModel.baseChange_a_comp {j k : I} (M : StageModel c κ ξ w j) (g : k ⟶ j) :
    (M.baseChange g).a ≫ M.baseChangeHom g = M.a :=
  pullback.lift_snd _ _ _

/-- The square formed by `q_k : Y_k ⟶ V_k`, `q : Y ⟶ V_j` and the projection `Y_k ⟶ Y`
commutes. -/
theorem StageModel.baseChange_q_comp {j k : I} (M : StageModel c κ ξ w j) (g : k ⟶ j) :
    (M.baseChange g).q ≫ yoneda.map (D.map g).hom = M.baseChangeHom g ≫ M.q :=
  pullback.condition

variable (c κ ξ w) in
/-- A **stage witness** at `j` of the witness `w` of `ξ`: a model `q : Y ⟶ V_j` which is an
isomorphism over `V_j ∖ Z_j`, with a morphism `y : Y ⟶ X'` restricting to `x'` over the limit and
with `|q|⁻¹ Z_j = |y|⁻¹ T'`. This is the data of a witness of an element of `F(V_j)` lifting `ξ`
except for its formal component
(`AlgebraicGeometry.Artin.ContractionSituation.StageWitness.exists_mapTriple_eq`). -/
structure StageWitness (j : I) extends StageModel c κ ξ w j where
  /-- `q` is an isomorphism over `V_j ∖ Z_j`. -/
  isIso_q : IsIso (pullback.snd q (Space.openSubspaceOfPoints B S hS _ Zᶜ).ι)
  /-- The morphism `y = x'_j : Y ⟶ X'`. -/
  y : Y ⟶ c.X'
  /-- `y` restricts to `x'` over the limit. -/
  a_y : a ≫ y = w.x'
  /-- `|q|⁻¹ Z_j = |y|⁻¹ T'`. -/
  preimage_q_eq : Space.pointsMap B S hS Y q ⁻¹' Z = Space.pointsMap B S hS Y y ⁻¹' c.T'

namespace StageWitness

variable {j : I} (W : StageWitness c κ ξ w j)

/-- The section `V_j ∖ Z_j ⟶ Y` of `q` over the complement of `Z_j`. -/
noncomputable def jY : (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).toFunctor ⟶ W.Y :=
  haveI := W.isIso_q
  inv (pullback.snd W.q (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι) ≫ pullback.fst _ _

/-- `j_Y` is a section of `q` over `V_j ∖ Z_j`. -/
theorem jY_q : W.jY ≫ W.q = (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι := by
  have := W.isIso_q
  simp [jY, pullback.condition]

/-- `y` maps the inverse image `|q|⁻¹ Z_j` into `T'`. -/
theorem subset_T' : Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z ⊆
    Space.pointsMap B S hS W.Y W.y ⁻¹' c.T' :=
  W.preimage_q_eq.subset

/-- `y ∘ j_Y` maps every point of `V_j ∖ Z_j` outside `T'`. -/
theorem range_pointsMap_jY_y : Set.range (Space.pointsMap B S hS _ (W.jY ≫ W.y)) ⊆ c.T'ᶜ := by
  rintro _ ⟨o, rfl⟩ ho
  rw [Space.pointsMap_comp_apply, ← Set.mem_preimage, ← W.preimage_q_eq, Set.mem_preimage,
    ← Space.pointsMap_comp_apply, jY_q] at ho
  have : Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι o ∈
      Set.range (Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι) :=
    ⟨o, rfl⟩
  rw [Space.range_pointsMap_ι_openSubspaceOfPoints] at this
  exact this ho

/-- The morphism `u'_j : V_j ∖ Z_j ⟶ U'`, the restriction of `y`. -/
noncomputable def u : (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).toFunctor ⟶ c.U'.toFunctor :=
  Subfunctor.lift (G := c.U') (W.jY ≫ W.y) (Space.range_le_openSubspaceOfPoints B S hS _ _
    fun o => W.range_pointsMap_jY_y ⟨o, rfl⟩)

/-- `y ∘ j_Y` is `u'_j` followed by the inclusion `U' ⟶ X'`. -/
theorem jY_y : W.jY ≫ W.y = W.u ≫ c.U'.ι := rfl

/-- The section `j_Y` over the stage restricts over the limit to the section `j` of `p`. -/
theorem restrict_jY : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app j).hom)
    ξ.Zᶜ W.Zᶜ W.compl_subset_preimage_compl_Z ≫ W.jY = w.j ≫ W.a := by
  have := W.isIso_q
  let r := Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app j).hom)
    ξ.Zᶜ W.Zᶜ W.compl_subset_preimage_compl_Z
  have hr : r ≫ (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι =
      (Space.openSubspaceOfPoints B S hS _ ξ.Zᶜ).ι ≫ yoneda.map (κ.π.app j).hom := rfl
  have h₁ : (r ≫ W.jY) ≫ W.q = r ≫ (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι := by
    rw [Category.assoc, jY_q]
  have h₂ : (w.j ≫ W.a) ≫ W.q = r ≫ (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι := by
    rw [Category.assoc, ← W.isPullback_a.w, ← Category.assoc, ← w.isPullback_j.w,
      Category.id_comp, hr]
  have e : pullback.lift _ _ h₁ = pullback.lift _ _ h₂ := by
    rw [← cancel_mono (pullback.snd W.q (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι),
      pullback.lift_snd, pullback.lift_snd]
  have := congrArg (· ≫ pullback.fst W.q (Space.openSubspaceOfPoints B S hS _ W.Zᶜ).ι) e
  rwa [pullback.lift_fst, pullback.lift_fst] at this

/-- `u'_j` restricts to `u'` over the limit. -/
theorem restrict_u : Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app j).hom)
    ξ.Zᶜ W.Zᶜ W.compl_subset_preimage_compl_Z ≫ W.u = ξ.u := by
  rw [← cancel_mono c.U'.ι, Category.assoc, ← jY_y, ← Category.assoc, restrict_jY,
    Category.assoc, W.a_y, w.restrict_x']

/-- **A stage witness with a compatible formal component is a witness at the stage**: given an
adic `x̂_j : V_{j,/Z_j} ⟶ W` with `x̂_j ∘ q_{/Z_j} = g ∘ y_{/Z_j}`, the morphisms `u'_j` and `x̂_j`
are compatible (by
`AlgebraicGeometry.Artin.ContractionSituation.nonempty_compatibilityWitness_of_isProper`). -/
theorem nonempty_compatibilityWitness
    (xhat : Space.completionSheaf B S hS (yoneda.obj (D.obj j).obj) W.Z ⟶ c.W)
    (hxhat : FormalSpace.IsAdicMorphism B S hS xhat)
    (hformal : Space.completionSheafRestrict B S hS W.q (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z)
        W.Z (fun _ hz => hz) ≫ xhat =
      Space.completionSheafRestrict B S hS W.y (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z) c.T'
        W.subset_T' ≫ c.g) :
    Nonempty (CompatibilityWitness c (D.obj j).obj W.Z W.u xhat) :=
  nonempty_compatibilityWitness_of_isProper c (D.obj j).property W.isClosed_Z W.u xhat hxhat
    W.isAlgebraicSpace_Y W.q W.isProper_q W.isIso_q W.jY W.jY_q W.y W.jY_y W.subset_T' hformal

/-- **The element over the limit comes from the stage** as soon as the stage witness has a
compatible adic formal component `x̂_j` restricting to `x̂` over the limit. -/
theorem exists_mapTriple_eq
    (xhat : Space.completionSheaf B S hS (yoneda.obj (D.obj j).obj) W.Z ⟶ c.W)
    (hxhat : FormalSpace.IsAdicMorphism B S hS xhat)
    (hformal : Space.completionSheafRestrict B S hS W.q (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z)
        W.Z (fun _ hz => hz) ≫ xhat =
      Space.completionSheafRestrict B S hS W.y (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z) c.T'
        W.subset_T' ≫ c.g)
    (hres : Space.completionSheafRestrict B S hS (yoneda.map (κ.π.app j).hom) ξ.Z W.Z
        W.subset_preimage_Z ≫ xhat = ξ.xhat) :
    ∃ t : Triple c (D.obj j).obj, mapTriple c (κ.π.app j).hom t = ξ := by
  refine ⟨⟨W.Z, W.isClosed_Z, W.u, xhat, hxhat, W.nonempty_compatibilityWitness xhat hxhat
    hformal⟩, ?_⟩
  have hu : ∀ (A : Set (Space.points B S hS (yoneda.obj κ.pt.obj))) (_ : A = ξ.Z)
      (h : Aᶜ ⊆ Space.pointsMap B S hS _ (yoneda.map (κ.π.app j).hom) ⁻¹' W.Zᶜ),
      HEq (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (κ.π.app j).hom) Aᶜ W.Zᶜ h ≫
        W.u) ξ.u := by
    rintro A rfl h
    exact heq_of_eq W.restrict_u
  have hx : ∀ (A : Set (Space.points B S hS (yoneda.obj κ.pt.obj))) (_ : A = ξ.Z)
      (h : A ⊆ Space.pointsMap B S hS _ (yoneda.map (κ.π.app j).hom) ⁻¹' W.Z),
      HEq (Space.completionSheafRestrict B S hS (yoneda.map (κ.π.app j).hom) A W.Z h ≫ xhat)
        ξ.xhat := by
    rintro A rfl h
    exact heq_of_eq hres
  exact Triple.mk_congr W.preimage_Z (hu _ W.preimage_Z _) (hx _ W.preimage_Z _)

/-- The **base change** of a stage witness along a morphism `g : k ⟶ j` of the index category. -/
noncomputable def baseChange {k : I} (g : k ⟶ j) : StageWitness c κ ξ w k where
  toStageModel := W.toStageModel.baseChange g
  isIso_q := Space.isIso_pullback_snd_ι_pullback_fst (D.map g).hom W.q W.isIso_q
  y := W.toStageModel.baseChangeHom g ≫ W.y
  a_y := by rw [← Category.assoc, StageModel.baseChange_a_comp, W.a_y]
  preimage_q_eq := by
    rw [StageModel.baseChange_Z, ← Set.preimage_comp, ← Space.pointsMap_comp,
      StageModel.baseChange_q_comp, Space.pointsMap_comp, Set.preimage_comp, W.preimage_q_eq,
      ← Set.preimage_comp, ← Space.pointsMap_comp]

end StageWitness

/-- **A point of `V'` lies over `Z_j` exactly when it lies over `T'`**, for a morphism
`y : Y_j ⟶ X'` restricting to `x'`. -/
private theorem StageModel.pointsMap_a_mem_Z_iff {j : I} (M : StageModel c κ ξ w j) {y : M.Y ⟶ c.X'}
    (hy : M.a ≫ y = w.x') (v : Space.points B S hS w.V') :
    Space.pointsMap B S hS _ M.q (Space.pointsMap B S hS _ M.a v) ∈ M.Z ↔
      Space.pointsMap B S hS _ y (Space.pointsMap B S hS _ M.a v) ∈ c.T' := by
  rw [← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply, ← M.isPullback_a.w, hy,
    Space.pointsMap_comp_apply]
  exact (Set.ext_iff.mp M.preimage_Z _).trans (Set.ext_iff.mp w.preimage_p_eq_preimage_x' v)

/-! ### Descending the stage data -/

section Descent

variable [IsCofiltered I]
  (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
include hκ hD

/-- **No point of a later stage maps into the image of a locally closed set of a model** that
no point of `V'` maps into. -/
theorem StageModel.exists_forall_notMem_image {j : I} (M : StageModel c κ ξ w j)
    {O K : Set (Space.points B S hS M.Y)} (hO : IsOpen O) (hK : IsClosed K)
    (h : ∀ v : Space.points B S hS w.V', Space.pointsMap B S hS _ M.a v ∉ O ∩ K) :
    ∃ (k : I) (g : k ⟶ j), ∀ v : Space.points B S hS (yoneda.obj (D.obj k).obj),
      Space.pointsMap B S hS _ (yoneda.map (D.map g).hom) v ∉
        Space.pointsMap B S hS M.Y M.q '' (O ∩ K) := by
  have hqc : Space.IsQuasiCompactSpace B S hS M.Y :=
    Space.isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS (D.obj j).obj (hD j)
      M.isAlgebraicSpace_Y (isAlgebraicSpace_yoneda B S hS _) M.q M.isProper_q.2.2
  refine Space.exists_stage_forall_notMem_image_inter_of_isLimit
    (E := D ⋙ ObjectProperty.ι _) (c := (ObjectProperty.ι _).mapCone κ) hκ hD j
    (D.obj j).property hqc M.q M.isProper_q.2.1.1 hO hK ?_
  rintro v ⟨t, ht, htv⟩
  obtain ⟨v', -, hv'⟩ := Space.exists_points_of_isPullback B S hS M.isPullback_a v t htv.symm
  exact h v' (hv' ▸ ht)

/-- **`|q|⁻¹ Z_k = |y|⁻¹ T'` at a later stage**: the two sides agree over the limit
(`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.preimage_p_eq_preimage_x'`),
and each half of their difference is a locally closed set of `|Y|` whose image misses the limit,
hence a later stage. -/
theorem StageModel.exists_preimage_eq {j : I} (M : StageModel c κ ξ w j) (y : M.Y ⟶ c.X')
    (hy : M.a ≫ y = w.x') :
    ∃ (k : I) (g : k ⟶ j), Space.pointsMap B S hS _ (M.baseChange g).q ⁻¹' (M.baseChange g).Z =
      Space.pointsMap B S hS _ (M.baseChangeHom g ≫ y) ⁻¹' c.T' := by
  have hqZ := M.isClosed_Z.preimage (Space.continuous_pointsMap B S hS M.q)
  have hyT := c.isClosed_T'.preimage (Space.continuous_pointsMap B S hS y)
  obtain ⟨k₁, g₁, h₁⟩ := M.exists_forall_notMem_image hκ hD hyT.isOpen_compl hqZ
    fun v hv => hv.1 ((M.pointsMap_a_mem_Z_iff hy v).1 hv.2)
  obtain ⟨k₂, g₂, h₂⟩ := M.exists_forall_notMem_image hκ hD hqZ.isOpen_compl hyT
    fun v hv => hv.1 ((M.pointsMap_a_mem_Z_iff hy v).2 hv.2)
  obtain ⟨k, e₁, e₂, he⟩ := IsCofiltered.cospan g₁ g₂
  refine ⟨k, e₁ ≫ g₁, ?_⟩
  ext t
  let s := Space.pointsMap B S hS _ (M.baseChangeHom (e₁ ≫ g₁)) t
  have hs : Space.pointsMap B S hS _ (yoneda.map (D.map (e₁ ≫ g₁)).hom)
      (Space.pointsMap B S hS _ (M.baseChange (e₁ ≫ g₁)).q t) =
      Space.pointsMap B S hS _ M.q s := by
    rw [← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply, M.baseChange_q_comp]
  have hst : ∀ (k' : I) (e : k ⟶ k') (g' : k' ⟶ j), e ≫ g' = e₁ ≫ g₁ →
      Space.pointsMap B S hS _ (yoneda.map (D.map g').hom)
        (Space.pointsMap B S hS _ (yoneda.map (D.map e).hom)
          (Space.pointsMap B S hS _ (M.baseChange (e₁ ≫ g₁)).q t)) =
        Space.pointsMap B S hS _ M.q s := by
    intro k' e g' hg
    rw [← Space.pointsMap_comp_apply, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      ← D.map_comp, hg, hs]
  rw [Set.mem_preimage, StageModel.baseChange_Z, Set.mem_preimage, hs, Set.mem_preimage,
    Space.pointsMap_comp_apply]
  exact ⟨fun hq => Classical.byContradiction fun hyt =>
      h₁ _ ⟨s, ⟨hyt, hq⟩, (hst k₁ e₁ g₁ rfl).symm⟩,
    fun hyt => Classical.byContradiction fun hq =>
      h₂ _ ⟨s, ⟨hq, hyt⟩, (hst k₂ e₂ g₂ he.symm).symm⟩⟩

/-- **The morphism `x' : V' ⟶ X'` comes from a morphism `Y_k ⟶ X'` at a later stage**
(`AlgebraicGeometry.Space.exists_stage_hom_restricting_of_isLimit`, applied over the terminal
sheaf to the morphism `(x', p) : V' ⟶ X' × V_j`, which is locally of finite presentation over
`V_j`). -/
theorem StageModel.exists_y (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))
    {j : I} (M : StageModel c κ ξ w j) :
    ∃ (k : I) (g : k ⟶ j) (y : (M.baseChange g).Y ⟶ c.X'),
      (M.baseChange g).a ≫ y = w.x' := by
  have : IsLocallyNoetherian S := c.isLocallyNoetherian_base
  have hT := Space.isAlgebraicSpace_terminal B S hS
  have hX'fp := (Space.isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS
    c.isAlgebraicSpace_X').2 (Space.limitPreserving_of_isLocallyOfFiniteType B S hS
      c.isAlgebraicSpace_X' c.isLocallyOfFiniteType_X')
  let V := (D.obj j).obj
  have hY₂ : IsAlgebraicSpace B S hS
      (pullback (terminal.from c.X') (terminal.from (yoneda.obj V))) :=
    isAlgebraicSpace_pullback B S hS _ _ c.isAlgebraicSpace_X' (isAlgebraicSpace_yoneda B S hS _)
      hT
  have hp₂ : Space.IsLocallyOfFinitePresentation B S hS
      (pullback.snd (terminal.from c.X') (terminal.from (yoneda.obj V))) :=
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (Space.isPullback_homMk B S hS c.isAlgebraicSpace_X' (isAlgebraicSpace_yoneda B S hS _) hT
        hY₂ (IsPullback.of_hasPullback _ _)) hX'fp
  let eV := M.isPullback_a.isoPullback
  let a : pullback (yoneda.map (κ.π.app j).hom) M.q ⟶
      pullback (terminal.from c.X') (terminal.from (yoneda.obj V)) :=
    eV.inv ≫ pullback.lift w.x' (w.p ≫ yoneda.map (κ.π.app j).hom) (terminal.hom_ext _ _)
  obtain ⟨k, a', -, -, h3⟩ := Space.exists_stage_hom_restricting_of_isLimit
    (E := D ⋙ ObjectProperty.ι _) (c := (ObjectProperty.ι _).mapCone κ) hκ hD hpt j
    M.isAlgebraicSpace_Y hY₂ hT.isSheaf (Space.limitPreserving_terminal B S hS) M.q M.isProper_q _
    hp₂ (terminal.from _) (terminal.from _) a (by
      simp only [a, eV, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, IsPullback.isoPullback_inv_fst]
      rfl) (terminal.hom_ext _ _)
  let a'' : (M.baseChange k.hom).Y ⟶
      pullback (terminal.from c.X') (terminal.from (yoneda.obj V)) := a'
  have h3'' : pullback.lift
      (pullback.fst (yoneda.map (κ.π.app j).hom) M.q ≫ yoneda.map (κ.π.app k.left).hom)
      (pullback.snd (yoneda.map (κ.π.app j).hom) M.q) (by
        rw [Category.assoc, ← Functor.map_comp, cone_π_hom_comp, pullback.condition]) ≫ a'' =
      a := h3
  have hak : (M.baseChange k.hom).a ≫ a'' = eV.hom ≫ a := by
    rw [← h3'', ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · show pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
        IsPullback.isoPullback_hom_fst]
    · show pullback.lift _ _ _ ≫ _ = _
      rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  refine ⟨k.left, k.hom, a'' ≫ pullback.fst _ _, ?_⟩
  rw [← Category.assoc, hak]
  simp only [a, eV, Iso.hom_inv_id_assoc, pullback.lift_fst]

variable (c ξ w) in
/-- **A model at a stage which is an isomorphism over the complement of `Z_j`**: the proper
model of `V'` (`AlgebraicGeometry.Space.exists_stage_isProper_model`) and the closed set
(`AlgebraicGeometry.Space.exists_stage_preimage_eq_of_isClosed`) at a common stage, and then
the isomorphism over the complement at a later one
(`AlgebraicGeometry.Space.exists_stage_isIso_openSubspace_of_isLimit`). -/
theorem exists_stageModel_isIso
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) :
    ∃ (j : I) (M : StageModel c κ ξ w j),
      IsIso (pullback.snd M.q (Space.openSubspaceOfPoints B S hS _ M.Zᶜ).ι) := by
  let V := κ.pt.obj
  have hN : ∀ V' : LocallyNoetherianOver B S hS,
      IsAffine ((BigFppfOver.toScheme B S hS).obj V'.obj) →
      IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V'.obj, ⊤) := fun V' hV' => by
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V'.obj) := V'.property
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have hNoeth := hN κ.pt hpt
  have hqc := Space.isQuasiCompactSpace_of_universallyClosed_of_isAffine B S hS V hpt
    w.isAlgebraicSpace_V' (isAlgebraicSpace_yoneda B S hS _) w.p w.isProper_p.2.2
  obtain ⟨k₁, Y₁, hY₁, p₁, a₁, hpb₁, hp₁⟩ := Space.exists_stage_isProper_model
    (E := D ⋙ ObjectProperty.ι _) (c := (ObjectProperty.ι _).mapCone κ) hκ hD hpt
    w.isAlgebraicSpace_V' w.p w.isProper_p hqc
    (Space.isLocallyOfFinitePresentation_of_isProper_yoneda w.isAlgebraicSpace_V' w.isProper_p)
  obtain ⟨k₂, Z₂, hZ₂c, hZ₂⟩ := Space.exists_stage_preimage_eq_of_isClosed
    (E := D ⋙ ObjectProperty.ι _) (c := (ObjectProperty.ι _).mapCone κ) hκ hD hpt hNoeth
    ξ.isClosed_Z
  let k₃ := IsCofiltered.min k₁ k₂
  let g₁ : k₃ ⟶ k₁ := IsCofiltered.minToLeft k₁ k₂
  let g₂ : k₃ ⟶ k₂ := IsCofiltered.minToRight k₁ k₂
  have hpb₁' : IsPullback w.p a₁ (yoneda.map (κ.π.app k₁).hom) p₁ := hpb₁
  let M₃ : StageModel c κ ξ w k₃ :=
    { Z := Space.pointsMap B S hS _ (yoneda.map (D.map g₂).hom) ⁻¹' Z₂
      isClosed_Z := hZ₂c.preimage (Space.continuous_pointsMap B S hS _)
      preimage_Z := preimage_preimage_Z g₂ hZ₂
      Y := pullback (yoneda.map (D.map g₁).hom) p₁
      isAlgebraicSpace_Y := isAlgebraicSpace_pullback B S hS _ _
        (isAlgebraicSpace_yoneda B S hS _) hY₁ (isAlgebraicSpace_yoneda B S hS _)
      q := pullback.fst _ _
      isProper_q := isProper_pullback_fst_yoneda _ hY₁ hp₁
      a := _
      isPullback_a := isPullback_lift_pullback g₁ hpb₁' }
  have hNoeth₃ := hN (D.obj k₃) (hD k₃)
  have hU : IsIso (pullback.snd w.p (Space.openSubspaceOfPoints B S hS _
      (Space.pointsMap B S hS _ (yoneda.map (κ.π.app k₃).hom) ⁻¹' M₃.Z)ᶜ).ι) := by
    rw [M₃.preimage_Z]
    have h := w.isPullback_j.flip.isoPullback_hom_snd
    rw [← Iso.eq_inv_comp, Category.comp_id] at h
    show IsIso (pullback.snd w.p (Space.openSubspaceOfPoints B S hS (yoneda.obj V) ξ.Zᶜ).ι)
    rw [h]
    infer_instance
  obtain ⟨j, F, hF⟩ := Space.exists_stage_isIso_openSubspace_of_isLimit
    (E := D ⋙ ObjectProperty.ι _) (c := (ObjectProperty.ι _).mapCone κ) hκ hD hpt k₃ hNoeth₃
    M₃.isClosed_Z M₃.isAlgebraicSpace_Y M₃.q M₃.isProper_q
    (Space.isLocallyOfFinitePresentation_of_isProper_yoneda M₃.isAlgebraicSpace_Y M₃.isProper_q)
    w.p M₃.a M₃.isPullback_a hU
  have hF' : IsIso (pullback.snd (pullback.snd M₃.q (yoneda.map (D.map F).hom))
      (Space.openSubspaceOfPoints B S hS _
        (Space.pointsMap B S hS _ (yoneda.map (D.map F).hom) ⁻¹' M₃.Z)ᶜ).ι) := hF
  refine ⟨j, M₃.baseChange F, ?_⟩
  exact Space.isIso_pullback_snd_ι_of_iso _ (pullbackSymmetry (yoneda.map (D.map F).hom) M₃.q)
    _ (pullbackSymmetry_hom_comp_snd _ _) _ hF'

variable (c ξ w) in
/-- **Stacks 0GI5, surjectivity, descending a witness**: an element `ξ` over the limit `V` of a
cofiltered system of Noetherian affine schemes, with a witness `w`, has a stage witness at some
stage `j`: everything of a witness of an element of `F(V_j)` lifting `ξ` but its formal
component. -/
theorem exists_stageWitness
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt)) :
    ∃ j : I, Nonempty (StageWitness c κ ξ w j) := by
  obtain ⟨j₀, M₀, h₀⟩ := exists_stageModel_isIso c ξ w hκ hD hpt
  obtain ⟨k₁, g₁, y₁, hy₁⟩ := M₀.exists_y hκ hD hpt
  have h₁ := Space.isIso_pullback_snd_ι_pullback_fst (D.map g₁).hom M₀.q h₀
  obtain ⟨k₂, g₂, hex⟩ := (M₀.baseChange g₁).exists_preimage_eq hκ hD y₁ hy₁
  exact ⟨k₂, ⟨{ toStageModel := (M₀.baseChange g₁).baseChange g₂
                isIso_q := Space.isIso_pullback_snd_ι_pullback_fst (D.map g₂).hom _ h₁
                y := (M₀.baseChange g₁).baseChangeHom g₂ ≫ y₁
                a_y := by rw [← Category.assoc, StageModel.baseChange_a_comp, hy₁]
                preimage_q_eq := hex }⟩⟩

variable (c ξ w) in
/-- **The surjectivity of the limit preservation, reduced to the formal component at a stage**:
if every stage witness `W` of `ξ` (at any stage `j`) acquires, after base change to some later
stage `k`, an adic formal component compatible with `q_k` and `y_k` and restricting to `x̂`, then
`ξ` comes from a stage. This is the `hcore` input of
`AlgebraicGeometry.Artin.ContractionSituation.limitPreserving_contractionFunctor_of_core` with
everything but the algebra of the last part of the proof of Stacks 0GI5 done. -/
theorem exists_stage_of_stageWitness
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))
    (hform : ∀ (j : I) (W : StageWitness c κ ξ w j), ∃ (k : I) (g : k ⟶ j)
      (xhat : Space.completionSheaf B S hS (yoneda.obj (D.obj k).obj) (W.baseChange g).Z ⟶ c.W),
      FormalSpace.IsAdicMorphism B S hS xhat ∧
      Space.completionSheafRestrict B S hS (W.baseChange g).q
          (Space.pointsMap B S hS (W.baseChange g).Y (W.baseChange g).q ⁻¹' (W.baseChange g).Z)
          (W.baseChange g).Z (fun _ hz => hz) ≫ xhat =
        Space.completionSheafRestrict B S hS (W.baseChange g).y
          (Space.pointsMap B S hS (W.baseChange g).Y (W.baseChange g).q ⁻¹' (W.baseChange g).Z)
          c.T' (W.baseChange g).subset_T' ≫ c.g ∧
      Space.completionSheafRestrict B S hS (yoneda.map (κ.π.app k).hom) ξ.Z (W.baseChange g).Z
          (W.baseChange g).subset_preimage_Z ≫ xhat = ξ.xhat) :
    ∃ (j : I) (t : Triple c (D.obj j).obj), mapTriple c (κ.π.app j).hom t = ξ := by
  obtain ⟨j, ⟨W⟩⟩ := exists_stageWitness c ξ w hκ hD hpt
  obtain ⟨k, g, xhat, hadic, hformal, hres⟩ := hform j W
  exact ⟨k, (W.baseChange g).exists_mapTriple_eq xhat hadic hformal hres⟩

end Descent

end Model

end AlgebraicGeometry.Artin.ContractionSituation

end
