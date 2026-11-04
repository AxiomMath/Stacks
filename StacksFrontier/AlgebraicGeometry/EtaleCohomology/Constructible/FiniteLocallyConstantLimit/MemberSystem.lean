module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCoveringsRefine
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageDirected
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCoveringsRefine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Member systems of a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of schemes inside a big étale site.
For an object `W` of the small étale site of a stage `X_i`, the base changes `W ×_{X_i} X_j`
over the stages `j ≥ i` form again a directed inverse system, whose limit is `W ×_{X_i} X`; if
the original system has affine transition morphisms and `W` is quasi-compact and
quasi-separated, so does the new one, with quasi-compact and quasi-separated stages. This is the
device by which the proof of Stacks Tag 0GL2 applies a statement about limits of schemes over a
member of a covering at a stage.

The file also records two further inputs of that proof: the refinement of an étale covering of
`X` by the inverse image of a finite covering of a stage can be chosen with affine members, and
an empty limit has empty stages from some stage on.

## Main definitions

* `AlgebraicGeometry.memberSystem` — the inverse system `j ↦ W ×_{X_i} X_j`, indexed by the
  stages beyond `i`.
* `AlgebraicGeometry.memberCone` — its cone with vertex `W ×_{X_i} X`.

## Main results

* `AlgebraicGeometry.memberConeIsLimit` — the member cone is a limit cone.
* `AlgebraicGeometry.memberSystem_isAffineHom`, `AlgebraicGeometry.memberSystem_compactSpace`,
  `AlgebraicGeometry.memberSystem_quasiSeparatedSpace` — the member system inherits affine
  transition morphisms and quasi-compact, quasi-separated stages.
* `AlgebraicGeometry.smallEtaleStagesCoveringsRefine_affine_of_isLimit` — Tag 0EYL for the
  small étale site, with affine members at the stage.
* `AlgebraicGeometry.exists_forall_isEmpty_stage_of_isEmpty` — an empty limit has empty stages
  from some stage on (Tag 05F3).

## Implementation notes

The member system is indexed by the subtype `{j : I // i ≤ j}`, so that its stages are
literally the fibre products `pullback W.obj.hom (systemStageHom B Dg j.2)` of the big étale
site. The limit property is deduced from that of the original cone restricted to the stages
beyond `i`, which is again a limit cone since that restriction is initial.

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 05F3](https://stacks.math.columbia.edu/tag/05F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Index

variable {I : Type*} [Preorder I]

/-- The inclusion of the stages beyond a fixed one into a directed preorder is final. -/
public instance final_subtype_le_functor [IsDirected I (· ≤ ·)] (i : I) :
    (Subtype.mono_coe (fun j : I => i ≤ j)).functor.Final := by
  rw [Monotone.final_functor_iff]
  intro k
  obtain ⟨l, hil, hkl⟩ := directed_of (· ≤ ·) i k
  exact ⟨⟨l, hil⟩, hkl⟩

end Index

section Member

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt) (i : I)
  (W : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)

/-- The transition morphism of an inverse system from a stage to itself is the identity. -/
@[simp]
public theorem systemStageHom_refl {j : I} (h : j ≤ j) : systemStageHom B Dg h = 𝟙 _ := by
  rw [systemStageHom, show (homOfLE h).op = 𝟙 (op j) from Subsingleton.elim _ _, Dg.map_id]

/-- The base change `W ×_{X_i} X_j → W ×_{X_i} X_k` of the transition morphism `X_j → X_k`, for
stages `i ≤ k ≤ j`. -/
public def memberSystemHom {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    pullback W.obj.hom (systemStageHom B Dg j.2) ⟶ pullback W.obj.hom (systemStageHom B Dg k.2) :=
  pullback.map W.obj.hom (systemStageHom B Dg j.2) W.obj.hom (systemStageHom B Dg k.2) (𝟙 _)
    (systemStageHom B Dg (show k.1 ≤ j.1 from h)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, systemStageHom_comp])

/-- The base change of a transition morphism is the identity on the `W`-component. -/
@[reassoc (attr := simp)]
public theorem memberSystemHom_fst {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    memberSystemHom B Dg i W h ≫ pullback.fst W.obj.hom (systemStageHom B Dg k.2) =
      pullback.fst W.obj.hom (systemStageHom B Dg j.2) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The base change of a transition morphism is the transition morphism on the stage
component. -/
@[reassoc (attr := simp)]
public theorem memberSystemHom_snd {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    memberSystemHom B Dg i W h ≫ pullback.snd W.obj.hom (systemStageHom B Dg k.2) =
      pullback.snd W.obj.hom (systemStageHom B Dg j.2) ≫
        systemStageHom B Dg (show k.1 ≤ j.1 from h) :=
  pullback.lift_snd _ _ _

/-- **The member system.** For an object `W` of the small étale site of the stage `X_i`, the
inverse system `j ↦ W ×_{X_i} X_j` of base changes, indexed by the stages beyond `i`. -/
public abbrev memberSystem : {j : I // i ≤ j}ᵒᵖ ⥤ B.Scheme where
  obj j := pullback W.obj.hom (systemStageHom B Dg j.unop.2)
  map {j k} e := memberSystemHom B Dg i W (leOfHom e.unop)
  map_id j := by
    apply pullback.hom_ext <;> simp
  map_comp {j k l} e e' := by
    apply pullback.hom_ext <;> simp [systemStageHom_comp]

/-- The objects of the member system are the base changes `W ×_{X_i} X_j`. -/
public theorem memberSystem_obj (j : {j : I // i ≤ j}) :
    (memberSystem B Dg i W).obj (op j) = pullback W.obj.hom (systemStageHom B Dg j.2) :=
  rfl

/-- The transition morphisms of the member system are the base changes of the transition
morphisms of the original system. -/
public theorem systemStageHom_memberSystem {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    systemStageHom B (memberSystem B Dg i W) h = memberSystemHom B Dg i W h :=
  rfl

/-- The transition morphisms of the member system are the identity on the `W`-component. -/
@[reassoc (attr := simp)]
public theorem systemStageHom_memberSystem_fst {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    systemStageHom B (memberSystem B Dg i W) h ≫
        pullback.fst W.obj.hom (systemStageHom B Dg k.2) =
      pullback.fst W.obj.hom (systemStageHom B Dg j.2) :=
  memberSystemHom_fst B Dg i W h

/-- The transition morphisms of the member system are the transition morphisms of the original
system on the stage component. -/
@[reassoc (attr := simp)]
public theorem systemStageHom_memberSystem_snd {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    systemStageHom B (memberSystem B Dg i W) h ≫
        pullback.snd W.obj.hom (systemStageHom B Dg k.2) =
      pullback.snd W.obj.hom (systemStageHom B Dg j.2) ≫
        systemStageHom B Dg (show k.1 ≤ j.1 from h) :=
  memberSystemHom_snd B Dg i W h

/-- The base change `W ×_{X_i} X → W ×_{X_i} X_j` of the projection `X → X_j`, for a stage
`j` beyond `i`. -/
public def memberConeHom (j : {j : I // i ≤ j}) :
    pullback W.obj.hom (coneStageHom B Dg c hX i) ⟶
      pullback W.obj.hom (systemStageHom B Dg j.2) :=
  pullback.map W.obj.hom (coneStageHom B Dg c hX i) W.obj.hom (systemStageHom B Dg j.2) (𝟙 _)
    (coneStageHom B Dg c hX j.1) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, coneStageHom_comp])

/-- The base change of a projection is the identity on the `W`-component. -/
@[reassoc (attr := simp)]
public theorem memberConeHom_fst (j : {j : I // i ≤ j}) :
    memberConeHom B Dg c hX i W j ≫ pullback.fst W.obj.hom (systemStageHom B Dg j.2) =
      pullback.fst W.obj.hom (coneStageHom B Dg c hX i) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The base change of a projection is the projection on the stage component. -/
@[reassoc (attr := simp)]
public theorem memberConeHom_snd (j : {j : I // i ≤ j}) :
    memberConeHom B Dg c hX i W j ≫ pullback.snd W.obj.hom (systemStageHom B Dg j.2) =
      pullback.snd W.obj.hom (coneStageHom B Dg c hX i) ≫ coneStageHom B Dg c hX j.1 :=
  pullback.lift_snd _ _ _

/-- The base changes of the projections are compatible with the base changes of the
transition morphisms. -/
@[reassoc (attr := simp)]
public theorem memberConeHom_comp_memberSystemHom {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    memberConeHom B Dg c hX i W j ≫ memberSystemHom B Dg i W h =
      memberConeHom B Dg c hX i W k := by
  apply pullback.hom_ext <;> simp [coneStageHom_comp]

/-- **The member cone.** The cone with vertex `W ×_{X_i} X` over the member system, whose legs
are the base changes of the projections of `X`. -/
public abbrev memberCone : Cone (memberSystem B Dg i W ⋙ B.inclusion) where
  pt := (pullback W.obj.hom (coneStageHom B Dg c hX i)).obj
  π :=
    { app j := B.inclusion.map (memberConeHom B Dg c hX i W j.unop)
      naturality j k e := by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map]
        rw [Category.id_comp]
        exact (congrArg B.inclusion.map
          (memberConeHom_comp_memberSystemHom B Dg c hX i W (leOfHom e.unop)).symm).trans
          (B.inclusion.map_comp _ _) }

/-- The vertex of the member cone lies in the big étale site. -/
public theorem memberCone_contains : B.Contains (memberCone B Dg c hX i W).pt :=
  (pullback W.obj.hom (coneStageHom B Dg c hX i)).property

/-- The vertex of the member cone, as an object of the big étale site, is the base change
`W ×_{X_i} X`. -/
public theorem memberCone_obj_pt :
    B.obj (memberCone B Dg c hX i W).pt (memberCone_contains B Dg c hX i W) =
      pullback W.obj.hom (coneStageHom B Dg c hX i) :=
  rfl

/-- The legs of the member cone are the base changes of the projections of `X`. -/
public theorem memberCone_π_app (j : {j : I // i ≤ j}ᵒᵖ) :
    (memberCone B Dg c hX i W).π.app j = B.inclusion.map (memberConeHom B Dg c hX i W j.unop) :=
  rfl

/-- The projections of the member cone are the base changes of the projections of `X`. -/
public theorem coneStageHom_memberCone (j : {j : I // i ≤ j}) :
    coneStageHom B (memberSystem B Dg i W) (memberCone B Dg c hX i W)
        (memberCone_contains B Dg c hX i W) j = memberConeHom B Dg c hX i W j :=
  rfl

/-- The projections of the member cone are the identity on the `W`-component. -/
@[reassoc (attr := simp)]
public theorem coneStageHom_memberCone_fst (j : {j : I // i ≤ j}) :
    coneStageHom B (memberSystem B Dg i W) (memberCone B Dg c hX i W)
        (memberCone_contains B Dg c hX i W) j ≫
        pullback.fst W.obj.hom (systemStageHom B Dg j.2) =
      pullback.fst W.obj.hom (coneStageHom B Dg c hX i) :=
  memberConeHom_fst B Dg c hX i W j

/-- The projections of the member cone are the projections of `X` on the stage component. -/
@[reassoc (attr := simp)]
public theorem coneStageHom_memberCone_snd (j : {j : I // i ≤ j}) :
    coneStageHom B (memberSystem B Dg i W) (memberCone B Dg c hX i W)
        (memberCone_contains B Dg c hX i W) j ≫
        pullback.snd W.obj.hom (systemStageHom B Dg j.2) =
      pullback.snd W.obj.hom (coneStageHom B Dg c hX i) ≫ coneStageHom B Dg c hX j.1 :=
  memberConeHom_snd B Dg c hX i W j

/-- The cone over the stages beyond `i` of the original system obtained from a cone over the
member system by projecting to the stage components. -/
public def memberStageCone (s : Cone (memberSystem B Dg i W ⋙ B.inclusion)) :
    Cone ((Subtype.mono_coe (fun j : I => i ≤ j)).functor.op ⋙ Dg ⋙ B.inclusion) where
  pt := s.pt
  π :=
    { app j := s.π.app j ≫ B.inclusion.map (pullback.snd W.obj.hom
        (systemStageHom B Dg j.unop.2))
      naturality j k e := by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map]
        rw [Category.id_comp, ← s.w e, Category.assoc, Functor.comp_map, Category.assoc]
        exact congrArg (s.π.app j ≫ ·) (((B.inclusion.map_comp _ _).symm.trans
          (congrArg B.inclusion.map (memberSystemHom_snd B Dg i W (leOfHom e.unop)))).trans
            (B.inclusion.map_comp _ _)) }

/-- The base change of a transition morphism is cartesian over that transition morphism. -/
public theorem isPullback_memberSystemHom {j k : {j : I // i ≤ j}} (h : k ≤ j) :
    IsPullback (memberSystemHom B Dg i W h) (pullback.snd W.obj.hom (systemStageHom B Dg j.2))
      (pullback.snd W.obj.hom (systemStageHom B Dg k.2))
      (systemStageHom B Dg (show k.1 ≤ j.1 from h)) := by
  refine IsPullback.of_right ?_ (memberSystemHom_snd B Dg i W h) (IsPullback.of_hasPullback _ _)
  rw [memberSystemHom_fst, systemStageHom_comp]
  exact IsPullback.of_hasPullback _ _

variable {B Dg i W} in
/-- The transition morphisms of the member system are affine when those of the original system
are. -/
public theorem memberSystem_isAffineHom
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    {p q : {j : I // i ≤ j}ᵒᵖ} (e : p ⟶ q) :
    IsAffineHom (B.inclusion.map ((memberSystem B Dg i W).map e)) :=
  MorphismProperty.of_isPullback
    ((isPullback_memberSystemHom B Dg i W (leOfHom e.unop)).map B.inclusion).flip (haff _)

variable {B Dg i W} in
/-- The projection `W ×_{X_i} X_j → W` is affine when the transition morphisms of the original
system are. -/
public theorem isAffineHom_memberSystem_fst
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (j : {j : I // i ≤ j}) :
    IsAffineHom (B.inclusion.map (pullback.fst W.obj.hom (systemStageHom B Dg j.2))) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback W.obj.hom (systemStageHom B Dg j.2)).map B.inclusion).flip
      (haff _)

variable {B Dg i W} in
/-- The stages of the member system are quasi-compact when `W` is quasi-compact and the
transition morphisms of the original system are affine. -/
public theorem memberSystem_compactSpace
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hW : CompactSpace W.obj.left.obj) (p : {j : I // i ≤ j}) :
    CompactSpace ((memberSystem B Dg i W).obj (op p)).obj := by
  have := isAffineHom_memberSystem_fst haff (W := W) p
  have : CompactSpace (B.inclusion.obj W.obj.left) := hW
  exact QuasiCompact.compactSpace_of_compactSpace
    (B.inclusion.map (pullback.fst W.obj.hom (systemStageHom B Dg p.2)))

variable {B Dg i W} in
/-- The stages of the member system are quasi-separated when `W` is quasi-separated and the
transition morphisms of the original system are affine. -/
public theorem memberSystem_quasiSeparatedSpace
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hW : QuasiSeparatedSpace W.obj.left.obj) (p : {j : I // i ≤ j}) :
    QuasiSeparatedSpace ((memberSystem B Dg i W).obj (op p)).obj := by
  have := isAffineHom_memberSystem_fst haff (W := W) p
  have : QuasiSeparatedSpace (B.inclusion.obj W.obj.left) := hW
  exact quasiSeparatedSpace_of_quasiSeparated
    (B.inclusion.map (pullback.fst W.obj.hom (systemStageHom B Dg p.2)))

/-- At the stage `i` itself, the first projection of `W ×_{X_i} X_i` followed by the structure
morphism of `W` is the second projection. -/
public theorem pullback_fst_hom_systemStageHom_refl :
    pullback.fst W.obj.hom (systemStageHom B Dg (le_refl i)) ≫ W.obj.hom =
      pullback.snd W.obj.hom (systemStageHom B Dg (le_refl i)) := by
  rw [pullback.condition, systemStageHom_refl, Category.comp_id]

/-- The `W`-components of the legs of a cone over the member system agree. -/
public theorem memberSystem_cone_fst (s : Cone (memberSystem B Dg i W ⋙ B.inclusion))
    (j : {j : I // i ≤ j}) :
    s.π.app (op j) ≫ B.inclusion.map (pullback.fst W.obj.hom (systemStageHom B Dg j.2)) =
      s.π.app (op ⟨i, le_rfl⟩) ≫
        B.inclusion.map (pullback.fst W.obj.hom (systemStageHom B Dg (le_refl i))) := by
  rw [← s.w (homOfLE j.2 : (⟨i, le_rfl⟩ : {j : I // i ≤ j}) ⟶ j).op, Category.assoc]
  exact (congrArg (s.π.app (op j) ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (memberSystemHom_fst B Dg i W _)))).symm

variable [IsDirected I (· ≤ ·)]

/-- **The member cone is a limit cone.** The base change `W ×_{X_i} X` is the limit of the
base changes `W ×_{X_i} X_j` over the stages beyond `i`. -/
public def memberConeIsLimit (hc : IsLimit c) : IsLimit (memberCone B Dg c hX i W) := by
  let ι := (Subtype.mono_coe (fun j : I => i ≤ j)).functor.op
  have hc' : IsLimit (c.whisker ι) := (Functor.Initial.isLimitWhiskerEquiv ι c).symm hc
  have hpb := (IsPullback.of_hasPullback W.obj.hom (coneStageHom B Dg c hX i)).map B.inclusion
  have hcomm : ∀ s : Cone (memberSystem B Dg i W ⋙ B.inclusion),
      (s.π.app (op ⟨i, le_rfl⟩) ≫
        B.inclusion.map (pullback.fst W.obj.hom (systemStageHom B Dg (le_refl i)))) ≫
          B.inclusion.map W.obj.hom =
        hc'.lift (memberStageCone B Dg i W s) ≫ B.inclusion.map (coneStageHom B Dg c hX i) := by
    intro s
    refine (Category.assoc _ _ _).trans (Eq.trans ?_
      (hc'.fac (memberStageCone B Dg i W s) (op ⟨i, le_rfl⟩)).symm)
    exact congrArg (s.π.app _ ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map (pullback_fst_hom_systemStageHom_refl B Dg i W)))
  exact
  { lift s := hpb.lift _ _ (hcomm s)
    fac s j := by
      have hl1 := hpb.lift_fst _ _ (hcomm s)
      have hl2 := hpb.lift_snd _ _ (hcomm s)
      generalize hpb.lift _ _ (hcomm s) = L at hl1 hl2 ⊢
      apply ((IsPullback.of_hasPullback W.obj.hom
        (systemStageHom B Dg j.unop.2)).map B.inclusion).hom_ext
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (memberSystem_cone_fst B Dg i W s
          j.unop).symm)
        refine Eq.trans ?_ hl1
        exact congrArg (L ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
          (congrArg B.inclusion.map (memberConeHom_fst B Dg c hX i W j.unop)))
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_
          (hc'.fac (memberStageCone B Dg i W s) j))
        refine Eq.trans ?_ (congrArg (· ≫ B.inclusion.map (coneStageHom B Dg c hX j.unop.1))
          hl2)
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        exact congrArg (L ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
          ((congrArg B.inclusion.map (memberConeHom_snd B Dg c hX i W j.unop)).trans
            (B.inclusion.map_comp _ _)))
    uniq s m hm := by
      apply hpb.hom_ext
      · refine Eq.trans ?_ (hpb.lift_fst _ _ (hcomm s)).symm
        rw [← hm (op ⟨i, le_rfl⟩), Category.assoc]
        exact congrArg (m ≫ ·) ((congrArg B.inclusion.map (memberConeHom_fst B Dg c hX i W
          ⟨i, le_rfl⟩)).symm.trans (B.inclusion.map_comp _ _))
      · refine Eq.trans ?_ (hpb.lift_snd _ _ (hcomm s)).symm
        refine hc'.uniq (memberStageCone B Dg i W s) _ fun j => ?_
        refine Eq.trans ?_ (congrArg (· ≫ B.inclusion.map (pullback.snd W.obj.hom
          (systemStageHom B Dg j.unop.2))) (hm j))
        refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        exact congrArg (m ≫ ·) ((B.inclusion.map_comp _ _).symm.trans
          ((congrArg B.inclusion.map (memberConeHom_snd B Dg c hX i W j.unop)).symm.trans
            (B.inclusion.map_comp _ _))) }

end Member

section Affine

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Stacks 0EYL for the small étale site, with affine members.** Let `X = lim X_i` be the limit
of a directed inverse system of quasi-compact, quasi-separated schemes with affine transition
morphisms inside a big étale site. Every covering of the final object of the small étale site of
`X` is refined by the inverse image of a finite covering of the final object at some stage beyond
a prescribed one, *whose members have affine underlying schemes*.

This strengthens `AlgebraicGeometry.smallEtaleStagesCoveringsRefine_of_isLimit`: the finite
covering at the stage it produces is refined once more, by a finite family of affine objects,
using that the stage is quasi-compact. -/
public theorem smallEtaleStagesCoveringsRefine_affine_of_isLimit (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (i : I) (K : Type (u + 1)) (V : K → SmallEtale B c.pt hX)
    (g : ∀ k, V k ⟶ SmallEtale.final B c.pt hX)
    (hg : Sieve.ofArrows V g ∈ SmallEtale.topology B c.pt hX (SmallEtale.final B c.pt hX)) :
    ∃ (j : I) (_ : i ≤ j) (K' : Type (u + 1)) (_ : Finite K')
      (W : K' → SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      (g' : ∀ k, W k ⟶ SmallEtale.final B (Dg.obj (op j)).obj (Dg.obj (op j)).property),
      Sieve.ofArrows W g' ∈
        SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property
          (SmallEtale.final B (Dg.obj (op j)).obj (Dg.obj (op j)).property) ∧
      (∀ k, IsAffine (W k).obj.left.obj) ∧
      ∀ k, ∃ m : K, Nonempty
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj (W k) ⟶ V m) := by
  obtain ⟨j, hij, K', hK', W, g', hcov, href⟩ :=
    smallEtaleStagesCoveringsRefine_of_isLimit B Dg c hX hc haff hqc hqs i K V g hg
  have : CompactSpace (Dg.obj (op j)).obj := hqc j
  obtain ⟨T, hT, Z, hZaff, hZref, hZsurj⟩ := exists_finite_affine_refinement_smallEtale B
    (Dg.obj (op j)).obj (Dg.obj (op j)).property W g' hcov
  refine ⟨j, hij, ULift.{u + 1} T, inferInstance, fun t => Z t.down,
    fun t => (SmallEtale.finalIsTerminal B (Dg.obj (op j)).obj
      (Dg.obj (op j)).property).from _, ?_, fun t => hZaff t.down, fun t => ?_⟩
  · refine SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B _ _ _ _ fun z => ?_
    obtain ⟨t, ht⟩ := hZsurj z
    refine ⟨ULift.up t, ?_⟩
    rwa [smallEtale_hom_left_to_final B (Dg.obj (op j)).obj (Dg.obj (op j)).property]
  · obtain ⟨m, ⟨q⟩⟩ := hZref t.down
    obtain ⟨n, ⟨r⟩⟩ := href m
    exact ⟨n, ⟨(smallEtaleBaseChange B (coneStageHom B Dg c hX j)).map q ≫ r⟩⟩

end Affine

section Empty

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))

/-- **An empty limit has empty stages.** If the limit `X = lim X_i` of a directed inverse system
of quasi-compact, quasi-separated schemes with affine transition morphisms is empty, then beyond
every stage there is a stage from which on all stages are empty. This is Tag 05F3 applied to the
identity of a stage. -/
@[ega "IV 8.3.6" "special case"]
public theorem exists_forall_isEmpty_stage_of_isEmpty (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) (he : IsEmpty c.pt) (i : I) :
    ∃ j, i ≤ j ∧ ∀ j', j ≤ j' → IsEmpty (Dg.obj (op j')).obj := by
  have : Nonempty I := ⟨i⟩
  let D := descentSituationOfBigEtaleCone B Dg c hc haff hqc hqs i
  have : CompactSpace (D.system.obj (op D.base)) := hqc i
  have hT : IsEmpty (pullback (𝟙 (D.system.obj (op D.base)))
      (D.limitCone.π.app (op D.base)) : Scheme) :=
    ⟨fun x => he.elim ((pullback.snd (𝟙 (D.system.obj (op D.base)))
      (D.limitCone.π.app (op D.base))) x)⟩
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.mp
    (eventually_isEmpty_pullback D _ (𝟙 (D.system.obj (op D.base))) hT)
  obtain ⟨j, hij, hj₀j⟩ := directed_of (· ≤ ·) i j₀
  exact ⟨j, hij, fun j' hjj' => ⟨fun x => (hj₀ j' (hj₀j.trans hjj') (hij.trans hjj')).elim
    ((pullback.lift (D.system.map (homOfLE (hij.trans hjj')).op)
      (𝟙 _) ((Category.comp_id _).trans (Category.id_comp _).symm)) x)⟩⟩

end Empty

end AlgebraicGeometry

end
