module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentedNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation

/-!
# Relative approximation from presented Noetherian approximations

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `Spec ℤ`, and suppose `X`
and `Y` have presented Noetherian approximations: directed inverse systems of quasi-separated
algebraic spaces of finite type over `Spec ℤ` with affine transition morphisms, whose limits are
`X` and `Y`, with presentations of their stages by objects of the site whose limits are
realised in the site. Then `f` is the limit of a
directed inverse system of morphisms between their stages, which is the conclusion of Stacks
0GS3.

The system is indexed by triples consisting of a stage `a` of the approximation of `X`, a stage
`b` of the approximation of `Y` and a morphism `X_a ⟶ Y_b` compatible with `f`. Stacks 0CP4,
which holds for presented approximations with no bound on the size of their index sets, says that
such a triple exists over every `b` and that any two triples are refined by a third; the two
projections to the index sets are then initial, and Stacks 002R identifies the limit of the
system with `f`.

## Main results

* `AlgebraicGeometry.Space.hasRelativeApproximation_of_presented`: a morphism between presheaves
  with presented Noetherian approximations has a relative approximation.

## References

* [Stacks Project, Tag 0GS3](https://stacks.math.columbia.edu/tag/0GS3)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 002R](https://stacks.math.columbia.edu/tag/002R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Aligned

attribute [local instance] NoetherianApproximation.preorder NoetherianApproximation.nonempty
  NoetherianApproximation.isDirected

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}

/-- Precomposing a factorisation through a stage with a transition morphism gives a factorisation
through the earlier stage. -/
private theorem π_app_comp_map_comp (S : PresentedNoetherianApproximation B hZ X)
    {i k : (S.I)ᵒᵖ} {T : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    {g : S.diagram.obj i ⟶ T} {h : X ⟶ T} (hg : S.π.app i ≫ g = h) (e : k ⟶ i) :
    S.π.app k ≫ (S.diagram.map e ≫ g) = h := by
  rw [← Category.assoc, (Cone.mk X S.π).w e, hg]

/-- The projection from the limit to a stage factors through the transition morphisms. -/
private theorem π_app_eq_comp_map (S : PresentedNoetherianApproximation B hZ X)
    {i j : (S.I)ᵒᵖ} (e : i ⟶ j) : S.π.app j = S.π.app i ≫ S.diagram.map e := by
  simpa using S.π.naturality e

/-- **Stacks 0CP4, the surjectivity half, over a stage of the target.** Over every stage `Y_j` of
a presented approximation of `Y`, the composite of `f` with the projection to `Y_j` factors through
some stage of a presented approximation of `X`. -/
private theorem exists_aligned_hom (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y)
    (j : (SY.I)ᵒᵖ) :
    ∃ (i : (SX.I)ᵒᵖ) (g : SX.diagram.obj i ⟶ SY.diagram.obj j),
      SX.π.app i ≫ g = f ≫ SY.π.app j :=
  SX.exists_stage_hom (SY.isAlgebraicSpace j)
    (SY.toNoetherianApproximation.isLocallyOfFinitePresentation_obj j) (f ≫ SY.π.app j)

/-- **Stacks 0CP4, the injectivity half, over a stage of the target.** Two morphisms from a stage
of a presented approximation of `X` to a stage of a presented approximation of `Y` which agree over
`X` agree after one transition morphism. -/
private theorem exists_eq_after_transition'
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y)
    {i : (SX.I)ᵒᵖ} {j : (SY.I)ᵒᵖ}
    (r s : SX.diagram.obj i ⟶ SY.diagram.obj j)
    (hlim : SX.π.app i ≫ r = SX.π.app i ≫ s) :
    ∃ (k : (SX.I)ᵒᵖ) (a : k ⟶ i), SX.diagram.map a ≫ r = SX.diagram.map a ≫ s :=
  SX.exists_stage_eq (SY.isAlgebraicSpace j)
    (SY.toNoetherianApproximation.isLocallyOfFinitePresentation_obj j) r s hlim

/-- A stage of the relative system: a stage of the approximation of `X`, a stage of the
approximation of `Y`, and a morphism between them compatible with `f` and the two
projections. -/
private structure AlignedStage {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (SX : PresentedNoetherianApproximation B hZ X)
    (SY : PresentedNoetherianApproximation B hZ Y) where
  /-- The stage of the approximation of the source. -/
  source : (SX.I)ᵒᵖ
  /-- The stage of the approximation of the target. -/
  target : (SY.I)ᵒᵖ
  /-- The morphism between the two stages. -/
  hom : SX.diagram.obj source ⟶ SY.diagram.obj target
  /-- It is compatible with `f` and the two projections. -/
  compatible : SX.π.app source ≫ hom = f ≫ SY.π.app target

variable {f : X ⟶ Y}

/-- One stage of the relative system refines another when both of its stages are later and the
two morphisms agree over the transition morphisms. -/
private def AlignedStage.Refines {SX : PresentedNoetherianApproximation B hZ X}
    {SY : PresentedNoetherianApproximation B hZ Y}
    (a b : AlignedStage f SX SY) : Prop :=
  ∃ (hi : b.source ⟶ a.source) (hj : b.target ⟶ a.target),
    SX.diagram.map hi ≫ a.hom = b.hom ≫ SY.diagram.map hj

private instance {SX : PresentedNoetherianApproximation B hZ X}
    {SY : PresentedNoetherianApproximation B hZ Y} :
    Preorder (AlignedStage f SX SY) where
  le a b := a.Refines b
  le_refl a := ⟨𝟙 _, 𝟙 _, by simp⟩
  le_trans a b c hab hbc := by
    obtain ⟨hab₁, hab₂, hab⟩ := hab
    obtain ⟨hbc₁, hbc₂, hbc⟩ := hbc
    exact ⟨hbc₁ ≫ hab₁, hbc₂ ≫ hab₂, by
      simp only [Functor.map_comp, Category.assoc, hab, reassoc_of% hbc]⟩

/-- Every stage of the approximation of `Y` carries a stage of the relative system, so the
relative system has at least one stage. -/
private theorem alignedStage_nonempty (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y) :
    Nonempty (AlignedStage f SX SY) := by
  obtain ⟨i, g, hg⟩ := exists_aligned_hom f SX SY (op (Classical.arbitrary SY.I))
  exact ⟨⟨i, _, g, hg⟩⟩

/-- Two composites from a later stage of the approximation of `X` to the target of a stage of
the relative system, one through a morphism compatible with `f`, agree over `X`. -/
private theorem AlignedStage.π_comp_map_eq {SX : PresentedNoetherianApproximation B hZ X}
    {SY : PresentedNoetherianApproximation B hZ Y} (c : AlignedStage f SX SY)
    {i₀ k : (SX.I)ᵒᵖ} {j : (SY.I)ᵒᵖ} (g₀ : SX.diagram.obj i₀ ⟶ SY.diagram.obj j)
    (hg₀ : SX.π.app i₀ ≫ g₀ = f ≫ SY.π.app j)
    (e : k ⟶ i₀) (jc : j ⟶ c.target) (ic : k ⟶ c.source) :
    SX.π.app k ≫ (SX.diagram.map e ≫ g₀ ≫ SY.diagram.map jc) =
      SX.π.app k ≫ (SX.diagram.map ic ≫ c.hom) := by
  rw [π_app_comp_map_comp SX (g := g₀ ≫ SY.diagram.map jc) (h := f ≫ SY.π.app c.target)
    (by rw [reassoc_of% hg₀, (Cone.mk Y SY.π).w jc]) e,
    π_app_comp_map_comp SX c.compatible ic]

/-- **Any two stages of the relative system are refined by a third.** Take a stage of the
approximation of `Y` below both targets and a stage of the relative system over it, and refine
its source below both sources. The two resulting morphisms into each of the given targets agree
over `X`, hence after a transition morphism, and a common refinement of the two witnesses
refines both given stages. -/
private theorem alignedStage_commonRefinement
    {SX : PresentedNoetherianApproximation B hZ X}
    {SY : PresentedNoetherianApproximation B hZ Y} (a b : AlignedStage f SX SY) :
    ∃ c : AlignedStage f SX SY, a ≤ c ∧ b ≤ c := by
  classical
  have _ : IsCofiltered (SX.I)ᵒᵖ := inferInstance
  have _ : IsCofiltered (SY.I)ᵒᵖ := inferInstance
  obtain ⟨i₀, g₀, hg₀⟩ :=
    exists_aligned_hom f SX SY (IsCofiltered.min a.target b.target)
  let ja := IsCofiltered.minToLeft a.target b.target
  let jb := IsCofiltered.minToRight a.target b.target
  let im := IsCofiltered.minToRight i₀ (IsCofiltered.min a.source b.source)
  let ii₀ := IsCofiltered.minToLeft i₀ (IsCofiltered.min a.source b.source)
  let iia := im ≫ IsCofiltered.minToLeft a.source b.source
  let iib := im ≫ IsCofiltered.minToRight a.source b.source
  obtain ⟨ka, hka, eqa⟩ := exists_eq_after_transition' SX SY
    (SX.diagram.map ii₀ ≫ g₀ ≫ SY.diagram.map ja) (SX.diagram.map iia ≫ a.hom)
    (a.π_comp_map_eq g₀ hg₀ ii₀ ja iia)
  obtain ⟨kb, hkb, eqb⟩ := exists_eq_after_transition' SX SY
    (SX.diagram.map ii₀ ≫ g₀ ≫ SY.diagram.map jb) (SX.diagram.map iib ≫ b.hom)
    (b.π_comp_map_eq g₀ hg₀ ii₀ jb iib)
  let hka' := IsCofiltered.minToLeft ka kb
  let hkb' := IsCofiltered.minToRight ka kb
  refine ⟨⟨IsCofiltered.min ka kb, IsCofiltered.min a.target b.target,
    SX.diagram.map (hka' ≫ hka ≫ ii₀) ≫ g₀, ?_⟩, ?_, ?_⟩
  · exact π_app_comp_map_comp SX hg₀ _
  · exact ⟨hka' ≫ hka ≫ iia, ja, by simp only [Functor.map_comp, Category.assoc, ← eqa]⟩
  · refine ⟨hkb' ≫ hkb ≫ iib, jb, ?_⟩
    rw [show hka' ≫ hka ≫ ii₀ = hkb' ≫ hkb ≫ ii₀ from Subsingleton.elim _ _]
    simp only [Functor.map_comp, Category.assoc, ← eqb]

/-- The chosen transition morphism of the sources underlying a refinement. -/
private noncomputable def alignedSourceMap {SX : PresentedNoetherianApproximation B hZ X}
    {SY : PresentedNoetherianApproximation B hZ Y}
    {a b : AlignedStage f SX SY} (h : b ≤ a) :
    a.source ⟶ b.source :=
  Classical.choose h

/-- The chosen transition morphism of the targets underlying a refinement. -/
private noncomputable def alignedTargetMap {SX : PresentedNoetherianApproximation B hZ X}
    {SY : PresentedNoetherianApproximation B hZ Y}
    {a b : AlignedStage f SX SY} (h : b ≤ a) :
    a.target ⟶ b.target :=
  Classical.choose (Classical.choose_spec h)

/-- The commuting square of a refinement, for the two chosen transition morphisms. -/
private theorem alignedSquare {SX : PresentedNoetherianApproximation B hZ X}
    {SY : PresentedNoetherianApproximation B hZ Y}
    {a b : AlignedStage f SX SY} (h : b ≤ a) :
    SX.diagram.map (alignedSourceMap h) ≫ b.hom =
      a.hom ≫ SY.diagram.map (alignedTargetMap h) :=
  Classical.choose_spec (Classical.choose_spec h)

/-! ### The relative system and its limit -/

/-- The inverse system of arrows indexed by the stages of the relative system. -/
private noncomputable def alignedDiagram (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y) :
    (AlignedStage f SX SY)ᵒᵖ ⥤ Arrow ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) where
  obj i := Arrow.mk i.unop.hom
  map {i j} h := Arrow.homMk' (SX.diagram.map (alignedSourceMap (leOfHom h.unop)))
    (SY.diagram.map (alignedTargetMap (leOfHom h.unop))) (alignedSquare (leOfHom h.unop))
  map_id i := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · exact (congrArg SX.diagram.map (Subsingleton.elim _ (𝟙 _))).trans
        (SX.diagram.map_id _)
    · exact (congrArg SY.diagram.map (Subsingleton.elim _ (𝟙 _))).trans
        (SY.diagram.map_id _)
  map_comp {i j k} g h := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · exact (congrArg SX.diagram.map (Subsingleton.elim _
        (alignedSourceMap (leOfHom g.unop) ≫ alignedSourceMap (leOfHom h.unop)))).trans
        (SX.diagram.map_comp _ _)
    · exact (congrArg SY.diagram.map (Subsingleton.elim _
        (alignedTargetMap (leOfHom g.unop) ≫ alignedTargetMap (leOfHom h.unop)))).trans
        (SY.diagram.map_comp _ _)

/-- The projection from the stages of the relative system to the stages of the approximation of
the source. -/
private noncomputable def alignedSourceProjection (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y) :
    (AlignedStage f SX SY)ᵒᵖ ⥤ (SX.I)ᵒᵖ where
  obj i := i.unop.source
  map h := alignedSourceMap (leOfHom h.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The projection from the stages of the relative system to the stages of the approximation of
the target. -/
private noncomputable def alignedTargetProjection (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y) :
    (AlignedStage f SX SY)ᵒᵖ ⥤ (SY.I)ᵒᵖ where
  obj i := i.unop.target
  map h := alignedTargetMap (leOfHom h.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The projection to the stages of the approximation of the source is initial: every stage of
the source is refined by the source of some stage of the relative system, and the morphism
types of the index sets are subsingletons. -/
private theorem alignedSourceProjection_initial (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y)
    [Nonempty (AlignedStage f SX SY)] [IsDirected (AlignedStage f SX SY) (· ≤ ·)] :
    (alignedSourceProjection f SX SY).Initial := by
  classical
  have _ : IsCofiltered (SX.I)ᵒᵖ := inferInstance
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    obtain ⟨i, g, hg⟩ := exists_aligned_hom f SX SY (op (Classical.arbitrary SY.I))
    exact ⟨op ⟨IsCofiltered.min i d, _, _,
      π_app_comp_map_comp SX hg (IsCofiltered.minToLeft i d)⟩, ⟨IsCofiltered.minToRight i d⟩⟩
  · intro d c s s'
    exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

/-- The projection to the stages of the approximation of the target is initial: every stage of
the target carries a stage of the relative system, and the morphism types of the index sets are
subsingletons. -/
private theorem alignedTargetProjection_initial (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y)
    [Nonempty (AlignedStage f SX SY)] [IsDirected (AlignedStage f SX SY) (· ≤ ·)] :
    (alignedTargetProjection f SX SY).Initial := by
  classical
  have _ : IsCofiltered (SY.I)ᵒᵖ := inferInstance
  apply Functor.initial_of_exists_of_isCofiltered
  · intro d
    obtain ⟨i, g, hg⟩ := exists_aligned_hom f SX SY
      (IsCofiltered.min (op (Classical.arbitrary SY.I)) d)
    exact ⟨op ⟨i, _, g, hg⟩,
      ⟨IsCofiltered.minToRight (op (Classical.arbitrary SY.I)) d⟩⟩
  · intro d c s s'
    exact ⟨c, 𝟙 c, Subsingleton.elim _ _⟩

/-- **The relative system of two aligned approximations, with its limiting cone.** The stages of
the relative system form a nonempty directed set, the two projections to the index sets of the
approximations are initial, and the cone in the arrow category whose components are the two
families of projections is limiting because its images under the two projections of the arrow
category are the restrictions of the two limiting cones along initial functors. -/
private noncomputable def relativeApproximationOfPresented (f : X ⟶ Y)
    (SX : PresentedNoetherianApproximation B hZ X) (SY : PresentedNoetherianApproximation B hZ Y) :
    RelativeApproximation B hZ f := by
  classical
  letI hne : Nonempty (AlignedStage f SX SY) := alignedStage_nonempty f SX SY
  letI hdir : IsDirected (AlignedStage f SX SY) (· ≤ ·) :=
    ⟨fun a b => alignedStage_commonRefinement a b⟩
  letI : (alignedSourceProjection f SX SY).Initial :=
    alignedSourceProjection_initial f SX SY
  letI : (alignedTargetProjection f SX SY).Initial :=
    alignedTargetProjection_initial f SX SY
  refine
    { I := AlignedStage f SX SY
      diagram := alignedDiagram f SX SY
      isAlgebraicSpace_left := fun j =>
        SX.isAlgebraicSpace ((alignedSourceProjection f SX SY).obj j)
      isAlgebraicSpace_right := fun j =>
        SY.isAlgebraicSpace ((alignedTargetProjection f SX SY).obj j)
      isAffineHom_left := fun g =>
        SX.isAffineHom_map ((alignedSourceProjection f SX SY).map g)
      isAffineHom_right := fun g =>
        SY.isAffineHom_map ((alignedTargetProjection f SX SY).map g)
      isAbsolutelyQuasiSeparated_left := fun j =>
        SX.isAbsolutelyQuasiSeparated ((alignedSourceProjection f SX SY).obj j)
      isAbsolutelyQuasiSeparated_right := fun j =>
        SY.isAbsolutelyQuasiSeparated ((alignedTargetProjection f SX SY).obj j)
      isFiniteTypeOverIntegers_left := fun j =>
        SX.isFiniteTypeOverIntegers ((alignedSourceProjection f SX SY).obj j)
      isFiniteTypeOverIntegers_right := fun j =>
        SY.isFiniteTypeOverIntegers ((alignedTargetProjection f SX SY).obj j)
      π :=
        { app := fun i => Arrow.homMk'
            (SX.π.app ((alignedSourceProjection f SX SY).obj i))
            (SY.π.app ((alignedTargetProjection f SX SY).obj i)) i.unop.compatible
          naturality := fun i j g => by
            refine Arrow.hom_ext _ _ ?_ ?_
            · exact (Category.id_comp _).trans <|
              π_app_eq_comp_map SX ((alignedSourceProjection f SX SY).map g)
            · exact (Category.id_comp _).trans <|
              π_app_eq_comp_map SY ((alignedTargetProjection f SX SY).map g) }
      isLimit := ?_ }
  exact Comma.fstSndJointlyReflectLimit
    ((Functor.Initial.isLimitWhiskerEquiv (alignedSourceProjection f SX SY)
      (Cone.mk X SX.π)).symm SX.isLimit)
    ((Functor.Initial.isLimitWhiskerEquiv (alignedTargetProjection f SX SY)
      (Cone.mk Y SY.π)).symm SY.isLimit)

end Aligned

/-- **A morphism between presheaves with presented Noetherian approximations has a relative
approximation.** The conclusion of Stacks 0GS3, for any morphism whose source and target admit
presented Noetherian approximations. -/
theorem hasRelativeApproximation_of_presented {B : BigFppfSite.{u}}
    {hZ : B.Contains (⊤_ Scheme.{u})} {X Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (SX : PresentedNoetherianApproximation B hZ X)
    (SY : PresentedNoetherianApproximation B hZ Y) :
    HasRelativeApproximation B hZ f :=
  ⟨relativeApproximationOfPresented f SX SY⟩

end AlgebraicGeometry.Space

end
