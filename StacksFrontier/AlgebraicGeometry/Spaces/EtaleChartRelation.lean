module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NoetherianQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleRelationChart
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionMiddle

/-!
# A separated étale chart of an algebraic space, with its kernel pair

An algebraic space over `S` has a surjective étale chart `u : h_U ⟶ F` whose underlying scheme
is separated ([Stacks Project, Tag 03FX]), and the kernel pair of such a chart is represented by
an object `R` of the site with étale projections ([Stacks Project, Tag 03FZ]).  This file bundles
that data: the two projections are separated as well as étale, and the relation carries a
diagonal, a flip, and a composition, all as morphisms of the site and all étale and separated.

## Main definitions

* `AlgebraicGeometry.Space.EtaleChartRelation` is the bundled chart with its kernel pair.
* `AlgebraicGeometry.Space.EtaleChartRelation.diag`,
  `AlgebraicGeometry.Space.EtaleChartRelation.flip` and
  `AlgebraicGeometry.Space.EtaleChartRelation.comp` are the three structure morphisms of the
  relation, and `AlgebraicGeometry.Space.EtaleChartRelation.two` with
  `AlgebraicGeometry.Space.EtaleChartRelation.first` and
  `AlgebraicGeometry.Space.EtaleChartRelation.second` is the object of composable pairs.

## Main results

* `AlgebraicGeometry.Space.EtaleChartRelation.exists_of_isAlgebraicSpace`: every algebraic space
  over `S` admits such a chart.
* `AlgebraicGeometry.Space.EtaleChartRelation.isSeparated_t` and `.isSeparated_s`: the two
  projections are separated.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasPullbacks_bigFppfOver preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A separated étale chart of a presheaf on the big fppf site, together with its kernel
pair.**  The chart is surjective and étale after every representable base change, its underlying
scheme is separated, and the two projections of the kernel pair are morphisms of the site. -/
structure EtaleChartRelation (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The chart. -/
  U : BigFppfOver B S hS
  /-- The object representing `U ×_F U`. -/
  R : BigFppfOver B S hS
  /-- The chart morphism. -/
  u : yoneda.obj U ⟶ F
  /-- The target projection of the kernel pair. -/
  t : R ⟶ U
  /-- The source projection of the kernel pair. -/
  s : R ⟶ U
  /-- `R` represents `U ×_F U`. -/
  isPullback : IsPullback (yoneda.map t) (yoneda.map s) u u
  /-- The underlying scheme of the chart is separated. -/
  isSeparated_U : Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj U)
  /-- The chart is surjective after every representable base change. -/
  surjective_u : (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf u
  /-- The chart is étale after every representable base change. -/
  etale_u : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf u

namespace EtaleChartRelation

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : EtaleChartRelation B S hS F)

/-- **Every algebraic space over `S` admits a separated étale chart with its kernel pair.** -/
theorem exists_of_isAlgebraicSpace (hF : IsAlgebraicSpace B S hS F) :
    Nonempty (EtaleChartRelation B S hS F) := by
  obtain ⟨U, u, hUsep, hsurj, hetale⟩ :=
    AlgebraicGeometry.IsAlgebraicSpace.exists_isSeparated_etale_surjective_atlas hF
  obtain ⟨R, t, s, hpb, -, -⟩ := exists_etale_kernelPair B S hS u hetale
  exact ⟨{
    U := U
    R := R
    u := u
    t := t
    s := s
    isPullback := hpb
    isSeparated_U := hUsep
    surjective_u := hsurj
    etale_u := hetale }⟩

/-! ### The two projections -/

/-- The target projection is étale: it is a represented base change of the chart. -/
theorem etale_t : Etale ((BigFppfOver.toScheme B S hS).map c.t) :=
  c.etale_u.property c.u (yoneda.map c.s) c.t c.isPullback.flip

/-- The source projection is étale: it is a represented base change of the chart. -/
theorem etale_s : Etale ((BigFppfOver.toScheme B S hS).map c.s) :=
  c.etale_u.property c.u (yoneda.map c.t) c.s c.isPullback

/-- The target projection is separated. -/
theorem isSeparated_t :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map c.t) :=
  isSeparated_of_isPullback_yoneda c.isSeparated_U c.isPullback.flip

/-- The source projection is separated. -/
theorem isSeparated_s :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map c.s) :=
  isSeparated_of_isPullback_yoneda c.isSeparated_U c.isPullback

/-! ### The diagonal -/

/-- The diagonal of the relation, a section of both projections. -/
def diag : c.U ⟶ c.R := yoneda.preimage (c.isPullback.lift (𝟙 _) (𝟙 _) rfl)

/-- The diagonal is the lift of the two identities through the cartesian square. -/
theorem yoneda_map_diag :
    yoneda.map c.diag = c.isPullback.lift (𝟙 _) (𝟙 _) rfl := yoneda.map_preimage _

/-- The diagonal is a section of the target projection. -/
@[simp] theorem diag_comp_t : c.diag ≫ c.t = 𝟙 c.U :=
  yoneda.map_injective (by simp [c.yoneda_map_diag])

/-- The diagonal is a section of the source projection. -/
@[simp] theorem diag_comp_s : c.diag ≫ c.s = 𝟙 c.U :=
  yoneda.map_injective (by simp [c.yoneda_map_diag])

/-- A morphism into `R` is étale once its composite with the target projection is. -/
private theorem etale_of_map_comp_t {X : BigFppfOver B S hS} (f : X ⟶ c.R)
    (h : Etale ((BigFppfOver.toScheme B S hS).map (f ≫ c.t))) :
    Etale ((BigFppfOver.toScheme B S hS).map f) := by
  have := c.etale_t
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.t) :=
    (locallyQuasiFinite_of_etale _).1
  rw [CategoryTheory.Functor.map_comp] at h
  exact Etale.of_comp _ ((BigFppfOver.toScheme B S hS).map c.t)

/-- A morphism into `R` is separated once its composite with the target projection is. -/
private theorem isSeparated_of_map_comp_t {X : BigFppfOver B S hS} (f : X ⟶ c.R)
    (h : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map (f ≫ c.t))) :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map f) := by
  rw [CategoryTheory.Functor.map_comp] at h
  exact IsSeparated.of_comp _ ((BigFppfOver.toScheme B S hS).map c.t)

/-- The diagonal is étale. -/
theorem etale_diag : Etale ((BigFppfOver.toScheme B S hS).map c.diag) :=
  c.etale_of_map_comp_t _ (by rw [c.diag_comp_t, CategoryTheory.Functor.map_id]; infer_instance)

/-- The diagonal is separated. -/
theorem isSeparated_diag :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map c.diag) :=
  c.isSeparated_of_map_comp_t _
    (by rw [c.diag_comp_t, CategoryTheory.Functor.map_id]; infer_instance)

/-! ### The flip -/

/-- The flip of the relation, interchanging the two projections. -/
def flip : c.R ⟶ c.R :=
  yoneda.preimage (c.isPullback.lift (yoneda.map c.s) (yoneda.map c.t) c.isPullback.w.symm)

/-- The flip is the lift of the two projections in the opposite order. -/
theorem yoneda_map_flip :
    yoneda.map c.flip =
      c.isPullback.lift (yoneda.map c.s) (yoneda.map c.t) c.isPullback.w.symm :=
  yoneda.map_preimage _

/-- The flip followed by the target projection is the source projection. -/
@[simp] theorem flip_comp_t : c.flip ≫ c.t = c.s :=
  yoneda.map_injective (by simp [c.yoneda_map_flip])

/-- The flip followed by the source projection is the target projection. -/
@[simp] theorem flip_comp_s : c.flip ≫ c.s = c.t :=
  yoneda.map_injective (by simp [c.yoneda_map_flip])

/-- The flip is étale. -/
theorem etale_flip : Etale ((BigFppfOver.toScheme B S hS).map c.flip) :=
  c.etale_of_map_comp_t _ (by rw [c.flip_comp_t]; exact c.etale_s)

/-- The flip is separated. -/
theorem isSeparated_flip :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map c.flip) :=
  c.isSeparated_of_map_comp_t _ (by rw [c.flip_comp_t]; exact c.isSeparated_s)

/-! ### Composable pairs and the composition -/

/-- The object of composable pairs of the relation, representing `R ×_{s, U, t} R`. -/
def two : BigFppfOver B S hS := pullback c.s c.t

/-- The first projection from the composable pairs. -/
def first : c.two ⟶ c.R := pullback.fst c.s c.t

/-- The second projection from the composable pairs. -/
def second : c.two ⟶ c.R := pullback.snd c.s c.t

/-- The composable pairs really are the fibre product. -/
theorem isPullback_two : IsPullback c.first c.second c.s c.t :=
  IsPullback.of_hasPullback _ _

/-- The source of the first member of a composable pair is the target of the second. -/
theorem first_comp_s : c.first ≫ c.s = c.second ≫ c.t := c.isPullback_two.w

/-- The first projection from the composable pairs is étale. -/
theorem etale_first : Etale ((BigFppfOver.toScheme B S hS).map c.first) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (c.isPullback_two.map (BigFppfOver.toScheme B S hS)).flip c.etale_t

/-- The second projection from the composable pairs is étale. -/
theorem etale_second : Etale ((BigFppfOver.toScheme B S hS).map c.second) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (c.isPullback_two.map (BigFppfOver.toScheme B S hS)) c.etale_s

/-- The first projection from the composable pairs is separated. -/
theorem isSeparated_first :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map c.first) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (c.isPullback_two.map (BigFppfOver.toScheme B S hS)).flip c.isSeparated_t

/-- The second projection from the composable pairs is separated. -/
theorem isSeparated_second :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map c.second) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (c.isPullback_two.map (BigFppfOver.toScheme B S hS)) c.isSeparated_s

/-- The two composable projections have the same composite to `F`. -/
theorem first_comp_u : yoneda.map (c.first ≫ c.t) ≫ c.u = yoneda.map (c.second ≫ c.s) ≫ c.u := by
  have h : yoneda.map (c.first ≫ c.s) ≫ c.u = yoneda.map (c.second ≫ c.t) ≫ c.u :=
    congrArg (fun k ↦ yoneda.map k ≫ c.u) c.first_comp_s
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, c.isPullback.w] at h ⊢
  exact h

/-- The composition of the relation. -/
def comp : c.two ⟶ c.R :=
  yoneda.preimage (c.isPullback.lift (yoneda.map (c.first ≫ c.t))
    (yoneda.map (c.second ≫ c.s)) c.first_comp_u)

/-- The composition is the lift of the outer two projections of a composable pair. -/
theorem yoneda_map_comp :
    yoneda.map c.comp =
      c.isPullback.lift (yoneda.map (c.first ≫ c.t)) (yoneda.map (c.second ≫ c.s))
        c.first_comp_u :=
  yoneda.map_preimage _

/-- The target of a composite is the target of the first member of the pair. -/
@[simp] theorem comp_comp_t : c.comp ≫ c.t = c.first ≫ c.t :=
  yoneda.map_injective (by simp [c.yoneda_map_comp])

/-- The source of a composite is the source of the second member of the pair. -/
@[simp] theorem comp_comp_s : c.comp ≫ c.s = c.second ≫ c.s :=
  yoneda.map_injective (by simp [c.yoneda_map_comp])

/-- The composition is étale. -/
theorem etale_comp : Etale ((BigFppfOver.toScheme B S hS).map c.comp) := by
  have := c.etale_t
  have := c.etale_first
  exact c.etale_of_map_comp_t _
    (by rw [c.comp_comp_t, CategoryTheory.Functor.map_comp]; infer_instance)

/-- The composition is separated. -/
theorem isSeparated_comp :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map c.comp) := by
  have := c.isSeparated_t
  have := c.isSeparated_first
  exact c.isSeparated_of_map_comp_t _
    (by rw [c.comp_comp_t, CategoryTheory.Functor.map_comp]; infer_instance)

/-! ### The five relation morphisms as chart morphisms over `F` -/

/-- The structure morphism of the relation object to `F`: the common composite of the two
projections with the chart. -/
abbrev chartR : yoneda.obj c.R ⟶ F := yoneda.map c.t ≫ c.u

/-- The structure morphism of the composable pairs to `F`. -/
abbrev chartTwo : yoneda.obj c.two ⟶ F := yoneda.map c.first ≫ c.chartR

/-- The target projection is a morphism over `F`. -/
theorem t_chart : yoneda.map c.t ≫ c.u = c.chartR := rfl

/-- The source projection is a morphism over `F`. -/
theorem s_chart : yoneda.map c.s ≫ c.u = c.chartR := c.isPullback.w.symm

/-- The first projection from the composable pairs is a morphism over `F`. -/
theorem first_chart : yoneda.map c.first ≫ c.chartR = c.chartTwo := rfl

/-- Composing with a morphism into `R` and then `chartR` is composing with `t` and then `u`. -/
private theorem map_comp_chartR {X : BigFppfOver B S hS} (f : X ⟶ c.R) :
    yoneda.map f ≫ c.chartR = yoneda.map (f ≫ c.t) ≫ c.u := by
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- The second projection from the composable pairs is a morphism over `F`. -/
theorem second_chart : yoneda.map c.second ≫ c.chartR = c.chartTwo := by
  rw [c.map_comp_chartR, ← c.first_comp_s, CategoryTheory.Functor.map_comp, Category.assoc,
    c.s_chart]

/-- The composition is a morphism over `F`. -/
theorem comp_chart : yoneda.map c.comp ≫ c.chartR = c.chartTwo := by
  rw [c.map_comp_chartR, c.comp_comp_t, ← c.map_comp_chartR]

/-- The diagonal is a morphism over `F`. -/
theorem diag_chart : yoneda.map c.diag ≫ c.chartR = c.u := by
  rw [c.map_comp_chartR, c.diag_comp_t, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The flip is a morphism over `F`. -/
theorem flip_chart : yoneda.map c.flip ≫ c.chartR = c.chartR := by
  rw [c.map_comp_chartR, c.flip_comp_t, c.s_chart]

end EtaleChartRelation

end AlgebraicGeometry.Space

end
