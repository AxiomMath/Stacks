module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.MorphismsIntoGluing.GluingReconstruction

/-!
# The mapping property for morphisms into a gluing, as a bijection

Morphisms from a locally ringed space `Y` into a gluing `D.glued` are in bijection with descent
data on `Y`: an open covering `Y = ⋃ V i` by *opens of `Y`* together with morphisms
`g i : V i ⟶ D.U i` whose inverse images of the prescribed overlaps are the pairwise
intersections of the covering and which agree, through the prescribed transitions, on those
intersections.

Recording the `V i` as actual opens of `Y` — rather than as abstract locally ringed spaces with
open immersions into `Y`, which is the general form in
`StacksFrontier.AlgebraicGeometry.Scheme.Glueing.MorphismsIntoGluing.GluingReconstruction` — is what
makes this a bijection on the nose: the covering of a descent datum is forced to be the
inverse-image covering of the morphism it determines, and for opens of `Y` that is an equality
rather than an isomorphism.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.GlueData.ChartDatumOpens`: descent data for a morphism
  into the gluing, with the covering recorded as a family of opens of `Y`.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.homIntoEquiv`: the bijection
  `(Y ⟶ D.glued) ≃ D.ChartDatumOpens Y`, the counterpart for morphisms into the gluing of
  `AlgebraicGeometry.LocallyRingedSpace.GlueData.homOutEquiv`.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.ChartDatumOpens.existsUnique_transitionLift`:
  the agreement condition of a descent datum, in the form in which the source states it, namely
  as factoring through the prescribed overlap by the prescribed transition.

## Implementation notes

The agreement condition is recorded as the equation `g i ≫ φ i = g j ≫ φ j` on `V i ∩ V j`,
read in the glued space. Because `D.V (i, j)` is the intersection of the two charts —
`vPullbackConeIsLimit` — this is *equivalent* to the source's form `g j = φ i j ∘ g i`, and
`ChartDatumOpens.existsUnique_transitionLift` records that equivalence by producing the unique
factorisation. The equation form is the one used here because it is a `Prop`: a data-valued
field would have to be transported along the equality of coverings in the proof that the two
constructions are mutually inverse.

Pairwise intersections are modelled by pullbacks of the covering immersions, as everywhere else
in these files; `ChartDatumOpens.range_pullback_fst` records that such a pullback has the
expected image `V i ∩ V j` in `Y`.

## References

* [Stacks Project, Tag 01JB](https://stacks.math.columbia.edu/tag/01JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

section MappingProperty

variable {D : LocallyRingedSpace.GlueData.{u}} {Y : LocallyRingedSpace.{u}}

/-- The open of `Y` over which a morphism `f : Y ⟶ D.glued` lies in the `i`-th chart, that is,
the inverse image `f ⁻¹' (U i)`. -/
def preimageChart (D : LocallyRingedSpace.GlueData.{u}) {Y : LocallyRingedSpace.{u}}
    (f : Y ⟶ D.glued) (i : D.J) : Opens Y.carrier :=
  ⟨f.base ⁻¹' Set.range (D.ι i).base,
    (inferInstance : LocallyRingedSpace.IsOpenImmersion
      (D.ι i)).base_open.isOpen_range.preimage f.base.hom.continuous⟩

/-- As a set, `D.preimageChart f i` is the inverse image under `f` of the range of `D.ι i`. -/
@[simp]
lemma coe_preimageChart (f : Y ⟶ D.glued) (i : D.J) :
    (D.preimageChart f i : Set Y.carrier) = f.base ⁻¹' Set.range (D.ι i).base := rfl

/-- The image in `Y` of the open subspace attached to an open `U` is `U` itself. -/
lemma range_ofRestrict_base (Y : LocallyRingedSpace.{u}) (U : Opens Y.carrier) :
    Set.range (Y.ofRestrict U.isOpenEmbedding).base = (U : Set Y.carrier) :=
  Opens.set_range_inclusion' U

/-- Over `f ⁻¹' (U i)` the morphism `f` has image inside the `i`-th chart. -/
lemma range_ofRestrict_comp_subset (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (f : Y ⟶ D.glued) (i : D.J) :
    Set.range (Y.ofRestrict (D.preimageChart f i).isOpenEmbedding ≫ f).base ⊆
      Set.range (D.ι i).base := by
  rintro _ ⟨x, rfl⟩
  exact x.2

/-- The factorisation of `f` through the `i`-th chart, over the open `f ⁻¹' (U i)` on which `f`
has image inside that chart. -/
noncomputable def chartFactor (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (f : Y ⟶ D.glued) (i : D.J) :
    Y.restrict (D.preimageChart f i).isOpenEmbedding ⟶ D.U i :=
  LocallyRingedSpace.IsOpenImmersion.lift (D.ι i)
    (Y.ofRestrict (D.preimageChart f i).isOpenEmbedding ≫ f)
    (D.range_ofRestrict_comp_subset f i)

/-- Descent datum for a morphism into a gluing, with the covering recorded as a family of opens
of `Y`. The fields are, in order: the opens `V i`; the statement that they cover `Y`; the
morphisms `g i` from the corresponding open subspaces to the pieces of the gluing datum; the
statement that `g i ⁻¹' (U i j) = V i ∩ V j`; and the statement that `g i` and `g j` agree on
`V i ∩ V j` after being carried into the glued space, which is the source's compatibility
`g j = φ i j ∘ g i` (see `ChartDatumOpens.existsUnique_transitionLift`). -/
structure ChartDatumOpens (D : LocallyRingedSpace.GlueData.{u})
    (Y : LocallyRingedSpace.{u}) where
  /-- The opens of `Y` covering it. -/
  V : D.J → Opens Y.carrier
  /-- `Y = ⋃ V i`. -/
  iSup_V : ⨆ i, V i = ⊤
  /-- The morphisms to the pieces of the gluing datum. -/
  g : ∀ i, Y.restrict (V i).isOpenEmbedding ⟶ D.U i
  /-- `g i ⁻¹' (U i j) = V i ∩ V j`, both sides read as subsets of `V i`. -/
  preimage_overlap : ∀ i j,
    (g i).base ⁻¹' Set.range (D.f i j).base =
      (Y.ofRestrict (V i).isOpenEmbedding).base ⁻¹'
        Set.range (Y.ofRestrict (V j).isOpenEmbedding).base
  /-- On `V i ∩ V j` the two local morphisms agree in the glued space. -/
  transition : ∀ i j,
    pullback.fst (Y.ofRestrict (V i).isOpenEmbedding)
          (Y.ofRestrict (V j).isOpenEmbedding) ≫ g i ≫ D.ι i =
      pullback.snd (Y.ofRestrict (V i).isOpenEmbedding)
          (Y.ofRestrict (V j).isOpenEmbedding) ≫ g j ≫ D.ι j

namespace ChartDatumOpens

variable (C : D.ChartDatumOpens Y)

/-- The open immersion presenting `C.V i` as an open subspace of `Y`. -/
noncomputable abbrev ι (i : D.J) : Y.restrict (C.V i).isOpenEmbedding ⟶ Y :=
  Y.ofRestrict (C.V i).isOpenEmbedding

/-- Every point of `Y` lies in some member `C.V i` of the covering. -/
lemma exists_mem (y : Y) : ∃ i, y ∈ C.V i := by
  have hy : y ∈ (⊤ : Opens Y.carrier) := trivial
  rw [← C.iSup_V] at hy
  simpa using hy

/-- The pairwise intersection of the covering, modelled as a pullback, has image `V i ∩ V j`. -/
lemma range_pullback_fst (i j : D.J) :
    Set.range (pullback.fst (C.ι i) (C.ι j) ≫ C.ι i).base =
      (C.V i : Set Y.carrier) ∩ (C.V j : Set Y.carrier) := by
  rw [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    range_pullback_fst_of_right, Set.image_preimage_eq_inter_range,
    range_ofRestrict_base, range_ofRestrict_base, Set.inter_comm]

/-- The general descent datum underlying a descent datum on opens. -/
noncomputable def toChartDatum : D.ChartDatum Y where
  V i := Y.restrict (C.V i).isOpenEmbedding
  v i := C.ι i
  v_open _ := inferInstance
  v_jointlySurjective y := by
    obtain ⟨i, hi⟩ := C.exists_mem y
    exact ⟨i, ⟨y, hi⟩, rfl⟩
  g := C.g
  preimage_overlap := C.preimage_overlap
  transitionLift i j := (D.vPullbackConeIsLimit i j).lift
    (PullbackCone.mk (pullback.fst (C.ι i) (C.ι j) ≫ C.g i)
      (pullback.snd (C.ι i) (C.ι j) ≫ C.g j)
      (by simpa only [Category.assoc] using C.transition i j))
  transitionLift_f i j := (D.vPullbackConeIsLimit i j).fac _ WalkingCospan.left
  transitionLift_t_f i j := (D.vPullbackConeIsLimit i j).fac _ WalkingCospan.right

/-- The immersions of the underlying general descent datum are the inclusions `C.ι i`. -/
@[simp]
lemma toChartDatum_v (i : D.J) : C.toChartDatum.v i = C.ι i := rfl

/-- The local morphisms of the underlying general descent datum are the `C.g i`. -/
@[simp]
lemma toChartDatum_g (i : D.J) : C.toChartDatum.g i = C.g i := rfl

/-- **Stacks Project, Tag 01JB.** The agreement condition of a descent datum in the form in
which the source states it: on `V i ∩ V j` the local morphism `g i` factors uniquely through the
prescribed overlap `D.V (i, j)`, and `g j` is obtained from that factorisation by the prescribed
transition `D.t i j`. -/
theorem existsUnique_transitionLift (i j : D.J) :
    ∃! k : pullback (C.ι i) (C.ι j) ⟶ D.V (i, j),
      k ≫ D.f i j = pullback.fst (C.ι i) (C.ι j) ≫ C.g i ∧
        k ≫ D.t i j ≫ D.f j i = pullback.snd (C.ι i) (C.ι j) ≫ C.g j := by
  refine ⟨C.toChartDatum.transitionLift i j,
    ⟨C.toChartDatum.transitionLift_f i j, C.toChartDatum.transitionLift_t_f i j⟩, ?_⟩
  intro l hl
  refine PullbackCone.IsLimit.hom_ext (D.vPullbackConeIsLimit i j) ?_ ?_
  · exact hl.1.trans (C.toChartDatum.transitionLift_f i j).symm
  · exact hl.2.trans (C.toChartDatum.transitionLift_t_f i j).symm

/-- The morphism `Y ⟶ D.glued` determined by a descent datum. -/
noncomputable def hom : Y ⟶ D.glued :=
  (D.existsUnique_hom_to_glued C.toChartDatum).choose

/-- Restricted to `C.V i`, the morphism `C.hom` is `C.g i` followed by `D.ι i`. -/
lemma hom_spec (i : D.J) : C.ι i ≫ C.hom = C.g i ≫ D.ι i :=
  (D.existsUnique_hom_to_glued C.toChartDatum).choose_spec.1 i

/-- `C.hom` is the unique morphism `Y ⟶ D.glued` whose restriction to each `C.V i` is
`C.g i ≫ D.ι i`. -/
lemma hom_unique {f : Y ⟶ D.glued} (hf : ∀ i, C.ι i ≫ f = C.g i ≫ D.ι i) : f = C.hom :=
  (D.existsUnique_hom_to_glued C.toChartDatum).choose_spec.2 f hf

end ChartDatumOpens

/-- The descent datum on opens induced by a morphism into the glued space: the covering is by the
inverse images of the charts, and the local morphisms are the factorisations of `f` through the
charts. -/
noncomputable def chartDatumOpensOfHom (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (f : Y ⟶ D.glued) : D.ChartDatumOpens Y where
  V i := D.preimageChart f i
  iSup_V := by
    refine Opens.ext ?_
    rw [Opens.coe_iSup, Opens.coe_top, Set.iUnion_eq_univ_iff]
    intro y
    obtain ⟨i, x, hx⟩ := D.ι_jointly_surjective (f.base y)
    exact ⟨i, x, hx⟩
  g i := D.chartFactor f i
  preimage_overlap i j := by
    have hfac (x : Y.restrict (D.preimageChart f i).isOpenEmbedding) :
        (D.ι i).base ((D.chartFactor f i).base x) =
          f.base ((Y.ofRestrict (D.preimageChart f i).isOpenEmbedding).base x) :=
      ConcreteCategory.congr_hom
        (congrArg (fun q ↦ q.base)
          (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (D.range_ofRestrict_comp_subset f i))) x
    ext x
    rw [Set.mem_preimage, Set.mem_preimage, D.range_overlap i j, Set.mem_preimage, hfac x,
      range_ofRestrict_base, coe_preimageChart, Set.mem_preimage]
  transition i j := by
    rw [chartFactor, chartFactor, LocallyRingedSpace.IsOpenImmersion.lift_fac,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, ← Category.assoc, ← Category.assoc,
      pullback.condition]

/-- The covering of `D.chartDatumOpensOfHom f` is by the opens `D.preimageChart f i`. -/
@[simp]
lemma chartDatumOpensOfHom_V (f : Y ⟶ D.glued) (i : D.J) :
    (D.chartDatumOpensOfHom f).V i = D.preimageChart f i := rfl

/-- The local morphisms of `D.chartDatumOpensOfHom f` are the factorisations
`D.chartFactor f i`. -/
@[simp]
lemma chartDatumOpensOfHom_g (f : Y ⟶ D.glued) (i : D.J) :
    (D.chartDatumOpensOfHom f).g i = D.chartFactor f i := rfl

/-- Each local morphism of `D.chartDatumOpensOfHom f`, followed by `D.ι i`, is the restriction
of `f` to the corresponding open. -/
lemma chartDatumOpensOfHom_g_comp_ι (f : Y ⟶ D.glued) (i : D.J) :
    (D.chartDatumOpensOfHom f).g i ≫ D.ι i = (D.chartDatumOpensOfHom f).ι i ≫ f :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (D.range_ofRestrict_comp_subset f i)

/-- A descent datum on opens is recovered from any morphism inducing it: the covering is forced
to be the inverse-image covering, and the local morphisms are then forced too. -/
theorem chartDatumOpensOfHom_eq (C : D.ChartDatumOpens Y) {f : Y ⟶ D.glued}
    (hf : ∀ i, C.ι i ≫ f = C.g i ≫ D.ι i) : D.chartDatumOpensOfHom f = C := by
  have hV : ∀ i, (D.chartDatumOpensOfHom f).V i = C.V i := by
    intro i
    refine Opens.ext ?_
    rw [chartDatumOpensOfHom_V, coe_preimageChart, ← C.toChartDatum.range_v hf i,
      ChartDatumOpens.toChartDatum_v]
    exact range_ofRestrict_base Y (C.V i)
  obtain ⟨V, hiSup, g, hpre, htr⟩ := C
  have hV' : (fun i ↦ (D.chartDatumOpensOfHom f).V i) = V := funext hV
  subst hV'
  have hg : (fun i ↦ (D.chartDatumOpensOfHom f).g i) = g := by
    funext i
    rw [← cancel_mono (D.ι i), chartDatumOpensOfHom_g_comp_ι, ← hf i]
  subst hg
  rfl

/-- The mapping property for morphisms *into* a gluing, as a bijection: a morphism `Y ⟶ D.glued` is
the same thing as a descent datum on `Y`, namely an open covering of `Y` together with compatible
morphisms from its members to the pieces of the gluing datum. The bijection sends `f` to the
covering by the inverse images `f ⁻¹' (U i)` and the factorisations of `f` through the charts.
This is the counterpart for morphisms into the gluing of
`AlgebraicGeometry.LocallyRingedSpace.GlueData.homOutEquiv`. -/
@[stacks 01JB "Mor(Y, X) is the set of descent data on an open covering of Y"]
noncomputable def homIntoEquiv (D : LocallyRingedSpace.GlueData.{u})
    (Y : LocallyRingedSpace.{u}) : (Y ⟶ D.glued) ≃ D.ChartDatumOpens Y where
  toFun f := D.chartDatumOpensOfHom f
  invFun C := C.hom
  left_inv f := ((D.chartDatumOpensOfHom f).hom_unique
    (fun i ↦ (chartDatumOpensOfHom_g_comp_ι f i).symm)).symm
  right_inv C := chartDatumOpensOfHom_eq C C.hom_spec

end MappingProperty

end AlgebraicGeometry.LocallyRingedSpace.GlueData

end
