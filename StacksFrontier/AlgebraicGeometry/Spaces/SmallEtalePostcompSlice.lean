module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# The slice of the small étale site at a chart is unchanged by an étale morphism

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `V` be an étale chart of `Y`.  Postcomposition with `f` carries `V` to an
étale chart of `X` with the same underlying scheme, and the slice of the small étale site of `Y`
at `V` is carried *isomorphically* onto the slice of the small étale site of `X` at that chart,
compatibly with the two localized topologies.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.postcompOverObj` and
  `AlgebraicGeometry.Space.SmallEtale.postcompOverInverse` read an étale chart of `X` over the
  composite chart as an étale chart of `Y` over `V`; this is the inverse of
  `CategoryTheory.Over.post (AlgebraicGeometry.Space.smallEtalePostcomp B S hS f hf)`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.postcompOverEquivalence`: the slice comparison is an
  equivalence of categories whose functor is postcomposition itself.
* `AlgebraicGeometry.Space.SmallEtale.coverPreserving_smallEtalePostcomp`: postcomposition is
  cover preserving for the two small étale topologies.
* `AlgebraicGeometry.Space.SmallEtale.coverPreserving_overPostcomp`,
  `AlgebraicGeometry.Space.SmallEtale.coverPreserving_postcompOverInverse` and the instances
  `AlgebraicGeometry.Space.SmallEtale.isContinuous_overPostcomp`,
  `AlgebraicGeometry.Space.SmallEtale.isContinuous_postcompOverInverse`: the slice comparison
  is an equivalence of *sites*, continuous in both directions.
* `AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`: a covering sieve of the
  composite chart pulls back to a covering sieve of `V`.

## Implementation notes

An object of the slice at `V` is an étale chart of `Y` together with a morphism of charts to
`V`; an object of the slice at the composite chart is an étale chart of `X` together with a
morphism of charts to it.  The two are interchangeable because a morphism of the big fppf site
of `S` into the source of `V` determines a chart of `Y` as well as a chart of `X` — étale in
both cases by parts (1) and (2) of Stacks 03EC, which is exactly the argument of
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationInverseObj`.  Both functors leave the
underlying object of the big fppf site of `S` unchanged, on objects and on morphisms, so the
unit and the counit are built from `CategoryTheory.Iso.refl`, as in
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationCounitIso`.

Every commuting triangle below is checked in term mode.  The source of the structure morphism
of the composite chart is the source of `V` only after unfolding an abbreviation, so a
`rewrite` inside any of these goals fails while building its motive, whereas an `exact`
elaborates at the transparency that does unfold it.  The two combinators
`map_comp_comp_eq_of_comp_eq` and `map_id_comp_eq` package the only two pieces of algebra that
occur, so that each obligation is discharged by a single `exact`.

Cover preservation is checked on the generating families of the localized topologies, which
`AlgebraicGeometry.Space.SmallEtale.over_topology_eq` presents as restrictions of the small
étale precoverage along the slice projections, using
`CategoryTheory.coverPreserving_of_generators`.  Since a covering family of charts is by
definition one whose underlying family of schemes is a chosen étale covering
(`AlgebraicGeometry.Space.SmallEtale.precoverage_eq_comap`) and both functors leave those
underlying schemes unchanged — `postcompOverInverse_comp_forget_comp_toSchemes` — each check
transports the witness unchanged.  Continuity then follows from cover preservation because an
equivalence is a right adjoint, hence representably flat.

Cover lifting is the cocontinuity of the composite `Over.post smallEtalePostcomp` with the
slice projection of the small étale site of `X`.  That composite *is* the slice projection at
`V` followed by postcomposition, and its two factors are cocontinuous: the first because it is
the functor of an equivalence whose inverse is cover preserving, the second because every slice
projection is.  Evaluating at the identity chart `Over.mk (𝟙 V)` and transporting back along
`CategoryTheory.Sieve.overEquiv` returns the pullback along postcomposition itself.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Presieve

/-- The inductive image of a presieve under a composite of functors is the iterated image. -/
theorem map_functor_comp {C₀ : Type*} [Category C₀] {D₀ : Type*} [Category D₀]
    {E₀ : Type*} [Category E₀] (F : C₀ ⥤ D₀) (G : D₀ ⥤ E₀) {A : C₀} (R : Presieve A) :
    R.map (F ⋙ G) = (R.map F).map G := by
  refine le_antisymm (fun Z g hg => ?_) (fun Z g hg => ?_)
  · obtain ⟨hu⟩ := hg
    exact map_map (map_map hu)
  · obtain ⟨hu⟩ := hg
    obtain ⟨hv⟩ := hu
    exact map_map hv

end CategoryTheory.Presieve

namespace AlgebraicGeometry.Space.SmallEtale

/-- Reassociation of the image of a composite under a functor, in the form in which the
commuting triangles of the slice comparison need it. -/
theorem map_comp_comp_eq_of_comp_eq {C₀ : Type*} [Category C₀] {D₀ : Type*}
    [Category D₀] (F : C₀ ⥤ D₀) {A A' A'' : C₀} {T : D₀} (m : A ⟶ A') (l : A' ⟶ A'')
    {l₀ : A ⟶ A''} (c : F.obj A'' ⟶ T) (h : m ≫ l = l₀) :
    F.map m ≫ F.map l ≫ c = F.map l₀ ≫ c := by
  subst h
  rw [F.map_comp, Category.assoc]

/-- The image of an identity under a functor is a unit for composition. -/
theorem map_id_comp_eq {C₀ : Type*} [Category C₀] {D₀ : Type*} [Category D₀]
    (F : C₀ ⥤ D₀) {A : C₀} {T : D₀} (c : F.obj A ⟶ T) : F.map (𝟙 A) ≫ c = c := by
  rw [F.map_id, Category.id_comp]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- An étale chart of `X` over the composite of an étale chart `V` of `Y` with an étale
`f : Y ⟶ X`, read as an étale chart of `Y` over `V`.

Its structure morphism to `V` is the morphism of the big fppf site of `S` underlying the given
structure morphism; that morphism is étale by part (2) of Stacks 03EC, hence its composite with
`V` is an étale chart of `Y` by part (1). -/
noncomputable def postcompOverObj (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) (Z : Over ((smallEtalePostcomp B S hS f hf).obj V)) :
    Over V :=
  Over.mk (Y := ⟨CostructuredArrow.mk (yoneda.map Z.hom.hom.left ≫ V.obj.hom),
      etale_comp_of_scheme B S hS Z.hom.hom.left V.obj.hom
        (MorphismProperty.of_relative_map
          (P := MorphismProperty.inverseImage
            (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)) (F := yoneda)
          (presheaf_etale_yoneda_map B S hS Z.hom.hom.left Z.left.property
            ((smallEtalePostcomp B S hS f hf).obj V).property (CostructuredArrow.w Z.hom.hom)))
        V.property⟩)
    (ObjectProperty.homMk (CostructuredArrow.homMk Z.hom.hom.left rfl))

/-- The inverse of postcomposition on the slice at an étale chart: an étale chart of `X` over
the composite chart is read as an étale chart of `Y` over the chart itself. -/
noncomputable def postcompOverInverse (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    Over ((smallEtalePostcomp B S hS f hf).obj V) ⥤ Over V where
  obj Z := postcompOverObj B S hS f hf V Z
  map {Z Z'} g :=
    have hw : g.left.hom.left ≫ Z'.hom.hom.left = Z.hom.hom.left :=
      congrArg (fun m => m.hom.left) (Over.w g)
    Over.homMk (ObjectProperty.homMk (CostructuredArrow.homMk g.left.hom.left
        (map_comp_comp_eq_of_comp_eq yoneda g.left.hom.left Z'.hom.hom.left V.obj.hom hw)))
      (ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ hw))
  map_id Z := by ext; rfl
  map_comp g g' := by ext; rfl

/-- The chart underlying the image of the inverse comparison. -/
theorem postcompOverInverse_obj_left_obj_hom (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) (Z : Over ((smallEtalePostcomp B S hS f hf).obj V)) :
    (((postcompOverInverse B S hS f hf V).obj Z).left).obj.hom =
      yoneda.map Z.hom.hom.left ≫ V.obj.hom := rfl

/-- The inverse comparison leaves the morphism of the site underlying a structure morphism
unchanged. -/
theorem postcompOverInverse_obj_hom_hom_left (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) (Z : Over ((smallEtalePostcomp B S hS f hf).obj V)) :
    ((postcompOverInverse B S hS f hf V).obj Z).hom.hom.left = Z.hom.hom.left := rfl

/-- The inverse comparison leaves the morphism of the site underlying a morphism of the slice
unchanged. -/
theorem postcompOverInverse_map_left_hom_left (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1)
    {Z Z' : Over ((smallEtalePostcomp B S hS f hf).obj V)} (g : Z ⟶ Z') :
    ((postcompOverInverse B S hS f hf V).map g).left.hom.left = g.left.hom.left := rfl

/-- The inverse comparison leaves the underlying object of `Sch_κ` unchanged, on charts and on
morphisms of charts at once. -/
theorem postcompOverInverse_comp_forget_comp_toSchemes (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (V : SmallEtale B S hS Y.1) :
    postcompOverInverse B S hS f hf V ⋙ Over.forget V ⋙ toSchemes B S hS Y.1 =
      Over.forget ((smallEtalePostcomp B S hS f hf).obj V) ⋙ toSchemes B S hS X.1 :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The unit of the comparison: an étale chart of `Y` over `V` is recovered from its structure
morphism to `V`. -/
noncomputable def postcompOverUnitIso (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    𝟭 (Over V) ≅ Over.post (X := V) (smallEtalePostcomp B S hS f hf) ⋙
      postcompOverInverse B S hS f hf V :=
  NatIso.ofComponents
    (fun W => Over.isoMk (ObjectProperty.isoMk (P := IsEtaleChart B S hS Y.1)
        (CostructuredArrow.isoMk (Iso.refl _)
          ((map_id_comp_eq yoneda (yoneda.map W.hom.hom.left ≫ V.obj.hom)).trans
            (CostructuredArrow.w W.hom.hom))))
      (ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (Category.id_comp _))))
    (fun _ => Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (CostructuredArrow.hom_ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))))

/-- The counit of the comparison: an étale chart of `X` over the composite chart is recovered
from its structure morphism to that chart. -/
noncomputable def postcompOverCounitIso (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    postcompOverInverse B S hS f hf V ⋙
        Over.post (X := V) (smallEtalePostcomp B S hS f hf) ≅
      𝟭 (Over ((smallEtalePostcomp B S hS f hf).obj V)) :=
  NatIso.ofComponents
    (fun Z => Over.isoMk (ObjectProperty.isoMk (P := IsEtaleChart B S hS X.1)
        (CostructuredArrow.isoMk (Iso.refl _)
          ((map_id_comp_eq yoneda Z.left.obj.hom).trans
            ((CostructuredArrow.w Z.hom.hom).symm.trans (Category.assoc _ _ _).symm))))
      (ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (Category.id_comp _))))
    (fun _ => Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (CostructuredArrow.hom_ext _ _ ((Category.comp_id _).trans (Category.id_comp _).symm))))

/-- **Stacks 04M0, slice form.** Postcomposition with an étale morphism `f : Y ⟶ X` of
algebraic spaces is an equivalence from the slice of the small étale site of `Y` at an étale
chart `V` onto the slice of the small étale site of `X` at the composite chart. -/
noncomputable def postcompOverEquivalence (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    Over V ≌ Over ((smallEtalePostcomp B S hS f hf).obj V) :=
  CategoryTheory.Equivalence.mk (Over.post (X := V) (smallEtalePostcomp B S hS f hf))
    (postcompOverInverse B S hS f hf V) (postcompOverUnitIso B S hS f hf V)
    (postcompOverCounitIso B S hS f hf V)

/-- Postcomposition on the slice at an étale chart is an equivalence. -/
instance isEquivalence_overPostcomp (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    (Over.post (X := V) (smallEtalePostcomp B S hS f hf)).IsEquivalence :=
  (postcompOverEquivalence B S hS f hf V).isEquivalence_functor

/-- The inverse of postcomposition on the slice at an étale chart is an equivalence. -/
instance isEquivalence_postcompOverInverse (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) : (postcompOverInverse B S hS f hf V).IsEquivalence :=
  (postcompOverEquivalence B S hS f hf V).isEquivalence_inverse

/-- Postcomposition leaves the underlying object of `Sch_κ` of a chart unchanged. -/
theorem smallEtalePostcomp_comp_toSchemes (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) :
    smallEtalePostcomp B S hS f hf ⋙ toSchemes B S hS X.1 = toSchemes B S hS Y.1 := rfl

/-- **Stacks 03LP.** Postcomposition along an étale morphism of algebraic spaces is cover
preserving for the small étale topologies: a covering family of charts of `Y` has, by
definition, a chosen étale covering family of underlying schemes, and postcomposition leaves
those unchanged. -/
theorem coverPreserving_smallEtalePostcomp (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) :
    CoverPreserving (topology B S hS Y.1) (topology B S hS X.1)
      (smallEtalePostcomp B S hS f hf) := by
  refine coverPreserving_of_generators _ (precoverage B S hS Y.1) _ ?_
  intro A R hR
  have h := precoverage_le_comap_smallEtalePostcomp B S hS f hf A hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff] at h
  rwa [← Sieve.generate_map_eq_functorPushforward]

/-- Postcomposition on the slice at an étale chart is cover preserving for the localized
topologies, being the slice of a cover preserving functor. -/
theorem coverPreserving_overPostcomp (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    CoverPreserving ((topology B S hS Y.1).over V)
      ((topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V))
      (Over.post (X := V) (smallEtalePostcomp B S hS f hf)) :=
  (coverPreserving_smallEtalePostcomp B S hS f hf).overPost V

/-- The inverse comparison on the slice at an étale chart is cover preserving for the localized
topologies: a covering family of the slice is a covering family of charts after forgetting the
structure morphism, hence is detected on the underlying objects of `Sch_κ`, which the inverse
comparison leaves unchanged. -/
theorem coverPreserving_postcompOverInverse (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    CoverPreserving ((topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V))
      ((topology B S hS Y.1).over V) (postcompOverInverse B S hS f hf V) := by
  rw [over_topology_eq B S hS X.1 ((smallEtalePostcomp B S hS f hf).obj V)]
  refine coverPreserving_of_generators _ _ _ ?_
  intro A R hR
  rw [← Sieve.generate_map_eq_functorPushforward, over_topology_eq B S hS Y.1 V]
  refine Precoverage.generate_mem_toGrothendieck ?_
  simp only [Precoverage.mem_comap_iff, precoverage_eq_comap, ← Presieve.map_functor_comp] at hR ⊢
  exact hR

/-- Postcomposition on the slice at an étale chart is continuous for the localized small étale
topologies, so restriction along it carries sheaves to sheaves. -/
instance isContinuous_overPostcomp (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    (Over.post (X := V) (smallEtalePostcomp B S hS f hf)).IsContinuous
      ((topology B S hS Y.1).over V)
      ((topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V)) := by
  have : (Over.post (X := V) (smallEtalePostcomp B S hS f hf)).IsRightAdjoint :=
    (postcompOverEquivalence B S hS f hf V).symm.isRightAdjoint_inverse
  exact Functor.isContinuous_iff_coverPreserving.2 (coverPreserving_overPostcomp B S hS f hf V)

/-- The inverse comparison on the slice at an étale chart is continuous for the localized small
étale topologies. -/
instance isContinuous_postcompOverInverse (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    (postcompOverInverse B S hS f hf V).IsContinuous
      ((topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V))
      ((topology B S hS Y.1).over V) := by
  have : (postcompOverInverse B S hS f hf V).IsRightAdjoint :=
    (postcompOverEquivalence B S hS f hf V).isRightAdjoint_inverse
  exact Functor.isContinuous_iff_coverPreserving.2
    (coverPreserving_postcompOverInverse B S hS f hf V)

/-- Postcomposition on the slice at an étale chart is cocontinuous for the localized small
étale topologies: it is the functor of an equivalence whose inverse is cover preserving. -/
theorem isCocontinuous_overPostcomp (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1) :
    (postcompOverEquivalence B S hS f hf V).functor.IsCocontinuous
      ((topology B S hS Y.1).over V)
      ((topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V)) :=
  ((postcompOverEquivalence B S hS f hf V).toAdjunction.isCocontinuous_iff_coverPreserving
    ((topology B S hS Y.1).over V)
    ((topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V))).2
    (coverPreserving_postcompOverInverse B S hS f hf V)

/-- **Cover lifting along postcomposition.** A covering sieve of the composite of an étale
chart `V` of `Y` with an étale `f : Y ⟶ X` pulls back to a covering sieve of `V`.

This is the cover-lifting half of the comparison of the two small étale sites at a chart: the
composite of postcomposition on the slice at `V` with the slice projection of the small étale
site of `X` *is* the composite of the slice projection at `V` with postcomposition, and both
factors are cocontinuous — the first because it is the functor of an equivalence whose inverse
is cover preserving, the second because every slice projection is.  Evaluating the lifted sieve
at the identity chart `Over.mk (𝟙 V)` and transporting it back along
`CategoryTheory.Sieve.overEquiv` returns exactly the pullback along postcomposition. -/
theorem smallEtalePostcomp_cover_lift (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS Y.1)
    (Sv : Sieve ((smallEtalePostcomp B S hS f hf).obj V))
    (hSv : Sv ∈ topology B S hS X.1 ((smallEtalePostcomp B S hS f hf).obj V)) :
    Sv.functorPullback (smallEtalePostcomp B S hS f hf) ∈ topology B S hS Y.1 V := by
  have hΦ := isCocontinuous_overPostcomp B S hS f hf V
  have hcomp : ((postcompOverEquivalence B S hS f hf V).functor ⋙
      Over.forget ((smallEtalePostcomp B S hS f hf).obj V)).IsCocontinuous
      ((topology B S hS Y.1).over V) (topology B S hS X.1) :=
    isCocontinuous_comp _ _ _
      ((topology B S hS X.1).over ((smallEtalePostcomp B S hS f hf).obj V))
  have h1 := Functor.cover_lift ((postcompOverEquivalence B S hS f hf V).functor ⋙
    Over.forget ((smallEtalePostcomp B S hS f hf).obj V))
    ((topology B S hS Y.1).over V) (topology B S hS X.1)
    (U := Over.mk (𝟙 V)) hSv
  rw [GrothendieckTopology.mem_over_iff] at h1
  refine (topology B S hS Y.1).superset_covering ?_ h1
  intro W g hg
  rw [Sieve.overEquiv_iff] at hg
  exact hg

end AlgebraicGeometry.Space.SmallEtale

end
