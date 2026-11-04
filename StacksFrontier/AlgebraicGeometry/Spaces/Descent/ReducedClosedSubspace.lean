module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The reduced closed subspace needs no effective descent

Let `X` be an algebraic space over a scheme `S` and let `T ⊆ |X|` be a closed set of points.
`AlgebraicGeometry.Space.reducedClosedSubspace` is the subspace of `X` it cuts out with the
reduced induced structure, built from the reduced induced closed subscheme of a chart. That it is
a *closed* subspace — that its inclusion is representable by closed immersions — is the effective
descent of a closed subscheme along the chart, and is known only under a hypothesis of effective
descent for immersions.

Two consequences of it are nevertheless unconditional, and they are what the consumers of the
reduced closed subspace actually need. First, it *is* an algebraic space: the chart supplies a
surjective étale atlas by a reduced scheme, the sheaf condition is the locality of factoring
through an immersion, and a subfunctor of a presheaf with representable diagonal has
representable diagonal. Second, the factorization criterion of Stacks 03JJ holds at it: a
morphism from an étale-locally reduced algebraic space whose image lies in `T` factors through
it. The point is that no descent is needed to *recognise* a map into the reduced induced
structure, only to construct the ideal cutting it out: a morphism from a reduced scheme factors
through a closed subscheme as soon as its image does, which is Stacks 0356, and that is applied
on a chart and then descended by the sheaf condition.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_diag_subfunctor`: a subfunctor of a presheaf
  with representable diagonal has representable diagonal.
* `AlgebraicGeometry.Space.isAlgebraicSpace_reducedClosedSubspaceOfChart` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_reducedClosedSubspace`: the reduced closed subspace
  is an algebraic space over `S`, with no descent hypothesis.
* `AlgebraicGeometry.Space.mem_subschemePoints_atlasReducedSubscheme_of_isReduced`: a morphism of
  the site out of a reduced object, all of whose points lie over `T`, factors through the reduced
  induced closed subscheme of the chart.
* `AlgebraicGeometry.Space.exists_lift_reducedClosedSubspaceOfChart_iff_pointsMap_range_subset`
  and `AlgebraicGeometry.Space.exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset`:
  **Stacks 03JJ at the reduced closed subspace, with no descent hypothesis.** A morphism from an
  étale-locally reduced algebraic space factors through the reduced closed subspace on `T`
  exactly when its image on points lies in `T`.

## Implementation notes

`AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset` is Stacks 03JJ
for an arbitrary closed subspace, and uses the closed-subspace hypothesis twice: to base change
the subspace to a chart of the source, and to know that the base change is a closed immersion of
schemes. At the reduced closed subspace neither is available unconditionally, and neither is
needed. The reduced induced closed subscheme of the chart of the *target* is already a closed
subscheme of a scheme, so Stacks 0356 — `exists_lift_subschemeι_iff_range_subset_support` —
factors a reduced chart of the source through it directly; what the chart of the source is used
for is only reducedness, which is the hypothesis `hred`, read on charts through Stacks 03E8.

The descent of that factorization from the chart of the source to the source itself is the sheaf
condition of the subspace against the surjective étale chart, through
`AlgebraicGeometry.Space.mem_obj_of_surjective_etale`; the chart is base changed to each object
of the site carrying a section, which is where its representability is used.

The diagonal clause is where the containment in `X` enters. For a subfunctor `W ⊆ F` a morphism
`yoneda.obj a ⟶ W.toFunctor` is representable as soon as its composite with the inclusion is,
because the inclusion is a monomorphism and so the two fibre products agree, which is
`CategoryTheory.IsPullback.of_comp_mono'` of
`StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono`; the criterion
`AlgebraicGeometry.Space.relativelyRepresentable_diag_of_forall` then applies. This is the one
place where the subspace is not treated as an abstract presheaf.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The diagonal of a subfunctor -/

/-- **A subfunctor of a presheaf with representable diagonal has representable diagonal.**

A morphism to the subfunctor from a representable presheaf is representable because its
composite with the inclusion is, by the diagonal of the ambient presheaf, and the inclusion is a
monomorphism, so the fibre product over the subfunctor is the fibre product over the ambient
presheaf. -/
theorem relativelyRepresentable_diag_subfunctor {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Subfunctor F) (hF : yoneda.relativelyRepresentable (diag F)) :
    yoneda.relativelyRepresentable (diag W.toFunctor) := by
  refine relativelyRepresentable_diag_of_forall fun {a} g => ?_
  intro b k
  obtain ⟨c, snd, fst, hsq⟩ :=
    Functor.relativelyRepresentable.of_diag hF (g ≫ W.ι) (k ≫ W.ι)
  exact ⟨c, snd, fst, IsPullback.of_comp_mono' W.ι hsq⟩

/-! ### Factoring a reduced object of the site through the reduced induced closed subscheme -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}

/-- **A morphism of the site out of a reduced object whose points all lie over a closed set `T`
factors through the reduced induced closed subscheme of the chart on `T`.**

This is Stacks 0356 at the vanishing ideal cutting out that subscheme: the support of the ideal
is the part of the chart lying over `T`, and the hypothesis says exactly that the image of the
morphism lies in it. -/
theorem mem_subschemePoints_atlasReducedSubscheme_of_isReduced (φ : yoneda.obj U ⟶ X)
    (T : Set (points B S hS X)) (hT : IsClosed T) {V : BigFppfOver B S hS}
    (hV : IsReduced ((BigFppfOver.toScheme B S hS).obj V)) (α : V ⟶ U)
    (hα : Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map α ≫ φ)) ⊆ T) :
    α ∈ (subschemePoints B S hS (atlasReducedSubscheme B S hS φ T hT)).obj (op V) := by
  have := hV
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map α).base ⊆
      ((atlasVanishingIdeal B S hS φ T hT).support :
        Set ((BigFppfOver.toScheme B S hS).obj U)) := by
    rw [coe_support_atlasVanishingIdeal]
    rintro y ⟨z, rfl⟩
    rw [mem_atlasPointSet_map_iff]
    exact hα ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    (atlasVanishingIdeal B S hS φ T hT) ((BigFppfOver.toScheme B S hS).map α)).2 hrange
  rw [mem_subschemePoints_iff]
  show (Subobject.mk (atlasVanishingIdeal B S hS φ T hT).subschemeι).Factors _
  rw [Subobject.mk_factors_iff]
  exact ⟨g, hg⟩

/-! ### The reduced closed subspace is an algebraic space -/

variable {φ : yoneda.obj U ⟶ X}

/-- **The subspace cut out by the reduced induced closed subscheme of a chart is an algebraic
space over `S`**, with no descent hypothesis.

The sheaf condition is `AlgebraicGeometry.Space.isSheaf_invariantSubspace`, the surjective étale
atlas is the presentation of the reduced induced closed subscheme supplied by
`AlgebraicGeometry.Space.exists_reducedChart`, and the diagonal is representable because the
subspace is a subfunctor of `X`. -/
theorem isAlgebraicSpace_reducedClosedSubspaceOfChart
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsAlgebraicSpace B S hS (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor where
  isSheaf := isSheaf_invariantSubspace B S hS hX.isSheaf _
    (isImmersion_arrow_atlasReducedSubscheme B S hS φ T hT)
  diagonal_representable := relativelyRepresentable_diag_subfunctor B S hS _
    hX.diagonal_representable
  exists_atlas := by
    obtain ⟨V, i, k, hks, hke, -, -, -⟩ := exists_reducedChart B S hS hs he T hT
    exact ⟨V, k, hks, hke⟩

/-- **The reduced closed subspace of an algebraic space on a closed set of points is an
algebraic space over `S`**, with no descent hypothesis. -/
theorem isAlgebraicSpace_reducedClosedSubspace (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsAlgebraicSpace B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor :=
  isAlgebraicSpace_reducedClosedSubspaceOfChart B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2 hX T hT

/-! ### Stacks 03JJ at the reduced closed subspace -/

/-- **Stacks 03JJ at the subspace cut out by the reduced induced closed subscheme of a chart**,
with no descent hypothesis. A morphism from an étale-locally reduced algebraic space factors
through that subspace exactly when its image on points lies in the closed set `T`.

One direction is formal. For the other, a surjective étale chart of the source lifted along the
morphism to the chart of the target is a reduced scheme, by Stacks 03E8, whose image lies over
`T`; so it factors through the reduced induced closed subscheme of the chart of the target by
Stacks 0356, hence through the subspace. The factorization is then descended to the source by
the sheaf condition of the subspace, the chart of the source being surjective étale. -/
theorem exists_lift_reducedClosedSubspaceOfChart_iff_pointsMap_range_subset
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hred : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsReduced Z))
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ (reducedClosedSubspaceOfChart B S hS φ T hT).toFunctor,
        g ≫ (reducedClosedSubspaceOfChart B S hS φ T hT).ι = f) ↔
      Set.range (pointsMap B S hS Y f) ⊆ T := by
  classical
  set Zs := reducedClosedSubspaceOfChart B S hS φ T hT
  constructor
  · rintro ⟨g, rfl⟩ x ⟨y, rfl⟩
    rw [← range_pointsMap_ι_reducedClosedSubspaceOfChart B S hS hs he T hT]
    exact ⟨pointsMap B S hS Y g y, (congrFun (pointsMap_comp B S hS Y g Zs.ι) y).symm⟩
  intro hf
  -- A surjective étale chart of the source, lifted along `f` to the chart of the target.
  obtain ⟨V, p, α, hpα, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hY hX f U φ hs he
  have hVred : IsReduced ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS Y (fun Z : Scheme.{u} => IsReduced Z) hY).1 hred
      V p hpEtale
  -- The chart of the source factors through the subspace.
  have hchartPoints :
      Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map α ≫ φ)) ⊆ T := by
    rw [← hpα]
    rintro x ⟨z, rfl⟩
    rw [congrFun (pointsMap_comp B S hS (yoneda.obj V) p f) z]
    exact hf ⟨_, rfl⟩
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : yoneda.obj V ⟶ Zs.toFunctor, g₀ ≫ Zs.ι = p ≫ f := by
    rw [← Subfunctor.mem_obj_iff_exists, hpα, yonedaEquiv_yoneda_map_comp]
    have hmem := mem_subschemePoints_atlasReducedSubscheme_of_isReduced B S hS φ T hT hVred
      α hchartPoints
    rwa [← preimage_invariantSubspace B S hS hs (atlasReducedSubscheme B S hS φ T hT)
      (isInvariantSubscheme_atlasReducedSubscheme B S hS hs he T hT)] at hmem
  -- Every section of the source lands in the subspace, the chart being surjective étale.
  have hle : Subfunctor.range f ≤ Zs := by
    rintro A _ ⟨y, rfl⟩
    obtain ⟨yA, rfl⟩ := yonedaEquiv.surjective y
    refine mem_obj_of_surjective_etale B S hS hX.isSheaf Zs
      (isAlgebraicSpace_reducedClosedSubspaceOfChart B S hS hs he hX T hT).isSheaf
      (hpSurj.rep.snd yA) (hpSurj.property_snd yA) (hpEtale.property_snd yA) _ ?_
    have hkey : yoneda.map (hpSurj.rep.snd yA) ≫ yA ≫ f =
        (hpSurj.rep.fst yA ≫ g₀) ≫ Zs.ι := by
      rw [← reassoc_of% hpSurj.rep.w yA, Category.assoc, hg₀]
    rw [← yonedaEquiv_comp, yonedaEquiv_naturality, hkey]
    exact (Subfunctor.mem_obj_iff_exists Zs _).2 ⟨_, rfl⟩
  exact ⟨Subfunctor.lift f hle, Subfunctor.lift_ι _ _⟩

/-- **Stacks 03JJ at the reduced closed subspace**, with no descent hypothesis. A morphism from
an étale-locally reduced algebraic space factors through the reduced closed subspace on a closed
set `T` of points of the target exactly when its image on points lies in `T`. -/
theorem exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hred : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsReduced Z))
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ (reducedClosedSubspace B S hS X hX T hT).toFunctor,
        g ≫ (reducedClosedSubspace B S hS X hX T hT).ι = f) ↔
      Set.range (pointsMap B S hS Y f) ⊆ T :=
  exists_lift_reducedClosedSubspaceOfChart_iff_pointsMap_range_subset B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2 hX T hT hY hred f

end AlgebraicGeometry.Space

end
