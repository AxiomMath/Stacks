module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a groupoid scheme along a disjoint union of morphisms

Step 3 of the proof of **Stacks 0489** restricts a groupoid scheme along the disjoint union
`g = ∐_i g_i` of a family of morphisms `g_i : U_i ⟶ U`, and needs the *reach map* of `g` — the
morphism `h : U' ×_{g, U, t} R ⟶ U` sending an arrow whose target lifts along `g` to its source
— to inherit flatness, local finite presentation and local quasi-finiteness from the reach maps
`h_i` of the `g_i`, and to be surjective.

This file does that.  The disjoint union is not required to be a coproduct: all that is used is
a morphism `gV : V ⟶ U` together with morphisms `incl i : U_i ⟶ V` over it whose underlying maps
are open immersions covering `V`, which is what a coproduct provides and is strictly weaker.
The comparison morphism `U_i ×_{g_i, U, t} R ⟶ V ×_{gV, U, t} R` is then a base change of
`incl i`, hence again an open immersion, and these comparisons cover the source of the reach map
of `gV`.  Local quasi-finiteness, flatness and local finite presentation are local at the source,
so they transfer along that cover.

For surjectivity there are two criteria.  The plain one asks that the images of the `h_i` cover
`U`.  The one Step 3 uses asks only that they cover the *finite type points* of `U`: the image of
`h` is then open, because `h` is flat and locally of finite presentation, and every nonempty
locally closed subset of a scheme contains a finite type point (**Stacks 02J4**), so the closed
complement of that image must be empty.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.reachComparison`: the comparison morphism from the source of
  the `i`-th reach map to the source of the reach map of `gV`.
* `AlgebraicGeometry.GroupoidScheme.sigmaOver`, `AlgebraicGeometry.GroupoidScheme.sigmaOverIncl`
  and `AlgebraicGeometry.GroupoidScheme.sigmaOverDesc`: the disjoint union `∐ᵢ Uᵢ` of a family of
  schemes over `S`, its inclusions, and the morphism `∐ᵢ gᵢ` out of it, which supply the data the
  results below ask for.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isPullback_reachComparison`: the comparison is a base change
  of `incl i`.
* `AlgebraicGeometry.GroupoidScheme.reachMap_mem_of_forall`: a property of morphisms of schemes
  which is Zariski-local at the source and holds for every `h_i` holds for the reach map of `gV`.
* `AlgebraicGeometry.GroupoidScheme.surjective_reachMap_of_iUnion_range` and
  `AlgebraicGeometry.GroupoidScheme.surjective_reachMap_of_finiteTypePoints`: the two
  surjectivity criteria.
* `AlgebraicGeometry.GroupoidScheme.isOpenImmersion_sigmaOverIncl_left`,
  `AlgebraicGeometry.GroupoidScheme.exists_mem_range_sigmaOverIncl_left` and
  `AlgebraicGeometry.GroupoidScheme.sigmaOverIncl_comp_sigmaOverDesc`: the disjoint union does
  satisfy those hypotheses, so none of them has to be assumed.

## Implementation notes

The fibre products are formed in `Over S`, while the morphism properties live on underlying
schemes; the pullback square is therefore transported by `CategoryTheory.Over.forget`, which
preserves pullbacks.

`AlgebraicGeometry.GroupoidScheme.reachComparison` is built with
`CategoryTheory.Limits.pullback.map` rather than as a literal fibre product, so that its source
is the fibre product `U_i ×_{g_i, U, t} R` that **Stacks 04N0** produces, with no transport along
the identification `incl i ≫ gV = g i`.  That identification is a hypothesis instead, which is
also what makes the statement apply to a disjoint union that is not a coproduct.

`AlgebraicGeometry.GroupoidScheme.sigmaOver` is the coproduct of the *underlying schemes*, made
a scheme over `S` by the morphism assembled from the structure morphisms, rather than the
coproduct formed in `Over S`.  The two agree, but taking it this way makes the underlying scheme
the coproduct `∐ᵢ Uᵢ` on the nose, so Mathlib's description of that coproduct — its inclusions
are open immersions and they cover it — applies with no comparison isomorphism.  The index type
may live in any universe, subject to the smallness `Small.{u}` that the coproduct of schemes
needs.

## References

* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 02J4](https://stacks.math.columbia.edu/tag/02J4)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S) {ι : Type v} {U : ι → Over S} {V : Over S}
  {g : ∀ i, U i ⟶ G.objects} (gV : V ⟶ G.objects) (incl : ∀ i, U i ⟶ V)
  (hincl : ∀ i, incl i ≫ gV = g i)

/-- The comparison morphism from the source `U_i ×_{g_i, U, t} R` of the `i`-th reach map to the
source `V ×_{gV, U, t} R` of the reach map of `gV`, induced by `incl i : U_i ⟶ V`. -/
public noncomputable def reachComparison (i : ι) :
    pullback (g i) G.target ⟶ pullback gV G.target :=
  pullback.map (g i) G.target gV G.target (incl i) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hincl]) (by rw [Category.comp_id, Category.id_comp])

/-- The comparison morphism covers `incl i` on the lifted targets. -/
public theorem reachComparison_comp_fst (i : ι) :
    reachComparison G gV incl hincl i ≫ pullback.fst gV G.target =
      pullback.fst (g i) G.target ≫ incl i := by
  simp only [reachComparison, pullback.map, pullback.lift_fst]

/-- The comparison morphism is the identity on the underlying arrow. -/
public theorem reachComparison_comp_snd (i : ι) :
    reachComparison G gV incl hincl i ≫ pullback.snd gV G.target =
      pullback.snd (g i) G.target := by
  simp only [reachComparison, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The reach map of `gV` restricts along the comparison morphism to the `i`-th reach map. -/
public theorem reachComparison_comp_reachMap (i : ι) :
    reachComparison G gV incl hincl i ≫ restrictionReachMap G gV =
      restrictionReachMap G (g i) := by
  change reachComparison G gV incl hincl i ≫ pullback.snd gV G.target ≫ G.source = _
  rw [← Category.assoc, reachComparison_comp_snd]

/-- The comparison morphism is a base change of `incl i`: the square whose top edge is the
projection to `U_i`, whose left edge is the comparison, whose right edge is `incl i` and whose
bottom edge is the projection to `V` is cartesian. -/
public theorem isPullback_reachComparison (i : ι) :
    IsPullback (pullback.fst (g i) G.target) (reachComparison G gV incl hincl i)
      (incl i) (pullback.fst gV G.target) := by
  refine IsPullback.of_bot ?_ (reachComparison_comp_fst G gV incl hincl i).symm
    (IsPullback.of_hasPullback gV G.target)
  rw [reachComparison_comp_snd, hincl]
  exact IsPullback.of_hasPullback (g i) G.target

/-- The comparison morphism, read on underlying schemes, is a base change of `incl i`. -/
public theorem isPullback_reachComparison_left (i : ι) :
    IsPullback (pullback.fst (g i) G.target).left (reachComparison G gV incl hincl i).left
      (incl i).left (pullback.fst gV G.target).left :=
  (isPullback_reachComparison G gV incl hincl i).map (Over.forget S)

/-- A base change of an open immersion is an open immersion, so the comparison morphism is one
whenever `incl i` is. -/
public theorem isOpenImmersion_reachComparison_left (i : ι)
    (h : IsOpenImmersion (incl i).left) :
    IsOpenImmersion (reachComparison G gV incl hincl i).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_reachComparison_left G gV incl hincl i) h

/-- The image of the comparison morphism is exactly the locus of arrows whose lifted target
lies in `U_i`. -/
public theorem range_reachComparison_left (i : ι) (h : IsOpenImmersion (incl i).left) :
    Set.range (reachComparison G gV incl hincl i).left =
      (pullback.fst gV G.target).left ⁻¹' Set.range (incl i).left := by
  have hsq := isPullback_reachComparison_left G gV incl hincl i
  have hfac : hsq.isoPullback.hom ≫
      pullback.snd (incl i).left (pullback.fst gV G.target).left =
      (reachComparison G gV incl hincl i).left := hsq.isoPullback_hom_snd
  have hiso : Function.Surjective (hsq.isoPullback.hom) :=
    (Scheme.homeoOfIso hsq.isoPullback).surjective
  have hrange : Set.range (reachComparison G gV incl hincl i).left =
      Set.range (pullback.snd (incl i).left (pullback.fst gV G.target).left) := by
    rw [← hfac]
    refine Set.ext fun z => ⟨?_, ?_⟩
    · rintro ⟨w, rfl⟩
      exact ⟨hsq.isoPullback.hom w, Scheme.Hom.comp_apply _ _ w⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨w', rfl⟩ := hiso w
      exact ⟨w', (Scheme.Hom.comp_apply _ _ w').symm⟩
  rw [hrange, IsOpenImmersion.range_pullbackSnd]
  simp

/-- The comparison morphisms cover the source of the reach map of `gV`. -/
public theorem exists_mem_range_reachComparison_left
    (hopen : ∀ i, IsOpenImmersion (incl i).left)
    (hcov : ∀ x : V.left, ∃ i, x ∈ Set.range (incl i).left)
    (z : (pullback gV G.target).left) :
    ∃ i, z ∈ Set.range (reachComparison G gV incl hincl i).left := by
  obtain ⟨i, hi⟩ := hcov ((pullback.fst gV G.target).left z)
  refine ⟨i, ?_⟩
  rw [range_reachComparison_left G gV incl hincl i (hopen i)]
  exact hi

/-- The open cover of the source of the reach map of `gV` by the sources of the `h_i`. -/
public noncomputable def reachCover (hopen : ∀ i, IsOpenImmersion (incl i).left)
    (hcov : ∀ x : V.left, ∃ i, x ∈ Set.range (incl i).left) :
    (pullback gV G.target).left.OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => (pullback (g i) G.target).left)
    (fun i => (reachComparison G gV incl hincl i).left)
    (fun z => by
      obtain ⟨i, w, hw⟩ := exists_mem_range_reachComparison_left G gV incl hincl hopen hcov z
      exact ⟨i, w, hw⟩)
    (fun i => isOpenImmersion_reachComparison_left G gV incl hincl i (hopen i))

/-- The reach map of `gV` restricts along the comparison morphism to the `i`-th reach map, read
on underlying schemes. -/
public theorem reachComparison_comp_reachMap_left (i : ι) :
    (reachComparison G gV incl hincl i).left ≫ (restrictionReachMap G gV).left =
      (restrictionReachMap G (g i)).left := by
  rw [← Over.comp_left, reachComparison_comp_reachMap]

include incl hincl in
/-- **Step 3 of the proof of Stacks 0489, the local half.** A property of morphisms of schemes
which is Zariski-local at the source and holds for the reach map of every `g_i` holds for the
reach map of `gV`.  Flatness, local finite presentation, local finite type and local
quasi-finiteness are all such properties. -/
public theorem reachMap_mem_of_forall {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P]
    (hopen : ∀ i, IsOpenImmersion (incl i).left)
    (hcov : ∀ x : V.left, ∃ i, x ∈ Set.range (incl i).left)
    (hP : ∀ i, P (restrictionReachMap G (g i)).left) :
    P (restrictionReachMap G gV).left := by
  refine IsZariskiLocalAtSource.of_openCover
    (reachCover G gV incl hincl hopen hcov) fun i => ?_
  rw [show (reachCover G gV incl hincl hopen hcov).f i ≫ (restrictionReachMap G gV).left =
      (restrictionReachMap G (g i)).left from
    reachComparison_comp_reachMap_left G gV incl hincl i]
  exact hP i

include incl hincl in
/-- The image of the reach map of `gV` contains the image of each `h_i`. -/
public theorem range_restrictionReachMap_le (i : ι) :
    Set.range (restrictionReachMap G (g i)).left ⊆
      Set.range (restrictionReachMap G gV).left := by
  rintro _ ⟨w, rfl⟩
  refine ⟨(reachComparison G gV incl hincl i).left w, ?_⟩
  rw [← reachComparison_comp_reachMap_left G gV incl hincl i]
  exact (Scheme.Hom.comp_apply _ _ w).symm

include incl hincl in
/-- **Step 3 of the proof of Stacks 0489, the crude surjectivity criterion.** If the images of
the reach maps of the `g_i` already cover the object scheme, the reach map of `gV` is
surjective. -/
public theorem surjective_reachMap_of_iUnion_range
    (hsurj : ∀ y : G.objects.left, ∃ i, y ∈ Set.range (restrictionReachMap G (g i)).left) :
    Surjective (restrictionReachMap G gV).left := by
  refine ⟨fun y => ?_⟩
  obtain ⟨i, hy⟩ := hsurj y
  exact range_restrictionReachMap_le G gV incl hincl i hy

include incl hincl in
/-- **Step 3 of the proof of Stacks 0489, the surjectivity criterion actually used.** If the
reach map of `gV` is flat and locally of finite presentation, and the images of the reach maps of
the `g_i` cover the *finite type points* of the object scheme, then the reach map of `gV` is
surjective.

Being flat and locally of finite presentation, the reach map is universally open
(**Stacks 01UA**), so its image is open.  Were the closed complement of that image nonempty it
would be a nonempty locally closed subset, hence would contain a finite type point
(**Stacks 02J4**), which by hypothesis lies in the image. -/
public theorem surjective_reachMap_of_finiteTypePoints
    [Flat (restrictionReachMap G gV).left]
    [LocallyOfFinitePresentation (restrictionReachMap G gV).left]
    (hft : ∀ y : G.objects.left, AlgebraicGeometry.IsFiniteTypePoint y →
      ∃ i, y ∈ Set.range (restrictionReachMap G (g i)).left) :
    Surjective (restrictionReachMap G gV).left := by
  have hopenmap : IsOpenMap (restrictionReachMap G gV).left :=
    (restrictionReachMap G gV).left.isOpenMap
  have hopen : IsOpen (Set.range (restrictionReachMap G gV).left) := by
    simpa using hopenmap _ isOpen_univ
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hclosed : IsClosed (Set.range (restrictionReachMap G gV).left)ᶜ := hopen.isClosed_compl
  have hne : ((Set.range (restrictionReachMap G gV).left)ᶜ).Nonempty := ⟨y, hy⟩
  have hloc : IsLocallyClosed (Set.range (restrictionReachMap G gV).left)ᶜ :=
    ⟨Set.univ, _, isOpen_univ, hclosed, by ext z; simp⟩
  obtain ⟨z, hzc, hzft⟩ := AlgebraicGeometry.inter_finiteTypePoints_nonempty hloc hne
  obtain ⟨i, hzi⟩ := hft z hzft
  exact hzc (range_restrictionReachMap_le G gV incl hincl i hzi)

section Coproduct

variable {S : Scheme.{u}} {ι : Type v} [Small.{u} ι] (U : ι → Over S)

/-- The disjoint union of a family of schemes over `S`, built from the coproduct of the
underlying schemes and the morphism to `S` assembled from the structure morphisms.  Taking it
this way rather than as a coproduct in `Over S` makes its underlying scheme the coproduct
`∐ᵢ Uᵢ` on the nose, so that Mathlib's description of that coproduct applies directly. -/
public noncomputable abbrev sigmaOver : Over S :=
  Over.mk (Sigma.desc fun i => (U i).hom)

/-- The `i`-th inclusion into the disjoint union. -/
public noncomputable def sigmaOverIncl (i : ι) : U i ⟶ sigmaOver U :=
  Over.homMk (Sigma.ι (fun i => (U i).left) i) (Sigma.ι_comp_desc _ _)

/-- The inclusions into the disjoint union are the coproduct inclusions of the underlying
schemes, hence open immersions. -/
public instance isOpenImmersion_sigmaOverIncl_left (i : ι) :
    IsOpenImmersion (sigmaOverIncl U i).left :=
  inferInstanceAs (IsOpenImmersion (Sigma.ι (fun i => (U i).left) i))

/-- The inclusions into the disjoint union cover it. -/
public theorem exists_mem_range_sigmaOverIncl_left (x : (sigmaOver U).left) :
    ∃ i, x ∈ Set.range (sigmaOverIncl U i).left := by
  obtain ⟨i, hi⟩ := (sigmaOpenCover (fun i => (U i).left)).exists_eq x
  exact ⟨i, hi⟩

variable {G : GroupoidScheme S} (g : ∀ i, U i ⟶ G.objects)

/-- The morphism out of the disjoint union assembled from a family of morphisms to the object
scheme of a groupoid scheme: the `∐ᵢ gᵢ` of Step 3 of the proof of **Stacks 0489**. -/
public noncomputable def sigmaOverDesc : sigmaOver U ⟶ G.objects :=
  Over.homMk (Sigma.desc fun i => (g i).left) (by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [sigmaOver, Over.mk_hom, ← Category.assoc, Sigma.ι_comp_desc]
    exact (g i).w)

/-- The assembled morphism restricts along the `i`-th inclusion to `gᵢ`. -/
public theorem sigmaOverIncl_comp_sigmaOverDesc (i : ι) :
    sigmaOverIncl U i ≫ sigmaOverDesc U g = g i := by
  refine Over.OverMorphism.ext ?_
  simp only [Over.comp_left, sigmaOverIncl, sigmaOverDesc, Over.homMk_left, Sigma.ι_comp_desc]

end Coproduct

end AlgebraicGeometry.GroupoidScheme

end
