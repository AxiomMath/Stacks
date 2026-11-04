module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
import StacksCore.Tactic.StacksAttribute

/-!
# The three-stage refinement of a quasi-compact covering

A quasi-compact covering of an object `U` of the locally quasi-compact site is refined, locally on
`U` for the Zariski topology, by a single proper surjection followed by a Zariski covering.
Precisely, there is a Zariski covering `{V → U}` such that over every member `v : V ⟶ U` there is a
proper arrow `f : W ⟶ V` which by itself is a quasi-compact covering of `V`, and a Zariski covering
of `W` each of whose members factors through the original covering along `f ≫ v`.

A point `x` of `U` has, by the quasi-compactness of the given covering, finitely many compact sets
`K i` inside finitely many members `D i` of the covering whose images cover a neighbourhood `O` of
`x`; the Zariski covering is by those neighbourhoods. Over the open `V ⊆ U` cut out by `O`, the
fibre product of `V` with the disjoint union `Σ i, K i` — a compact space, so its map to `U` is
proper — projects properly and surjectively onto `V`, and that single arrow is a quasi-compact
covering of `V` because the preimage of a compact neighbourhood is compact. Finally the fibre
products of `V` with the individual `K i` form a Zariski covering of that fibre product, each
member of which maps to the corresponding `D i`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.exists_zariskiRefinement_properMorphisms`:
  condition (5) of Situation 0EZ3 for this situation, the refinement of a quasi-compact covering by
  a Zariski covering, one proper arrow which is a quasi-compact covering over each of its members,
  and a Zariski covering of the source of that arrow.

## Implementation notes

Stacks 0EZI asserts the five conditions of Situation 0EZ3, of which
`exists_zariskiRefinement_properMorphisms` is the fifth.

The properness of the first projection of a fibre product is
`Stacks.Topology.isProperMap_subtype_fst`, which asks only that the second map be proper and the
target Hausdorff; the fibre products here are formed as explicit subspaces of a product rather than
through `CategoryTheory.Limits.pullback`, because their cardinality has to be bounded by hand to
place them in the bounded subcategory.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 09X5](https://stacks.math.columbia.edu/tag/09X5)
* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology

universe u w

/-- The fibre product of two continuous maps between locally compact Hausdorff spaces, formed as a
subspace of the product, is locally compact. -/
theorem locallyCompactSpace_eqSubtype {A B D : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    [T2Space A] [T2Space B] [T2Space D] [LocallyCompactSpace A] [LocallyCompactSpace B]
    (f : C(A, D)) (g : C(B, D)) :
    LocallyCompactSpace {p : A × B // f p.1 = g p.2} :=
  (isClosed_eq (f.continuous.comp continuous_fst)
    (g.continuous.comp continuous_snd)).isClosedEmbedding_subtypeVal.locallyCompactSpace

namespace LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- A family of open embeddings of objects of the site which is jointly surjective on points is a
Zariski covering. -/
theorem mem_zariskiPrecoverage_ofArrows {U : S.category} {ι : Type*}
    (V : ι → S.category) (v : ∀ i, V i ⟶ U)
    (he : ∀ i, Topology.IsOpenEmbedding (v i : (V i).obj → U.obj))
    (hs : ∀ x : U.obj, ∃ i y, v i y = x) :
    Presieve.ofArrows V v ∈ S.zariskiPrecoverage U := by
  constructor
  · simp only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Types.ofArrows_mem_jointlySurjectivePrecoverage_iff]
    exact hs
  · simp only [Presieve.map_ofArrows, MorphismProperty.ofArrows_mem_precoverage,
      TopCat.isOpenEmbedding_iff]
    exact he

/-- A disjoint union of finitely many types below the size cutoff of the site is again below the
cutoff. -/
theorem lt_cutoff_sigma {n : ℕ} (A : Fin n → Type u)
    (hA : ∀ i, Cardinal.mk (A i) < S.qcSite.cutoff) :
    Cardinal.mk (Σ i, A i) < S.qcSite.cutoff := by
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_lift_mk_mul_iSup _).trans_lt
    (Cardinal.mul_lt_of_lt S.qcSite.boundedSubcategory.aleph0_lt_cutoff.le ?_ ?_)
  · simpa using (Cardinal.natCast_lt_aleph0 : (n : Cardinal.{u}) < _).trans
      S.qcSite.boundedSubcategory.aleph0_lt_cutoff
  · refine Cardinal.lift_iSup_lt_of_lt_cof_ord ?_ hA
    simpa using (Cardinal.natCast_lt_aleph0 : (n : Cardinal.{u}) < _).trans
      S.qcSite.boundedSubcategory.aleph0_lt_cutoff_cof

/-- A fibre product of two types below the size cutoff of the site is below the cutoff. -/
theorem lt_cutoff_eqSubtype {A B D : Type u} (f : A → D) (g : B → D)
    (hA : Cardinal.mk A < S.qcSite.cutoff) (hB : Cardinal.mk B < S.qcSite.cutoff) :
    Cardinal.mk {p : A × B // f p.1 = g p.2} < S.qcSite.cutoff :=
  (Cardinal.mk_subtype_le _).trans_lt (by
    simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
      Cardinal.mul_lt_of_lt S.qcSite.boundedSubcategory.aleph0_lt_cutoff.le hA hB)

/-- The fibre product of a continuous map `v'` out of an object of the site with a continuous map
`a` from a space below the size cutoff, as an object of the site. -/
abbrev eqSubtypeObj (U V : S.category) (v' : C(V.obj, U.obj)) {A : Type u}
    [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] (a : C(A, U.obj))
    (ha : Cardinal.mk A < S.qcSite.cutoff) : S.category :=
  ⟨LocallyQuasiCompactHausdorff.of {p : V.obj × A // v' p.1 = a p.2}
      (locallyCompactSpace_eqSubtype v' a),
    lt_cutoff_eqSubtype S v' a V.property ha⟩

/-- **Stacks 09X5**, for an arrow of the site: a proper surjection of the site is by itself a
quasi-compact covering. -/
theorem singleton_mem_qcPretopology_of_properMap_surjective {V W : S.category} (f : W ⟶ V)
    (hp : IsProperMap (f : W.obj → V.obj)) (hs : Function.Surjective (f : W.obj → V.obj)) :
    Presieve.singleton f ∈ S.qcSite.pretopology V := by
  let E : PreZeroHypercover V := { I₀ := Unit, X := fun _ => W, f := fun _ => f }
  have hE : S.qcSite.IsQcCovering E := by
    change _root_.IsQcCovering (fun _ : Unit => (f : W.obj → V.obj))
    intro y
    obtain ⟨K, hc, hn⟩ := exists_compact_mem_nhds y
    refine ⟨{()}, fun _ => f ⁻¹' K, fun _ _ => hp.isCompact_preimage hc, ?_⟩
    simpa [Set.image_preimage_eq _ hs, Set.iUnion_const] using hn
  simpa [LocallyQuasiCompactQcSite.IsCovering, E, PreZeroHypercover.presieve₀,
    Presieve.ofArrows_of_unique] using (S.qcSite.isCovering_iff_isQcCovering E).2 hE

/-- The arrow of the site given by a continuous map between the underlying spaces. -/
private def ofContinuousMap {X Y : S.category} (g : C(X.obj, Y.obj)) : X ⟶ Y :=
  ObjectProperty.homMk (ObjectProperty.homMk (TopCat.ofHom g))

/-- Suppose that finitely many arrows `r i : D i ⟶ U` of the site carry compact subsets `K i` whose
images together cover the image of `v : V ⟶ U`. Then the fibre product `W` of `V` with the disjoint
union of the `K i` maps properly and surjectively to `V`, so is a quasi-compact covering of `V` by
itself, and the fibre products of `V` with the individual `K i` form a Zariski covering of `W`
factoring through the family `{r i}` along `f ≫ v`. -/
theorem exists_properMap_zariskiRefinement_of_compactFamily {U V : S.category} (v : V ⟶ U)
    {n : ℕ} (D : Fin n → S.category) (r : ∀ i, D i ⟶ U)
    (K : ∀ i, Set (D i).obj) (hK : ∀ i, IsCompact (K i))
    (hv : ∀ y : V.obj, ∃ i z, z ∈ K i ∧ r i z = v y) :
    ∃ (W : S.category) (f : W ⟶ V), IsProperMap (f : W.obj → V.obj) ∧
      Presieve.singleton f ∈ S.qcSite.pretopology V ∧
      ∃ T : Presieve W, T ∈ S.zariskiPrecoverage W ∧
        T.FactorsThruAlong (Presieve.ofArrows D r) (f ≫ v) := by
  let E (i : Fin n) : Type u := K i
  let _ (i : Fin n) : CompactSpace (E i) := isCompact_iff_compactSpace.mp (hK i)
  let Z := Σ i, E i
  let ai (i : Fin n) : C(E i, U.obj) :=
    ⟨fun z => r i z, (r i).hom.hom.hom.continuous.comp continuous_subtype_val⟩
  have hlt (i : Fin n) : Cardinal.mk (E i) < S.qcSite.cutoff :=
    (Cardinal.mk_subtype_le (K i)).trans_lt (D i).property
  let a : C(Z, U.obj) := ⟨fun z => ai z.1 z.2, continuous_sigma fun i => (ai i).continuous⟩
  let v' : C(V.obj, U.obj) := v.hom.hom.hom
  let W : S.category := eqSubtypeObj S U V v' a (lt_cutoff_sigma S E hlt)
  let f : W ⟶ V := ofContinuousMap S ⟨fun p => (p : V.obj × Z).1,
    continuous_fst.comp continuous_subtype_val⟩
  have hp : IsProperMap (f : W.obj → V.obj) :=
    isProperMap_subtype_fst v'.continuous a.continuous.isProperMap
  have hs : Function.Surjective (f : W.obj → V.obj) := fun y =>
    let ⟨i, z, hz, he⟩ := hv y
    ⟨⟨(y, ⟨i, z, hz⟩), he.symm⟩, rfl⟩
  refine ⟨W, f, hp, singleton_mem_qcPretopology_of_properMap_surjective S f hp hs, ?_⟩
  let B (i : Fin n) : S.category := eqSubtypeObj S U V v' (ai i) (hlt i)
  let t (i : Fin n) : B i ⟶ W :=
    ofContinuousMap S ⟨fun p => ⟨((p : V.obj × E i).1, ⟨i, (p : V.obj × E i).2⟩), p.2⟩, by fun_prop⟩
  refine ⟨Presieve.ofArrows B t, mem_zariskiPrecoverage_ofArrows S B t
    (fun i => Set.restrictPreimage_isOpenEmbedding {p : V.obj × Z | v' p.1 = a p.2}
      (Topology.IsOpenEmbedding.id.prodMap Topology.IsOpenEmbedding.sigmaMk))
    (fun ⟨⟨y, ⟨i, z⟩⟩, h⟩ => ⟨i, ⟨(y, z), h⟩, rfl⟩), ?_⟩
  rintro A g ⟨i⟩
  let k : B i ⟶ D i := ofContinuousMap S ⟨fun p : {p : V.obj × E i // v' p.1 = ai i p.2} =>
    (show K i from (p : V.obj × E i).2).val, by fun_prop⟩
  refine ⟨D i, k, r i, Presieve.ofArrows.mk i, ?_⟩
  ext p
  exact p.2.symm

/-- Every point of `U` has an open neighbourhood `V` over which the given quasi-compact covering is
refined by a proper quasi-compact covering of `V` followed by a Zariski covering. -/
theorem exists_zariskiNeighbourhood_properMap_refinement {U : S.category} (R : Presieve U)
    (hR : R ∈ S.qcSite.pretopology U) (x : U.obj) :
    ∃ (V : S.category) (v : V ⟶ U),
      Topology.IsOpenEmbedding (v : V.obj → U.obj) ∧ x ∈ Set.range (v : V.obj → U.obj) ∧
      ∃ (W : S.category) (f : W ⟶ V), IsProperMap (f : W.obj → V.obj) ∧
        Presieve.singleton f ∈ S.qcSite.pretopology V ∧
        ∃ T : Presieve W, T ∈ S.zariskiPrecoverage W ∧ T.FactorsThruAlong R (f ≫ v) := by
  obtain ⟨s, K, hc, hn⟩ := S.qcSite.covering_is_qc R hR x
  obtain ⟨O, hOsub, hOopen, hx⟩ := mem_nhds_iff.mp hn
  let O' : Opens U.obj := ⟨O, hOopen⟩
  let V := ((S.opensToSlice U).1.obj O').left
  let v : V ⟶ U := ((S.opensToSlice U).1.obj O').hom
  obtain ⟨he, hrange⟩ := (S.opensToSlice U).2 O'
  refine ⟨V, v, he, hrange.symm.subset hx, ?_⟩
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let idx (i : Fin (Fintype.card s)) := (e i).1
  let D (i : Fin (Fintype.card s)) := R.preZeroHypercover.X (idx i)
  let r (i : Fin (Fintype.card s)) : D i ⟶ U := R.preZeroHypercover.f (idx i)
  have hcover : ∀ y : V.obj, ∃ i z, z ∈ K (idx i) ∧ r i z = v y := by
    intro y
    obtain ⟨j, hj, z, hz, heq⟩ :=
      Set.mem_iUnion₂.mp (hOsub (hrange.subset (Set.mem_range_self y)))
    obtain ⟨i, hi⟩ := e.surjective ⟨j, hj⟩
    obtain rfl : idx i = j := congrArg Subtype.val hi
    exact ⟨i, z, hz, heq⟩
  obtain ⟨W, f, hp, hq, T, ht, hf⟩ :=
    exists_properMap_zariskiRefinement_of_compactFamily S v D r
      (fun i => K (idx i)) (fun i => hc _ (e i).2) hcover
  refine ⟨W, f, hp, hq, T, ht, fun A g hg => ?_⟩
  obtain ⟨B, k, b, ⟨i⟩, hcomm⟩ := hf hg
  exact ⟨_, k, _, (idx i).2, hcomm⟩

/-- **Stacks 0EZI**, the covering-refinement condition. Every quasi-compact covering `R` of an
object `U` of the site is refined in three stages: a Zariski covering `Q` of `U`, then over each
member `v : V ⟶ U` of `Q` a single proper arrow `f : W ⟶ V` which is itself a quasi-compact
covering of `V`, and then a Zariski covering of `W` all of whose members factor through `R` along
`f ≫ v`.

The quasi-compact coverings are stated as membership in the underlying precoverage of the site's
chosen pretopology, which is the same condition. -/
@[stacks 0EZI "condition (5) of Situation 0EZ3 for this situation: the three-stage refinement of \
a quasi-compact covering, by a Zariski covering, then one proper arrow over each member, then a \
Zariski covering of its source.  This is the field \
`ComparingTopologies.CohomologyComparison.covering_refinement`, proved outright and carrying no \
hypothesis beyond the covering itself.  The five conditions of Situation 0EZ3 are items (1)-(5) \
of that tag
`(0EZ7)` names used elsewhere in this directory are this development's own.  ALL FIVE ARE NOW \
PROVED for this situation, and Situation 0EZ3 is nevertheless still NOT instantiated here: \
condition (1) is `morphismProperty_baseChange` (ZariskiComparisonSituationData.lean), condition \
(2) is `weakSerre_relocalizationInverseImage` (same file), condition (3) is \
`isSheaf_qc_zariskiPullbackClass` (ZariskiPullbackClassQcSheaf.lean) and condition (4) is \
`zariskiPullbackClass_rightDerived_overMapPushforward` (ZariskiHigherDirectImageClass.lean).  \
What is missing is one coefficient universe.  The carrier of a `CohomologyComparison` has to be \
`CategoryTheory.SmallModel S.category`, `S.category` having morphisms in `Type u` and only \
`EssentiallySmall.{u}`
`LocallyQuasiCompactQcSite.category_essentiallySmall`, so the small model and \
`CategoryTheory.equivSmallModel` are available
coefficients at `AddCommGrpCat.{u}`.  Conditions (1) and (5) are universe-free, (3) is proved \
there, and (2) now holds at every `AddCommGrpCat.{max u t}`, but (4) is stated only at \
`AddCommGrpCat.{max (u+1) v}` and every input of its proof carries that universe in its own \
statement, so it cannot be instantiated at `u` without generalizing the proper-base-change \
chain.  Transporting the five conditions along `equivSmallModel` is also not done"]
theorem exists_zariskiRefinement_properMorphisms
    (U : S.category) (R : Presieve U) (hR : R ∈ S.qcSite.pretopology.toPrecoverage U) :
    ∃ Q : Presieve U, Q ∈ S.zariskiPrecoverage U ∧
      ∀ ⦃V : S.category⦄ (v : V ⟶ U), Q v →
        ∃ (W : S.category) (f : W ⟶ V), S.properMorphisms f ∧
          Presieve.singleton f ∈ S.qcSite.pretopology.toPrecoverage V ∧
          ∃ T : Presieve W, T ∈ S.zariskiPrecoverage W ∧ T.FactorsThruAlong R (f ≫ v) := by
  choose V v he hx h using exists_zariskiNeighbourhood_properMap_refinement S R hR
  exact ⟨Presieve.ofArrows V v, mem_zariskiPrecoverage_ofArrows S V v he fun x => ⟨x, hx x⟩,
    fun _ _ ⟨x⟩ => h x⟩

end LocallyQuasiCompactZariskiSituation

end Stacks.Topology

end
