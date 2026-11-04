module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiFibreProductSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperSurjectiveQcCovering
import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-compact covering is refined by Zariski, proper, and Zariski stages

Situation 0EZ3 asks of the pair of topologies it compares that every covering for the finer one
admit a three-stage refinement: first a covering for the coarser topology, then over each of its
members a single arrow of the distinguished class which alone covers for the finer topology, and
finally a covering for the coarser topology of that arrow's source, the composites refining the
originally given covering. For the comparison `ε : LC_qc → LC_Zar` and the choice Stacks 0EZI
makes — the proper maps as the distinguished class — this file proves that condition.

A quasi-compact covering `{a_i : A_i → U}` gives, at each point `x` of `U`, finitely many arrows
`a_{i_1}, …, a_{i_m}` and quasi-compact subsets `E_j ⊆ A_{i_j}` whose images cover a neighbourhood
of `x`; the first stage is the family of those neighbourhoods, shrunk to open ones. The finite
disjoint union `Y = ⨿_j E_j` is a quasi-compact Hausdorff space, hence an object of the site, and
`Y → U` is proper because its source is quasi-compact and its target Hausdorff. Over an open `V`
from the first stage the base change `Y ×_U V → V` is proper, and it is surjective because `V` lies
inside the union of the images of the `E_j`; a proper surjection is a quasi-compact covering by
Stacks 09X5, so it is the second stage all by itself. Its source decomposes into the `m` open
pieces lying over the summands of `Y`, and that open cover is the third stage: the piece over the
`j`-th summand maps to `A_{i_j}`, so the composites factor through the given covering.

## Main definitions

* `LocallyQuasiCompactZariskiSituation.opensObj`: an open subset of an object of the site, as an
  object of the site.
* `LocallyQuasiCompactZariskiSituation.opensHom`: its open immersion.

## Main results

* `exists_fin_of_isQcCovering`: at one point, the finitely many members and quasi-compact subsets
  witnessing a quasi-compact covering, reindexed by `Fin m`.
* `LocallyQuasiCompactZariskiSituation.exists_properMorphisms_refinement_of_pieces`: the
  three-stage refinement over one open set of the first stage.
* `LocallyQuasiCompactZariskiSituation.exists_zariski_properMorphisms_refinement`: condition (0EZ8)
  of Situation 0EZ3 for the comparison of the quasi-compact and the Zariski topology, with the
  proper arrows as the distinguished class.

## Implementation notes

The index type of the canonical family of arrows of a presieve on the site lies in `Type (u + 1)`,
one universe above the spaces, so the finitely many members chosen at a point have to be reindexed
by `Fin m`, which `exists_fin_of_isQcCovering` does, before their disjoint union can be formed as
a space in `Type u`.

Membership of the disjoint union in the bounded subcategory is a cardinal computation: a sum of
finitely many cardinals below the cutoff stays below it, the cutoff being uncountable.

Open subobjects are taken here as `opensObj`, whose underlying space is the subtype of the open
set, rather than through `opensToSlice`, whose underlying space is only characterized up to the
unique isomorphism over the ambient object. The third stage has to *build* an arrow out of an open
piece, which needs the underlying space on the nose.

The open pieces of `Y ×_U V` are the preimages of the open ranges of the summand inclusions of
`Y`, and the map from a piece to the corresponding member of the covering is the summand
inclusion's inverse on its range — a homeomorphism because a summand inclusion is an open
embedding. Writing it that way avoids transporting a dependent equality `(q z).1 = j` through the
construction of a continuous map.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0EZ8](https://stacks.math.columbia.edu/tag/0EZ8)
* [Stacks Project, Tag 09X5](https://stacks.math.columbia.edu/tag/09X5)
* [Stacks Project, Tag 09X0](https://stacks.math.columbia.edu/tag/09X0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology

universe u w

/-- The witnesses of a quasi-compact covering at a point, reindexed by `Fin m`: a quasi-compact
covering gives, at every point of the target, a finite set of indices and a quasi-compact subset of
each corresponding source whose images cover a neighbourhood of the point, with the finite index
set replaced by `Fin m` along a bijection. -/
theorem exists_fin_of_isQcCovering {ι : Type*} {X : ι → Type*} {Y : Type*}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y] {f : ∀ i, X i → Y}
    (h : IsQcCovering f) (y : Y) :
    ∃ (m : ℕ) (idx : Fin m → ι) (E : ∀ j : Fin m, Set (X (idx j))),
      (∀ j, IsCompact (E j)) ∧ (⋃ j, f (idx j) '' E j) ∈ nhds y := by
  classical
  obtain ⟨s, K, hK, hnhds⟩ := h y
  have key : ∀ (j : Fin s.card) (y' : {x // x ∈ s}), s.equivFin.symm j = y' →
      ∀ z : Y, z ∈ f y' '' K y' →
        z ∈ f (s.equivFin.symm j : ι) '' K (s.equivFin.symm j : ι) := by
    intro j y' hjy z hz
    cases hjy
    exact hz
  refine ⟨s.card, fun j => (s.equivFin.symm j : ι), fun j => K _, fun j => ?_, ?_⟩
  · exact hK _ (s.equivFin.symm j).2
  · refine Filter.mem_of_superset hnhds ?_
    intro z hz
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨i, hi, hz⟩ := hz
    exact ⟨s.equivFin ⟨i, hi⟩, key _ ⟨i, hi⟩ (Equiv.symm_apply_apply _ _) z hz⟩

/-- A disjoint union of finitely many types each of size below an uncountable cardinal has size
below that cardinal. -/
private theorem mk_sigma_fin_lt {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
    {m : ℕ} (T : Fin m → Type u) (h : ∀ j, Cardinal.mk (T j) < κ) :
    Cardinal.mk ((j : Fin m) × T j) < κ := by
  have hsup : (⨆ j, Cardinal.mk (T j)) < κ := by
    rcases m with _ | m
    · exact lt_of_le_of_lt (ciSup_le' fun j => j.elim0) (lt_trans Cardinal.aleph0_pos hκ)
    · obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j => Cardinal.mk (T j)
      exact lt_of_le_of_lt (ciSup_le' hj₀) (h j₀)
  rw [Cardinal.mk_sigma]
  refine lt_of_le_of_lt (Cardinal.sum_le_lift_mk_mul_iSup _)
    (Cardinal.mul_lt_of_lt hκ.le ?_ hsup)
  rw [Cardinal.lift_mk_fin]
  exact lt_trans Cardinal.natCast_lt_aleph0 hκ

namespace LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- An open subset of an object of the site, as an object of the site: its underlying space is the
open subspace itself, which stays below the size cutoff because it has no more points. -/
noncomputable def opensObj (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (T : S.category) (O : Opens T.obj) : S.category :=
  ⟨openLocallyQuasiCompactHausdorff S T O,
    (openLocallyQuasiCompactHausdorff_size_le S T O).trans_lt T.property⟩

/-- The open immersion of an open subset of an object of the site. -/
noncomputable def opensHom (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (T : S.category) (O : Opens T.obj) : S.opensObj T O ⟶ T :=
  ⟨⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩⟩⟩

/-- The open immersion of an open subset is the inclusion of the subtype, on points. -/
theorem opensHom_apply (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (T : S.category) (O : Opens T.obj) (z : (S.opensObj T O).obj) :
    (S.opensHom T O : (S.opensObj T O).obj → T.obj) z = z.1 := rfl

/-- The open immersion of an open subset has that subset as its range. -/
theorem range_opensHom (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (T : S.category) (O : Opens T.obj) :
    Set.range (S.opensHom T O : (S.opensObj T O).obj → T.obj) = (O : Set T.obj) :=
  Subtype.range_val

/-- The open immersion of an open subset is an open embedding. -/
theorem isOpenEmbedding_opensHom (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (T : S.category) (O : Opens T.obj) :
    Topology.IsOpenEmbedding (S.opensHom T O : (S.opensObj T O).obj → T.obj) :=
  O.2.isOpenEmbedding_subtypeVal

/-- The underlying map of a morphism of the site is continuous. -/
private theorem continuous_coe (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    {X Y : S.category} (k : X ⟶ Y) : Continuous (k : X.obj → Y.obj) :=
  (ConcreteCategory.hom ((siteToTop S).map k)).continuous

/-- An open covering of an object of the site is a Zariski covering family, as a presieve. -/
theorem opens_ofArrows_mem_zariskiPrecoverage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {T : S.category} {ι : Type*}
    (O : ι → Opens T.obj) (hcov : ∀ x : T.obj, ∃ i, x ∈ O i) :
    Presieve.ofArrows (fun i => S.opensObj T (O i)) (fun i => S.opensHom T (O i))
      ∈ S.zariskiPrecoverage T := by
  show _ ∈ (TopCat.precoverage.comap
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop)) T
  rw [Precoverage.mem_comap_iff]
  simp only [Presieve.map_ofArrows]
  show _ ∧ _
  refine ⟨?_, ?_⟩
  · rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
    intro y
    obtain ⟨i, hi⟩ := hcov y
    refine ⟨i, ?_⟩
    show y ∈ Set.range (S.opensHom T (O i) : (S.opensObj T (O i)).obj → T.obj)
    rw [S.range_opensHom T (O i)]
    exact hi
  · rw [MorphismProperty.ofArrows_mem_precoverage]
    exact fun i => S.isOpenEmbedding_opensHom T (O i)

/-- Let `{a_i : A_i → U}` be a family of arrows of the site belonging to a presieve `R`, let
`E_j ⊆ A_{i_j}` be quasi-compact subsets of finitely many of the sources, and let `V ⊆ U` be an
open subset contained in the union of the images of the `E_j`. Then there is an object `W` of the
site and a proper arrow `f : W ⟶ V` which on its own is a quasi-compact covering of `V`, together
with a Zariski covering of `W` whose composites to `U` factor through `R`. -/
theorem exists_properMorphisms_refinement_of_pieces
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    {U : S.category} (R : Presieve U) {ι : Type*} (A : ι → S.category) (a : ∀ i, A i ⟶ U)
    (hA : ∀ i, R (a i)) {m : ℕ} (idx : Fin m → ι)
    (E : ∀ j : Fin m, Set ((A (idx j)).obj)) (hE : ∀ j, IsCompact (E j)) (V : Opens U.obj)
    (hV : (V : Set U.obj) ⊆ ⋃ j, (a (idx j) : (A (idx j)).obj → U.obj) '' E j) :
    ∃ (W : S.category) (f : W ⟶ S.opensObj U V),
      S.properMorphisms f ∧
        Presieve.singleton f ∈ S.qcSite.pretopology (S.opensObj U V) ∧
          ∃ P : Presieve W, P ∈ S.zariskiPrecoverage W ∧
            P.FactorsThruAlong R (f ≫ S.opensHom U V) := by
  classical
  have : ∀ j, CompactSpace (E j) := fun j => isCompact_iff_compactSpace.mp (hE j)
  have hYsize : Cardinal.mk ((j : Fin m) × (E j)) < S.qcSite.cutoff :=
    mk_sigma_fin_lt S.qcSite.boundedSubcategory.aleph0_lt_cutoff _ fun j =>
      lt_of_le_of_lt (Cardinal.mk_set_le (E j)) (A (idx j)).property
  let Yob : S.category :=
    ⟨LocallyQuasiCompactHausdorff.of ((j : Fin m) × (E j)) inferInstance, hYsize⟩
  have hycont : Continuous
      (fun p : (j : Fin m) × (E j) => (a (idx p.1) : (A (idx p.1)).obj → U.obj) p.2.1) :=
    continuous_sigma fun j =>
      (S.continuous_coe (a (idx j))).comp continuous_subtype_val
  let yU : Yob ⟶ U := ⟨⟨TopCat.ofHom ⟨_, hycont⟩⟩⟩
  have hyapp : ∀ p : (j : Fin m) × (E j),
      (yU : Yob.obj → U.obj) p = (a (idx p.1) : (A (idx p.1)).obj → U.obj) p.2.1 := fun _ => rfl
  have : CompactSpace ((siteToTop S).obj Yob) :=
    inferInstanceAs (CompactSpace ((j : Fin m) × (E j)))
  have : T2Space ((siteToTop S).obj U) := U.obj.property.1
  have hyproper : _root_.IsProperMap
      (((siteToTop S).map yU).hom : (siteToTop S).obj Yob → (siteToTop S).obj U) :=
    (ConcreteCategory.hom ((siteToTop S).map yU)).continuous.isProperMap
  let Vob : S.category := S.opensObj U V
  let vU : Vob ⟶ U := S.opensHom U V
  have hVrange : Set.range (vU : Vob.obj → U.obj) = (V : Set U.obj) := S.range_opensHom U V
  let Z : S.category := Limits.pullback vU yU
  let p : Z ⟶ Vob := Limits.pullback.fst vU yU
  let q : Z ⟶ Yob := Limits.pullback.snd vU yU
  have hp : S.properMorphisms p := S.isProperMap_pullback_fst yU vU hyproper
  have hcond : (siteToTop S).map p ≫ (siteToTop S).map vU
      = (siteToTop S).map q ≫ (siteToTop S).map yU := by
    rw [← Functor.map_comp, ← Functor.map_comp, Limits.pullback.condition]
  have hcondpt : ∀ z : Z.obj, (vU : Vob.obj → U.obj) ((p : Z.obj → Vob.obj) z)
      = (yU : Yob.obj → U.obj) ((q : Z.obj → Yob.obj) z) := fun z =>
    ConcreteCategory.congr_hom hcond z
  have hpsurj : Function.Surjective (p : Z.obj → Vob.obj) := by
    intro b
    have hb : (vU : Vob.obj → U.obj) b ∈ (V : Set U.obj) := by
      rw [← hVrange]; exact Set.mem_range_self b
    obtain ⟨j, e, heE, hae⟩ : ∃ (j : Fin m) (e : (A (idx j)).obj), e ∈ E j ∧
        (a (idx j) : (A (idx j)).obj → U.obj) e = (vU : Vob.obj → U.obj) b := by
      have hmem := hV hb
      simp only [Set.mem_iUnion, Set.mem_image] at hmem
      obtain ⟨j, e, heE, hae⟩ := hmem
      exact ⟨j, e, heE, hae⟩
    refine ⟨(zariskiPullbackHomeo S yU vU).symm ⟨(b, ⟨j, ⟨e, heE⟩⟩), hae.symm⟩, ?_⟩
    have hfst := zariskiPullbackHomeo_fst S yU vU
      ((zariskiPullbackHomeo S yU vU).symm ⟨(b, ⟨j, ⟨e, heE⟩⟩), hae.symm⟩)
    rw [Homeomorph.apply_symm_apply] at hfst
    exact hfst.symm
  have hsingle : Presieve.singleton p ∈ S.qcSite.pretopology Vob := by
    have h := (S.qcSite.isCovering_iff_isQcCovering
      ({ I₀ := PUnit.{u + 1}, X := fun _ => Z, f := fun _ => p } :
        PreZeroHypercover.{u} Vob)).mpr ?_
    · rw [← Presieve.ofArrows_pUnit p]
      exact h
    · intro b
      obtain ⟨n, Ks, hKs, hnhds⟩ := proper_surjective_isQcCovering
        (p : Z.obj → Vob.obj) hp hpsurj b
      refine ⟨{PUnit.unit}, fun _ => ⋃ k, Ks k, fun _ _ => isCompact_iUnion hKs, ?_⟩
      refine Filter.mem_of_superset hnhds ?_
      intro z hz
      simp only [Set.mem_iUnion] at hz ⊢
      obtain ⟨k, y, hy, hyz⟩ := hz
      exact ⟨PUnit.unit, Finset.mem_singleton_self _,
        ⟨y, Set.mem_iUnion.mpr ⟨k, hy⟩, hyz⟩⟩
  have hqcont : Continuous (q : Z.obj → Yob.obj) := S.continuous_coe q
  let O : Fin m → Opens Z.obj := fun j =>
    ⟨(q : Z.obj → Yob.obj) ⁻¹' Set.range (Sigma.mk (β := fun k : Fin m => (E k)) j),
      isOpen_range_sigmaMk.preimage hqcont⟩
  refine ⟨Z, p, hp, hsingle,
    Presieve.ofArrows (fun j => S.opensObj Z (O j)) (fun j => S.opensHom Z (O j)), ?_, ?_⟩
  · refine S.opens_ofArrows_mem_zariskiPrecoverage O fun z => ?_
    exact ⟨((q : Z.obj → Yob.obj) z).1, ⟨((q : Z.obj → Yob.obj) z).2, rfl⟩⟩
  · rintro - - ⟨j⟩
    have hind : Topology.IsInducing
        (Set.codRestrict (Sigma.mk (β := fun k : Fin m => (E k)) j)
          (Set.range (Sigma.mk (β := fun k : Fin m => (E k)) j))
          fun x => Set.mem_range_self x) :=
      (Topology.IsEmbedding.sigmaMk (σ := fun k : Fin m => (E k)) (i := j)).isInducing.codRestrict
        fun x => Set.mem_range_self x
    let ej : (E j) ≃ₜ Set.range (Sigma.mk (β := fun k : Fin m => (E k)) j) :=
      Equiv.toHomeomorphOfIsInducing
        (Equiv.ofInjective (Sigma.mk (β := fun k : Fin m => (E k)) j) sigma_mk_injective) hind
    have hej : ∀ x : (E j),
        ((ej x : Set.range (Sigma.mk (β := fun k : Fin m => (E k)) j)) :
          (j : Fin m) × (E j)) = ⟨j, x⟩ := fun _ => rfl
    have hifun : Continuous
        (fun z : (S.opensObj Z (O j)).obj =>
          ((ej.symm ⟨(q : Z.obj → Yob.obj) z.1, z.2⟩ : (E j)) : (A (idx j)).obj)) :=
      (ej.symm.continuous.comp
        ((hqcont.comp continuous_subtype_val).subtype_mk _)).subtype_val
    refine ⟨A (idx j), ⟨⟨TopCat.ofHom ⟨_, hifun⟩⟩⟩, a (idx j), hA (idx j), ?_⟩
    refine ConcreteCategory.hom_ext _ _ fun z => ?_
    show (a (idx j) : (A (idx j)).obj → U.obj)
        ((ej.symm ⟨(q : Z.obj → Yob.obj) z.1, z.2⟩ : (E j)) : (A (idx j)).obj)
      = (vU : Vob.obj → U.obj) ((p : Z.obj → Vob.obj) z.1)
    have hgoal : ∀ x : (E j), (⟨j, x⟩ : (j : Fin m) × (E j)) = (q : Z.obj → Yob.obj) z.1 →
        (a (idx j) : (A (idx j)).obj → U.obj) (x : (A (idx j)).obj)
          = (vU : Vob.obj → U.obj) ((p : Z.obj → Vob.obj) z.1) := fun x hx =>
      (hyapp ⟨j, x⟩).symm.trans
        ((congrArg (fun t : Yob.obj => (yU : Yob.obj → U.obj) t) hx).trans (hcondpt z.1).symm)
    refine hgoal _ ?_
    exact (hej (ej.symm ⟨(q : Z.obj → Yob.obj) z.1, z.2⟩)).symm.trans
      (congrArg Subtype.val (ej.apply_symm_apply ⟨(q : Z.obj → Yob.obj) z.1, z.2⟩))

/-- **Stacks 0EZI**, the refinement condition. Every quasi-compact covering of an object `U` of the
site is refined in three stages: by a Zariski covering `{V ⟶ U}`, then over each `V` by a single
proper arrow `f : W ⟶ V` which is itself a quasi-compact covering, and finally by a Zariski
covering of `W` whose composites factor through the given covering. This is condition (0EZ8) of
Situation 0EZ3 with the proper arrows as the class `P`, the quasi-compact topology as `τ` and the
Zariski topology as `τ'`. -/
@[stacks 0EZI "condition (0EZ8) of Situation 0EZ3: a quasi-compact covering is refined by a
Zariski covering, then one proper arrow, then a Zariski covering"]
theorem exists_zariski_properMorphisms_refinement
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (U : S.category) (R : Presieve U) (hR : R ∈ S.qcSite.pretopology U) :
    ∃ T : Presieve U, T ∈ S.zariskiPrecoverage U ∧
      ∀ ⦃V : S.category⦄ (v : V ⟶ U), T v →
        ∃ (W : S.category) (f : W ⟶ V), S.properMorphisms f ∧
          Presieve.singleton f ∈ S.qcSite.pretopology V ∧
            ∃ P : Presieve W, P ∈ S.zariskiPrecoverage W ∧
              P.FactorsThruAlong R (f ≫ v) := by
  classical
  have hqc : IsQcCovering (fun i => (R.preZeroHypercover.f i :
      (R.preZeroHypercover.X i).obj → U.obj)) := S.qcSite.covering_is_qc R hR
  have hA : ∀ i, R (R.preZeroHypercover.f i) := by
    intro i
    have h := R.preZeroHypercover.presieve₀_f i
    rwa [R.presieve₀_preZeroHypercover] at h
  choose m idx E hEc hnhds using fun x : U.obj => exists_fin_of_isQcCovering hqc x
  choose V hVsub hVopen hxV using fun x : U.obj => mem_nhds_iff.mp (hnhds x)
  refine ⟨Presieve.ofArrows (fun x : U.obj => S.opensObj U ⟨V x, hVopen x⟩)
      (fun x : U.obj => S.opensHom U ⟨V x, hVopen x⟩),
    S.opens_ofArrows_mem_zariskiPrecoverage (fun x => ⟨V x, hVopen x⟩)
      (fun x => ⟨x, hxV x⟩), ?_⟩
  rintro - - ⟨x⟩
  exact S.exists_properMorphisms_refinement_of_pieces R R.preZeroHypercover.X
    R.preZeroHypercover.f hA (idx x) (E x) (hEc x) ⟨V x, hVopen x⟩ (hVsub x)

end LocallyQuasiCompactZariskiSituation

end Stacks.Topology

end
