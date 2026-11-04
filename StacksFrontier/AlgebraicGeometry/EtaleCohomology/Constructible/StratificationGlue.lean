module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocallyClosedStratum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Assembling one constructible stratification out of finitely many

A `AlgebraicGeometry.ConstructibleStratification` of an open subscheme is a finite partition of it
by constructible locally closed subschemes. Two operations on such partitions are needed to pass
between the local and the global form of constructibility of an étale sheaf, and both are carried
out here, for an arbitrary condition `P` on the strata which is stable under isomorphism of sheaves
and under inverse image.

* **Restriction.** A stratification of the whole scheme restricts to any open subscheme: intersect
  each stratum with the open subscheme.
* **Gluing.** Finitely many quasi-compact opens covering an open subscheme, each carrying a
  stratification, assemble into one stratification of the union: order the opens, and cut the
  strata of the `j`-th one down to the part lying outside the earlier ones.

In both cases the new stratum is cut out **inside the stratum scheme**, as the reduced induced
subscheme on the preimage there of a locally closed subset of the ambient — never as a subscheme of
the ambient with the same image. The distinction is the whole point: the condition `P` on a stratum
is a condition on sheaves over *that* scheme, so it is transported to the new stratum by inverse
image along the morphism `AlgebraicGeometry.BigEtaleSite.strataCutHom`, which exists only because
the new stratum is built over the old one. A subscheme of the ambient with the same image would
have to be factored through the original immersion, and for an arbitrary immersion there is no such
factorization.

## Main definitions

* `AlgebraicGeometry.smallEtalePullObj` — inverse image of a sheaf along a morphism of the big
  étale site, as an abbreviation.
* `AlgebraicGeometry.BigEtaleSite.strataCutObj` and
  `AlgebraicGeometry.BigEtaleSite.strataCutHom` — the part of an immersed subscheme lying over a
  locally closed subset of the ambient, and its immersion into that subscheme.

## Main results

* `AlgebraicGeometry.BigEtaleSite.range_strataCutHom_comp` — the cut part has image the
  intersection of the original image with the locally closed subset.
* `AlgebraicGeometry.strataCondition_strataCutHom` — the condition on the strata passes to the cut
  part.
* `AlgebraicGeometry.isConstructible_range_of_isConstructible_top` — constructibility inside the
  top open subscheme is constructibility in the scheme.
* `AlgebraicGeometry.exists_constructibleStratification_restrict` — the restriction operation.
* `AlgebraicGeometry.exists_constructibleStratification_of_cover` — the gluing operation.

## Implementation notes

`AlgebraicGeometry.ConstructibleStratification.ofPartition` is **not** usable for either operation,
despite being the file's natural-looking constructor: it builds each stratum as
`AlgebraicGeometry.BigEtaleSite.locallyClosedObj` of the *ambient* scheme, i.e. with the reduced
induced structure over the ambient, and that is exactly the shape from which the condition on the
strata cannot be recovered. The records here are built field by field instead.

The strata of the glued stratification are indexed by a sigma type over the covering opens, carried
to `Fin (∑ j, (s j).n)` by `finSigmaFinEquiv`.

Quasi-separatedness of the ambient scheme enters once, and only in the gluing: the constructibility
field of an input stratification is a statement inside the covering open, and it is turned into a
statement about a subset of the ambient scheme by
`CategoryTheory.isConstructible_preimage_iff_of_isOpenEmbedding`, whose retrocompactness hypothesis
for a quasi-compact open is quasi-separatedness. Going back down to the open subscheme being
stratified needs nothing, since `Topology.IsConstructible.preimage_of_isOpenEmbedding` is free.

No `@[stacks]` attribute appears in this file. The two operations are infrastructure for Tag 095E,
not statements of the source.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 095E](https://stacks.math.columbia.edu/tag/095E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe v w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {D : Type w} [Category.{v} D]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- Inverse image of a sheaf along a morphism of the big étale site. -/
public abbrev smallEtalePullObj {S T : B.Scheme} (q : T ⟶ S)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) D) :
    Sheaf (SmallEtale.topology B T.obj T.property) D :=
  ((smallEtaleBaseChange B q).sheafPullback D
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).obj G

variable (Z : B.Scheme)

namespace BigEtaleSite

/-- The part of a subscheme immersed in `Z` lying over a locally closed subset `L` of `Z`: the
reduced induced subscheme of the stratum on the preimage of `L`, which is locally closed there. -/
@[ega "IV 6.9.3" "partial"]
public def strataCutObj {Y : B.Scheme} (ι : Y ⟶ Z) {L : Set Z.obj}
    (hL : IsLocallyClosed L) : B.Scheme :=
  B.locallyClosedObj Y (hL.preimage (B.inclusion.map ι).base.hom.continuous)

/-- The immersion of `AlgebraicGeometry.BigEtaleSite.strataCutObj` into the subscheme it was cut
out of. -/
public def strataCutHom {Y : B.Scheme} (ι : Y ⟶ Z) {L : Set Z.obj}
    (hL : IsLocallyClosed L) : B.strataCutObj Z ι hL ⟶ Y :=
  B.locallyClosedHom Y (hL.preimage (B.inclusion.map ι).base.hom.continuous)

/-- The image of a composite of morphisms of the big étale site is the image of the image. -/
private theorem range_inclusion_map_comp {X Y W : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ W) :
    Set.range (B.inclusion.map (f ≫ g)).base =
      ⇑(B.inclusion.map g).base '' Set.range (B.inclusion.map f).base := by
  rw [show B.inclusion.map (f ≫ g) = B.inclusion.map f ≫ B.inclusion.map g from
      Functor.map_comp _ _ _,
    show (⇑(B.inclusion.map f ≫ B.inclusion.map g)) =
      ⇑(B.inclusion.map g) ∘ ⇑(B.inclusion.map f) from funext fun z => Scheme.Hom.comp_apply _ _ _,
    Set.range_comp]

/-- **The cut part has the expected image**: the intersection of the image of the original
immersion with the locally closed subset. -/
public theorem range_strataCutHom_comp {Y : B.Scheme} (ι : Y ⟶ Z) {L : Set Z.obj}
    (hL : IsLocallyClosed L) :
    Set.range (B.inclusion.map (B.strataCutHom Z ι hL ≫ ι)).base =
      Set.range (B.inclusion.map ι).base ∩ L := by
  have h1 : Set.range ⇑(B.inclusion.map (B.strataCutHom Z ι hL)) =
      ⇑(B.inclusion.map ι) ⁻¹' L :=
    B.range_locallyClosedHom Y (hL.preimage (B.inclusion.map ι).base.hom.continuous)
  rw [range_inclusion_map_comp, h1, Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The cut part is immersed in the ambient scheme. -/
public theorem isImmersion_strataCutHom_comp {Y : B.Scheme} (ι : Y ⟶ Z)
    (hι : IsImmersion (B.inclusion.map ι)) {L : Set Z.obj} (hL : IsLocallyClosed L) :
    IsImmersion (B.inclusion.map (B.strataCutHom Z ι hL ≫ ι)) := by
  have h1 : IsImmersion (B.inclusion.map (B.strataCutHom Z ι hL)) :=
    B.isImmersion_map_locallyClosedHom Y _
  rw [Functor.map_comp]
  infer_instance

end BigEtaleSite

/-- Constructibility of a subset can be checked after pulling back along a surjective open
embedding. -/
private theorem isConstructible_of_preimage_of_surjective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenEmbedding f) (hs : Function.Surjective f)
    {S : Set Y} (h : IsConstructible (f ⁻¹' S)) : IsConstructible S :=
  (isConstructible_preimage_iff_of_isOpenEmbedding hf (hs.range_eq ▸ IsRetrocompact.univ)
    (hs.range_eq ▸ S.subset_univ)).mp h

/-- **The condition on a stratum passes to the cut part.** This is where the cut part being built
*over the stratum* is used: the inverse image along
`AlgebraicGeometry.BigEtaleSite.strataCutHom` carries the condition there, and the composition law
for inverse image identifies the result with the inverse image along the composite. -/
public theorem strataCondition_strataCutHom
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    {Y : B.Scheme} (ι : Y ⟶ Z) {L : Set Z.obj} (hL : IsLocallyClosed L)
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D)
    (h : P Y (smallEtalePullObj B ι G)) :
    P (B.strataCutObj Z ι hL) (smallEtalePullObj B (B.strataCutHom Z ι hL ≫ ι) G) :=
  hPIso _ ((smallEtaleSheafPullbackCompIso B (B.strataCutObj Z ι hL) Y Z
    (B.strataCutHom Z ι hL) ι D).app G) (hPPull _ _ (B.strataCutHom Z ι hL) _ h)

/-- Constructibility of the image of an immersed subscheme as a subset of the ambient scheme, from
its constructibility inside the top open subscheme. The top open subscheme has the whole space as
image, so no compactness is involved. -/
public theorem isConstructible_range_of_isConstructible_top {Y : B.Scheme} (ι : Y ⟶ Z)
    (h : IsConstructible
      ((⊤ : Z.obj.Opens).ι.base ⁻¹' Set.range (B.inclusion.map ι).base)) :
    IsConstructible (Set.range (B.inclusion.map ι).base) := by
  refine isConstructible_of_preimage_of_surjective (f := ⇑(⊤ : Z.obj.Opens).ι.base)
    (⊤ : Z.obj.Opens).isOpenEmbedding ?_ h
  rw [← Set.range_eq_univ, (⊤ : Z.obj.Opens).range_ι]
  rfl

/-- **A stratification of the whole scheme restricts to any open subscheme.** Each stratum is
replaced by its part lying over the open subscheme, an open subscheme of that stratum; the
condition on the strata follows it there. -/
public theorem exists_constructibleStratification_restrict
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D) (Vopen : Z.obj.Opens)
    (t : ConstructibleStratification B Z ⊤)
    (ht : ∀ i, P (t.piece i) (smallEtalePullObj B (t.inclusion i) G)) :
    ∃ t' : ConstructibleStratification B Z Vopen,
      ∀ i, P (t'.piece i) (smallEtalePullObj B (t'.inclusion i) G) := by
  have hVlc : IsLocallyClosed ((Vopen : Z.obj.Opens) : Set Z.obj) := Vopen.2.isLocallyClosed
  have hrange : ∀ i, Set.range (B.inclusion.map (B.strataCutHom Z (t.inclusion i) hVlc ≫
        t.inclusion i)).base =
      Set.range (B.inclusion.map (t.inclusion i)).base ∩ ((Vopen : Z.obj.Opens) : Set Z.obj) :=
    fun i => B.range_strataCutHom_comp Z _ _
  have hpre : Vopen.ι.base ⁻¹' ((Vopen : Z.obj.Opens) : Set Z.obj) = Set.univ := by
    rw [Set.preimage_eq_univ_iff, Vopen.range_ι]
  refine ⟨{ n := t.n
            piece := fun i => B.strataCutObj Z (t.inclusion i) hVlc
            inclusion := fun i => B.strataCutHom Z (t.inclusion i) hVlc ≫ t.inclusion i
            isImmersion := fun i =>
              B.isImmersion_strataCutHom_comp Z _ (t.isImmersion i) _
            contained := fun i => Set.Subset.trans (hrange i).subset Set.inter_subset_right
            constructible := fun i => by
              rw [hrange, Set.preimage_inter, hpre, Set.inter_univ]
              exact (isConstructible_range_of_isConstructible_top B Z (t.inclusion i)
                (t.constructible i)).preimage_of_isOpenEmbedding Vopen.isOpenEmbedding
            pairwise_disjoint := fun i i' hii' => by
              rw [hrange, hrange]
              exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left
                (t.pairwise_disjoint i i' hii')
            covers := by
              have hcov := t.covers
              simp only [TopologicalSpace.Opens.coe_top] at hcov
              refine Set.Subset.antisymm (fun x hx => ?_)
                (Set.iUnion_subset fun i => Set.Subset.trans (hrange i).subset
                  Set.inter_subset_right)
              obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
              exact Set.mem_iUnion.mpr ⟨i, (hrange i).symm.subset ⟨hi, hx⟩⟩ }, ?_⟩
  exact fun i => strataCondition_strataCutHom B Z P hPIso hPPull _ _ G (ht i)

/-- **A stratification of an open subscheme pushes forward along an open immersion.** The strata
are the *same* objects of the big étale site; only their structure morphism changes, by composition
with the open immersion, so the condition on them follows by the composition law for inverse image.

The target open subscheme is given together with the identification of its underlying set as the
image of the source one, which is how the statement is used: the image of an affine open under an
open immersion. -/
public theorem exists_constructibleStratification_image
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    {Y : B.Scheme} (y : Y ⟶ Z) (hyim : IsOpenImmersion (B.inclusion.map y))
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D)
    (Uopen : Y.obj.Opens) (Vopen : Z.obj.Opens)
    (hV : ((Vopen : Z.obj.Opens) : Set Z.obj) =
      ⇑(B.inclusion.map y).base '' ((Uopen : Y.obj.Opens) : Set Y.obj))
    (t : ConstructibleStratification B Y Uopen)
    (ht : ∀ i, P (t.piece i)
      (smallEtalePullObj B (t.inclusion i) (smallEtalePullObj B y G))) :
    ∃ t' : ConstructibleStratification B Z Vopen,
      ∀ i, P (t'.piece i) (smallEtalePullObj B (t'.inclusion i) G) := by
  have hy : Topology.IsOpenEmbedding ⇑(B.inclusion.map y).base :=
    (B.inclusion.map y).isOpenEmbedding
  have hrange : ∀ i, Set.range (B.inclusion.map (t.inclusion i ≫ y)).base =
      ⇑(B.inclusion.map y).base '' Set.range (B.inclusion.map (t.inclusion i)).base :=
    fun i => BigEtaleSite.range_inclusion_map_comp B _ _
  have hcon : ∀ i, IsConstructible (Vopen.ι.base ⁻¹'
      (⇑(B.inclusion.map y).base '' Set.range (B.inclusion.map (t.inclusion i)).base)) := by
    intro i
    let eh : (Uopen : Type u) ≃ₜ (Vopen : Type u) :=
      (hy.isEmbedding.homeomorphImage ((Uopen : Y.obj.Opens) : Set Y.obj)).trans
        (Homeomorph.setCongr hV.symm)
    have hcompat : ∀ z : (Uopen : Type u), (Vopen.ι.base (eh z) : Z.obj) =
        (B.inclusion.map y).base (Uopen.ι.base z) := fun _ => rfl
    have hpre : eh ⁻¹' (Vopen.ι.base ⁻¹'
        (⇑(B.inclusion.map y).base '' Set.range (B.inclusion.map (t.inclusion i)).base)) =
        Uopen.ι.base ⁻¹' Set.range (B.inclusion.map (t.inclusion i)).base := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image, hcompat z]
      refine ⟨fun ⟨a, ha, hae⟩ => ?_, fun hz => ⟨Uopen.ι.base z, hz, rfl⟩⟩
      exact hy.injective hae ▸ ha
    refine isConstructible_of_preimage_of_surjective eh.isOpenEmbedding eh.surjective ?_
    rw [hpre]
    exact t.constructible i
  refine ⟨{ n := t.n
            piece := t.piece
            inclusion := fun i => t.inclusion i ≫ y
            isImmersion := fun i => by
              have h1 : IsImmersion (B.inclusion.map (t.inclusion i)) := t.isImmersion i
              rw [Functor.map_comp]
              infer_instance
            contained := fun i => by
              rw [hrange, hV]
              exact Set.image_mono (t.contained i)
            constructible := fun i => by rw [hrange]; exact hcon i
            pairwise_disjoint := fun i i' hii' => by
              rw [hrange, hrange]
              exact Set.disjoint_image_of_injective hy.injective
                (t.pairwise_disjoint i i' hii')
            covers := by
              rw [hV, t.covers, Set.image_iUnion]
              exact Set.iUnion_congr fun i => (hrange i).symm }, ?_⟩
  exact fun i => hPIso _
    ((smallEtaleSheafPullbackCompIso B (t.piece i) Y Z (t.inclusion i) y D).app G) (ht i)

variable [QuasiSeparatedSpace Z.obj]

/-- **Finitely many stratified quasi-compact opens glue to one stratification of their union.**
The opens are ordered by their index; the strata of the `j`-th one are cut down to the part lying
outside all the earlier opens, which makes the resulting family disjoint without changing the
union, and the condition on the strata follows each stratum into its cut part. -/
public theorem exists_constructibleStratification_of_cover
    (P : ∀ T : B.Scheme, Sheaf (SmallEtale.topology B T.obj T.property) D → Prop)
    (hPIso : ∀ (T : B.Scheme) {F G : Sheaf (SmallEtale.topology B T.obj T.property) D},
      (F ≅ G) → P T F → P T G)
    (hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) D),
      P T G → P T' (smallEtalePullObj B q G))
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) D) (Vopen : Z.obj.Opens)
    {m : ℕ} (O : Fin m → Z.obj.Opens) (hOc : ∀ j, IsCompact (O j : Set Z.obj))
    (hOsub : ∀ j, (O j : Set Z.obj) ⊆ (Vopen : Set Z.obj))
    (hcov : (Vopen : Set Z.obj) = ⋃ j, (O j : Set Z.obj))
    (s : ∀ j, ConstructibleStratification B Z (O j))
    (hs : ∀ j i, P ((s j).piece i) (smallEtalePullObj B ((s j).inclusion i) G)) :
    ∃ t : ConstructibleStratification B Z Vopen,
      ∀ i, P (t.piece i) (smallEtalePullObj B (t.inclusion i) G) := by
  classical
  set Olt : Fin m → Set Z.obj := fun j => ⋃ j' ∈ {j' : Fin m | j' < j}, (O j' : Set Z.obj)
    with hOltDef
  have hOltOpen : ∀ j, IsOpen (Olt j) := fun j => isOpen_biUnion fun j' _ => (O j').2
  have hOltComp : ∀ j, IsCompact (Olt j) := fun j =>
    (Set.toFinite _).isCompact_biUnion fun j' _ => hOc j'
  have hOltLC : ∀ j, IsLocallyClosed (Olt j)ᶜ := fun j =>
    (hOltOpen j).isClosed_compl.isLocallyClosed
  have hOltsub : ∀ {j j' : Fin m}, j' < j → (O j' : Set Z.obj) ⊆ Olt j := by
    intro j j' hlt
    exact Set.subset_biUnion_of_mem (u := fun k => (O k : Set Z.obj))
      (show j' ∈ {k | k < j} from hlt)
  set pc : (Σ j : Fin m, Fin ((s j).n)) → B.Scheme :=
    fun p => B.strataCutObj Z ((s p.1).inclusion p.2) (hOltLC p.1)
  set ic : ∀ p : (Σ j : Fin m, Fin ((s j).n)), pc p ⟶ Z :=
    fun p => B.strataCutHom Z ((s p.1).inclusion p.2) (hOltLC p.1) ≫ (s p.1).inclusion p.2
  have hrange : ∀ p, Set.range (B.inclusion.map (ic p)).base =
      Set.range (B.inclusion.map ((s p.1).inclusion p.2)).base ∩ (Olt p.1)ᶜ :=
    fun p => B.range_strataCutHom_comp Z _ _
  have hRangeCon : ∀ (j : Fin m) (i : Fin ((s j).n)),
      IsConstructible (Set.range (B.inclusion.map ((s j).inclusion i)).base) := by
    intro j i
    have hOE : IsOpenEmbedding ⇑(O j).ι.base := (O j).isOpenEmbedding
    have hR : Set.range ⇑(O j).ι.base = ((O j : Z.obj.Opens) : Set Z.obj) := (O j).range_ι
    have hRetro : IsRetrocompact (Set.range ⇑(O j).ι.base) := by
      rw [hR]; exact (hOc j).isRetrocompact (O j).2
    have hsub : Set.range (B.inclusion.map ((s j).inclusion i)).base ⊆
        Set.range ⇑(O j).ι.base := by
      rw [hR]; exact (s j).contained i
    exact (isConstructible_preimage_iff_of_isOpenEmbedding hOE hRetro hsub).mp
      ((s j).constructible i)
  have hCutCon : ∀ p, IsConstructible (Set.range (B.inclusion.map (ic p)).base) := by
    intro p
    rw [hrange p]
    exact (hRangeCon p.1 p.2).inter (((hOltComp p.1).isConstructible (hOltOpen p.1)).compl)
  let e := finSigmaFinEquiv (n := fun j : Fin m => (s j).n)
  refine ⟨{ n := ∑ j, (s j).n
            piece := fun k => pc (e.symm k)
            inclusion := fun k => ic (e.symm k)
            isImmersion := fun k =>
              B.isImmersion_strataCutHom_comp Z _ ((s _).isImmersion _) _
            contained := fun k => by
              rw [hrange]
              exact Set.Subset.trans Set.inter_subset_left
                (Set.Subset.trans ((s _).contained _) (hOsub _))
            constructible := fun k =>
              (hCutCon (e.symm k)).preimage_of_isOpenEmbedding Vopen.isOpenEmbedding
            pairwise_disjoint := ?_
            covers := ?_ }, ?_⟩
  · have key : ∀ p p' : (Σ j : Fin m, Fin ((s j).n)), p ≠ p' →
        Disjoint (Set.range (B.inclusion.map (ic p)).base)
          (Set.range (B.inclusion.map (ic p')).base) := by
      rintro ⟨j, i⟩ ⟨j', i'⟩ hne
      rw [hrange, hrange]
      rcases eq_or_ne j j' with rfl | hjj'
      · have hii' : i ≠ i' := by
          intro h
          exact hne (by rw [h])
        exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left
          ((s j).pairwise_disjoint i i' hii')
      · rcases lt_or_gt_of_ne hjj' with hlt | hlt
        · refine Set.disjoint_left.mpr ?_
          intro x hx hx'
          exact hx'.2 (hOltsub hlt ((s j).contained i hx.1))
        · refine Set.disjoint_left.mpr ?_
          intro x hx hx'
          exact hx.2 (hOltsub hlt ((s j').contained i' hx'.1))
    exact fun k k' hkk' => key _ _ fun h => hkk' (e.symm.injective h)
  · refine Set.Subset.antisymm (fun x hxV => ?_) ?_
    · have hx : x ∈ ⋃ j, (O j : Set Z.obj) := by rw [← hcov]; exact hxV
      obtain ⟨j0, hj0⟩ := Set.mem_iUnion.mp hx
      have hmin : ∃ j : Fin m, x ∈ (O j : Set Z.obj) ∧
          ∀ j' : Fin m, j' < j → x ∉ (O j' : Set Z.obj) := by
        have hTne : (Finset.univ.filter (fun j : Fin m => x ∈ (O j : Set Z.obj))).Nonempty :=
          ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩⟩
        refine ⟨_, (Finset.mem_filter.mp (Finset.min'_mem _ hTne)).2, fun j' hj' hmem => ?_⟩
        exact absurd (Finset.min'_le _ j' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩))
          (not_le.mpr hj')
      obtain ⟨jm, hjmmem, hjmmin⟩ := hmin
      have hnotlt : x ∈ (Olt jm)ᶜ := by
        intro hmem
        simp only [hOltDef, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hmem
        obtain ⟨j', hj'lt, hj'mem⟩ := hmem
        exact hjmmin j' hj'lt hj'mem
      have hjm2 : x ∈ ((O jm : Z.obj.Opens) : Set Z.obj) := hjmmem
      rw [(s jm).covers] at hjm2
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hjm2
      refine Set.mem_iUnion.mpr ⟨e ⟨jm, i⟩, ?_⟩
      rw [Equiv.symm_apply_apply, hrange]
      exact ⟨hi, hnotlt⟩
    · refine Set.iUnion_subset fun k => ?_
      rw [hrange]
      exact Set.Subset.trans Set.inter_subset_left
        (Set.Subset.trans ((s _).contained _) (hOsub _))
  · exact fun k => strataCondition_strataCutHom B Z P hPIso hPPull _ _ G (hs _ _)

end AlgebraicGeometry

end
