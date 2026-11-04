module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Irreducible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleNeighbourhood.FiberLifting
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Branches
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchEtaleCriterion

/-!
# Branches of a fibre via étale neighbourhoods of the total space

Let `f : X ⟶ S` and let `x` be a point of `X`. The number of branches of the fibre
`f.fiber (f x)` at `f.asFiber x` is the supremum, over the elementary étale neighbourhoods `U` of
`x` in `X`, of the number of irreducible components of the fibre of `U.toBase ≫ f` over `f x`
passing through the distinguished point. The same formula computes the number of geometric
branches, with the supremum taken over all étale neighbourhoods. Consequently the fibre is
unibranch at the point exactly when every one of those fibres of elementary étale neighbourhoods
has a single irreducible component through its distinguished point, and geometrically unibranch
exactly when the same holds over all étale neighbourhoods.

The two formulae are deduced from the corresponding formulae for a point of a scheme by comparing
étale neighbourhoods of the fibre with fibres of étale neighbourhoods of the total space, in both
directions: an étale neighbourhood of `x` induces one of `f.asFiber x` by taking fibres, and
conversely every étale neighbourhood of `f.asFiber x` is refined by such a fibre.

## Main results

* `AlgebraicGeometry.numberOfBranches_fiber_eq_iSup_encard_irreducibleComponentsThrough`: the
  number of branches of a fibre.
* `AlgebraicGeometry.numberOfGeometricBranches_fiber_eq_iSup_encard`: the number of geometric
  branches of a fibre.
* `AlgebraicGeometry.isUnibranchAt_fiber_iff_existsUnique_irreducibleComponent`: the unibranch
  criterion for a fibre.
* `AlgebraicGeometry.isGeometricallyUnibranchAt_fiber_iff_existsUnique_irreducibleComponent`: the
  geometrically unibranch criterion for a fibre.

## Implementation notes

The distinguished point of each neighbourhood's fibre is obtained from the homeomorphism between
that fibre and the inverse image of the base point, and the counts use extended cardinality, as
do the numbers of branches themselves.

The two unibranch criteria are obtained from the formulae exactly as their counterparts for a
point of a scheme are obtained from theirs: the supremum equals one precisely when every term
does, because every term is at least one and the index sets are nonempty, witnessed by
`AlgebraicGeometry.EtaleNeighborhood.self`. "Exactly one irreducible component through the
distinguished point" is again written as unique existence in the subtype
`irreducibleComponents`.

## References

* [Stacks Project, Tag 0CB5](https://stacks.math.columbia.edu/tag/0CB5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Irreducible components through a point and open embeddings -/

/-- The closure of the image of an irreducible component under an open embedding, taken through a
point of the component, is an irreducible component of the target. -/
private theorem closure_image_component_mem {Y Z : Type u} [TopologicalSpace Y]
    [TopologicalSpace Z] (e : Y → Z) (he : Topology.IsOpenEmbedding e) (y : Y) {C : Set Y}
    (hC : C ∈ irreducibleComponents Y) (hy : y ∈ C) :
    closure (e '' C) ∈ irreducibleComponents Z := by
  have hE : IsIrreducible (closure (e '' C)) := (hC.1.image e he.continuous.continuousOn).closure
  refine ⟨hE, fun F hF hEF => ?_⟩
  have hne : (F ∩ Set.range e).Nonempty :=
    ⟨e y, hEF (subset_closure ⟨y, hy, rfl⟩), ⟨y, rfl⟩⟩
  have hpre : IsIrreducible (e ⁻¹' F) := hF.preimage he hne
  have hpreC : e ⁻¹' F ⊆ C :=
    hC.2 hpre (fun z hz => hEF (subset_closure ⟨z, hz, rfl⟩))
  have hFclosure : F ⊆ closure (F ∩ Set.range e) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hF.2 he.isOpen_range hne
  rw [← Set.image_preimage_eq_inter_range] at hFclosure
  exact hFclosure.trans (closure_mono (Set.image_mono hpreC))

/-- An open embedding induces a bijection between the irreducible components through a point and
the irreducible components through its image. -/
private theorem encard_irreducibleComponents_through_eq_of_isOpenEmbedding
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y → Z) (he : Topology.IsOpenEmbedding e) (y : Y) :
    Set.encard {C ∈ irreducibleComponents Y | y ∈ C} =
      Set.encard {D ∈ irreducibleComponents Z | e y ∈ D} := by
  let s : Set (Set Y) := {C ∈ irreducibleComponents Y | y ∈ C}
  let t : Set (Set Z) := {D ∈ irreducibleComponents Z | e y ∈ D}
  let F : s → t := fun C =>
    ⟨closure (e '' (C : Set Y)),
      closure_image_component_mem e he y C.2.1 C.2.2,
      subset_closure ⟨y, C.2.2, rfl⟩⟩
  let G : t → s := fun D =>
    ⟨e ⁻¹' (D : Set Z),
      preimage_mem_irreducibleComponents D.2.1 he ⟨e y, D.2.2, ⟨y, rfl⟩⟩,
      D.2.2⟩
  have hGF : Function.LeftInverse G F := fun C => Subtype.ext <| Set.Subset.antisymm
    (C.2.1.2 (preimage_mem_irreducibleComponents (F C).2.1 he ⟨e y, (F C).2.2, ⟨y, rfl⟩⟩).1
      (fun z hz => subset_closure ⟨z, hz, rfl⟩))
    (fun z hz => subset_closure ⟨z, hz, rfl⟩)
  have hFG : Function.RightInverse G F := fun D => Subtype.ext <|
    closure_image_preimage_of_isPreirreducible e he.isOpenMap (D : Set Z)
      ⟨y, D.2.2⟩ D.2.1.1.2 (isClosed_of_mem_irreducibleComponents _ D.2.1)
  exact Set.encard_congr ⟨F, G, hGF, hFG⟩

/-! ### Fibres of étale neighbourhoods as étale neighbourhoods of the fibre -/

/-- A preimmersion induces an isomorphism of residue fields at every point of its source. -/
private lemma residueFieldMap_isIso_of_isPreimmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsPreimmersion g] (x : X) : IsIso (g.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(g.residueFieldMap x).hom.injective, fun b => ?_⟩
  obtain ⟨a, ha⟩ := X.residue_surjective x b
  obtain ⟨c, hc⟩ := g.stalkMap_surjective x a
  refine ⟨Y.residue (g x) c, ?_⟩
  show (g.residueFieldMap x).hom ((Y.residue (g x)).hom c) = b
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.residue_residueFieldMap g x,
    CommRingCat.hom_comp, RingHom.comp_apply, hc, ha]

/-- If `f` has an isomorphism on residue fields at `x`, then so does `f ≫ g` exactly when `g`
does at `f x`. -/
private lemma isIso_residueFieldMap_comp_iff_left {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (f.residueFieldMap x)] :
    IsIso ((f ≫ g).residueFieldMap x) ↔ IsIso (g.residueFieldMap (f x)) := by
  rw [Scheme.residueFieldMap_comp]
  show IsIso (g.residueFieldMap (f x) ≫ f.residueFieldMap x) ↔ _
  exact ⟨fun _ => IsIso.of_isIso_comp_right _ (f.residueFieldMap x), fun _ => inferInstance⟩

/-- If `g` has an isomorphism on residue fields at `f x`, then so does `f ≫ g` at `x` exactly
when `f` does. -/
private lemma isIso_residueFieldMap_comp_iff_right {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) [IsIso (g.residueFieldMap (f x))] :
    IsIso ((f ≫ g).residueFieldMap x) ↔ IsIso (f.residueFieldMap x) := by
  rw [Scheme.residueFieldMap_comp]
  show IsIso (g.residueFieldMap (f x) ≫ f.residueFieldMap x) ↔ _
  exact ⟨fun _ => IsIso.of_isIso_comp_left (g.residueFieldMap (f x)) _, fun _ => inferInstance⟩

/-- In a commutative square `a ≫ b = c ≫ d` whose legs `a` and `d` are isomorphisms on residue
fields at the relevant points, `b` is one at `a w` exactly when `c` is one at `w`. -/
private lemma isIso_residueFieldMap_iff_of_comm {W X Y Z : Scheme.{u}} {a : W ⟶ X} {b : X ⟶ Z}
    {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) (w : W) [IsIso (a.residueFieldMap w)]
    [IsIso (d.residueFieldMap (c w))] :
    IsIso (b.residueFieldMap (a w)) ↔ IsIso (c.residueFieldMap w) := by
  rw [← isIso_residueFieldMap_comp_iff_left a b w, h, isIso_residueFieldMap_comp_iff_right c d w]

/-- The map from the fibre of `U.toBase ≫ f` over `f x` to the fibre of `f` over `f x`, for an
étale neighbourhood `U` of `x`. -/
private noncomputable def fiberCompToFiber {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood X x) : (U.toBase ≫ f).fiber (f x) ⟶ f.fiber (f x) :=
  ((pullbackRightPullbackFstIso f (S.fromSpecResidueField (f x)) U.toBase).symm ≪≫
      pullbackSymmetry U.toBase (pullback.fst f (S.fromSpecResidueField (f x)))).hom ≫
    pullback.fst (f.fiberι (f x)) U.toBase

/-- The fibre of `U.toBase ≫ f` over `f x` is the pullback of the fibre of `f` along
`U.toBase`. -/
private lemma isPullback_fiberCompToFiber {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (U : EtaleNeighborhood X x) :
    IsPullback ((U.toBase ≫ f).fiberι (f x)) (fiberCompToFiber f x U) U.toBase
      (f.fiberι (f x)) := by
  let g : U.scheme ⟶ S := U.toBase ≫ f
  let e : g.fiber (f x) ≅
      pullback (pullback.fst f (S.fromSpecResidueField (f x))) U.toBase :=
    (pullbackRightPullbackFstIso f (S.fromSpecResidueField (f x)) U.toBase).symm ≪≫
      pullbackSymmetry U.toBase (pullback.fst f (S.fromSpecResidueField (f x)))
  refine (IsPullback.of_hasPullback (f.fiberι (f x)) U.toBase).flip.of_iso'
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · dsimp [e]
    simp only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
      Iso.symm_hom, pullbackRightPullbackFstIso_inv_fst,
      Scheme.Hom.fiberι, Scheme.Hom.fiber, g, Category.comp_id]
  · rfl
  · simp
  · simp

/-- The fibre over `f x` of an étale neighbourhood of `x` in `X` is an étale neighbourhood of
`f.asFiber x` in the fibre `f.fiber (f x)`. -/
private noncomputable def etaleNeighborhoodOfFiber {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (U : EtaleNeighborhood X x) :
    EtaleNeighborhood (f.fiber (f x)) (f.asFiber x) := by
  let g : U.scheme ⟶ S := U.toBase ≫ f
  let p : g.fiber (f x) ⟶ f.fiber (f x) := fiberCompToFiber f x U
  have hpull : IsPullback (g.fiberι (f x)) p U.toBase (f.fiberι (f x)) :=
    isPullback_fiberCompToFiber f x U
  have : Etale p := MorphismProperty.of_isPullback hpull inferInstance
  have hu : g U.point = f x := by simp [g, U.map_point]
  let u : g.fiber (f x) :=
    (g.fiberHomeo (f x)).symm ⟨U.point, by simpa [g] using hu⟩
  have huPoint : g.fiberι (f x) u = U.point :=
    Scheme.Hom.fiberι_fiberHomeo_symm g (f x) ⟨U.point, by simpa [g] using hu⟩
  refine ⟨g.fiber (f x), u, p, ?_⟩
  apply (f.fiberι (f x)).isEmbedding.injective
  change (p ≫ f.fiberι (f x)) u = (f.fiberι (f x)) (f.asFiber x)
  rw [Scheme.Hom.fiberι_asFiber, ← hpull.w]
  change U.toBase (g.fiberι (f x) u) = x
  rw [huPoint, U.map_point]

/-- The fibre of an elementary étale neighbourhood is an elementary étale neighbourhood of the
fibre. -/
private theorem etaleNeighborhoodOfFiber_isElementary {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (U : EtaleNeighborhood X x) (hU : U.IsElementary) :
    (etaleNeighborhoodOfFiber f x U).IsElementary := by
  let g : U.scheme ⟶ S := U.toBase ≫ f
  let p : g.fiber (f x) ⟶ f.fiber (f x) := fiberCompToFiber f x U
  have hpull : IsPullback (g.fiberι (f x)) p U.toBase (f.fiberι (f x)) :=
    isPullback_fiberCompToFiber f x U
  have hu : g U.point = f x := by simp [g, U.map_point]
  let u : g.fiber (f x) := (g.fiberHomeo (f x)).symm ⟨U.point, by simpa [g] using hu⟩
  have huPoint : g.fiberι (f x) u = U.point :=
    Scheme.Hom.fiberι_fiberHomeo_symm g (f x) ⟨U.point, by simpa [g] using hu⟩
  have := residueFieldMap_isIso_of_isPreimmersion (g.fiberι (f x)) u
  have := residueFieldMap_isIso_of_isPreimmersion (f.fiberι (f x)) (p u)
  have hbase : IsIso (U.toBase.residueFieldMap (g.fiberι (f x) u)) := by
    rw [huPoint]
    exact U.isElementary_iff.mp hU
  have hP : IsIso (p.residueFieldMap u) := (isIso_residueFieldMap_iff_of_comm hpull.w u).mp hbase
  show IsIso (((f.fiber (f x)).residueFieldCongr
    (etaleNeighborhoodOfFiber f x U).map_point).inv ≫ p.residueFieldMap u)
  exact IsIso.comp_isIso' inferInstance hP

/-- If an étale neighbourhood of `x` in `X` has a fibre which refines an elementary étale
neighbourhood of `f.asFiber x` in the fibre, then that neighbourhood of `x` is itself
elementary. -/
private theorem elementary_of_fiber_openImmersion {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : EtaleNeighborhood (f.fiber (f x)) (f.asFiber x)) (hV : V.IsElementary)
    (U : EtaleNeighborhood X x) (u : (U.toBase ≫ f).fiber (f x))
    (p : (U.toBase ≫ f).fiber (f x) ⟶ f.fiber (f x))
    (q : (U.toBase ≫ f).fiber (f x) ⟶ V.scheme)
    (huι : (U.toBase ≫ f).fiberι (f x) u = U.point)
    (hpι : p ≫ f.fiberι (f x) = (U.toBase ≫ f).fiberι (f x) ≫ U.toBase)
    (hq : q ≫ V.toBase = p) (hqu : q u = V.point)
    (hqOpen : IsOpenImmersion q) : U.IsElementary := by
  have : IsIso (q.residueFieldMap u) := inferInstance
  have hVbase : IsIso (V.toBase.residueFieldMap (q u)) := by
    rw [hqu]
    exact V.isElementary_iff.mp hV
  have hp := (isIso_residueFieldMap_comp_iff_left q V.toBase u).mpr hVbase
  rw [hq] at hp
  have := residueFieldMap_isIso_of_isPreimmersion ((U.toBase ≫ f).fiberι (f x)) u
  have := residueFieldMap_isIso_of_isPreimmersion (f.fiberι (f x)) (p u)
  have hbase := (isIso_residueFieldMap_iff_of_comm hpι.symm u).mpr hp
  rw [huι] at hbase
  exact U.isElementary_iff.mpr hbase

/-! ### The two formulae -/

/-- Counting irreducible components through the image of a point `u` of the fibre of an étale
neighbourhood over the distinguished point, an open embedding out of the fibre does not increase
the count. -/
private theorem encard_irreducibleComponents_through_le_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (U : EtaleNeighborhood X x) (u : (U.toBase ≫ f).fiber (f x))
    (huι : (U.toBase ≫ f).fiberι (f x) u = U.point) {W : Type u} [TopologicalSpace W]
    (q : (U.toBase ≫ f).fiber (f x) → W) (hq : Topology.IsOpenEmbedding q) :
    Set.encard {D ∈ irreducibleComponents W | q u ∈ D} ≤
      Set.encard
        {Z ∈ irreducibleComponents ((U.toBase ≫ f).fiber (f x)) |
          ((U.toBase ≫ f).fiberHomeo (f x)).symm ⟨U.point, by simp [U.map_point]⟩ ∈ Z} := by
  have hwu : ((U.toBase ≫ f).fiberHomeo (f x)).symm ⟨U.point, by simp [U.map_point]⟩ = u := by
    apply ((U.toBase ≫ f).fiberι (f x)).isEmbedding.injective
    rw [Scheme.Hom.fiberι_fiberHomeo_symm, huι]
  rw [hwu]
  exact (encard_irreducibleComponents_through_eq_of_isOpenEmbedding q hq u).symm.le

/-- **Stacks Project, Tag 0CB5.** The branches of a fibre are counted by
irreducible components through the distinguished points of fibres of
elementary étale neighborhoods. -/
@[stacks 0CB5 "fibre_branches"]
public theorem numberOfBranches_fiber_eq_iSup_encard_irreducibleComponentsThrough
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    numberOfBranches (f.fiber (f x)) (f.asFiber x) =
      ⨆ (U : EtaleNeighborhood X x) (_ : U.IsElementary),
        Set.encard
          {Z ∈ irreducibleComponents ((U.toBase ≫ f).fiber (f x)) |
            ((U.toBase ≫ f).fiberHomeo (f x)).symm
              ⟨U.point, by simp [U.map_point]⟩ ∈ Z} := by
  classical
  rw [numberOfBranches_eq_iSup_encard_irreducibleComponentsThrough]
  apply le_antisymm
  · refine iSup₂_le fun V hV => ?_
    obtain ⟨U, u, p, q, huι, hpι, -, -, hq, hqu, hqOpen⟩ :=
      exists_etaleNeighborhood_fiber_openImmersion f x V
    have hcounts := encard_irreducibleComponents_through_le_fiber f x U u huι q
      q.isOpenEmbedding
    rw [hqu] at hcounts
    exact le_iSup₂_of_le U
      (elementary_of_fiber_openImmersion f x V hV U u p q huι hpι hq hqu hqOpen) hcounts
  · exact iSup₂_le fun U hU => le_iSup₂_of_le (etaleNeighborhoodOfFiber f x U)
      (etaleNeighborhoodOfFiber_isElementary f x U hU) le_rfl

/-- **Stacks Project, Tag 0CB5.** Geometric branches of a fibre are counted by
irreducible components through the distinguished points of fibres of étale
neighbourhoods. -/
@[stacks 0CB5 "fibre_geometric_branches"]
public theorem numberOfGeometricBranches_fiber_eq_iSup_encard
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    numberOfGeometricBranches (f.fiber (f x)) (f.asFiber x) =
      ⨆ U : EtaleNeighborhood X x,
        Set.encard
          {Z ∈ irreducibleComponents ((U.toBase ≫ f).fiber (f x)) |
            ((U.toBase ≫ f).fiberHomeo (f x)).symm
              ⟨U.point, by simp [U.map_point]⟩ ∈ Z} := by
  classical
  rw [numberOfGeometricBranches_eq_iSup_encard]
  apply le_antisymm
  · refine iSup_le fun V => ?_
    obtain ⟨U, u, p, h, huι, -, -, -, -, huv, hopen⟩ :=
      exists_etaleNeighborhood_fiber_openImmersion f x V
    have hcounts := encard_irreducibleComponents_through_le_fiber f x U u huι h h.isOpenEmbedding
    rw [huv] at hcounts
    exact le_iSup_of_le U hcounts
  · exact iSup_le fun U => le_iSup_of_le (etaleNeighborhoodOfFiber f x U) le_rfl

/-! ### The two unibranch criteria -/

/-- **Stacks Project, Tag 0CB5.** The fibre is unibranch at the point if and only if for every
elementary étale neighbourhood of the point in the total space there is exactly one irreducible
component of its fibre passing through the distinguished point. -/
@[stacks 0CB5 "fibre_unibranch_iff"]
public theorem isUnibranchAt_fiber_iff_existsUnique_irreducibleComponent
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsUnibranchAt (f.fiber (f x)) (f.asFiber x) ↔
      ∀ U : EtaleNeighborhood X x, U.IsElementary →
        ∃! Z : irreducibleComponents ((U.toBase ≫ f).fiber (f x)),
          ((U.toBase ≫ f).fiberHomeo (f x)).symm ⟨U.point, by simp [U.map_point]⟩ ∈
            (Z : Set ((U.toBase ≫ f).fiber (f x))) := by
  rw [← numberOfBranches_eq_one_iff,
    numberOfBranches_fiber_eq_iSup_encard_irreducibleComponentsThrough]
  simp_rw [← encard_irreducibleComponentsThrough_eq_one_iff]
  refine ⟨fun h U hU => le_antisymm ?_ (one_le_encard_irreducibleComponentsThrough _),
    fun h => le_antisymm (iSup₂_le fun U hU => (h U hU).le) ?_⟩
  · rw [← h]
    exact le_iSup₂_of_le U hU le_rfl
  · exact le_iSup₂_of_le _ (EtaleNeighborhood.isElementary_self X x)
      (h _ (EtaleNeighborhood.isElementary_self X x)).ge

/-- **Stacks Project, Tag 0CB5, part (4), stated about the fibre.** The fibre is geometrically
unibranch at the point if and only if for every étale neighbourhood of the point in the total
space there is exactly one irreducible component of its fibre passing through the distinguished
point.

The source states part (4) as "`X` is geometrically unibranch at `x`", not `X_s`, while its
right-hand side is about the irreducible components of the *fibre* `U_s`. That pairing of `X`
with `U_s` is the asymmetry: parts (1), (2) and (3) are all about `X_s`, part (4) is the
geometric counterpart of part (3), and the cited proof (Tags 0CB4 and 0CAS) yields the statement
about the fibre. The fibre statement is what is proved here; the deviation from the literal text
of part (4) is recorded rather than silently adopted.

The deviation is not a choice between two defensible readings:
`AlgebraicGeometry.not_forall_isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent`
refutes the literal statement about `X`, so the reading about the fibre proved here is the only
true one. -/
@[stacks 0CB5 "fibre_geometrically_unibranch_iff"]
public theorem isGeometricallyUnibranchAt_fiber_iff_existsUnique_irreducibleComponent
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsGeometricallyUnibranchAt (f.fiber (f x)) (f.asFiber x) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z : irreducibleComponents ((U.toBase ≫ f).fiber (f x)),
          ((U.toBase ≫ f).fiberHomeo (f x)).symm ⟨U.point, by simp [U.map_point]⟩ ∈
            (Z : Set ((U.toBase ≫ f).fiber (f x))) := by
  have : Nonempty (EtaleNeighborhood X x) := ⟨EtaleNeighborhood.self X x⟩
  rw [← numberOfGeometricBranches_eq_one_iff, numberOfGeometricBranches_fiber_eq_iSup_encard]
  simp_rw [← encard_irreducibleComponentsThrough_eq_one_iff]
  refine ⟨fun h U => le_antisymm ?_ (one_le_encard_irreducibleComponentsThrough _), fun h => ?_⟩
  · rw [← h]
    exact le_iSup_of_le U le_rfl
  · rw [iSup_congr h, iSup_const]

end AlgebraicGeometry

end
