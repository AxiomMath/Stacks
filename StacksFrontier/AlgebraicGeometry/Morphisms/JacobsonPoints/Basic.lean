module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint

/-!
# Finite type points of a scheme

The finite type points of a scheme `S` are the points `s` at which the canonical morphism
`Spec(κ(s)) ⟶ S` from the spectrum of the residue field is of finite type. This file collects
the basic properties of that subset: it is exactly the union, over the open subschemes of `S`, of
their sets of closed points, it is preserved by morphisms locally of finite type, it
meets every nonempty locally closed subset — hence is dense in every closed subset — and a
surjective morphism locally of finite type maps it onto the finite type points of the target.

## Main definitions

* `AlgebraicGeometry.Scheme.finiteTypePoints` is the set of finite type points of a scheme.

## Main results

* `AlgebraicGeometry.mapsTo_finiteTypePoints`: a locally finite type morphism maps finite type
  points to finite type points.
* `AlgebraicGeometry.inter_finiteTypePoints_nonempty`: a nonempty locally closed subset meets
  the set of finite type points.
* `AlgebraicGeometry.closure_inter_finiteTypePoints`: the finite type points in a closed subset
  are dense in that subset.
* `AlgebraicGeometry.image_finiteTypePoints_eq`: the image of the finite type points under a
  surjective, locally finite type morphism.
* `AlgebraicGeometry.Scheme.finiteTypePoints_eq_iUnion_closedPoints`: the finite type points
  are the union of the closed points of the open subschemes, and equally the union of the
  closed points of the affine open subschemes.

## Implementation notes

The image containment is expressed as `Set.MapsTo` for the underlying map of topological
spaces, and density in a closed subset `T` by the ambient-space equality
`closure (T ∩ S.finiteTypePoints) = T`. Closed points are expressed by closed singleton
subsets.

The set of closed points of an open subscheme `U` is `closedPoints ↑U`, a subset of the
topological space `↑U`; it is transported into `S` along `Subtype.val`, so that the two
descriptions of the finite type points are equalities of subsets of `S`. The two
descriptions — over all opens and over all affine opens — are recorded separately as
`AlgebraicGeometry.Scheme.finiteTypePoints_eq_iUnion_opens` and
`AlgebraicGeometry.Scheme.finiteTypePoints_eq_iUnion_affineOpens`, and jointly as their
conjunction.

## References

* [Stacks Project, Tag 01TA](https://stacks.math.columbia.edu/tag/01TA)
* [Stacks Project, Tag 02J1](https://stacks.math.columbia.edu/tag/02J1)
* [Stacks Project, Tag 02J2](https://stacks.math.columbia.edu/tag/02J2)
* [Stacks Project, Tag 02J3](https://stacks.math.columbia.edu/tag/02J3)
* [Stacks Project, Tag 02J4](https://stacks.math.columbia.edu/tag/02J4)
* [Stacks Project, Tag 06EB](https://stacks.math.columbia.edu/tag/06EB)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- The set of finite type points of a scheme. -/
@[stacks 02J1 "finite_type_points_set"]
abbrev Scheme.finiteTypePoints (S : Scheme.{u}) : Set S :=
  {s | AlgebraicGeometry.IsFiniteTypePoint s}

/-- The image of a locally finite type morphism from the spectrum of a field, viewed as a point
of the target through `Scheme.SpecToEquivOfField`, is a finite type point. -/
private lemma isFiniteTypePoint_of_locallyOfFiniteType_specField
    {k : Type u} [Field k] {S : Scheme.{u}} (g : Spec (.of k) ⟶ S)
    (hg : LocallyOfFiniteType g) :
    AlgebraicGeometry.IsFiniteTypePoint
      ((Scheme.SpecToEquivOfField k S) g).1 := by
  let s := ((Scheme.SpecToEquivOfField k S) g).1
  let k' : Type u := IsLocalRing.ResidueField (S.presheaf.stalk s)
  let g' : Spec (.of k') ⟶ S := S.fromSpecResidueField s
  have hg' : (Scheme.SpecToEquivOfField k' S) g' =
      ⟨s, CommRingCat.ofHom (RingHom.id k')⟩ := by
    apply (Scheme.SpecToEquivOfField k' S).symm.injective
    rw [(Scheme.SpecToEquivOfField k' S).symm_apply_apply]
    show g' = Spec.map (𝟙 (.of k')) ≫ S.fromSpecResidueField s
    rw [Spec.map_id]
    exact (Category.id_comp _).symm
  apply ((finiteType_specField_tfae g').out 4 1).mp
  obtain ⟨U, hU, x, hx, hxc, hfin⟩ :=
    ((finiteType_specField_tfae g).out 2 4).mp hg
  refine ⟨U, ?_, x, ?_, hxc, ?_⟩
  · refine (Scheme.preimage_eq_top_of_closedPoint_mem g' ?_).ge
    show ((Scheme.SpecToEquivOfField k' S) g').1 ∈ U.1
    rw [hg', ← hx]
    exact x.property
  · simpa only [hg'] using hx
  · show let q := (Scheme.SpecToEquivOfField k' S) g'
      let := q.2.hom.toAlgebra
      Module.Finite (S.residueField q.1) k'
    rw [hg']
    show Module.Finite k' k'
    infer_instance

/-- A locally finite type morphism of schemes sends finite type points to finite type
points. -/
@[stacks 02J3]
theorem mapsTo_finiteTypePoints {T S : Scheme.{u}} (f : T ⟶ S)
    [LocallyOfFiniteType f] :
    Set.MapsTo f.base T.finiteTypePoints S.finiteTypePoints := by
  intro t ht
  have : LocallyOfFiniteType (T.fromSpecResidueField t) := ht.1
  have h := isFiniteTypePoint_of_locallyOfFiniteType_specField (T.fromSpecResidueField t ≫ f)
      (AlgebraicGeometry.locallyOfFiniteType_comp (hf := ht.1) (hg := inferInstance) _ _)
  have heq : ((Scheme.SpecToEquivOfField (T.residueField t) S)
      (T.fromSpecResidueField t ≫ f)).1 = f t := by
    show f (T.fromSpecResidueField t (IsLocalRing.closedPoint (T.residueField t))) = f t
    congr 1
    exact Scheme.fromSpecResidueField_apply t _
  show AlgebraicGeometry.IsFiniteTypePoint (f t)
  rwa [← heq]

/-- A point of a scheme that is closed in some affine open neighbourhood is a finite type
point. -/
private theorem finiteTypePoint_of_closed_in_affineOpen {S : Scheme.{u}} {x : S}
    {U : S.Opens} (hU : IsAffineOpen U) (hx : x ∈ U)
    (hclosed : IsClosed ({⟨x, hx⟩} : Set (↑U))) :
    AlgebraicGeometry.IsFiniteTypePoint x := by
  let f := S.fromSpecResidueField x
  have hspec : (Scheme.SpecToEquivOfField (S.residueField x) S) f =
      ⟨x, CommRingCat.ofHom (RingHom.id (S.residueField x))⟩ := by
    apply (Scheme.SpecToEquivOfField (S.residueField x) S).symm.injective
    rw [(Scheme.SpecToEquivOfField (S.residueField x) S).symm_apply_apply]
    show f = Spec.map (𝟙 (.of (S.residueField x))) ≫ S.fromSpecResidueField x
    rw [Spec.map_id, Category.id_comp]
  have hcoord : ((Scheme.SpecToEquivOfField (S.residueField x) S) f).1 = x := by
    rw [hspec]
  have hclosedmem : f (IsLocalRing.closedPoint (S.residueField x)) ∈ U := by
    show ((Scheme.SpecToEquivOfField (S.residueField x) S) f).1 ∈ U
    rw [hspec]
    exact hx
  have hpre : (⊤ : (Spec (.of (S.residueField x))).Opens) ≤ f ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem f hclosedmem).ge
  apply ((finiteType_specField_tfae f).out 4 1).mp
  refine ⟨⟨U, hU⟩, hpre, ⟨x, hx⟩, hcoord.symm, hclosed, ?_⟩
  show let q := (Scheme.SpecToEquivOfField (S.residueField x) S) f
    let := q.2.hom.toAlgebra
    Module.Finite (S.residueField q.1) (S.residueField x)
  rw [hspec]
  show Module.Finite (S.residueField x) (S.residueField x)
  infer_instance

/-- Every nonempty locally closed subset of a scheme contains a finite type point. -/
@[stacks 02J4 "locally closed subsets"]
theorem inter_finiteTypePoints_nonempty {S : Scheme.{u}} {T : Set S}
    (hT : IsLocallyClosed T) (hne : T.Nonempty) :
    (T ∩ S.finiteTypePoints).Nonempty := by
  obtain ⟨U, hU, hTU⟩ := ((isLocallyClosed_tfae T).out 1 5).mp hT
  obtain ⟨x, hxT⟩ := hne
  have hxT' : x ∈ U ∩ closure T := hTU ▸ hxT
  have hxU : x ∈ U := hxT'.1
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxU hU
  let xv : V := ⟨x, hxV⟩
  let p := hV.primeIdealOf xv
  have hpne : p.asIdeal ≠ ⊤ := p.2.ne_top'
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal hpne
  let qps : PrimeSpectrum Γ(S, V) := ⟨m, hm.isPrime⟩
  let q : Spec Γ(S, V) := qps
  let e := hV.isoSpec.hom.homeomorph
  let yv : V := e.symm q
  have hspecV : xv ⤳ yv := by
    apply (e.isInducing.specializes_iff).mp
    have hpq : p ≤ qps := by
      show p.asIdeal ≤ qps.asIdeal
      simpa [qps] using hpm
    have hpq' := (PrimeSpectrum.le_iff_specializes p qps).mp hpq
    have heq₁ : e xv = p := rfl
    have heq₂ : e yv = q := e.apply_symm_apply q
    rwa [heq₁, heq₂]
  have hspecS : x ⤳ (yv : S) := hspecV.map continuous_subtype_val
  have hyclosure : (yv : S) ∈ closure T :=
    closure_mono (Set.singleton_subset_iff.mpr hxT)
      (specializes_iff_mem_closure.mp hspecS)
  have hyT : (yv : S) ∈ T := by
    rw [hTU]
    exact ⟨hVU yv.property, hyclosure⟩
  have hqclosed : IsClosed ({q} : Set (Spec Γ(S, V))) := by
    show IsClosed ({qps} : Set (PrimeSpectrum Γ(S, V)))
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal qps).mpr hm
  have hyclosed : IsClosed ({yv} : Set (↑V)) := by
    show IsClosed ({e.symm q} : Set (↑V))
    simpa only [Set.image_singleton] using e.symm.isClosedMap ({q} : Set (Spec Γ(S, V))) hqclosed
  exact ⟨yv, hyT, finiteTypePoint_of_closed_in_affineOpen hV yv.property hyclosed⟩

/-- The finite type points lying in a closed subset of a scheme are dense in that subset. -/
@[stacks 02J4 "closed subsets"]
theorem closure_inter_finiteTypePoints {S : Scheme.{u}} {T : Set S}
    (hT : IsClosed T) : closure (T ∩ S.finiteTypePoints) = T := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.inter_subset_left hT
  · intro x hxT
    rw [mem_closure_iff]
    intro U hU hxU
    have hTloc : IsLocallyClosed T :=
      ⟨Set.univ, T, isOpen_univ, hT, by ext y; simp⟩
    have hUloc : IsLocallyClosed U :=
      ⟨U, Set.univ, hU, isClosed_univ, by ext y; simp⟩
    obtain ⟨y, hy⟩ := inter_finiteTypePoints_nonempty (hTloc.inter hUloc)
      ⟨x, ⟨hxT, hxU⟩⟩
    exact ⟨y, hy.1.2, hy.1.1, hy.2⟩

/-- A surjective morphism which is locally of finite type maps the finite type points of its
source onto those of its target. -/
@[stacks 06EB]
theorem image_finiteTypePoints_eq {T S : Scheme.{u}} (f : T ⟶ S)
    [LocallyOfFiniteType f] [Surjective f] :
    f.base '' T.finiteTypePoints = S.finiteTypePoints := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩; exact mapsTo_finiteTypePoints f ht
  · intro s hs
    obtain ⟨U, hU, x, hx, hclosed, _⟩ :=
      ((finiteType_specField_tfae (S.fromSpecResidueField s)).out 1 4).mp hs
    have hsclosed : IsLocallyClosed ({s} : Set S) := by
      rw [← hx.trans ((Scheme.SpecToEquivOfField_apply_fst _ _ _).trans
        (Scheme.fromSpecResidueField_apply _ _)), ← Set.image_singleton]
      exact hclosed.isLocallyClosed.image U.1.isOpen.isOpenEmbedding_subtypeVal.isInducing
        U.1.isOpen.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed
    obtain ⟨t, hft, ht⟩ := inter_finiteTypePoints_nonempty
      (hsclosed.preimage f.base.hom.continuous) (f.surjective s |>.imp fun _ h ↦ h)
    exact ⟨t, ht, hft⟩

/-- A point of a scheme that is closed in some open neighbourhood is a finite type point:
shrinking the neighbourhood to an affine open reduces this to the affine case. -/
private theorem finiteTypePoint_of_closed_in_open {S : Scheme.{u}} {x : S} {U : S.Opens}
    (hx : x ∈ U) (hclosed : IsClosed ({⟨x, hx⟩} : Set (↑U))) :
    AlgebraicGeometry.IsFiniteTypePoint x := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  refine finiteTypePoint_of_closed_in_affineOpen hV hxV ?_
  refine mem_closedPoints_iff.mp (preimage_closedPoints_subset
    (Set.inclusion_injective hVU) (continuous_inclusion hVU) ?_)
  exact mem_closedPoints_iff.mpr hclosed

/-- The finite type points of a scheme are exactly the points that are closed in some affine
open subscheme. -/
theorem Scheme.finiteTypePoints_eq_iUnion_affineOpens (S : Scheme.{u}) :
    S.finiteTypePoints = ⋃ U : S.affineOpens, Subtype.val '' closedPoints ↑U.1 := by
  refine Set.Subset.antisymm (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · obtain ⟨U, -, x, hx, hclosed, -⟩ :=
      ((finiteType_specField_tfae (S.fromSpecResidueField s)).out 1 4).mp hs
    refine Set.mem_iUnion.mpr ⟨U, x, mem_closedPoints_iff.mpr hclosed, ?_⟩
    exact hx.trans ((Scheme.SpecToEquivOfField_apply_fst _ _ _).trans
      (Scheme.fromSpecResidueField_apply _ _))
  · obtain ⟨U, x, hxc, rfl⟩ := Set.mem_iUnion.mp hs
    exact finiteTypePoint_of_closed_in_affineOpen U.2 x.2 (mem_closedPoints_iff.mp hxc)

/-- The finite type points of a scheme are exactly the points that are closed in some open
subscheme. -/
theorem Scheme.finiteTypePoints_eq_iUnion_opens (S : Scheme.{u}) :
    S.finiteTypePoints = ⋃ U : S.Opens, Subtype.val '' closedPoints ↑U := by
  refine Set.Subset.antisymm ?_ (fun s hs ↦ ?_)
  · rw [S.finiteTypePoints_eq_iUnion_affineOpens]
    intro s hs
    obtain ⟨U, hsU⟩ := Set.mem_iUnion.mp hs
    exact Set.mem_iUnion.mpr ⟨U.1, hsU⟩
  · obtain ⟨U, x, hxc, rfl⟩ := Set.mem_iUnion.mp hs
    exact finiteTypePoint_of_closed_in_open x.2 (mem_closedPoints_iff.mp hxc)

/-- The set of finite type points of a scheme `S` is the union, over the open subschemes `U` of
`S`, of the sets of closed points of `U`; the same union taken over the affine open subschemes
of `S` has the same value. -/
@[stacks 02J2]
theorem Scheme.finiteTypePoints_eq_iUnion_closedPoints (S : Scheme.{u}) :
    S.finiteTypePoints = (⋃ U : S.Opens, Subtype.val '' closedPoints ↑U) ∧
      S.finiteTypePoints = ⋃ U : S.affineOpens, Subtype.val '' closedPoints ↑U.1 :=
  ⟨S.finiteTypePoints_eq_iUnion_opens, S.finiteTypePoints_eq_iUnion_affineOpens⟩

end AlgebraicGeometry
