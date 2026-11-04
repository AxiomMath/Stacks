module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.IrreducibleComponents

/-!
# The geometric fibre count of a locally quasi-finite morphism

For a locally quasi-finite morphism of schemes, the number of geometrically irreducible
components of each fibre agrees with the number of geometrically connected components, and if the
source is quasi-compact this count attains a finite maximum.

## Main results

* `AlgebraicGeometry.geometricIrreducibleComponentCount_eq_numGeometricConnectedComponents`
  identifies the two functions counting components of geometric fibres.
* `AlgebraicGeometry.geometricIrreducibleComponentCount_eq_card` computes the count of a locally
  quasi-finite morphism as the number of points of a geometric fibre, and
  `AlgebraicGeometry.geometricIrreducibleComponentCount_eq_card_of_isPullback` reads that number
  off an arbitrary cartesian square over the spectrum of the separable closure.
* `AlgebraicGeometry.exists_forall_geometricIrreducibleComponentCount_le`: over a quasi-compact
  source the count is bounded by a natural number.
* `AlgebraicGeometry.exists_isGreatest_range_geometricIrreducibleComponentCount`: on a nonempty
  target that bound is attained, so the count has a greatest value.

## Implementation notes

Both counts are `ℕ∞`-valued functions on the points of the target. "`f` is locally quasi-finite"
is the pair of typeclasses `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`, and quasi-compactness of the source is `CompactSpace`; the
agreement of the two counts needs only `AlgebraicGeometry.LocallyQuasiFinite`. The maximum is
attained only on a nonempty target, which
`AlgebraicGeometry.exists_isGreatest_range_geometricIrreducibleComponentCount` assumes; the bound
`AlgebraicGeometry.exists_forall_geometricIrreducibleComponentCount_le` needs no such hypothesis.

## References

* [Stacks Project, Tag 0F35](https://stacks.math.columbia.edu/tag/0F35)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- On a discrete space, the quotient map to the connected components is bijective. -/
private lemma bijective_mk_connectedComponents_of_discrete (α : Type*) [TopologicalSpace α]
    [DiscreteTopology α] :
    Function.Bijective (ConnectedComponents.mk : α → ConnectedComponents α) := by
  refine ⟨fun a b hab => ?_, ConnectedComponents.surjective_coe⟩
  have hc := ConnectedComponents.coe_eq_coe.mp hab
  rw [connectedComponent_eq_singleton, connectedComponent_eq_singleton] at hc
  simpa using congrArg (fun s : Set α => a ∈ s) hc

private lemma discrete_component_counts_agree (α : Type u) [TopologicalSpace α]
    [DiscreteTopology α] :
    (irreducibleComponents α).encard = ENat.card (ConnectedComponents α) := by
  have hcomponents : irreducibleComponents α =
      Set.range (fun x : α => ({x} : Set α)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨x, hx⟩ := isIrreducible_iff_singleton.mp hs.1
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨isIrreducible_singleton, ?_⟩
      intro t ht hxt
      obtain ⟨y, rfl⟩ := isIrreducible_iff_singleton.mp ht
      obtain rfl := Set.singleton_subset_singleton.mp hxt
      rfl
  have hIrred : (irreducibleComponents α).encard = (Set.univ : Set α).encard := by
    rw [hcomponents, ← Set.image_univ]
    exact (show Function.Injective (fun x : α => ({x} : Set α)) from
      fun x y hxy => Set.singleton_injective hxy).encard_image Set.univ
  rw [hIrred, Set.encard_univ]
  exact ENat.card_congr (Equiv.ofBijective _ (bijective_mk_connectedComponents_of_discrete α))

/-- The geometric fibre over the separable closure of a residue field is discrete for a locally
quasi-finite morphism. -/
private lemma discreteTopology_geometricFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (y : Y) :
    DiscreteTopology (geometricFiber f y (SeparableClosure (Y.residueField y))) := by
  let K := SeparableClosure (Y.residueField y)
  let g : geometricFiber f y K ⟶ Spec (CommRingCat.of K) :=
    pullback.snd (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))
  have : LocallyQuasiFinite (f.fiberToSpecResidueField y) := by
    show LocallyQuasiFinite (pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  have hg : LocallyQuasiFinite g := by
    show LocallyQuasiFinite (pullback.snd (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))))
    infer_instance
  have h := g.isDiscrete_preimage_singleton (Classical.arbitrary (Spec (CommRingCat.of K)))
  rw [Set.eq_univ_of_forall (s := g ⁻¹' {Classical.arbitrary (Spec (CommRingCat.of K))})
    fun _ => Subsingleton.elim _ _] at h
  exact isDiscrete_univ_iff.mp h

/-- For a locally quasi-finite morphism, the functions counting geometrically irreducible and
geometrically connected components of its fibres agree. -/
@[stacks 0F35 "agreement"]
theorem geometricIrreducibleComponentCount_eq_numGeometricConnectedComponents
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    geometricIrreducibleComponentCount f =
      numGeometricConnectedComponents f := by
  funext y
  have := discreteTopology_geometricFiber f y
  exact discrete_component_counts_agree _

/-- The geometric fibre count of a locally quasi-finite morphism is the cardinality of a
geometric fibre. -/
theorem geometricIrreducibleComponentCount_eq_card
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y) :
    geometricIrreducibleComponentCount f y =
      ENat.card (geometricFiber f y (SeparableClosure (Y.residueField y))) := by
  have := discreteTopology_geometricFiber f y
  rw [geometricIrreducibleComponentCount_eq_numGeometricConnectedComponents]
  exact (ENat.card_congr
    (Equiv.ofBijective _ (bijective_mk_connectedComponents_of_discrete _))).symm

/-- The geometric fibre count of `f` at `y` is the cardinality of `P`, for any cartesian square
exhibiting `P` as the base change of `f` to the spectrum of the separable closure of the residue
field at `y`. -/
theorem geometricIrreducibleComponentCount_eq_card_of_isPullback
    {X Y P : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (p : P ⟶ X) (q : P ⟶ Spec (.of (SeparableClosure (Y.residueField y))))
    (h : IsPullback p q f
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
        (SeparableClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y)) :
    geometricIrreducibleComponentCount f y = ENat.card P := by
  rw [geometricIrreducibleComponentCount_eq_card]
  exact ENat.card_congr (Scheme.homeoOfIso
    (((IsPullback.of_hasPullback (f.fiberToSpecResidueField y)
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
        (SeparableClosure (Y.residueField y)))))).paste_horiz
          (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))).isoIsPullback _ _ h)).toEquiv

/-- A locally quasi-finite morphism with quasi-compact source admits a natural number bounding
the number of points of each of its base changes to the spectrum of a field. -/
private theorem exists_cardinalMk_pullback_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] :
    ∃ N : ℕ, ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      Cardinal.mk (pullback g f : Scheme.{u}) ≤ N := by
  obtain ⟨n, hn⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite f
  refine ⟨n.toNat, cardinalMk_pullback_le_of_degree_le f n.toNat fun k _ g => ?_⟩
  obtain ⟨r, hr, hrank⟩ := (boundsFiberDegrees_iff_field_baseChange f n).mp hn k g
  exact ⟨r, by exact_mod_cast hr.trans (Int.self_le_toNat n), hrank⟩

/-- The geometric fibre count of a locally quasi-finite morphism whose source is quasi-compact
is bounded by a natural number. -/
@[stacks 0F35 "boundedness"]
theorem exists_forall_geometricIrreducibleComponentCount_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] :
    ∃ d : ℕ, ∀ y : Y, geometricIrreducibleComponentCount f y ≤ (d : ℕ∞) := by
  obtain ⟨N, hN⟩ := exists_cardinalMk_pullback_le f
  refine ⟨N, fun y => ?_⟩
  rw [geometricIrreducibleComponentCount_eq_card_of_isPullback f y _ _
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (SeparableClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y) f).flip]
  exact Cardinal.toENat_le_natCast.mpr (hN (SeparableClosure (Y.residueField y)) _)

/-- The geometric fibre count of a locally quasi-finite morphism whose source is quasi-compact
and whose target is nonempty attains a finite maximum: its set of values has a greatest element.
-/
@[stacks 0F35 "maximum, the target is assumed nonempty"]
theorem exists_isGreatest_range_geometricIrreducibleComponentCount {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] [Nonempty Y] :
    ∃ d : ℕ, IsGreatest (Set.range (geometricIrreducibleComponentCount f)) (d : ℕ∞) := by
  classical
  obtain ⟨c, hc⟩ := exists_forall_geometricIrreducibleComponentCount_le f
  have hfin : ∀ y : Y, ∃ n : ℕ, geometricIrreducibleComponentCount f y = (n : ℕ∞) := fun y => by
    obtain ⟨n, hn⟩ :=
      ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top c) (hc y))
    exact ⟨n, hn.symm⟩
  choose m hm using hfin
  have hbdd : BddAbove (Set.range m) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨y, rfl⟩
    simpa [hm y] using hc y
  obtain ⟨d, ⟨y₀, hy₀⟩, hub⟩ := hbdd.exists_isGreatest_of_nonempty (Set.range_nonempty m)
  refine ⟨d, ⟨y₀, by rw [hm y₀, hy₀]⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  rw [hm y]
  exact_mod_cast hub (Set.mem_range_self y)

end AlgebraicGeometry
