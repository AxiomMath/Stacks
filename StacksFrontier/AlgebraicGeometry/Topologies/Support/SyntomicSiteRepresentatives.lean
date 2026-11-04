module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Stability
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence
public import StacksFrontier.CategoryTheory.Sites.Pretopology.EquivalenceComparison
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite

/-!
# Syntomic families represented in a big syntomic site

A syntomic covering of a scheme in a big syntomic site, whose source schemes are each
isomorphic to a site object, is tautologically equivalent to a chosen covering of the site.

## Main results

* `AlgebraicGeometry.BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_of_sources_iso`
  realizes the given syntomic family by a covering of the big syntomic site.

## Implementation notes

The arbitrary syntomic family is represented by a `PreZeroHypercover` in schemes. Its
sources need only be isomorphic as schemes to site objects; compatibility with the maps to
the target is obtained by transporting those maps through the isomorphisms and the full
subcategory inclusion. The conclusion uses tautological equivalence of families, not just
equality of their generated sieves.

The main result is nested inside the `BigSyntomicSite` namespace because
`AlgebraicGeometry.exists_isCovering_tautologicallyEquivalent_of_sources_iso` already names
the corresponding statement for a big fppf site, whose hypotheses are different.

## References

* [Stacks Project, Tag 03X2](https://stacks.math.columbia.edu/tag/03X2)
-/

@[expose] public section

open CategoryTheory

universe u w

/-- Combinatorial equivalence of families is preserved by applying a functor. -/
private theorem CategoryTheory.PreZeroHypercover.CombinatoriallyEquivalent.map
    {C : Type*} [Category C] {D : Type*} [Category D] {U : C}
    {E : PreZeroHypercover.{w} U} {F : PreZeroHypercover.{w} U}
    (h : E.CombinatoriallyEquivalent F) (G : C ⥤ D) :
    (E.map G).CombinatoriallyEquivalent (F.map G) := by
  obtain ⟨⟨α, hα, eα⟩, ⟨β, hβ, eβ⟩⟩ := h
  refine ⟨⟨α, fun i => congrArg G.obj (hα i), fun i => ?_⟩,
    ⟨β, fun i => congrArg G.obj (hβ i), fun i => ?_⟩⟩
  · simp [PreZeroHypercover.map, eα i, eqToHom_map]
  · simp [PreZeroHypercover.map, eβ i, eqToHom_map]

namespace AlgebraicGeometry

/-- Precomposing the members of a syntomic covering with isomorphisms gives a syntomic
covering. -/
theorem IsSyntomicCovering.iso_comp {T : Scheme.{u}} {I : Type*} {X Y : I → Scheme.{u}}
    {f : ∀ i, X i ⟶ T} (hf : IsSyntomicCovering X f) (e : ∀ i, Y i ≅ X i) :
    IsSyntomicCovering Y (fun i => (e i).hom ≫ f i) := by
  refine ⟨fun i => MorphismProperty.comp_mem (@Syntomic) _ _
      ((isSyntomicCovering_singleton_of_isIso (e i).hom).1 ()) (hf.1 i),
    Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hf.2 x)
  refine Set.mem_iUnion.mpr ⟨i, (e i).inv y, ?_⟩
  change f i ((e i).hom ((e i).inv y)) = f i y
  simp

/-- Shrinking a syntomic covering family to its presieve of arrows leaves a syntomic
covering family. -/
private lemma isSyntomicCovering_shrink {T : Scheme.{u}}
    (U : PreZeroHypercover.{w} T)
    (hU : IsSyntomicCovering U.X U.f) :
    IsSyntomicCovering U.shrink.X U.shrink.f := by
  classical
  refine ⟨fun i => ?_, Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  · obtain ⟨j, hX, hf⟩ := Presieve.ofArrows_surj U.f _ i.2
    change Syntomic i.1.2
    rw [hf]
    exact MorphismProperty.comp_mem (@Syntomic) (eqToHom hX.symm) (U.f j)
      ((isSyntomicCovering_singleton_of_isIso (eqToHom hX.symm)).1 ()) (hU.1 j)
  · obtain ⟨j, y, rfl⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hU.2 x)
    exact Set.mem_iUnion.mpr ⟨⟨⟨U.X j, U.f j⟩, Presieve.ofArrows.mk j⟩, y, rfl⟩

/-- If every source of a family is isomorphic to a site object, the same holds after
shrinking. -/
private lemma shrink_source_iso {B : BigSyntomicSite.{u}} {T : Scheme.{u}}
    {U : PreZeroHypercover.{w} T}
    (hrep : ∀ i, ∃ V : B.category, Nonempty (U.X i ≅ B.inclusion.obj V))
    (i : U.shrink.I₀) :
    ∃ V : B.category, Nonempty (U.shrink.X i ≅ B.inclusion.obj V) := by
  classical
  obtain ⟨j, hX, -⟩ := Presieve.ofArrows_surj U.f _ i.2
  obtain ⟨V, ⟨e⟩⟩ := hrep j
  exact ⟨V, ⟨(eqToIso hX.symm) ≪≫ e⟩⟩

/-- A covering family is tautologically equivalent to its shrinking. -/
private lemma tautologicallyEquivalent_shrink {S : Scheme.{u}}
    (E : PreZeroHypercover.{w} S) :
    PreZeroHypercover.TautologicallyEquivalent E E.shrink := by
  constructor
  · refine ⟨E.toShrink.s₀, fun i => ⟨Iso.refl _, ?_⟩⟩
    simpa [PreZeroHypercover.toShrink] using E.toShrink.w₀ i
  · refine ⟨E.fromShrink.s₀, fun i => ⟨eqToIso (show E.shrink.X i = E.X (E.fromShrink.s₀ i) from
      (Presieve.ofArrows_surj E.f _ i.2).choose_spec.1.symm), ?_⟩⟩
    convert E.fromShrink.w₀ i using 1
    rfl

/-- A syntomic covering family whose sources are isomorphic to objects of a big syntomic
site is tautologically equivalent to a selected covering in that site. -/
public theorem BigSyntomicSite.exists_isCovering_tautologicallyEquivalent_of_sources_iso
    (B : BigSyntomicSite.{u}) (T : B.category)
    (U : PreZeroHypercover.{w} (B.inclusion.obj T))
    (hU : IsSyntomicCovering U.X U.f)
    (hrep : ∀ i, ∃ V : B.category, Nonempty (U.X i ≅ B.inclusion.obj V)) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U (V.map B.inclusion) := by
  classical
  let S := U.shrink
  choose X hX using shrink_source_iso hrep
  let e (i : S.I₀) : S.X i ≅ B.inclusion.obj (X i) := Classical.choice (hX i)
  let W : PreZeroHypercover.{u + 1} T :=
    { I₀ := S.I₀
      X := X
      f := fun i => ⟨(e i).inv ≫ S.f i⟩ }
  have hSW : PreZeroHypercover.TautologicallyEquivalent S (W.map B.inclusion) :=
    ⟨⟨id, fun i => ⟨e i, (e i).hom_inv_id_assoc _⟩⟩, ⟨id, fun i => ⟨(e i).symm, rfl⟩⟩⟩
  obtain ⟨W', hW'cover, ht, hcomb⟩ := B.has_coveringRepresentative ⟨T, W⟩
    ((isSyntomicCovering_shrink U hU).iso_comp fun i => (e i).symm)
  cases ht
  change PreZeroHypercover.CombinatoriallyEquivalent W W'.2 at hcomb
  exact ⟨W'.2, hW'cover, PreZeroHypercover.tautologicallyEquivalent_trans _ _ _
    (PreZeroHypercover.tautologicallyEquivalent_trans _ _ _
      (tautologicallyEquivalent_shrink U) hSW)
    (PreZeroHypercover.tautologicallyEquivalent_of_combinatoriallyEquivalent _ _
      (hcomb.map B.inclusion))⟩

end AlgebraicGeometry
