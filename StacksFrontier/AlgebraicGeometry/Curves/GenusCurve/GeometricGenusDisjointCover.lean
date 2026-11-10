module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusReduction

/-!
# Additivity of the geometric genus over a partition into clopen pieces

Let `k` be a field and let `X` be a proper scheme over `k` which is partitioned by finitely many
closed subschemes whose underlying sets are open, pairwise disjoint and cover `X`.  Then the
geometric genus of `X` over `k` is the sum of the geometric genera of the pieces.

A finite family of open immersions with pairwise disjoint ranges covering the target exhibits
that target as a coproduct of schemes, so this is the additivity of the geometric genus over a
finite coproduct.  The pieces may be non-reduced; the geometric genus does not see nilpotents.

## Main results

* `AlgebraicGeometry.image_mem_irreducibleComponents_of_isClopen_range`: the image of an
  irreducible component under an embedding with clopen range is an irreducible component.
* `AlgebraicGeometry.exists_vanishingIdeal_subschemeIso_of_image_eq`: a closed immersion
  identifies the reduced closed subscheme cut out by a closed subset of its source with the one
  cut out by the image of that subset.
* `AlgebraicGeometry.geometricGenus_image_irreducibleComponentIdeal`: a closed immersion matches
  the geometric genus of an irreducible component of its source with that of the corresponding
  irreducible component of its target.
* `AlgebraicGeometry.geometricGenus_eq_of_iso`: the geometric genus is invariant under an
  isomorphism over the base field.
* `AlgebraicGeometry.geometricGenus_eq_sum_of_isClopen_cover`: the geometric genus is the sum of
  the geometric genera of the pieces of a finite partition into closed subschemes with open
  underlying sets.

## References

* [Stacks Project, Tag 0CE1](https://stacks.math.columbia.edu/tag/0CE1)
* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

/-! ### Irreducible sets and clopen sets -/

/-- A preirreducible set meeting a clopen set is contained in it. -/
public theorem IsPreirreducible.subset_of_isClopen {X : Type u} [TopologicalSpace X]
    {Z U : Set X} (hZ : IsPreirreducible Z) (hU : IsClopen U) (hne : (Z ∩ U).Nonempty) :
    Z ⊆ U := by
  obtain h | h := isPreirreducible_iff_isClosed_union_isClosed.mp hZ U Uᶜ hU.isClosed
    hU.isOpen.isClosed_compl (by simp)
  · exact h
  · obtain ⟨x, hxZ, hxU⟩ := hne
    exact absurd hxU (h hxZ)

namespace AlgebraicGeometry

/-- The image of an irreducible component under an embedding whose range is clopen is an
irreducible component. -/
public theorem image_mem_irreducibleComponents_of_isClopen_range
    {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
    {f : A → Y} (hf : Topology.IsEmbedding f) (hr : IsClopen (Set.range f))
    {Z : Set A} (hZ : Z ∈ irreducibleComponents A) :
    f '' Z ∈ irreducibleComponents Y := by
  obtain ⟨E, hE, hZE⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (hZ.1.image f hf.continuous.continuousOn)
  obtain ⟨x, hx⟩ := hZ.1.1
  have hne : (E ∩ Set.range f).Nonempty := ⟨f x, hZE ⟨x, hx, rfl⟩, ⟨x, rfl⟩⟩
  have hEr : E ⊆ Set.range f := hE.1.2.subset_of_isClopen hr hne
  have hpre : f ⁻¹' E ∈ irreducibleComponents A :=
    preimage_mem_irreducibleComponents hE ⟨hf, hr.isOpen⟩ hne
  have heq : Z = f ⁻¹' E :=
    Set.Subset.antisymm (Set.image_subset_iff.mp hZE)
      (hZ.2 hpre.1 (Set.image_subset_iff.mp hZE))
  rwa [heq, Set.image_preimage_eq_of_subset hEr]

/-! ### Transporting a reduced closed subscheme along a closed immersion -/

/-- Let `f : A ⟶ Y` be a closed immersion and let `Z ⊆ A` be closed with image `W ⊆ Y`.  The
reduced closed subschemes of `A` and of `Y` cut out by `Z` and by `W` are isomorphic over `Y`. -/
public alias exists_vanishingIdeal_subschemeIso_of_image_eq := exists_subschemeIso_of_image_eq

/-- A closed immersion matches the geometric genus of an irreducible component of its source,
taken with its reduced structure, with the geometric genus of the corresponding irreducible
component of its target. -/
public theorem geometricGenus_image_irreducibleComponentIdeal {k : Type u} [Field k]
    {A Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [IsProper p] (f : A ⟶ Y) [IsClosedImmersion f]
    (D : irreducibleComponents A) (E : irreducibleComponents Y)
    (hE : f.base '' (D : Set A) = E) :
    geometricGenus k ((irreducibleComponentIdeal D).subschemeι ≫ f ≫ p) =
      geometricGenus k ((irreducibleComponentIdeal E).subschemeι ≫ p) := by
  obtain ⟨e, he⟩ := exists_vanishingIdeal_subschemeIso_of_image_eq f
    ⟨D.1, isClosed_of_mem_irreducibleComponents _ D.2⟩
    ⟨E.1, isClosed_of_mem_irreducibleComponents _ E.2⟩ hE
  simp only [← reassoc_of% he]
  exact geometricGenus_eq_of_surjective_isClosedImmersion _ e.hom

/-- The geometric genus of a proper scheme over a field is invariant under an isomorphism over
that field. -/
public theorem geometricGenus_eq_of_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    {p : X ⟶ Spec (.of k)} [IsProper p] (q : Y ⟶ Spec (.of k)) [IsProper q] (e : X ≅ Y)
    (he : e.hom ≫ q = p) : geometricGenus k p = geometricGenus k q := by
  subst he
  exact geometricGenus_eq_of_surjective_isClosedImmersion q e.hom

/-! ### Additivity over a partition into clopen pieces -/

/-- A scheme proper over a field is Noetherian. -/
private theorem isNoetherian_of_isProper_spec {k : Type u} [Field k] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of k)) [IsProper q] : IsNoetherian Z :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q }

/-- **Additivity of the geometric genus over a finite partition into clopen pieces.**  Let `X` be
a proper scheme over a field `k` and let `f i : A i ⟶ X` be finitely many closed immersions whose
ranges are open, pairwise disjoint and cover `X`.  Then the geometric genus of `X` over `k` is the
sum of the geometric genera of the `A i`. -/
public theorem geometricGenus_eq_sum_of_isClopen_cover {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsProper g] {ι : Type*} [Fintype ι] {A : ι → Scheme.{u}}
    (f : ∀ i, A i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    (hopen : ∀ i, IsOpen (Set.range (f i).base))
    (hdisj : Pairwise fun i j ↦ Disjoint (Set.range (f i).base) (Set.range (f j).base))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (f i).base) :
    geometricGenus k g = ∑ i, geometricGenus k (f i ≫ g) := by
  classical
  have hXnoeth := isNoetherian_of_isProper_spec g
  have hAnoeth (i : ι) := isNoetherian_of_isProper_spec (f i ≫ g)
  have : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  have (i : ι) : Finite (irreducibleComponents (A i)) :=
    (finite_irreducibleComponents_of_isNoetherian (X := A i)).to_subtype
  let (i : ι) : Fintype (irreducibleComponents (A i)) := Fintype.ofFinite _
  have hclopen (i : ι) : IsClopen (Set.range (f i).base) :=
    ⟨(f i).isClosedEmbedding.isClosed_range, hopen i⟩
  let j : (Σ i, irreducibleComponents (A i)) → irreducibleComponents X := fun iD ↦
    ⟨(f iD.1).base '' (iD.2 : Set (A iD.1)),
      image_mem_irreducibleComponents_of_isClopen_range
        (f iD.1).isClosedEmbedding.isEmbedding (hclopen iD.1) iD.2.2⟩
  have hj : Function.Bijective j := by
    constructor
    · rintro ⟨i, D⟩ ⟨i', D'⟩ h
      have hii : i = i' := by
        by_contra hne
        obtain ⟨x, hx⟩ := D.2.1.1
        have hx' : (f i).base x ∈ (f i').base '' (D' : Set (A i')) := by
          change (f i).base x ∈ (j ⟨i', D'⟩ : Set X)
          rw [← h]
          exact ⟨x, hx, rfl⟩
        exact Set.disjoint_left.mp (hdisj hne) ⟨x, rfl⟩ (Set.image_subset_range _ _ hx')
      subst i'
      exact congrArg (Sigma.mk i) (Subtype.ext ((Set.image_injective.mpr
        (f i).isClosedEmbedding.injective) (congrArg Subtype.val h)))
    · intro E
      obtain ⟨y, hy⟩ := E.2.1.1
      obtain ⟨i, hi⟩ := hcover y
      have hEr : (E : Set X) ⊆ Set.range (f i).base :=
        E.2.1.2.subset_of_isClopen (hclopen i) ⟨y, hy, hi⟩
      exact ⟨⟨i, ⟨(f i).base ⁻¹' (E : Set X), preimage_mem_irreducibleComponents E.2
        ⟨(f i).isClosedEmbedding.isEmbedding, hopen i⟩ ⟨y, hy, hi⟩⟩⟩,
        Subtype.ext (Set.image_preimage_eq_of_subset hEr)⟩
  have hR : ∑ i, geometricGenus k (f i ≫ g) =
      ∑ i, ∑ D : irreducibleComponents (A i),
        geometricGenus k ((irreducibleComponentIdeal D).subschemeι ≫ (f i ≫ g)) :=
    Finset.sum_congr rfl fun i _ ↦ geometricGenus_eq_sum_all_components (f i ≫ g)
  rw [geometricGenus_eq_sum_all_components g, hR,
    ← Fintype.sum_sigma (f := fun iD : (Σ i, irreducibleComponents (A i)) ↦
      geometricGenus k ((irreducibleComponentIdeal iD.2).subschemeι ≫ (f iD.1 ≫ g)))]
  refine (Fintype.sum_equiv (Equiv.ofBijective j hj) _ _ fun iD ↦ ?_).symm
  exact geometricGenus_image_irreducibleComponentIdeal g (f iD.1) iD.2 _ rfl

end AlgebraicGeometry

end
