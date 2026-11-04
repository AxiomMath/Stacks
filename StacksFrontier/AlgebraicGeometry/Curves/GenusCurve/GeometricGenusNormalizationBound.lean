module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusAlgClosure
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic

/-!
# The geometric genus is at most the genus of the normalization

Over an algebraically closed field `K`, the geometric genus of a proper scheme `Z` of dimension
at most one is the sum, over the irreducible components of `Z` of dimension one, of the genus of
the normalization of the component with its reduced structure.  By [Stacks, Tag 0CDV] the
normalization of `Z` is the disjoint union of the normalizations of those reduced components, and
the genus is additive over a disjoint union, so that sum — once the components of dimension other
than one are added back, which only increases it — is the genus of the normalization of `Z`:

`g_geom(Z/K) ≤ g(Z^ν)`.

This is the first half of the per-fibre bound of [Stacks, Tag 0CE5]; the second half is
`g(Z^ν) ≤ g(Z)`, which is [Stacks, Tag 0CE3]
(`AlgebraicGeometry.genus_le_of_isFinite_of_isClosedImmersion_over_dense_open`) applied to the
normalization morphism, and needs a dense open of `Z` over which that morphism is a closed
immersion.

## Main results

* `AlgebraicGeometry.genus_comp_iso_eq`: the genus is unchanged by precomposition with an
  isomorphism.
* `AlgebraicGeometry.genus_normalizationOverField_eq_sum_components`: the genus of the
  normalization is the sum of the genera of the normalizations of the reduced irreducible
  components.
* `AlgebraicGeometry.geometricGenus_le_genus_normalizationOverField`: over an algebraically
  closed field, the geometric genus of a proper scheme of dimension at most one is at most the
  genus of its normalization.

## Implementation notes

The reduced irreducible components of [Stacks, Tag 0CDV],
`AlgebraicGeometry.Scheme.reducedComponent`, and the ones the geometric genus is defined by,
`AlgebraicGeometry.irreducibleComponentIdeal`, are the same reduced closed subscheme: both are
the subscheme of the vanishing ideal of the component as a closed set.  The two normalization
morphisms are likewise the same, their differing finiteness hypotheses being propositions.

## References

* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 0CE1](https://stacks.math.columbia.edu/tag/0CE1)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The genus of a proper scheme over a field is unchanged by precomposition with an
isomorphism: the isomorphism is a base change along the identity of the ground field. -/
public theorem genus_comp_iso_eq (k : Type u) [Field k] {A B : Scheme.{u}}
    (p : B ⟶ Spec (.of k)) [IsProper p] (e : A ≅ B) : genus (e.hom ≫ p) = genus p := by
  refine genus_baseChange k k e.hom (e.hom ≫ p) p ?_
  rw [show Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) by simp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **The genus of the normalization is the sum over the irreducible components.**  By [Stacks,
Tag 0CDV] the normalization of a scheme locally of finite type over a field is the disjoint union
of the normalizations of its reduced irreducible components, and the genus is additive over a
disjoint union. -/
public theorem genus_normalizationOverField_eq_sum_components (K : Type u) [Field K]
    {Z : Scheme.{u}} (q : Z ⟶ Spec (.of K)) [IsProper q]
    [Fintype (irreducibleComponents Z)] :
    genus (normalizationOverField K q ≫ q) =
      ∑ W : irreducibleComponents Z,
        genus (normalizationOverField K ((irreducibleComponentIdeal W).subschemeι ≫ q) ≫
          ((irreducibleComponentIdeal W).subschemeι ≫ q)) := by
  classical
  have hprop : IsProper (normalizationOverField K q ≫ q) :=
    isProper_normalizationOverField_comp K q
  obtain ⟨e, he⟩ := Z.exists_iso_normalizationScheme_sigma_reducedComponent
    (finite_irreducibleComponents_of_locallyOfFiniteType K q)
  rw [← genus_comp_iso_eq K (normalizationOverField K q ≫ q) e, ← Category.assoc, he]
  have hprop' : IsProper ((Sigma.desc fun W : irreducibleComponents Z ↦
      (Z.reducedComponent W).normalization (Z.finite_irreducibleComponents_reducedComponent W) ≫
        Z.reducedComponentι W) ≫ q) := by
    rw [← he, Category.assoc]
    infer_instance
  rw [genus_sigma]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  rw [← Category.assoc, Sigma.ι_desc, Category.assoc]

/-- **The geometric genus is at most the genus of the normalization.**  Let `K` be an
algebraically closed field and let `Z` be a proper scheme of dimension at most one over `K`.
Then `g_geom(Z/K) ≤ g(Z^ν)`. -/
public theorem geometricGenus_le_genus_normalizationOverField (K : Type u) [Field K]
    [IsAlgClosed K] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of K)) [IsProper q]
    (hdim : topologicalKrullDim (Z : Type u) ≤ 1) :
    geometricGenus K q ≤ genus (normalizationOverField K q ≫ q) := by
  classical
  have : IsNoetherian Z :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q }
  have : Finite (irreducibleComponents Z) :=
    (finite_irreducibleComponents_of_isNoetherian (X := Z)).to_subtype
  let : Fintype (irreducibleComponents Z) := Fintype.ofFinite _
  rw [geometricGenus_eq_sum_all_components q, genus_normalizationOverField_eq_sum_components K q]
  refine Finset.sum_le_sum fun W _ ↦ ?_
  have hirr : IrreducibleSpace (irreducibleComponentIdeal W).subscheme := by
    apply Scheme.IdealSheafData.irreducibleSpace_subscheme
    rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    exact W.2.1
  have hdimW : topologicalKrullDim ((irreducibleComponentIdeal W).subscheme : Type u) ≤ 1 :=
    le_trans
      (irreducibleComponentIdeal W).subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le
      hdim
  rw [geometricGenus_eq_ite_genus_normalizationOverField K
    ((irreducibleComponentIdeal W).subschemeι ≫ q) hdimW]
  exact (ite_le_sup _ _ _).trans_eq (by simp)

end AlgebraicGeometry

end
