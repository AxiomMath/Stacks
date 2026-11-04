module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDownUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic

/-!
# The geometric genus is at most the genus, with no hypothesis on the components

Over an algebraically closed field `K`, a proper scheme `Z` of dimension at most one satisfies
`g_geom(Z/K) ≤ g(Z)`.  This is the per-fibre bound of [Stacks, Tag 0CE5], and unlike
`AlgebraicGeometry.geometricGenus_le_genus_of_irreducible` it asks nothing of the irreducible
components: `Z` may be reducible and non-reduced.

The proof runs through the normalization.
`AlgebraicGeometry.geometricGenus_le_genus_normalizationOverField` gives
`g_geom(Z/K) ≤ g(Z^ν)` out of [Stacks, Tag 0CDV], and the remaining `g(Z^ν) ≤ g(Z)` is two
applications of [Stacks, Tag 0CE3]
(`AlgebraicGeometry.genus_le_of_isFinite_of_isClosedImmersion_over_dense_open`) along the
factorization `Z^ν ⟶ Z_red ⟶ Z` of the normalization morphism:

* `Z_red ⟶ Z` is a closed immersion, so Tag 0CE3 applies to it with the dense open `⊤`;
* `Z^ν ⟶ Z_red` is the normalization morphism of the *reduced* scheme `Z_red` ([Stacks, Tag
  035O]), hence birational ([Stacks, Tag 0BXC]), hence an isomorphism over a dense open of
  `Z_red` ([Stacks, Tag 0BAJ]), and an isomorphism is in particular a closed immersion.

## Main results

* `AlgebraicGeometry.isClosedImmersion_pullback_snd_of_isIso_morphismRestrict`: a morphism that
  restricts to an isomorphism over an open of its target has a closed immersion for its base
  change along that open.
* `AlgebraicGeometry.genus_normalizationOverField_le`: `g(Z^ν) ≤ g(Z)` for a proper scheme of
  dimension at most one over a field.
* `AlgebraicGeometry.geometricGenus_le_genus_of_dim_le_one`: **the per-fibre bound of [Stacks,
  Tag 0CE5]** — over an algebraically closed field, `g_geom(Z/K) ≤ g(Z)`.

## Implementation notes

[Stacks, Tag 0CE3] as proved in this library asks for `IsClosedImmersion (pullback.snd f U.ι)`
while [Stacks, Tag 0BAJ] produces `IsIso (f ∣_ U)`; the two are compared through
`AlgebraicGeometry.isPullback_morphismRestrict`, which makes the restriction square a pullback,
so the chosen pullback and the restriction differ by an isomorphism over `U`.

Finiteness of the normalization morphism, which Tag 0CE3 needs, is
`AlgebraicGeometry.isFinite_normalizationOverField`, available for any scheme locally of finite
type over a field; no integrality is required.

## References

* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism that restricts to an isomorphism over an open `V` of its target has a closed
immersion for its base change along `V`: the restriction square is a pullback, so the chosen
pullback and the restriction differ by an isomorphism over `V`. -/
public theorem isClosedImmersion_pullback_snd_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] :
    IsClosedImmersion (pullback.snd f V.ι) := by
  have h := isPullback_morphismRestrict f V
  have h' := (IsPullback.of_hasPullback f V.ι).flip
  have hα : (h.isoIsPullback _ _ h').hom ≫ pullback.snd f V.ι = f ∣_ V :=
    h.isoIsPullback_hom_fst _ _ h'
  have heq : pullback.snd f V.ι = (h.isoIsPullback _ _ h').inv ≫ (f ∣_ V) :=
    (Iso.eq_inv_comp _).mpr hα
  have : IsIso (pullback.snd f V.ι) := by rw [heq]; infer_instance
  infer_instance

/-- **The genus of the normalization is at most the genus.**  For a proper scheme `Z` of
dimension at most one over a field `K`, `g(Z^ν) ≤ g(Z)`.  The normalization morphism factors
through the reduction of `Z`; the closed immersion `Z_red ⟶ Z` and the normalization morphism of
the reduced scheme `Z_red`, which is an isomorphism over a dense open, are each handled by
[Stacks, Tag 0CE3]. -/
public theorem genus_normalizationOverField_le (K : Type u) [Field K] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of K)) [IsProper q] (hdim : topologicalKrullDim (Z : Type u) ≤ 1) :
    genus (normalizationOverField K q ≫ q) ≤ genus q := by
  classical
  have hZfin : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_locallyOfFiniteType K q
  have hRfin := Z.finite_irreducibleComponents_reduction hZfin
  have hred : IsReduced Z.nilradical.subscheme := isReduced_nilradical_subscheme Z
  -- the reduction and its normalization
  have hdimR : topologicalKrullDim (Z.nilradical.subscheme : Type u) ≤ 1 :=
    le_trans Z.nilradical.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le hdim
  have hνfin : IsFinite (Z.nilradical.subscheme.normalization hRfin) :=
    isFinite_normalizationOverField K (Z.nilradical.subschemeι ≫ q)
  have hprop : IsProper (Z.nilradical.subscheme.normalization hRfin ≫
      (Z.nilradical.subschemeι ≫ q)) := inferInstance
  -- the normalization of `Z` is the normalization of its reduction
  obtain ⟨e, he⟩ := Z.exists_normalizationScheme_iso_reduction hZfin
  have hmor : normalizationOverField K q ≫ q =
      e.hom ≫ (Z.nilradical.subscheme.normalization hRfin ≫ (Z.nilradical.subschemeι ≫ q)) := by
    rw [show normalizationOverField K q = _ from he.symm, Category.assoc, Category.assoc]
  -- the normalization of the reduction is an isomorphism over a dense open
  have hnoeth : ∀ {W : Scheme.{u}} (g : W ⟶ Spec (.of K)) [IsProper g], IsNoetherian W :=
    fun g => { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
               toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  have hNoeth := hnoeth (Z.nilradical.subscheme.normalization hRfin ≫ (Z.nilradical.subschemeι ≫ q))
  have hNoethR := hnoeth (Z.nilradical.subschemeι ≫ q)
  have : Finite (irreducibleComponents (Z.nilradical.subscheme.normalizationScheme hRfin)) :=
    (finite_irreducibleComponents_of_isNoetherian
      (X := Z.nilradical.subscheme.normalizationScheme hRfin)).to_subtype
  have : Finite (irreducibleComponents Z.nilradical.subscheme) :=
    (finite_irreducibleComponents_of_isNoetherian (X := Z.nilradical.subscheme)).to_subtype
  obtain ⟨V, hVdense, hViso⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational
    (Z.nilradical.subscheme.normalization hRfin)
    (Scheme.isBirational_normalization Z.nilradical.subscheme hRfin)
    (Or.inl inferInstance) (Or.inl ⟨inferInstance, hred⟩)
  calc genus (normalizationOverField K q ≫ q)
      = genus (Z.nilradical.subscheme.normalization hRfin ≫
          (Z.nilradical.subschemeι ≫ q)) := by rw [hmor, genus_comp_iso_eq]
    _ ≤ genus (Z.nilradical.subschemeι ≫ q) :=
        genus_le_of_isFinite_of_isClosedImmersion_over_dense_open K
          (Z.nilradical.subschemeι ≫ q) (Z.nilradical.subscheme.normalization hRfin) hdimR V
          hVdense (isClosedImmersion_pullback_snd_of_isIso_morphismRestrict _ V)
    _ ≤ genus q :=
        genus_le_of_isFinite_of_isClosedImmersion_over_dense_open K q Z.nilradical.subschemeι
          hdim ⊤ dense_univ inferInstance

/-- **The per-fibre bound of [Stacks, Tag 0CE5].**  Over an algebraically closed field `K`, the
geometric genus of a proper scheme of dimension at most one is at most its genus.  No hypothesis
is made on the irreducible components: the scheme may be reducible and non-reduced. -/
@[stacks 0CE5 "the per-fibre bound, over an algebraically closed field"]
public theorem geometricGenus_le_genus_of_dim_le_one (K : Type u) [Field K] [IsAlgClosed K]
    {Z : Scheme.{u}} (q : Z ⟶ Spec (.of K)) [IsProper q]
    (hdim : topologicalKrullDim (Z : Type u) ≤ 1) :
    geometricGenus K q ≤ genus q :=
  (geometricGenus_le_genus_normalizationOverField K q hdim).trans
    (genus_normalizationOverField_le K q hdim)

end AlgebraicGeometry

end
