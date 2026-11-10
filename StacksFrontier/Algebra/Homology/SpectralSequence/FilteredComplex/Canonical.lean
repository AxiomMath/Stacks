module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The spectral sequence of a filtered complex, as a functor

Stacks, Homological Algebra, Section 12.24 builds from a filtered complex `(K^•, F)` of an abelian
category `𝒜` a cohomological spectral sequence ([Stacks, Tag 012M]) and shows the construction to
be functorial in filtration-preserving chain maps ([Stacks, Tag 012O]). The object half is
`CochainComplex.filteredSpectralSequence` and the morphism half is
`CochainComplex.filteredSpectralSequenceMap`, whose identity and composition laws are
`CochainComplex.filteredSpectralSequenceMap_id` and
`CochainComplex.filteredSpectralSequenceMap_comp`. This file assembles those four declarations into
the functor they present, and records the identification of its pages with the cycle-boundary
quotients `E_r^{p, q} = Z_r^{p, q} / (D_r^{p, q} ⊓ Z_r^{p, q})` read through that functor.

## Main definitions

* `CochainComplex.Filtered.spectralSequenceFunctor` is the functor
  `Filtered 𝒜 ⥤ CohomologicalSpectralSequence 𝒜 0` sending a filtered complex to its spectral
  sequence and a morphism of filtered complexes to the induced morphism of spectral sequences.

## Main results

* `CochainComplex.Filtered.pageIso` identifies the object of the `r`-th page of
  `spectralSequenceFunctor.obj K` at the bidegree `(p, q)` with the subquotient
  `FilteredComplexSpectralSequence.pageObj` of `K^{p + q}`.
* `CochainComplex.Filtered.pageIso_hom` and `CochainComplex.Filtered.pageIso_inv`: that
  identification is the identity, the page being that subquotient on the nose.

## Implementation notes

The bundled datum a consumer quantifies over is `CochainComplex.Filtered 𝒜`, the 012L-tagged
filtered complex of `StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs`; it is
already a bundled structure with a category structure, so no wrapper around it is introduced here.
The subobject-valued filtration it carries degreewise is
`CochainComplex.filtrationSubobject`, decreasing by `CochainComplex.filtrationSubobject_antitone`,
and the filtration induced on cohomology is `CochainComplex.Filtered.inducedFiltrationStep`; all
three are reused rather than respelled.

`pageIso` exists because a consumer reaching a page through the functor has a goal stated against
`spectralSequenceFunctor.obj K` rather than against the underlying
`FilteredComplexSpectralSequence.spectralSequence`, and `FilteredComplexSpectralSequence.eIso`
does not apply to it syntactically. It carries no mathematical content of its own: both its
components are identities.

No `@[stacks]` attribute is attached. Tag 012M is registered on
`CochainComplex.exists_cohomologicalSpectralSequence` and tag 012O on
`FilteredComplexSpectralSequence.spectralSequenceMap`; this file is the functorial packaging of
those results, not a further row.

## Ownership

Cluster 09 owns this module. It was written at the request of the run controller to unblock
cluster 13's tags 0BKD and 0BKE, whose statements quantify over a bundled filtered complex and
over its spectral sequence as a functor.

It is a port of an earlier auxiliary development of the same functor, not a copy: that development
cannot be compiled. Its central structure `FilteredComplexEntirelyAbelianC` is declared nowhere in
the tree, and the modules that were to supply it and its subobject calculus are likewise absent, so
every proof there is written against a data layout whose definition is missing. What the
port establishes instead is that the tracked framework already carries the same mathematics: the
legacy bundled structure was a skin over `CategoryTheory.FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ`,
its `degreeFiltration` is `CochainComplex.filtrationSubobject`, its page objects are
`FilteredComplexSpectralSequence.pageObj`, and its spectral sequence carried a `Classical.choice`
that the explicit construction here does not need.

## References

* [Stacks Project, Lemma 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Lemma 012O](https://stacks.math.columbia.edu/tag/012O)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CochainComplex

namespace Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The spectral sequence of a filtered complex, as a functor.** It sends a filtered complex
`K` of `C` to the cohomological spectral sequence `(E_r(K), d_r)_{r ≥ 0}` of [Stacks, Tag 012M],
and a filtration-preserving chain map to the morphism of spectral sequences it induces on every
page ([Stacks, Tag 012O]). -/
@[ega "0 11.2.3" "page part of E(u)"]
noncomputable def spectralSequenceFunctor :
    Filtered C ⥤ CohomologicalSpectralSequence C 0 where
  obj K := filteredSpectralSequence K
  map φ := filteredSpectralSequenceMap φ
  map_id K := filteredSpectralSequenceMap_id K
  map_comp φ ψ := filteredSpectralSequenceMap_comp φ ψ

/-- The spectral sequence functor sends a filtered complex to its spectral sequence. -/
@[simp]
lemma spectralSequenceFunctor_obj (K : Filtered C) :
    spectralSequenceFunctor.obj K = filteredSpectralSequence K :=
  rfl

/-- The spectral sequence functor sends a filtration-preserving chain map to the morphism of
spectral sequences it induces. -/
@[simp]
lemma spectralSequenceFunctor_map {K L : Filtered C} (φ : K ⟶ L) :
    spectralSequenceFunctor.map φ = filteredSpectralSequenceMap φ :=
  rfl

/-- **The pages of `spectralSequenceFunctor` are the cycle-boundary quotients.** The object of the
`r`-th page at the bidegree `(p, q)` is `Z_r^{p, q} / (D_r^{p, q} ⊓ Z_r^{p, q})`, a subquotient of
`K^{p + q}`, where the cycles and boundaries are those of the degreewise filtration
`CochainComplex.filtrationSubobject`. -/
noncomputable def pageIso (K : Filtered C) (r p q : ℤ) (hr : 0 ≤ r) :
    ((spectralSequenceFunctor.obj K).page r hr).X (p, q) ≅
      FilteredComplexSpectralSequence.pageObj K.X (filtrationSubobject K) r p (p + q) :=
  FilteredComplexSpectralSequence.eIso K.X (filtrationSubobject K)
    (filtrationSubobject_antitone K) r p q (p + q) hr rfl

/-- The page identification is the identity: the page is the subquotient on the nose. -/
@[simp]
lemma pageIso_hom (K : Filtered C) (r p q : ℤ) (hr : 0 ≤ r) :
    (pageIso K r p q hr).hom = 𝟙 _ := by
  simp [pageIso]

/-- The page identification is the identity: the page is the subquotient on the nose. -/
@[simp]
lemma pageIso_inv (K : Filtered C) (r p q : ℤ) (hr : 0 ≤ r) :
    (pageIso K r p q hr).inv = 𝟙 _ := by
  simp [pageIso]

/-- **The differentials of `spectralSequenceFunctor` are induced by the differential of the
complex.** Reading the `r`-th page as the cycle-boundary quotient `Z_r / (D_r ⊓ Z_r)` through
`pageIso`, the differential `d_r^{p, q}` is the map induced by `d^n : K^n ⟶ K^{n + 1}` on
`Z_r^{p, q} ⟶ Z_r^{p + r, q - r + 1}`. -/
lemma exists_pageIso_d (K : Filtered C) :
    ∃ e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q),
        ((spectralSequenceFunctor.obj K).page r hr).X (p, q) ≅
          Limits.cokernel (Subobject.ofLE _ _ (inf_le_right :
            FilteredComplexSpectralSequence.boundaries K.X (filtrationSubobject K) r p n ⊓
                FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r p n ≤
              FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r p n)),
      ∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
        ∃ δ : (FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r p n : C) ⟶
            (FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r (p + r)
              (n + 1) : C),
          δ ≫ (FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r (p + r)
                (n + 1)).arrow =
              (FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r p n).arrow ≫
                K.X.d n (n + 1) ∧
          Limits.cokernel.π (Subobject.ofLE _ _ (inf_le_right :
              FilteredComplexSpectralSequence.boundaries K.X (filtrationSubobject K) r p n ⊓
                  FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r p n ≤
                FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r p n)) ≫
                (e r p q n hr hn).inv ≫
                ((spectralSequenceFunctor.obj K).page r hr).d (p, q) (p + r, q - r + 1) =
            δ ≫ Limits.cokernel.π (Subobject.ofLE _ _ (inf_le_right :
                FilteredComplexSpectralSequence.boundaries K.X (filtrationSubobject K) r (p + r)
                      (n + 1) ⊓
                    FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r (p + r)
                      (n + 1) ≤
                  FilteredComplexSpectralSequence.cycles K.X (filtrationSubobject K) r (p + r)
                    (n + 1))) ≫
              (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv := by
  refine ⟨fun r p q n hr hn => FilteredComplexSpectralSequence.eIso K.X (filtrationSubobject K)
    (filtrationSubobject_antitone K) r p q n hr hn, ?_⟩
  intro r p q n hr hn
  subst hn
  refine ⟨FilteredComplexSpectralSequence.deltaCycles K.X (filtrationSubobject K) r p (p + q),
    FilteredComplexSpectralSequence.deltaCycles_arrow K.X (filtrationSubobject K) r p (p + q), ?_⟩
  change Limits.cokernel.π
      (FilteredComplexSpectralSequence.den K.X (filtrationSubobject K) r p (p + q)) ≫
      (FilteredComplexSpectralSequence.eIso K.X (filtrationSubobject K)
        (filtrationSubobject_antitone K) r p q (p + q) hr rfl).inv ≫
      ((FilteredComplexSpectralSequence.spectralSequence K.X (filtrationSubobject K)
        (filtrationSubobject_antitone K)).page r hr).d (p, q) (p + r, q - r + 1) =
    FilteredComplexSpectralSequence.deltaCycles K.X (filtrationSubobject K) r p (p + q) ≫
      Limits.cokernel.π
        (FilteredComplexSpectralSequence.den K.X (filtrationSubobject K) r (p + r) (p + q + 1)) ≫
      (FilteredComplexSpectralSequence.eIso K.X (filtrationSubobject K)
        (filtrationSubobject_antitone K) r (p + r) (q - r + 1) (p + q + 1) hr (by ring)).inv
  rw [FilteredComplexSpectralSequence.spectralSequence_d,
    FilteredComplexSpectralSequence.eIso_inv_rfl, Category.id_comp,
    ← Category.assoc, FilteredComplexSpectralSequence.π_comp_pageMap, Category.assoc]

end Filtered

end CochainComplex

end
