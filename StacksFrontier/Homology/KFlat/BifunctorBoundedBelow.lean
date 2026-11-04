module

public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# Bounded below K-flat complexes: colimits, and the reduction to canonical truncation

The hypothesis `hGE` of `CochainComplex.KFlatMonoidal.derivedPlusMonoidal` asks that a complex
vanishing in degrees below `a` receive a quasi-isomorphism from a K-flat complex vanishing in
degrees below some `a'`.  `CochainComplex.KFlatBifunctor.kFlat_of_isColimit` produces K-flat
complexes and records no bound; the K-flat resolutions this library constructs record no bound
either.  This file supplies the two statements that bound them, and with the second it reduces
`hGE` to a single property of the canonical truncation.

**Degreewise flatness is not enough.**  A complex which is degreewise flat
and bounded below need *not* be K-flat, so a Cartan-Eilenberg flat resolution of a bounded below
complex does not supply `hGE`, not even over a ring of flat dimension one.  Over `ℤ`, take `P`
to be `ℤ →^2 ℤ →^2 ℤ → ⋯` in degrees `0, 1, 2, …`, which is degreewise free and vanishes below
`0`, and `Z` the acyclic complex with `Z^q = ℤ/4` in every degree and differential
multiplication by `2`.  Then `(P ⊗ Z)^m = ⨁_{p ≥ 0} ℤ/4` with differential
`(c_p) ↦ (2c_{p-1} ± 2c_p)`, whose cycles are the sequences of even entries and whose
boundaries are those whose halved entries sum to zero; so `Hᵐ(P ⊗ Z) ≅ ℤ/2 ≠ 0` for every `m`,
and `P` is not K-flat.  K-flatness of a bounded below complex therefore cannot be read off its
terms: it has to come either from an assembly out of complexes bounded on *both* sides, where
`CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_isStrictlyGE` applies, or from a
truncation of a complex already known to be K-flat.

## Main results

* `CochainComplex.isStrictlyGE_of_isColimit`: **a colimit of complexes which all vanish in
  degrees below `a` vanishes in degrees below `a`.**  Colimits of complexes are computed
  degreewise, so this is the vanishing of a colimit of zero objects.
* `CochainComplex.KFlatBifunctor.kFlat_isStrictlyGE_of_isColimit`: **a colimit of K-flat
  complexes which all vanish in degrees below `a` is K-flat and vanishes in degrees below `a`**,
  under the hypotheses of `CochainComplex.KFlatBifunctor.kFlat_of_isColimit`.  This is the shape
  in which a bounded below K-flat resolution is assembled from bounded pieces.
* `CochainComplex.KFlatBifunctor.exists_kFlat_resolution_isStrictlyGE_of_kFlat_truncGE`:
  **bounded below K-flat resolutions exist, with `a' = a - 1`, as soon as the canonical
  truncation `P.truncGE m` of a K-flat complex `P` with `Hⁱ(P) = 0` for `i ≤ m` is K-flat.**
  That is the whole remaining content of `hGE`: unbounded K-flat resolutions are already
  available — for abelian sheaves they are
  `Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves` — and `CochainComplex.truncGE` is
  what cuts one down to a bounded below complex.

  The side condition `P.IsGE (m + 1)` is not decoration.  Without it the statement is false:
  over `ℤ` the complex `ℤ →^2 ℤ` in degrees `-1, 0` is K-flat, being bounded above with free
  terms, while its truncation at `0` is `ℤ/2` in degree `0`, which is not flat and so not
  K-flat.  With it, the degree `m` term of `P.truncGE m` is `coker(dᵐ⁻¹)`, which exactness of
  `P` at `m` identifies with the image of `dᵐ`, a subobject of `Pᵐ⁺¹` — and that is where flat
  dimension one would enter, as a subobject of a flat object being flat.

## Implementation notes

The quasi-isomorphism of
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_isStrictlyGE_of_kFlat_truncGE` runs the
right way only because of `CochainComplex.πTruncGE`.  Truncating a resolution `φ : P ⟶ G`
produces `P.πTruncGE m : P ⟶ P.truncGE m`, a map *out of* `P`, which is the wrong direction for
`hGE`; applying `CochainComplex.truncGEMap` to `φ` instead gives `P.truncGE m ⟶ G.truncGE m`,
and `G.πTruncGE m` is an isomorphism because `G` is already strictly bounded below, so the
target is `G` itself.

## References

* [Stacks Project, Tag 06YR](https://stacks.math.columbia.edu/tag/06YR)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {B : Type*} [Category B] [Preadditive B]
  {J : Type*} [Category J] [HasColimitsOfShape J B]

/-- **A colimit of cochain complexes which all vanish in degrees below `a` vanishes in degrees
below `a`.**  Colimits of complexes are computed degreewise, so in a degree below `a` the vertex
is a colimit of zero objects, and a colimit of zero objects is zero because every leg into it is
zero.

Mathlib has this for a *finite* shape, as the instance
`(CochainComplex.plus B).IsClosedUnderColimitsOfShape J`, where the bound is produced by taking
a minimum over the finitely many indices.  For an infinite shape no such minimum exists and the
bound has to be given, which is what makes this a separate statement rather than an instance:
the assembly of a bounded below resolution is a sequential colimit, and the bound is uniform in
the index by construction. -/
theorem isStrictlyGE_of_isColimit {Dg : J ⥤ CochainComplex B ℤ} (c : Cocone Dg)
    (hc : IsColimit c) (a : ℤ) (hGE : ∀ j, (Dg.obj j).IsStrictlyGE a) :
    c.pt.IsStrictlyGE a := by
  rw [isStrictlyGE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  refine (isColimitOfPreserves (HomologicalComplex.eval B (ComplexShape.up ℤ) i) hc).hom_ext
    fun j => ?_
  let := hGE j
  exact ((Dg.obj j).isZero_of_isStrictlyGE a i hi).eq_of_src _ _

end CochainComplex

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [HasZeroObject B] [HasBinaryBiproducts B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  {J : Type*} [Category J] [HasColimitsOfShape J B] [HasColimitsOfShape J D]

omit [HasZeroObject B] [HasBinaryBiproducts B]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- **A colimit of K-flat complexes which all vanish in degrees below `a` is K-flat and vanishes
in degrees below `a`.**  The two halves are
`CochainComplex.KFlatBifunctor.kFlat_of_isColimit` and
`CochainComplex.isStrictlyGE_of_isColimit`; they are stated together because the consumer which
needs a bounded below K-flat complex needs them of the same complex.

The hypotheses on `F` and on `D` are those of
`CochainComplex.KFlatBifunctor.kFlat_of_isColimit`, and for `F = ⊗_O` on a ringed site and a
filtered shape both hold: the first because `Mod(O)` is monoidal closed, the second because
`Mod(O)` satisfies AB5. -/
theorem kFlat_isStrictlyGE_of_isColimit {Dg : J ⥤ CochainComplex B ℤ} (c : Cocone Dg)
    (hc : IsColimit c)
    (hF : ∀ X : A, PreservesColimitsOfShape J (F.obj X))
    (hexact : ∀ (E : J ⥤ CochainComplex D ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic)
    (hDg : ∀ j, KFlat F (Dg.obj j)) (a : ℤ) (hGE : ∀ j, (Dg.obj j).IsStrictlyGE a) :
    KFlat F c.pt ∧ c.pt.IsStrictlyGE a :=
  ⟨kFlat_of_isColimit F c hc hF hexact hDg, isStrictlyGE_of_isColimit c hc a hGE⟩

end CochainComplex.KFlatBifunctor

namespace CochainComplex.KFlatBifunctor

section Truncation

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **Bounded below K-flat resolutions exist, with `a' = a - 1`, as soon as the canonical
truncation of a K-flat complex is K-flat.**

The two hypotheses separate what is already available from what is not.  `hres` is the existence
of K-flat resolutions with no bound, which this library has unconditionally wherever it has a
derived tensor product at all — for abelian sheaves it is
`Stacks.Cohomology.exists_kFlat_resolution_abelianSheaves`.  `htrunc` is the one remaining
input: that `CochainComplex.truncGE` at `m` takes a K-flat complex whose cohomology vanishes in
degrees `≤ m` to a K-flat complex.  Together they give the hypothesis `hGE` of
`CochainComplex.KFlatMonoidal.derivedPlusMonoidal`, with the bound `a - 1` on the resolution of
a complex vanishing below `a`.

The proof is the truncation of the resolution, with the direction of the quasi-isomorphism
repaired as the module documentation describes: `CochainComplex.truncGEMap` applied to
`φ : P ⟶ G` lands in `G.truncGE (a-1)`, and `G.πTruncGE (a-1)` is invertible because `G`
vanishes below `a`.  The cohomological hypothesis of `htrunc` is available because `φ` is a
quasi-isomorphism, so `P` and `G` have the same cohomology
(`HomologicalComplex.isSupported_iff_of_quasiIso`).

`htrunc` is false without its cohomological side condition, and the side condition is exactly
what makes the bottom term of the truncation a subobject of a flat object; see the module
documentation. -/
theorem exists_kFlat_resolution_isStrictlyGE_of_kFlat_truncGE
    (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
      KFlat F P ∧ QuasiIso f)
    (htrunc : ∀ (m : ℤ) (P : CochainComplex B ℤ), KFlat F P → P.IsGE (m + 1) →
      KFlat F (P.truncGE m))
    (a : ℤ) (G : CochainComplex B ℤ) (hG : G.IsStrictlyGE a) :
    ∃ (a' : ℤ) (P : CochainComplex B ℤ) (f : P ⟶ G), P.IsStrictlyGE a' ∧
      KFlat F P ∧ QuasiIso f := by
  obtain ⟨P, φ, hP, hφ⟩ := hres G
  let _ := hG
  let hPGE : P.IsGE a :=
    (HomologicalComplex.isSupported_iff_of_quasiIso φ (ComplexShape.embeddingUpIntGE a)).2
      inferInstance
  let _ : G.IsStrictlyGE (a - 1) := G.isStrictlyGE_of_ge (a - 1) a (by omega)
  let _ : QuasiIso (CochainComplex.truncGEMap φ (a - 1)) := by
    rw [CochainComplex.quasiIso_truncGEMap_iff]
    exact fun i _ => inferInstance
  exact ⟨a - 1, P.truncGE (a - 1),
    CochainComplex.truncGEMap φ (a - 1) ≫ inv (G.πTruncGE (a - 1)), inferInstance,
    htrunc (a - 1) P hP (by rwa [sub_add_cancel]), inferInstance⟩

end Truncation

end CochainComplex.KFlatBifunctor

end
