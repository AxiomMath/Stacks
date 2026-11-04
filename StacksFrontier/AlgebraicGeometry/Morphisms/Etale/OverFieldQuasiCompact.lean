module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField

/-!
# Quasi-compact schemes étale over a field

A scheme étale over a field is a disjoint union of spectra of finite separable extensions of that
field, with no bound on the number of summands. When the scheme is quasi-compact the number of
summands is finite: the images of the summands are an open cover with no proper subcover, since
each summand has a point.

## Main results

* `AlgebraicGeometry.finite_index_of_iso_sigma`: a compact scheme isomorphic to a coproduct of
  schemes each of which has a point has a finite index type.
* `AlgebraicGeometry.Etale.exists_finite_iso_coproduct_spectra_finite_separable`: a quasi-compact
  scheme étale over a field is a finite disjoint union of spectra of finite separable extensions,
  compatibly with the morphism to the spectrum of the field.

## Implementation notes

Finiteness of the index type is isolated from étaleness: it needs only compactness of the total
space and a point in every summand, which is why it is stated for an arbitrary coproduct. A point
is asked for explicitly rather than through an emptiness hypothesis, so that the spectrum of a
field can be supplied by its unique point.

The source of the decomposition itself is
`AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable`; this file only adds the
count. Quasi-compactness of the structure morphism is used through compactness of the spectrum of
the field, so the hypothesis is the weakest one that gives a compact source.

## References

* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A compact disjoint union of inhabited schemes has finitely many summands.** The open images
of the summands cover the total space, and the point `z i` of the `i`-th summand lies in no other
image, so every index occurs in a finite subcover. -/
theorem finite_index_of_iso_sigma {I : Type u} {Z : I → Scheme.{u}} {U : Scheme.{u}}
    [CompactSpace U] (e : U ≅ ∐ Z) (z : ∀ i, Z i) : Finite I := by
  classical
  have hOopen (i : I) : IsOpen ((Sigma.ι Z i).opensRange.1 : Set ↥(∐ Z)) :=
    (Sigma.ι Z i).opensRange.is_open'
  have hCover : (Set.univ : Set ↥U) ⊆ ⋃ i, e.hom ⁻¹' (Sigma.ι Z i).opensRange.1 := by
    intro x _hx
    obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Z).surjective (e.hom x)
    rw [sigmaMk_mk] at hy
    exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun i ↦ e.hom.continuous.isOpen_preimage _ (hOopen i)) hCover
  have hall (i : I) : i ∈ t := by
    have hsurj : Surjective e.hom := inferInstance
    obtain ⟨x, hx⟩ := hsurj.surj (Sigma.ι Z i (z i))
    obtain ⟨j, hj, w, hw⟩ := by
      simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
    have heq : Sigma.ι Z j w = Sigma.ι Z i (z i) := hw.trans hx
    exact (Sigma.mk.inj ((sigmaι_eq_iff Z j i w (z i)).mp heq)).1 ▸ hj
  exact Finite.of_finite_univ (t.finite_toSet.subset fun i _ ↦ hall i)

/-- **A quasi-compact scheme étale over a field is a finite disjoint union of spectra of finite
separable extensions of that field**, compatibly with its morphism to the spectrum of the field.
This sharpens `AlgebraicGeometry.etale_iff_iso_coproduct_spectra_finite_separable`, whose index
type carries no finiteness, by counting the summands of a quasi-compact source. -/
theorem Etale.exists_finite_iso_coproduct_spectra_finite_separable
    (k : Type u) [Field k] {U : Scheme.{u}} (f : U ⟶ Spec (.of k)) [Etale f] [QuasiCompact f] :
    ∃ (I : Type u) (_ : Finite I) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
      (_ : ∀ i, Algebra.IsSeparable k (K i))
      (e : U ≅ ∐ fun i ↦ Spec (.of (K i))),
      e.hom ≫ Sigma.desc (fun i ↦
        Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
  obtain ⟨I, K, hK, hAlg, hFin, hSep, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k f).mp inferInstance
  let (i : I) : Field (K i) := hK i
  have hcompact : CompactSpace ↥U :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ⟩
  have hfinite : Finite I :=
    finite_index_of_iso_sigma e fun i ↦ (inferInstance : Inhabited (Spec (.of (K i)))).default
  exact ⟨I, hfinite, K, hK, hAlg, hFin, hSep, e, he⟩

end AlgebraicGeometry

end
