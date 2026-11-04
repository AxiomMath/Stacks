module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Basic

/-!
# Quasi-separatedness after a change of base field

Let `k` be a field, `X` a scheme over `k` and `K/k` a field extension. If the base change `X_K`
is quasi-separated over `K`, then `X` is quasi-separated over `k`. More generally,
quasi-separatedness of the underlying space of a scheme transfers along any surjective
quasi-compact morphism of schemes, and `Spec(K) → Spec(k)` is one. Together with
`AlgebraicGeometry.compactSpace_of_fieldExtension` this gives the opening step of the proof of
[Stacks, Tag 0BDC].

## Main results

* `AlgebraicGeometry.quasiSeparatedSpace_of_surjective_of_quasiCompact`: quasi-separatedness of
  the underlying space of a scheme transfers along a surjective quasi-compact morphism of
  schemes.
* `AlgebraicGeometry.quasiSeparatedSpace_of_faithfullyFlat_baseChange` and
  `AlgebraicGeometry.quasiSeparated_of_faithfullyFlat_baseChange`: quasi-separatedness descends
  along the base change by a faithfully flat algebra.
* `AlgebraicGeometry.quasiSeparatedSpace_of_fieldExtension` and
  `AlgebraicGeometry.quasiSeparated_of_fieldExtension`: quasi-separatedness descends from a
  field extension.
* `AlgebraicGeometry.compactSpace_and_quasiSeparatedSpace_of_fieldExtension`: quasi-compactness
  and quasi-separatedness of the underlying space both descend from a field extension.

## Implementation notes

Quasi-separatedness is tested on pairs of affine opens
(`AlgebraicGeometry.quasiSeparatedSpace_iff_forall_affineOpens`, [Stacks, Tag 01KO]). The
hypothesis `Module.FaithfullyFlat R S` enters only through the surjectivity of
`Spec(S) → Spec(R)`.

## References

* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Quasi-separatedness of the underlying space of a scheme transfers along a surjective
quasi-compact morphism. -/
public theorem quasiSeparatedSpace_of_surjective_of_quasiCompact {Y X : Scheme.{u}} (p : Y ⟶ X)
    [Surjective p] [QuasiCompact p] [QuasiSeparatedSpace Y] : QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  have h := (QuasiSeparatedSpace.inter_isCompact _ _
    (p ⁻¹ᵁ U.1).2 (p.isCompact_preimage U.2.isCompact)
    (p ⁻¹ᵁ V.1).2 (p.isCompact_preimage V.2.isCompact)).image p.continuous
  simpa [← Set.preimage_inter, Set.image_preimage_eq _ p.surjective] using h

section FaithfullyFlat

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- If the base change of a scheme along a faithfully flat algebra is quasi-separated over the
larger ring, then the scheme has quasi-separated underlying space. -/
public theorem quasiSeparatedSpace_of_faithfullyFlat_baseChange
    (h : QuasiSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    QuasiSeparatedSpace X :=
  have := h
  have := quasiSeparatedSpace_of_quasiSeparated
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  quasiSeparatedSpace_of_surjective_of_quasiCompact
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- Quasi-separatedness of a morphism to an affine scheme descends along the base change by a
faithfully flat algebra. -/
public theorem quasiSeparated_of_faithfullyFlat_baseChange
    (h : QuasiSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    QuasiSeparated f :=
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_faithfullyFlat_baseChange f h
  inferInstance

end FaithfullyFlat

section FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- A scheme over a field has quasi-separated underlying space as soon as its base change to
some extension field is quasi-separated over that field. -/
public theorem quasiSeparatedSpace_of_fieldExtension
    (h : QuasiSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_faithfullyFlat_baseChange f h

/-- Quasi-separatedness descends from a field extension. -/
public theorem quasiSeparated_of_fieldExtension
    (h : QuasiSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    QuasiSeparated f :=
  quasiSeparated_of_faithfullyFlat_baseChange f h

/-- Quasi-compactness and quasi-separatedness of the underlying space both descend from a field
extension. -/
public theorem compactSpace_and_quasiSeparatedSpace_of_fieldExtension
    (hqc : QuasiCompact (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (hqs : QuasiSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨compactSpace_of_fieldExtension k K f hqc, quasiSeparatedSpace_of_fieldExtension k K f hqs⟩

end FieldExtension

end AlgebraicGeometry

end
