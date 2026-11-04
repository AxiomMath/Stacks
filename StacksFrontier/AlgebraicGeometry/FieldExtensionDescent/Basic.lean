module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type and quasi-compactness after a change of base field

Let `k` be a field, `X` a scheme over `k` and `K/k` a field extension. [Stacks, Tag 0BDE]
asserts that `X` is quasi-projective over `k` as soon as `X_K` is quasi-projective over `K`.
Quasi-projectivity is the conjunction of three conditions — locally of finite type,
quasi-compact, and the existence of a relatively ample invertible sheaf — and this file proves
the descent of the first two.

The reason to isolate them is that they descend for a reason that has nothing to do with
invertible sheaves: `Spec(K) → Spec(k)` is faithfully flat and quasi-compact, so it is an
fpqc covering, and both conditions descend along such a morphism. Nothing in this file is
special to fields, so everything is stated for a faithfully flat algebra and then specialized.

## Main results

* `AlgebraicGeometry.compactSpace_of_surjective`: quasi-compactness of the underlying space of a
  scheme transfers along a surjection of schemes.
* `AlgebraicGeometry.surjective_SpecMap_algebraMap`,
  `AlgebraicGeometry.flat_SpecMap_algebraMap` and
  `AlgebraicGeometry.surjective_inf_flat_inf_quasiCompact_SpecMap_algebraMap`: the morphism of
  spectra induced by a faithfully flat algebra is surjective, flat, and an fpqc covering.
* `AlgebraicGeometry.locallyOfFiniteType_of_faithfullyFlat_baseChange` and
  `AlgebraicGeometry.locallyOfFiniteType_of_fieldExtension`: being locally of finite type
  descends along a faithfully flat base change, in particular along a field extension.
* `AlgebraicGeometry.compactSpace_of_faithfullyFlat_baseChange`,
  `AlgebraicGeometry.quasiCompact_of_faithfullyFlat_baseChange`,
  `AlgebraicGeometry.compactSpace_of_fieldExtension` and
  `AlgebraicGeometry.quasiCompact_of_fieldExtension`: quasi-compactness descends likewise.
* `AlgebraicGeometry.locallyOfFiniteType_and_quasiCompact_of_fieldExtension`: the two together,
  which is the finite-type half of [Stacks, Tag 0BDE].

## Implementation notes

The source proves the finite-type statement ring-theoretically: an affine open `Spec(A) ⊆ X`
has `Spec(A_K) ⊆ X_K` affine open, so `A_K` is a `K`-algebra of finite type, so `A` is a
`k`-algebra of finite type by [Stacks, Tag 00QP]. The route taken here is the scheme-level
form of that argument, `CategoryTheory.MorphismProperty.of_pullback_snd_of_descendsAlong`
against Mathlib's instance that `AlgebraicGeometry.LocallyOfFiniteType` descends along
surjective flat quasi-compact morphisms, which is itself the descent of [Stacks, Tag 00QP]
and is already available; the two agree, and the second needs no affine-open bookkeeping.

For quasi-compactness the source argues that `X_K → X` is surjective and `X_K` is
quasi-compact. That is reproduced directly: `Spec(K) → Spec(k)` is surjective because the
algebra is faithfully flat, surjectivity is stable under base change, and the image of a
compact space is compact.

The ample half of [Stacks, Tag 0BDE] rests on the descent of ampleness along a field extension,
[Stacks, Tag 0BDC]; the full statement is in
`StacksFrontier/AlgebraicGeometry/FieldExtensionDescent/Unconditional.lean`.

## References

* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 00QP](https://stacks.math.columbia.edu/tag/00QP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The underlying space of a scheme that is the image of a scheme with quasi-compact space is
itself quasi-compact. -/
public theorem compactSpace_of_surjective {Y X : Scheme.{u}} (p : Y ⟶ X) [Surjective p]
    [CompactSpace Y] : CompactSpace X :=
  ⟨by
    rw [← Set.image_univ_of_surjective p.surjective]
    exact isCompact_univ.image p.base.hom.continuous⟩

section FaithfullyFlat

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]

/-- The morphism of spectra induced by a faithfully flat algebra is surjective. -/
public instance surjective_SpecMap_algebraMap :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R S))).2
    (RingHom.faithfullyFlat_algebraMap_iff.mpr ‹Module.FaithfullyFlat R S›)).2

/-- The morphism of spectra induced by a faithfully flat algebra is flat. -/
public instance flat_SpecMap_algebraMap :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R S))).2
    (RingHom.faithfullyFlat_algebraMap_iff.mpr ‹Module.FaithfullyFlat R S›)).1

/-- The morphism of spectra induced by a faithfully flat algebra is an fpqc covering: surjective,
flat and quasi-compact. -/
public theorem surjective_inf_flat_inf_quasiCompact_SpecMap_algebraMap :
    ((@Surjective ⊓ @Flat) ⊓ @QuasiCompact : MorphismProperty Scheme)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- Being locally of finite type descends along the base change by a faithfully flat algebra. -/
public theorem locallyOfFiniteType_of_faithfullyFlat_baseChange
    (h : LocallyOfFiniteType
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    LocallyOfFiniteType f :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @LocallyOfFiniteType) (Q := (@Surjective ⊓ @Flat) ⊓ @QuasiCompact)
    surjective_inf_flat_inf_quasiCompact_SpecMap_algebraMap h

/-- If the base change of a scheme along a faithfully flat algebra is quasi-compact over the
larger ring, then the scheme has quasi-compact underlying space. -/
public theorem compactSpace_of_faithfullyFlat_baseChange
    (h : QuasiCompact (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    CompactSpace X :=
  have := h.compactSpace_of_compactSpace
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  compactSpace_of_surjective (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- Quasi-compactness of a morphism to an affine scheme descends along the base change by a
faithfully flat algebra. -/
@[ega "IV 2.7.3" "(i), special case"]
public theorem quasiCompact_of_faithfullyFlat_baseChange
    (h : QuasiCompact (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    QuasiCompact f :=
  have : CompactSpace X := compactSpace_of_faithfullyFlat_baseChange f h
  (quasiCompact_iff_compactSpace f).mpr this

end FaithfullyFlat

section FieldExtension

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- Being locally of finite type descends from a field extension. This is the first assertion of
the proof of [Stacks, Tag 0BDE]. -/
public theorem locallyOfFiniteType_of_fieldExtension
    (h : LocallyOfFiniteType (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    LocallyOfFiniteType f :=
  locallyOfFiniteType_of_faithfullyFlat_baseChange f h

/-- A scheme over a field has quasi-compact underlying space as soon as its base change to some
extension field is quasi-compact over that field. -/
public theorem compactSpace_of_fieldExtension
    (h : QuasiCompact (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    CompactSpace X :=
  compactSpace_of_faithfullyFlat_baseChange f h

/-- Quasi-compactness descends from a field extension. This is the second assertion of the proof
of [Stacks, Tag 0BDE]. -/
public theorem quasiCompact_of_fieldExtension
    (h : QuasiCompact (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    QuasiCompact f :=
  quasiCompact_of_faithfullyFlat_baseChange f h

/-- Being of finite type — locally of finite type and quasi-compact — descends from a field
extension. This is the finite-type half of [Stacks, Tag 0BDE]; the other half is the descent of
a relatively ample invertible sheaf. -/
public theorem locallyOfFiniteType_and_quasiCompact_of_fieldExtension
    (h : LocallyOfFiniteType (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      QuasiCompact (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    LocallyOfFiniteType f ∧ QuasiCompact f :=
  ⟨locallyOfFiniteType_of_fieldExtension k K f h.1, quasiCompact_of_fieldExtension k K f h.2⟩

end FieldExtension

end AlgebraicGeometry

end
