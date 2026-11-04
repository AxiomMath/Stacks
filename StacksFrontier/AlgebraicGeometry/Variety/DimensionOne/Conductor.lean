module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Ideals with complementary zero loci

Let `A` be a reduced ring and let `I` and `J` be ideals whose zero loci cover `Spec A`. Then
`I ⊓ J = 0`, because the zero locus of the intersection is everything and the ring is reduced.
Consequently passage to `A ⧸ J` identifies `I` with its extension, and more generally
multiplication by `I` is unchanged after quotienting a flat module by its `J`-multiple.

## Main definitions

* `Ideal.multipleQuotientMap` is the canonical map from `I • P` to `I • (P ⧸ J • P)`.

## Main results

* `Ideal.inf_eq_bot_of_zeroLocus_union_eq_univ` identifies the intersection `I ⊓ J` with zero.
* `Ideal.idealMap_quotient_bijective` says that the canonical map `I → I (A ⧸ J)` is an
  isomorphism.
* `Ideal.multipleQuotientMap_bijective` says that `I • P → I • (P ⧸ J • P)` is an isomorphism
  for a flat module `P`, hence for a projective module.

## References

* [Stacks Project, Tag 09NW](https://stacks.math.columbia.edu/tag/09NW)
-/

@[expose] public section

namespace Ideal

universe u v

/-- The canonical map from `I • P` to `I • (P ⧸ J • P)`. -/
public noncomputable def multipleQuotientMap
    {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]
    (I J : Ideal A) :
    ↥(I • (⊤ : Submodule A P)) →ₗ[A]
      ↥(I • (⊤ : Submodule A (P ⧸ (J • (⊤ : Submodule A P))))) :=
  LinearMap.restrict (p := I • (⊤ : Submodule A P))
    (q := (I • (⊤ : Submodule A (P ⧸ (J • (⊤ : Submodule A P))))))
    (Submodule.mkQ (J • (⊤ : Submodule A P))) fun _ hx ↦ by
      rw [← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
        ← Submodule.map_top, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem hx

/-- In a reduced ring, ideals whose zero loci cover the spectrum have zero
intersection. -/
@[stacks 09NW]
public theorem inf_eq_bot_of_zeroLocus_union_eq_univ
    {A : Type u} [CommRing A] [IsReduced A] (I J : Ideal A)
    (h : PrimeSpectrum.zeroLocus (I : Set A) ∪
      PrimeSpectrum.zeroLocus (J : Set A) = Set.univ) :
    I ⊓ J = ⊥ :=
  eq_bot_iff.2 fun x hx => (Ideal.mem_bot).2 (IsReduced.eq_zero x
    ((PrimeSpectrum.zeroLocus_eq_univ_iff (I ⊓ J : Ideal A)).mp
      (by simpa only [PrimeSpectrum.zeroLocus_inf] using h) hx))

/-- If `V(I) ∪ V(J) = Spec A` in a reduced ring, the canonical map from `I`
to its extension in `A ⧸ J` is an isomorphism of `A`-modules. -/
@[stacks 09NW]
public theorem idealMap_quotient_bijective
    {A : Type u} [CommRing A] [IsReduced A] (I J : Ideal A)
    (h : PrimeSpectrum.zeroLocus (I : Set A) ∪
      PrimeSpectrum.zeroLocus (J : Set A) = Set.univ) :
    Function.Bijective (Algebra.idealMap (A ⧸ J) I) := by
  refine ⟨fun x y hxy => Subtype.ext ?_, fun y => ?_⟩
  · have hd : Disjoint I (LinearMap.ker (Algebra.linearMap A (A ⧸ J))) := by
      rw [disjoint_iff, ← inf_eq_bot_of_zeroLocus_union_eq_univ I J h]
      congr 1
      ext
      exact Ideal.Quotient.eq_zero_iff_mem
    exact LinearMap.disjoint_ker_iff_injOn.mp hd x.2 y.2 (congr_arg Subtype.val hxy)
  · obtain ⟨x, hx, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- If `V(I) ∪ V(J) = Spec A`, the quotient map induces an isomorphism
`I • P ≅ I • (P ⧸ J • P)` for every flat `A`-module `P`. In particular this applies when
`P` is projective. -/
@[stacks 09NW]
public theorem multipleQuotientMap_bijective
    {A : Type u} [CommRing A] [IsReduced A] (I J : Ideal A)
    {P : Type v} [AddCommGroup P] [Module A P] [Module.Flat A P]
    (h : PrimeSpectrum.zeroLocus (I : Set A) ∪
      PrimeSpectrum.zeroLocus (J : Set A) = Set.univ) :
    Function.Bijective (multipleQuotientMap (P := P) I J) := by
  refine ⟨fun x y hxy => Subtype.ext ?_, fun y => ?_⟩
  · have hd : Disjoint (I • (⊤ : Submodule A P))
        (LinearMap.ker (Submodule.mkQ (J • (⊤ : Submodule A P)))) := by
      rw [Submodule.ker_mkQ, disjoint_iff, ideal_smul_top_inf,
        inf_eq_bot_of_zeroLocus_union_eq_univ I J h, Submodule.bot_smul]
    exact LinearMap.disjoint_ker_iff_injOn.mp hd x.2 y.2 (congr_arg Subtype.val hxy)
  · obtain ⟨x, hx, hxy⟩ : (y : P ⧸ (J • (⊤ : Submodule A P))) ∈
        Submodule.map (Submodule.mkQ (J • (⊤ : Submodule A P))) (I • (⊤ : Submodule A P)) := by
      simpa only [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)] using y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

end Ideal
