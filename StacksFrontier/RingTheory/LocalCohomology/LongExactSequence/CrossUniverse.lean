module

public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Functoriality

/-!
# Comparing Čech cohomology across universes

Let `A` be a commutative ring in `Type u` and `f₁, …, f_r ∈ A`. The Čech complex
`C^•(f₁, …, f_r; M)` of an `A`-module `M` in `Type w` is a complex of modules in `Type (max u w)`,
so the Čech complexes of `M` and of `ULift.{v} M` live in different categories and no isomorphism
between them can be written down. Their *cohomology* is nonetheless the same, and that is what this
file proves.

The reason the comparison is possible at all is that `LinearEquiv` is universe-heterogeneous: there
is an honest `A`-linear equivalence `ULift.{v} M ≃ₗ[A] M`, and
`Stacks.LocalCohomology.cechTermLinearMap` — the functoriality of a Čech term in its coefficient
module — is likewise stated for modules in arbitrary universes, because `DirectSum.lmap` and
`IsLocalizedModule.map` both are. So a linear equivalence of modules induces a degreewise linear
equivalence of the two Čech complexes, compatible with the differentials, and exactness in a degree
transfers by chasing elements.

This is the comparison that the equivalence (1) ⇔ (2) of [Stacks, Tag 0DX7] needs: condition (1)
is about local cohomology of `A` as an object of `ModuleCat.{u} A`, condition (2) quantifies over
`ModuleCat.{max u v} A`, and the free module appearing in its proof is a direct sum of copies of
`ULift.{v} A`.

## Main definitions

* `Stacks.LocalCohomology.LongExactSequence.cechTermLinearEquiv` — the equivalence of Čech terms
  induced by a linear equivalence of coefficient modules, possibly across universes.

## Main results

* `Stacks.LocalCohomology.LongExactSequence.moduleCat_exactAt_iff` — exactness of a complex of
  modules in a degree, in elements.
* `Stacks.LocalCohomology.LongExactSequence.exactAt_of_degreewise_linearEquiv` — exactness in a
  degree transfers along degreewise linear equivalences, between complexes of modules in two
  different universes.
* `Stacks.LocalCohomology.isZero_homology_cechComplex_iff_of_linearEquiv` — **Čech cohomology only
  depends on the coefficient module up to linear equivalence**, across universes.
* `Stacks.LocalCohomology.isZero_homology_cechComplex_uliftModule_iff` — the `ULift` case.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₂ w₁ w v u

namespace Stacks.LocalCohomology

/-! ### Exactness of a complex of modules, in elements -/

namespace LongExactSequence

variable {R : Type u} [CommRing R]

/-- Exactness of a complex of modules in a degree, spelled out in elements: every element of the
kernel of the outgoing differential is in the image of the incoming one. -/
theorem moduleCat_exactAt_iff {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{w} R) c) (n : ι) :
    K.ExactAt n ↔ ∀ x : K.X n, ((K.d n (c.next n)).hom) x = 0 →
      ∃ y : K.X (c.prev n), ((K.d (c.prev n) n).hom) y = x := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
  exact ⟨fun h u hu => h u hu, fun h u hu => h u hu⟩

/-- **Exactness transfers along degreewise linear equivalences.** The two complexes may be
complexes of modules in two different universes: what is required of them is only that they have
the same shape and that the equivalences commute with the differentials. -/
theorem exactAt_of_degreewise_linearEquiv {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{w₁} R) c) (L : HomologicalComplex (ModuleCat.{w₂} R) c)
    (e : ∀ n, (K.X n) ≃ₗ[R] (L.X n))
    (he : ∀ (i j : ι) (x : K.X i), e j ((K.d i j).hom x) = (L.d i j).hom (e i x))
    (n : ι) (h : K.ExactAt n) : L.ExactAt n := by
  rw [moduleCat_exactAt_iff] at h ⊢
  intro x hx
  have key : ((K.d n (c.next n)).hom) ((e n).symm x) = 0 := by
    apply (e (c.next n)).injective
    rw [he, LinearEquiv.apply_symm_apply, hx, map_zero]
  obtain ⟨y, hy⟩ := h ((e n).symm x) key
  exact ⟨e _ y, by rw [← he, hy, LinearEquiv.apply_symm_apply]⟩

/-! ### The Čech terms of equivalent modules -/

variable {r : ℕ} (f : Fin r → R)

/-- The equivalence of degree-`p` Čech terms induced by a linear equivalence of coefficient
modules. The two modules may live in different universes. -/
def cechTermLinearEquiv {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (e : N ≃ₗ[R] P) (p : ℕ) : Cech.cechTerm f N p ≃ₗ[R] Cech.cechTerm f P p :=
  LinearEquiv.ofLinearMap (cechTermLinearMap f e.toLinearMap p)
    (cechTermLinearMap f e.symm.toLinearMap p)
    (by
      rw [← cechTermLinearMap_comp,
        show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from by ext x; simp,
        cechTermLinearMap_id])
    (by
      rw [← cechTermLinearMap_comp,
        show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from by ext x; simp,
        cechTermLinearMap_id])

/-- The equivalence `cechTermLinearEquiv f e p` acts on a Čech term as the linear map
`cechTermLinearMap f e.toLinearMap p` induced by `e`. -/
@[simp] theorem cechTermLinearEquiv_apply {N P : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (e : N ≃ₗ[R] P) (p : ℕ) (x : Cech.cechTerm f N p) :
    cechTermLinearEquiv f e p x = cechTermLinearMap f e.toLinearMap p x :=
  rfl

end LongExactSequence

/-! ### Čech cohomology across universes -/

section CrossUniverse

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  {N : Type w₁} [AddCommGroup N] [Module R N] {P : Type w₂} [AddCommGroup P] [Module R P]

/-- Exactness of the Čech complex in a degree depends on the coefficient module only up to linear
equivalence, which may be across universes. -/
theorem exactAt_cechComplex_of_linearEquiv (e : N ≃ₗ[R] P) (n : ℕ)
    (h : (Cech.cechComplex f N).ExactAt n) : (Cech.cechComplex f P).ExactAt n :=
  LongExactSequence.exactAt_of_degreewise_linearEquiv _ _
    (fun p => LongExactSequence.cechTermLinearEquiv f e p)
    (fun i j x => LongExactSequence.cechTermLinearMap_cechComplex_d f e.toLinearMap i j x) n h

/-- **Čech cohomology across universes.** The Čech complexes of two linearly equivalent modules,
which may live in two different universes and hence give complexes in two different categories,
vanish in the same degrees. -/
theorem isZero_homology_cechComplex_iff_of_linearEquiv (e : N ≃ₗ[R] P) (n : ℕ) :
    IsZero ((Cech.cechComplex f N).homology n) ↔
      IsZero ((Cech.cechComplex f P).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨exactAt_cechComplex_of_linearEquiv f e n,
    exactAt_cechComplex_of_linearEquiv f e.symm n⟩

/-- **Čech cohomology is insensitive to a universe lift of the coefficient module.** -/
theorem isZero_homology_cechComplex_uliftModule_iff (n : ℕ) :
    IsZero ((Cech.cechComplex f N).homology n) ↔
      IsZero ((Cech.cechComplex f (ULift.{v} N)).homology n) :=
  isZero_homology_cechComplex_iff_of_linearEquiv f
    (ULift.moduleEquiv : ULift.{v} N ≃ₗ[R] N).symm n

end CrossUniverse

end Stacks.LocalCohomology

end
