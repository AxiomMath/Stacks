module

public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.RingHomPi
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.Defs

import StacksCore.Tactic.StacksAttribute

/-!
# Constructible subsets as images of finitely presented affine schemes

A constructible subset of `Spec R` is a finite union of locally closed pieces
`D(f) ∩ V(g₁, …, gₙ)`.  Each piece is the image of the spectrum of the localization of
`R/(g₁, …, gₙ)` at `f`; taking the finite product of these rings realizes the union.
Both quotienting by the finitely generated ideal `(g₁, …, gₙ)` and localizing at one
element are of finite presentation, as is their finite product.
-/

@[expose] public section

open Topology
open scoped Pointwise

namespace PrimeSpectrum

universe u

/-- **Stacks 00F8.** Every constructible subset of `Spec R` is the image of `Spec S` for a
finitely presented `R`-algebra `S`. -/
@[stacks 00F8]
theorem exists_range_eq_of_isConstructible_finitePresentation {R : Type u} [CommRing R]
    {s : Set (PrimeSpectrum R)} (hs : IsConstructible s) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S),
      f.FinitePresentation ∧ Set.range (comap f) = s := by
  obtain ⟨s, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  let A (i : s) := R ⧸ Ideal.span (Set.range i.1.g)
  let a (i : s) : A i := Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)) i.1.f
  let B (i : s) := Localization.Away (a i)
  let f (i : s) : R →+* B i :=
    (algebraMap (A i) (B i)).comp (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g)))
  have hf (i : s) : (f i).FinitePresentation := by
    let : Algebra R (A i) := (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g))).toAlgebra
    have hI : (Ideal.span (Set.range i.1.g)).FG :=
      Submodule.fg_span (Set.finite_range i.1.g)
    let : Algebra.FinitePresentation R (A i) :=
      Algebra.FinitePresentation.quotient hI
    have hq : (Ideal.Quotient.mk (Ideal.span (Set.range i.1.g))).FinitePresentation := by
      show (algebraMap R (A i)).FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance
    have hl : (algebraMap (A i) (B i)).FinitePresentation := by
      rw [RingHom.finitePresentation_algebraMap]
      exact IsLocalization.Away.finitePresentation (a i)
    exact RingHom.finitePresentation_stableUnderComposition _ _ hq hl
  refine ⟨∀ i : s, B i, inferInstance, RingHom.pi f,
    RingHom.FinitePresentation.pi f hf, ?_⟩
  rw [← iUnion_range_comap_comp_evalRingHom, ConstructibleSetData.toSet]
  simp_rw [← Finset.mem_coe, Set.biUnion_eq_iUnion]
  congr! with _ _ C
  let I := Ideal.span (Set.range C.1.g)
  let x := Ideal.Quotient.mk I C.1.f
  trans comap (Ideal.Quotient.mk I) '' (Set.range (comap (algebraMap _ (Localization.Away x))))
  · rw [← Set.range_comp]
    rfl
  · rw [localization_away_comap_range _ x, ← comap_basicOpen,
      TopologicalSpace.Opens.coe_comap, ContinuousMap.coe_mk,
      Set.image_preimage_eq_inter_range,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      BasicConstructibleSetData.toSet, Set.sdiff_eq_compl_inter,
      basicOpen_eq_zeroLocus_compl, Ideal.mk_ker, zeroLocus_span]

end PrimeSpectrum

end
