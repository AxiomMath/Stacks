module

public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Depth.SemilinearEquivCohenMacaulay

/-!
# The single nonvanishing cohomology module of a dualizing complex is maximal Cohen--Macaulay

Let `A` be a Noetherian local ring and `K` a dualizing complex over `A` all of whose cohomology
modules vanish outside one degree `n`. Then `H^n(K)` is a maximal Cohen--Macaulay `A`-module.

This is the last clause of [Stacks, Tag 0AWS] with the normalization hypothesis removed.
`Dualizing.dualizingModule_isMaximalCohenMacaulay` concludes maximal Cohen--Macaulayness of
`Dualizing.dualizingModule K = H^{-\dim A}(K)` for a *normalized* `K`, and a consumer that
arrives with a complex concentrated in some other degree — the globally constant degree of
[Stacks, Tag 0AWT], say — cannot use it on the nose. The two are reconciled here: exactly one
shift of `K` is normalized (`Dualizing.exists_isNormalizedDualizingComplex_shift`), that shift
moves the single nonvanishing degree without creating a second one, and a dualizing complex over
a Noetherian local ring is nonzero, so the single degree of the normalized shift *is*
`-\dim A`. The shift between `n` and `-\dim A` is therefore determined, and the dualizing module
of the normalized shift is `H^n(K)` itself.

## Main results

* `Dualizing.exists_not_isZero_homology` — a dualizing complex over a Noetherian local ring has a
  nonvanishing cohomology module. Its normalized shift has one in degree `-depth(A)` by
  [Stacks, Tag 0AWR].
* `Dualizing.isMaximalCohenMacaulay_homology_of_concentrated` — the clause itself.

## Implementation notes

Both results are stated for an arbitrary dualizing complex at the standard model of the derived
category, which is the model `Dualizing.IsNormalizedDualizingComplex` is pinned at; see the
implementation notes of `StacksFrontier/RingTheory/Dualizing/NormalizedShift.lean` for why that pin
is forced and why it is harmless over `ModuleCat A`.

`Dualizing.homologyShiftObjIsoOfEq` is the degree bookkeeping `H^i(K⟦m⟧) ≅ H^{m+i}(K)`, the shift
sequence of `DerivedCategory.homologyFunctor`. The same definition is `private` in
`StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayLocus.lean`, whose copy predates this file;
it is public here because both statements above are about a shift.

## References

* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0AWR](https://stacks.math.columbia.edu/tag/0AWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-- **Shifting a complex shifts its cohomology**: `H^i(K⟦m⟧) ≅ H^{m+i}(K)`. This is the shift
sequence of `DerivedCategory.homologyFunctor`, whose degree-`i` member is the `i`-th shift of the
degree-zero one. -/
def homologyShiftObjIsoOfEq {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m i j : ℤ) (h : m + i = j) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦m⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso m i j h).app K

/-- If `H^j(K)` vanishes then so does `H^i(K⟦m⟧)`, where `m + i = j`. -/
private theorem isZero_homology_shift_of_isZero {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m i j : ℤ) (h : m + i = j)
    (hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦m⟧)) :=
  hz.of_iso (homologyShiftObjIsoOfEq K m i j h)

/-- **A dualizing complex over a Noetherian local ring is nonzero.** Its normalized shift has a
nonvanishing cohomology module in degree `-depth(A)` by [Stacks, Tag 0AWR]. -/
theorem exists_not_isZero_homology {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K) :
    ∃ i : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0} K hK
  obtain ⟨δ, hleast, -⟩ := depth_eq_least_nonzero_homology (K⟦-m⟧) hm
  exact ⟨-m + -(δ : ℤ), fun hz =>
    hleast.1 (isZero_homology_shift_of_isZero K (-m) _ _ rfl hz)⟩

/-- **Stacks Project, Tag 0AWS, the final assertion, with the normalization hypothesis removed.**
If a dualizing complex over a Noetherian local ring has all its cohomology concentrated in one
degree `n`, then that cohomology module is maximal Cohen--Macaulay.

The degree `n` is not assumed to be `-\dim A`: it is *forced* to be, because the normalizing
shift moves the single nonvanishing degree to `-\dim A` and a dualizing complex is nonzero, so
the shift is zero. -/
theorem isMaximalCohenMacaulay_homology_of_concentrated {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDualizingComplex K) (n : ℤ)
    (hn : ∀ i : ℤ, i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    Module.IsMaximalCohenMacaulay A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K) := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0} K hK
  -- The normalized shift is concentrated in degree `n + m`.
  have hshift : ∀ i : ℤ, i ≠ n + m →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦-m⟧)) := by
    intro i hi
    exact isZero_homology_shift_of_isZero K (-m) i _ rfl (hn _ (by omega))
  -- Hence `A` is Cohen–Macaulay.
  have hconc : IsCohomologicallyConcentratedInOneDegree (K⟦-m⟧) := ⟨n + m, hshift⟩
  have hA : IsCohenMacaulayLocalRing A :=
    ((isCohenMacaulay_tfae_dualizingComplex (K⟦-m⟧) hm).out 2 1).mp hconc
  -- And the normalized shift is the dualizing module in degree `-dim A`.
  obtain ⟨e⟩ := ((isCohenMacaulay_tfae_dualizingComplex (K⟦-m⟧) hm).out 1 3).mp hA
  have hdim : ∀ i : ℤ, i ≠ -(localRingDimension A : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (K⟦-m⟧)) := by
    intro i hi
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e)
    exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ)
        (-(localRingDimension A : ℤ)) (dualizingModule (K⟦-m⟧)) i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app
        ((CochainComplex.singleFunctor (ModuleCat.{u} A)
          (-(localRingDimension A : ℤ))).obj (dualizingModule (K⟦-m⟧))))
  -- The two single degrees agree, the complex being nonzero.
  obtain ⟨j, hj⟩ := exists_not_isZero_homology (K⟦-m⟧) hm.1
  have hj₁ : j = n + m := by by_contra hc; exact hj (hshift j hc)
  have hj₂ : j = -(localRingDimension A : ℤ) := by by_contra hc; exact hj (hdim j hc)
  have hmcm := dualizingModule_isMaximalCohenMacaulay (K⟦-m⟧) hm hA
  -- Transport along `H^{-dim A}(K⟦-m⟧) ≅ H^n(K)`.
  have eiso : dualizingModule (K⟦-m⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K := by
    refine Iso.trans ?_ (homologyShiftObjIsoOfEq K (-m) (n + m) n (by omega))
    exact eqToIso (by rw [dualizingModule, ← hj₂, hj₁])
  exact Module.isMaximalCohenMacaulay_of_semilinearEquiv (RingEquiv.refl A)
    eiso.toLinearEquiv.toAddEquiv (fun a x => eiso.toLinearEquiv.map_smul a x) hmcm

end Dualizing

end
