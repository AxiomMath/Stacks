module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.RingTheory.Depth.SemilinearEquiv
public import StacksFrontier.RingTheory.Dualizing.CanonicalModule
public import StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# A dualizing module of a two-dimensional local domain has depth two

Let `A` be a Noetherian local domain of dimension two and `ω_A` a dualizing module
([Stacks, Tag 0B4R]): `ω_A[n]` is a dualizing complex for some `n`. Then `depth(ω_A) ≥ 2`. Some
shift of `ω_A[n]` is a normalized dualizing complex ([Stacks, Tag 0A7M]); it is a single module
in one degree, and its cohomology in degree `-2` has support the whole spectrum
([Stacks, Tag 0AWE], part (1)), so that degree is `-2` and the module is `ω_A`; part (2) of
[Stacks, Tag 0AWE] gives the depth. This is the depth input of the proof of [Stacks, Tag 0EA2].

## Main results

* `AlgebraicGeometry.DualizingDivisor.two_le_depth_of_isDualizingRingModule`.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.DualizingDivisor

/-- **A dualizing module of a two-dimensional Noetherian local domain has depth at least two**
([Stacks, Tag 0AWE] for the normalized shift of `ω_A[n]`). -/
theorem two_le_depth_of_isDualizingRingModule {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain A] (hdim : ringKrullDim A = 2) (M : Type u) [AddCommGroup M]
    [Module A M] (h : Stacks.Duality.IsDualizingRingModule A M) :
    (2 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) M := by
  obtain ⟨-, n, hK⟩ := h
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A M)
  obtain ⟨m, hm⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} K hK
  have hd : ringKrullDim A = ((2 : ℕ) : WithBot ℕ∞) := by simpa using hdim
  -- the support of `H^{-2}` of the normalized complex is everything
  have hmem : (⊥ : PrimeSpectrum A) ∈ Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-((2 : ℕ) : ℤ))).obj (K⟦-m⟧)) := by
    rw [Dualizing.support_canonicalModule (K⟦-m⟧) hm 2 hd]
    have hirr : Set.univ ∈ irreducibleComponents (PrimeSpectrum A) := by
      rw [irreducibleComponents_eq_singleton]
      rfl
    refine ⟨Set.univ, ⟨hirr, ?_⟩, Set.mem_univ _⟩
    rw [← (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hd]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.Set.univ (PrimeSpectrum A)).isHomeomorph
  have hnm : n + m = -2 := by
    by_contra hne
    have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-((2 : ℕ) : ℤ))).obj
        (K⟦-m⟧)) :=
      ((HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) (n + m)
        (ModuleCat.of A M) (-((2 : ℕ) : ℤ)) (by omega)).of_iso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) _).app _)).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) _).mapIso
          (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-m) (n + m) n
            (by omega)).app (ModuleCat.of A M)))
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    rw [Module.support_eq_empty] at hmem
    exact hmem
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-((2 : ℕ) : ℤ))).obj (K⟦-m⟧) ≅
      ModuleCat.of A M :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) _).mapIso
      (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-m) (-2) n
        (by omega)).app (ModuleCat.of A M)) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) (-2)).app _
  have hdepth := Dualizing.min_two_le_depth_canonicalModule 2 (K⟦-m⟧) hm hd
  rw [Module.depth_eq_of_semilinearEquiv (RingEquiv.refl A) _ e.toLinearEquiv.toAddEquiv
    (fun a x => e.toLinearEquiv.map_smul a x)] at hdepth
  simpa using hdepth

end AlgebraicGeometry.DualizingDivisor

end
