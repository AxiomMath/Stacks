module

public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayRings
public import StacksFrontier.RingTheory.Dualizing.NormalizedResidueFieldExt
import StacksCore.Tactic.StacksAttribute

/-!
# The normalizing shift of a dualizing module over a Cohen–Macaulay local ring

Let `(A, 𝔪, κ)` be a Noetherian local ring and `ω_A` a *dualizing module* for `A`: a finite
module which, placed in **some** cohomological degree, is a dualizing complex. The degree is not
part of the data — `Stacks.Duality.IsDualizingRingModule` of
`…/AlgebraicGeometry/Duality/DualizingModule.lean` quantifies it existentially, and every
consumer in the resolution-of-surfaces development takes the predicate in that form — so nothing
downstream knows which shift of `ω_A` is the *normalized* dualizing complex of
[Stacks, Section 47.16], and the normalization is what identifies `RHom_A(κ, ω_A^•)` with `κ`.

**Over a Cohen–Macaulay local ring the degree is pinned by the dimension**: the normalized
dualizing complex is `ω_A` placed in degree `-dim(A)`, and no hypothesis on the shift need be
carried. This is clause (3) of [Stacks, Tag 0AWS]
(`Dualizing.isCohenMacaulay_tfae_dualizingComplex`) combined with the uniqueness of the
normalizing shift.

## Main results

* `Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension`: for `A`
  Cohen–Macaulay, a module which is dualizing in *some* degree is the normalized dualizing
  complex in degree `-dim(A)`.
* `Dualizing.subsingleton_ext_residueField_single_of_ne_localRingDimension`: hence
  `Ext^i_A(κ, ω_A) = 0` for every `i ≠ dim(A)`, with the degree of the dualizing module left
  existentially quantified as its predicate leaves it.

## The proof

Some shift `K⟦-m⟧` of `K = ω_A[n]` is normalized, by
`Dualizing.exists_isNormalizedDualizingComplex_shift`, and only one is, by
`Dualizing.isNormalizedDualizingComplex_shift_iff_eq`. Shifting a module in degree `n` by `-m`
is the module in degree `n + m`, so `ω_A[n + m]` is the normalized complex. Clause (3) of
[Stacks, Tag 0AWS] identifies a normalized dualizing complex over a Cohen–Macaulay local ring
with a module in degree `-dim(A)`; a module placed in degree `n + m` has no cohomology in degree
`-dim(A)` unless `n + m = -dim(A)`, so if the two degrees differed then `ω_A` would be the zero
module. That case is not excluded — it is *absorbed*: for a zero `ω_A` the two complexes
`ω_A[n + m]` and `ω_A[-dim(A)]` are both zero objects, hence isomorphic, and being normalized
transports along an isomorphism (`Dualizing.isNormalizedDualizingComplex_congr`). So no
nonvanishing statement about a dualizing complex is needed anywhere.

## Implementation notes

`Dualizing.isCohenMacaulay_tfae_dualizingComplex` is stated at `ModuleCat.{u} A` and
`Dualizing.IsNormalizedDualizingComplex.{u, 0}`, so these results are too; that is the universe
`Stacks.Duality.IsDualizingRingModule` takes at a module in `Type u`.

A consumer holding `Stacks.Duality.IsDualizingRingModule A ω_A` supplies the degree `n` by
destructuring the existential half of that predicate: `obtain ⟨n, hn⟩ := hωA.2`. No statement of
this file mentions the predicate, so that `AlgebraicGeometry.Duality` import is not incurred
here.

## References

* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- Shifting a module in degree `n` by `-m` gives the module in degree `n + m`, which preserves
being a normalized dualizing complex. -/
private theorem isNormalizedDualizingComplex_shift_single_iff (ω : ModuleCat.{u} A) (n m : ℤ) :
    IsNormalizedDualizingComplex.{u, 0}
        (((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj ω)⟦-m⟧) ↔
      IsNormalizedDualizingComplex.{u, 0}
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (n + m)).obj ω) :=
  isNormalizedDualizingComplex_congr
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-m) (n + m) n
      (by omega)).app ω)

/-- **Over a Cohen–Macaulay local ring the normalizing shift of a dualizing module is minus the
dimension.** If `ω_A` placed in *some* degree `n` is a dualizing complex, then `ω_A` placed in
degree `-dim(A)` is the *normalized* dualizing complex of [Stacks, Section 47.16].

This is what a consumer of `Stacks.Duality.IsDualizingRingModule` needs and the predicate does
not give: that predicate asserts only `∃ n`, so on its own it does not say which shift satisfies
`RHom_A(κ, ω_A^•) = κ`. Clause (3) of [Stacks, Tag 0AWS] supplies the missing degree from the
dimension, and the normalizing shift being unique there is nothing left to choose. -/
theorem isNormalizedDualizingComplex_single_neg_localRingDimension
    (hA : IsCohenMacaulayLocalRing A) (ω : ModuleCat.{u} A) (n : ℤ)
    (hn : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj ω)) :
    IsNormalizedDualizingComplex.{u, 0}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A)
        (-(localRingDimension A : ℤ))).obj ω) := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, 0} _ hn
  have hnm : IsNormalizedDualizingComplex.{u, 0}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (n + m)).obj ω) :=
    (isNormalizedDualizingComplex_shift_single_iff ω n m).mp hm
  by_cases hω : IsZero ω
  · exact (isNormalizedDualizingComplex_congr
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) _).map_isZero hω).iso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) _).map_isZero hω))).mp hnm
  · have heq : n + m = -(localRingDimension A : ℤ) := by
      by_contra hne
      have hiso : Nonempty ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (n + m)).obj ω ≅
          (DerivedCategory.singleFunctor (ModuleCat.{u} A)
            (-(localRingDimension A : ℤ))).obj
            (dualizingModule ((DerivedCategory.singleFunctor (ModuleCat.{u} A)
              (n + m)).obj ω))) :=
        ((isCohenMacaulay_tfae_dualizingComplex _ hnm).out 1 3).mp hA
      obtain ⟨e⟩ := hiso
      refine hω (IsZero.of_iso ?_
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A)
          (n + m)).app ω).symm)
      refine IsZero.of_iso ?_
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n + m)).mapIso e)
      exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ)
          (-(localRingDimension A : ℤ)) _ (n + m) hne).of_iso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (n + m)).app
          ((CochainComplex.singleFunctor (ModuleCat.{u} A)
            (-(localRingDimension A : ℤ))).obj _))
    rw [heq] at hnm
    exact hnm

/-- **`Ext^i_A(κ, ω_A) = 0` for every `i ≠ dim(A)`**, for `ω_A` a dualizing module over a
Cohen–Macaulay Noetherian local ring, with the degree in which `ω_A` is a dualizing complex left
as the existential the predicate `Stacks.Duality.IsDualizingRingModule` gives it.

This is the cohomological reading of the normalization convention
(`Dualizing.subsingleton_ext_residueField_of_normalizingShift`) at the shift
`Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension` pins: the normalized
complex is `ω_A[-dim(A)]`, so the one degree in which `Ext_A(κ, ω_A[0])` survives is `dim(A)`. -/
theorem subsingleton_ext_residueField_single_of_ne_localRingDimension
    (hA : IsCohenMacaulayLocalRing A) (ω : ModuleCat.{u} A) (n : ℤ)
    (hn : IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj ω))
    {i : ℤ} (hi : i ≠ (localRingDimension A : ℤ)) :
    Subsingleton (DerivedCategory.Ext (residueFieldSingle.{u, 0} A)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj ω) i) := by
  refine subsingleton_ext_residueField_of_normalizingShift
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj ω)
    (-(localRingDimension A : ℤ)) ?_ (by omega)
  refine (isNormalizedDualizingComplex_shift_single_iff ω 0 (-(localRingDimension A : ℤ))).mpr ?_
  have h := isNormalizedDualizingComplex_single_neg_localRingDimension hA ω n hn
  rwa [show (0 : ℤ) + -(localRingDimension A : ℤ) = -(localRingDimension A : ℤ) by ring]

end Dualizing

end
