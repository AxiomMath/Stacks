module

public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.RegularLocalNormalizedShift
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldShift

/-!
# Normalized dualizing complexes over a field

Over a field `k` the normalized dualizing complex is `k` itself, placed in degree zero: `k[0]`
is a normalized dualizing complex, and every normalized dualizing complex over `k` is
isomorphic to it.

A field is a regular local ring of Krull dimension zero, so
`Dualizing.exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift` — which
says that over a regular local ring the normalizing shift of the regular module is the Krull
dimension — gives the first statement with no shift to undo. For the second, a normalized
dualizing complex `L` is in particular dualizing, hence a simple object of `D(k)`
(`Dualizing.simple_of_isDualizingComplex_field`) with bounded cohomology, hence a shift of
`k[0]` (`Dualizing.simple_bounded_iso_shift_field`); and the normalizing shift is unique
(`Dualizing.isNormalizedDualizingComplex_shift_iff_eq`), so that shift is zero.

## Main definitions

* `Dualizing.singleSelfLifted` — the ring itself in degree zero, universe-lifted in the shape
  `Dualizing.IsNormalizedDualizingComplex` compares its argument against.

## Main results

* `Dualizing.isNormalizedDualizingComplex_singleSelfLifted_of_field` — over a field, `k[0]` is a
  normalized dualizing complex.
* `Dualizing.nonempty_iso_singleSelfLifted_of_isNormalizedDualizingComplex_field` — over a
  field, every normalized dualizing complex is isomorphic to `k[0]`.

## Implementation notes

The module universe is pinned to `0`, i.e. the module category is `ModuleCat.{u}` for `k` in
`Type u` and the universe lift is the trivial one. That is the reading in which
`Dualizing.exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift` is stated,
and the one in which `Dualizing.simple_bounded_iso_shift_field` produces exactly
`Dualizing.singleSelfLifted`.

The regular module `k` and its universe lift `ULift k` are different modules, so the result
quoted from the regular-local case needs one transport along
`ModuleCat.uliftFunctorIsoSelf`-style comparison; it is supplied here by `ULift.moduleEquiv`.

## References

* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The ring itself placed in degree zero, universe-lifted: the object against which
`Dualizing.IsNormalizedDualizingComplex` compares derived Hom from the residue field, read at
the ring in place of its residue field. -/
public abbrev singleSelfLifted (k : Type u) [CommRing k] :
    DerivedCategory (ModuleCat.{u} k) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
    ((ModuleCat.uliftFunctor.{0} k).obj (ModuleCat.of k k))

/-- **Over a field, the field in degree zero is a normalized dualizing complex.** A field is a
regular local ring of Krull dimension zero, and over a regular local ring the normalizing shift
of the regular module is the Krull dimension. -/
public theorem isNormalizedDualizingComplex_singleSelfLifted_of_field (k : Type u) [Field k] :
    IsNormalizedDualizingComplex.{u, 0} (singleSelfLifted k) := by
  obtain ⟨d, hd, hnorm⟩ :=
    exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift k
  have hd0 : d = 0 := by
    have hz : ((d : ℕ∞) : WithBot ℕ∞) = 0 := by
      rw [← hd, ringKrullDim_eq_zero_of_field k]
    simpa using hz
  subst hd0
  refine (isNormalizedDualizingComplex_congr.{u, 0} ?_).1 hnorm
  refine ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).app
    ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))) ≪≫ ?_
  exact (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).mapIso
    (ULift.moduleEquiv.{u, u, 0} (R := k) (M := k)).toModuleIso.symm

/-- **Over a field, a normalized dualizing complex is the field in degree zero.** A dualizing
complex over a field is a simple object with bounded cohomology, hence a shift of `k[0]`; the
normalizing shift being unique, that shift is zero. -/
public theorem nonempty_iso_singleSelfLifted_of_isNormalizedDualizingComplex_field
    {k : Type u} [Field k] (L : DerivedCategory (ModuleCat.{u} k))
    (hL : IsNormalizedDualizingComplex.{u, 0} L) :
    Nonempty (L ≅ singleSelfLifted k) := by
  have hdual : IsDualizingComplex L := hL.1
  have : Simple L := simple_of_isDualizingComplex_field.{u, 0} L hdual
  obtain ⟨a, b, I, hge, hle, _, ⟨eI⟩⟩ := hdual.finiteInjectiveDimension
  have := hge
  have := hle
  have : L.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eI.symm a
  have : L.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso eI.symm b
  obtain ⟨n, ⟨en⟩⟩ := simple_bounded_iso_shift_field.{u, 0} L a b
  have hzero : IsNormalizedDualizingComplex.{u, 0} ((singleSelfLifted k)⟦-(0 : ℤ)⟧) := by
    simp only [neg_zero]
    exact (isNormalizedDualizingComplex_congr.{u, 0}
      ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).app (singleSelfLifted k))).2
      (isNormalizedDualizingComplex_singleSelfLifted_of_field k)
  have hn : IsNormalizedDualizingComplex.{u, 0} ((singleSelfLifted k)⟦-(-n)⟧) := by
    simp only [neg_neg]
    exact (isNormalizedDualizingComplex_congr.{u, 0} en).1 hL
  have hne : -n = 0 :=
    (isNormalizedDualizingComplex_shift_iff_eq.{u, 0} (singleSelfLifted k) 0 hzero (-n)).1 hn
  have hn0 : n = 0 := by omega
  subst hn0
  exact ⟨en ≪≫ (shiftFunctorZero (DerivedCategory (ModuleCat.{u} k)) ℤ).app
    (singleSelfLifted k)⟩

end Dualizing

end
