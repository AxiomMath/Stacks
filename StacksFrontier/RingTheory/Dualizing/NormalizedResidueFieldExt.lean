module

public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Length.MaximalIdealPower
import all StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
import StacksCore.Tactic.StacksAttribute

/-!
# The normalization convention read on cohomology

Let `(A, 𝔪, κ)` be a Noetherian local ring and `ω_A^•` a dualizing complex for `A`. The
normalization convention of [Stacks, Section 47.16] fixes the shift by asking
`RHom_A(κ, ω_A^•) = κ[0]`; the condition is `Dualizing.IsNormalizedDualizingComplex`, and the
normalizing shift exists and is unique by `Dualizing.exists_isNormalizedDualizingComplex_shift`
and `Dualizing.isNormalizedDualizingComplex_shift_iff_eq`.

This file reads that convention **on cohomology**: for a normalized `ω_A^•`,

`Ext^i_A(κ, ω_A^•) = 0` for every `i ≠ 0`,

and, for a dualizing complex normalized after the shift by `-m`,

`Ext^i_A(κ, ω_A^•) = 0` for every `i ≠ -m`.

The second form is what a consumer holding an unnormalized complex — in particular a *dualizing
module*, whose degree `Stacks.Duality.IsDualizingRingModule` only quantifies existentially — can
use.

## Main results

* `Dualizing.subsingleton_ext_residueField_of_isNormalized`: `Ext^i_A(κ, ω_A^•) = 0` for `i ≠ 0`
  when `ω_A^•` is normalized.
* `Dualizing.subsingleton_ext_residueField_of_normalizingShift`: the same for an arbitrary
  dualizing complex, with the exceptional degree read off the normalizing shift.
* `Dualizing.isFiniteLength_uliftResidueField`: the residue field has finite length as a module
  over the ring.

## The proof

`Dualizing.finiteLength_ext_subsingleton_of_ne_zero` is the statement for an arbitrary
finite-length module: Matlis duality identifies `RHom_A(N, ω_A^•)` with `Hom_A(N, E)` in degree
zero for such an `N`, so there is no cohomology elsewhere. The residue field has finite length, so
the first result is that lemma at `N = κ`. The same conclusion is clause (1) of [Stacks, Tag 0A7U]
(`Dualizing.ext_degree_mem_Icc_of_nontrivial`) at `M = κ`, where `dim Supp κ = 0` collapses the
interval `[-d, 0]` to `{0}`.

The second result is the first transported along the shift: `Ext^i(K, -)` of a shifted target is
`Ext` of the target in the shifted degree, by `CategoryTheory.shiftFunctorAdd'`, and the target
shift `-m` moves the exceptional degree from `0` to `-m`.

## Implementation notes

The residue field is lifted to `Type (max v u)` by `ULift`, the universe
`Dualizing.IsNormalizedDualizingComplex` and `Dualizing.finiteLength_ext_subsingleton_of_ne_zero`
are stated at; the lift is an `A`-linear equivalence, so finite length transports along it.

## References

* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A7Q](https://stacks.math.columbia.edu/tag/0A7Q)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **The residue field placed in degree zero**, as an object of the derived category of
`A`-modules in the universe the normalization convention is stated at. -/
noncomputable abbrev residueFieldSingle (A : Type u) [CommRing A] [IsLocalRing A] :
    DerivedCategory (ModuleCat.{max v u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A (ULift.{v} (IsLocalRing.ResidueField A)))

/-- **The residue field has finite length as a module over the ring.** It is the quotient of `A`
by the first power of the maximal ideal, and
`Module.finiteLength_quotient_of_contains_maximalIdealPower` applies; the universe lift is an
`A`-linear equivalence. -/
theorem isFiniteLength_uliftResidueField :
    IsFiniteLength A (ULift.{v} (IsLocalRing.ResidueField A)) :=
  (ULift.moduleEquiv (R := A) (M := IsLocalRing.ResidueField A)).symm.isFiniteLength
    (Module.finiteLength_quotient_of_contains_maximalIdealPower A A
      (IsLocalRing.maximalIdeal A) 0 (by simp))

/-- **The normalization convention of [Stacks, Section 47.16] read on cohomology.** For a
*normalized* dualizing complex `ω_A^•` over a Noetherian local ring `A`,

`Ext^i_A(κ, ω_A^•) = 0` for every `i ≠ 0`.

The convention itself says `RHom_A(κ, ω_A^•) ≅ κ[0]`, and this is the vanishing half of that
isomorphism read degree by degree. The residue field has finite length, so
`Dualizing.finiteLength_ext_subsingleton_of_ne_zero` applies; clause (1) of
[Stacks, Tag 0A7U] at `M = κ` gives the same conclusion, `dim Supp κ` being zero. -/
theorem subsingleton_ext_residueField_of_isNormalized
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) {i : ℤ} (hi : i ≠ 0) :
    Subsingleton (DerivedCategory.Ext (residueFieldSingle.{u, v} A) K i) :=
  finiteLength_ext_subsingleton_of_ne_zero K hK isFiniteLength_uliftResidueField.{u, v} hi

/-- **The cohomological normalization at an unnormalized dualizing complex.** If `K⟦-m⟧` is the
normalized dualizing complex — which by `Dualizing.exists_isNormalizedDualizingComplex_shift`
some `m` makes it, and by `Dualizing.isNormalizedDualizingComplex_shift_iff_eq` only one does —
then

`Ext^i_A(κ, K) = 0` for every `i ≠ -m`.

This is `Dualizing.subsingleton_ext_residueField_of_isNormalized` at `K⟦-m⟧` in degree `i + m`,
transported back along `(K⟦-m⟧)⟦i + m⟧ ≅ K⟦i⟧`.

A consumer holding a *dualizing module* `ω_A` rather than a complex is in this situation: the
degree of `Stacks.Duality.IsDualizingRingModule` is existentially quantified, so `m` is not
known from the predicate and has to be pinned by something else — over a Cohen–Macaulay local
ring, by clause (3) of [Stacks, Tag 0AWS]
(`Dualizing.isCohenMacaulay_tfae_dualizingComplex`) together with the dimension. -/
theorem subsingleton_ext_residueField_of_normalizingShift
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (m : ℤ) (hm : IsNormalizedDualizingComplex.{u, v} (K⟦-m⟧))
    {i : ℤ} (hi : i ≠ -m) :
    Subsingleton (DerivedCategory.Ext (residueFieldSingle.{u, v} A) K i) := by
  have hsub := subsingleton_ext_residueField_of_isNormalized (K⟦-m⟧) hm
    (i := i + m) (by omega)
  refine ⟨fun f g => ?_⟩
  let e := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{max v u} A)) (-m) (i + m) i
    (by omega)).app K
  exact (cancel_mono e.hom).1 (hsub.elim (f ≫ e.hom) (g ≫ e.hom))

end Dualizing

end
