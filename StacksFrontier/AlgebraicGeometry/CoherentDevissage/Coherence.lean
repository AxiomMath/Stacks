module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageCoherent.Basic

/-!
# Coherence transport on a ringed space, in an arbitrary universe

`SheafOfModules.IsCoherent` (the coherence predicate of [Stacks, Tag 01BV]) is
stated for `M : SheafOfModules.{u} R` over a sheaf of rings `R` on an arbitrary topological
space `X : Type u`. The transport lemmas for it that this repository already carries —
`Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isCoherent_of_iso` and
`isCoherent_of_isZero` — were written before that class was widened off `Type`, and so are
available only in universe `0`. Nothing in their proofs is universe-specific, and the two
statements are needed in universe `u` by every argument about coherent modules on a general
`Scheme.{u}`. They are therefore restated here in the general form.

`Stacks.AlgebraicGeometry.HigherDirectImageCoherent.isFiniteType_of_iso` is already stated for
an arbitrary site and an arbitrary universe, and is reused rather than restated.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.isZero_over_of_isZero`: restriction to an open
  preserves zero sheaves of modules.
* `Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso`: coherence is invariant under
  isomorphism.
* `Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero`: a zero sheaf of modules is
  coherent.

## Implementation notes

The universe variable of `isFiniteType_of_iso` is not inferable from the isomorphism alone at
every use site — elaboration defaults it to `0` and the application then fails with a universe
mismatch — so each application passes the ring sheaf explicitly as `(R := R)`, which pins it.
In the coherence-condition field the relevant ring sheaf is the restricted one, `R.over U`, not
`R`; passing `R` there is a type error rather than a universe error.

`PreservesColimitsOfSize.{u, u} (overFunctor R U)` has to be produced by hand from
`SheafOfModules.overPushforwardOverAdj`: at universe `0` instance search found it, but the
instance is not found for a general `u`, and without it `mapFreeIso` does not apply.

No tag attribute is attached: [Stacks, Tag 01BV] is the definition of coherence, the class
`SheafOfModules.IsCoherent`, and these are transport lemmas for it rather than any
tag's statement.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory SheafOfModules Limits TopologicalSpace
open Stacks.AlgebraicGeometry.HigherDirectImage
open Stacks.AlgebraicGeometry.HigherDirectImageCoherent

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **Restriction to an open preserves zero sheaves of modules.** A zero sheaf of modules is
the free sheaf on the empty index type, which the restriction functor preserves because that
functor is a left adjoint and so preserves coproducts. -/
theorem isZero_over_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) (U : Opens X) :
    IsZero (M.over U) := by
  have h1 : PreservesColimitsOfSize.{u, u} (overFunctor R U) :=
    (SheafOfModules.overPushforwardOverAdj.{u} (R := R) U).leftAdjoint_preservesColimits
  exact IsZero.of_iso (isZero_free_pempty (R := R.over U))
    ((overFunctor R U).mapIso (hM.iso (isZero_free_pempty (R := R))) ≪≫
      (mapFreeIso (overFunctor R U) PEmpty.{u + 1} (Iso.refl _)).symm)

/-- **Coherence is invariant under isomorphism.** Both conditions of [Stacks, Tag 01BV]
transport: finite type by `isFiniteType_of_iso`, and the finite-type kernel condition because
postcomposing a map out of a free sheaf with an isomorphism leaves its kernel unchanged. -/
theorem isCoherent_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [N.IsCoherent] :
    M.IsCoherent where
  isFiniteType :=
    have := SheafOfModules.IsCoherent.isFiniteType (M := N)
    isFiniteType_of_iso (R := R) e
  kernel_isFiniteType U I hI φ := by
    have := SheafOfModules.IsCoherent.kernel_isFiniteType (M := N) U I hI
      (φ ≫ ((overFunctor R U).mapIso e).hom)
    exact isFiniteType_of_iso (R := R.over U)
      (kernelCompMono φ ((overFunctor R U).mapIso e).hom).symm

/-- **A zero sheaf of modules is coherent.** It is of finite type, being the free sheaf on the
empty index type, and every map out of a free sheaf into it is zero, so the kernels occurring
in the coherence condition are the free sheaves themselves, which are of finite type. -/
theorem isCoherent_of_isZero {M : SheafOfModules.{u} R} (hM : IsZero M) : M.IsCoherent where
  isFiniteType := isFiniteType_of_iso (R := R) (hM.iso (isZero_free_pempty (R := R)))
  kernel_isFiniteType U I hI φ := by
    have : Finite I := hI
    exact isFiniteType_of_iso (R := R.over U)
      ((kernelIsoOfEq ((isZero_over_of_isZero hM U).eq_of_tgt φ 0)).trans kernelZeroIsoSource)

end Stacks.AlgebraicGeometry.CoherentDevissage

end
