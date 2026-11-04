module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# Finiteness of an algebra sheaf is finiteness of type of its underlying module

`Stacks.RelativeSpec.AlgebraSheaf.IsFinite` is a condition on *rings*: over every affine open `U`
of `X`, the structural ring map `Γ(X, U) → Γ(A, U)` is module-finite.
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` is the same sheaf of sections viewed as an
`𝒪_X`-module, by restricting scalars along that very ring map. This file proves that the two
finiteness notions agree:

> for a quasi-coherent algebra sheaf `A`, `A` is finite if and only if `underlyingModule A` is of
> finite type,

and records the corollary that coherence of the underlying module suffices. Local Noetherianity of
`X` is assumed only for the statements that conclude coherence.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.isFinite_iff_isFiniteType_underlyingModule`: **for a
  quasi-coherent algebra sheaf, finiteness and finiteness of type of the underlying module are the
  same condition.**
* `Stacks.RelativeSpec.AlgebraSheaf.isFinite_of_isCoherent_underlyingModule`: **coherence of the
  underlying module makes an algebra sheaf finite.** No Noetherian hypothesis.
* `Stacks.RelativeSpec.AlgebraSheaf.isCoherent_underlyingModule_of_isFinite` and
  `isFinite_iff_isCoherent_underlyingModule`: the converse and the resulting equivalence, over a
  locally Noetherian scheme.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a plain `def` for `SheafOfModules _`, so instance search
does not unfold it. For a variable of type `X.Modules` that is invisible, but `underlyingModule A`
is a *term*, and the instance `SheafOfModules.IsCoherent.isFiniteType` fails to fire on it: the
instance's ring sheaf has to be unified with `X.ringCatSheaf` through the unexposed `def`. The
proofs below therefore take the finiteness predicates as ordinary hypotheses and pass them
positionally with `@`, rather than binding them as instances and letting search find them. The
same reason keeps `IsQuasicoherent` an explicit argument here even though the imported lemmas
declare it as an instance.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}}

/-! ### Finiteness and finiteness of type of the underlying module -/

/-- **A quasi-coherent algebra sheaf whose underlying module is of finite type is finite.** -/
theorem isFinite_of_isFiniteType_underlyingModule (A : AlgebraSheaf X) (hqc : A.IsQuasicoherent)
    (hft : (underlyingModule A).IsFiniteType) : A.IsFinite :=
  fun U hU =>
    @AlgebraicGeometry.moduleFinite_sections_on_affine X (underlyingModule A) hqc hft U hU

/-- **The underlying module of a finite quasi-coherent algebra sheaf is of finite type.** -/
theorem isFiniteType_underlyingModule_of_isFinite (A : AlgebraSheaf X) (hqc : A.IsQuasicoherent)
    (hA : A.IsFinite) : (underlyingModule A).IsFiniteType :=
  @isFiniteType_of_cover_isFiniteTildeOn X (underlyingModule A) X.affineOpens
    (fun V => (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X)) (fun V => V.2)
    fun V => @isFiniteTildeOn_of_moduleFinite_sections X (underlyingModule A) hqc V (hA V.1 V.2)

/-- **For a quasi-coherent algebra sheaf, finiteness and finiteness of type of the underlying
module are the same condition.** No Noetherian hypothesis on `X`. -/
theorem isFinite_iff_isFiniteType_underlyingModule (A : AlgebraSheaf X)
    (hqc : A.IsQuasicoherent) : A.IsFinite ↔ (underlyingModule A).IsFiniteType :=
  ⟨isFiniteType_underlyingModule_of_isFinite A hqc,
    isFinite_of_isFiniteType_underlyingModule A hqc⟩

/-! ### Coherence of the underlying module -/

/-- **An algebra sheaf whose underlying module is coherent is finite.** No Noetherian hypothesis
on `X` is needed. -/
theorem isFinite_of_isCoherent_underlyingModule (A : AlgebraSheaf X)
    (hcoh : (underlyingModule A).IsCoherent) : A.IsFinite :=
  (@isQuasicoherent_isFiniteType_of_isCoherent X (underlyingModule A) hcoh).elim
    (isFinite_of_isFiniteType_underlyingModule A)

/-- **Over a locally Noetherian scheme, the underlying module of a finite quasi-coherent algebra
sheaf is coherent.** -/
theorem isCoherent_underlyingModule_of_isFinite [IsLocallyNoetherian X] (A : AlgebraSheaf X)
    (hqc : A.IsQuasicoherent) (hA : A.IsFinite) : (underlyingModule A).IsCoherent :=
  @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType X _
    (underlyingModule A) hqc (isFiniteType_underlyingModule_of_isFinite A hqc hA)

/-- **Over a locally Noetherian scheme, a quasi-coherent algebra sheaf is finite if and only if
its underlying module is coherent.** -/
theorem isFinite_iff_isCoherent_underlyingModule [IsLocallyNoetherian X] (A : AlgebraSheaf X)
    (hqc : A.IsQuasicoherent) : A.IsFinite ↔ (underlyingModule A).IsCoherent :=
  ⟨isCoherent_underlyingModule_of_isFinite A hqc, isFinite_of_isCoherent_underlyingModule A⟩

end Stacks.RelativeSpec.AlgebraSheaf

end
