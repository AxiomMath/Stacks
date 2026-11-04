module

public import StacksFrontier.AlgebraicGeometry.AmpleCluster.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine nonvanishing loci on quasi-affine schemes, for a globally trivialised module

Stacks Tag 0F20 says that on a quasi-affine scheme `X`, for *every* invertible `𝒪_X`-module `L`
and every finite `E` inside an open `W`, some global section `s` of `L` has `X_s` affine with
`E ⊆ X_s ⊆ W`. This file proves that conclusion under an added hypothesis: that `L` carries a
nowhere-vanishing global basis, `Stacks.Ample.NonvanishingBasis`. The names below carry
`of_nonvanishingBasis` and `unitModule` for exactly that reason, and the general case of the tag
is **not** proved here — see "What is not done".

## The route

With a basis `b` of `M`, every nonvanishing locus of a global section of `M` is a basic open of
the structure sheaf: `Stacks.Ample.NonvanishingBasis.nonvanishingLocus_smul_gen` gives
`X_{g · b.gen} = X.basicOpen g`. So the whole content is to find one `g : Γ(X, ⊤)` with
`X.basicOpen g` affine, containing `E`, and inside `W`, which is
`Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine` in the sibling file --
prime avoidance in `Γ(X, ⊤)` against the finitely many primes of `Spec Γ(X, ⊤)` under `E`.

This collapses the source's induction on `#E` entirely. The induction is there to handle a
section that vanishes somewhere it should not, and is repaired by adding a second section; here
a single section is produced outright.

## The nonvanishing locus is produced existentially

The natural formal statement of this tag uses Tag 01CY's `nonvanishingOpen`, the nonvanishing
locus bundled with the openness theorem of Stacks Tag 01CY. That openness theorem is not
available to this file, so as in `Stacks.Ample.IsAmpleForPowers` the open set is produced
existentially: `∃ U : X.Opens, ↑U = X_s ∧ …`. This is not a weakening. The first conjunct forces
`U` to be `X_s`, so the statement *implies* that `X_s` is open and that the affineness and the two
containments are assertions about `X_s` itself;
`Stacks.Ample.isAmpleForPowers_iff_isOpen` is the same equivalence for the ampleness predicate,
proved there with no hypothesis.

Global sections are `Γ(M, ⊤)` rather than the categorical `SheafOfModules.sections`,
following the convention of `Stacks.Ample.IsAmpleForPowers`: for a sheaf the two agree, and a
consumer holding `s : M.sections` passes `s.eval (Opposite.op ⊤)`.

## Main results

* `Stacks.AmpleCluster.exists_affine_nonvanishingLocus_containing_finite_of_nonvanishingBasis`:
  the tag's conclusion for a module with a nowhere-vanishing global basis.
* `Stacks.AmpleCluster.exists_affine_nonvanishingLocus_containing_finite_unitModule`: its
  instance at `M = 𝒪_X`, which is the tag's own statement for `L = 𝒪_X`; the tag's
  invertibility hypothesis on that module holds, by `Stacks.Ample.isInvertibleModule_unit`.

## Implementation notes

No invertibility hypothesis appears. `Stacks.Ample.nonvanishingLocus` is defined for an arbitrary
`𝒪_X`-module, and a `NonvanishingBasis` is strictly stronger than invertibility for the purpose
of this argument, so stating invertibility as well would add nothing. A statement through
Tag 01CY's `nonvanishingOpen` would carry it only because that locus cannot be written without it.

No transparency workaround is needed in this file; the two needed by the prime avoidance are
described in the sibling file.

## References

* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)

## What is not done

The tag itself is not proved, and no stacks attribute for 0F20 is attached by this file. The gap
is precisely the added hypothesis: a general invertible `𝒪_X`-module on a quasi-affine scheme has
no global basis, and then the nonvanishing loci of its global sections are no longer basic opens,
so none of this argument survives.

The source's own route needs three ingredients not available in the library. First, that every
quasi-coherent module on a quasi-affine scheme is globally generated, which supplies a global
section not vanishing at one prescribed point; Mathlib has no such statement about
`AlgebraicGeometry.Scheme.IsQuasiAffine` at the pin. Second, the reduced closed subscheme
structure on the complement of `W` and its quasi-coherent ideal sheaf, used to force
`X_{s'} ⊆ W`. Third, an induction over the points of `E` in which a section vanishing at the last
point is repaired by adding a section supported away from the closures of the earlier ones; that
step needs a point of `E` that is not a specialization of the others, and the fact that
`X_{s + s'}` contains a point at which exactly one of `s, s'` vanishes. Only the last of these is
near at hand: it is the local-ring statement behind
`Stacks.Ample.nonvanishingLocus_add_subset`, which as stated bounds `X_{s + s'}` above rather
than below.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Ample

universe u

namespace Stacks.AmpleCluster

/-- **Stacks Tag 0F20 for a module with a nowhere-vanishing global basis.** On a quasi-affine
scheme, a finite subset `E` of an open `W` is contained in the nonvanishing locus of a global
section of `M`, that locus being affine and contained in `W`.

The hypothesis `b : NonvanishingBasis M` is **an addition to the source**, which asks only that
`M` be invertible; with it every nonvanishing locus of a global section of `M` is a basic open of
the structure sheaf, which is what makes the proof a single application of prime avoidance. The
open set is produced existentially rather than by the bundled `nonvanishingOpen` of Stacks Tag
01CY, whose openness theorem is not available here; the defining equation in the first conjunct
makes that equivalent. -/
@[ega "II 4.5.4" "special case", sga "3 V 6.1"]
theorem exists_affine_nonvanishingLocus_containing_finite_of_nonvanishingBasis
    {X : Scheme.{u}} [X.IsQuasiAffine] {M : X.Modules} (b : NonvanishingBasis M)
    {E : Set X} (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ s : Γ(M, ⊤), ∃ U : X.Opens, (U : Set X) = nonvanishingLocus M s ∧ IsAffineOpen U ∧
      E ⊆ (U : Set X) ∧ U ≤ W := by
  obtain ⟨g, haff, hEU, hUW⟩ := exists_affine_basicOpen_of_finite_of_isQuasiAffine hE W hEW
  exact ⟨g • b.gen, X.basicOpen g, (b.nonvanishingLocus_smul_gen g).symm, haff, hEU, hUW⟩

/-- **Stacks Tag 0F20 for the structure sheaf.** The instance of the previous result at
`M = 𝒪_X`, whose basis is `Stacks.Ample.unitBasis`. This is the tag's own statement in the case
`L = 𝒪_X`: that module is invertible, by `Stacks.Ample.isInvertibleModule_unit`, so the tag's
invertibility hypothesis is met and nothing but the generality in `L` is missing. -/
theorem exists_affine_nonvanishingLocus_containing_finite_unitModule (X : Scheme.{u})
    [X.IsQuasiAffine] {E : Set X} (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ s : Γ(unitModule X, ⊤), ∃ U : X.Opens,
      (U : Set X) = nonvanishingLocus (unitModule X) s ∧ IsAffineOpen U ∧
        E ⊆ (U : Set X) ∧ U ≤ W :=
  exists_affine_nonvanishingLocus_containing_finite_of_nonvanishingBasis (unitBasis X) hE W hEW

end Stacks.AmpleCluster

end
