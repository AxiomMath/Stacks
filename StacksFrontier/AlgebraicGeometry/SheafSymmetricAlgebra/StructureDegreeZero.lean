module

public import StacksFrontier.AlgebraicGeometry.LocallyProjectiveHProjective.Sym
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart

/-!
# The degree-zero structure map of `Sym(E)` over an affine open is surjective

The degree-zero part of `Sym(ℰ)` is the structure sheaf, so over an affine open the degree-zero
part of the graded ring of sections of `Sym(ℰ)` is the image of the ring of functions. That
statement is formalized, as
`Stacks.LocallyProjectiveHProjective.exists_strHom_eq`; this file reads it as surjectivity of
`Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf`, the corestriction of the structure
map to the degree-zero part, which is the shape the coordinate cut of [Stacks, Tag 02NP] uses:
the chart generators there are polynomials over the degree-zero part of the graded ring, and the
morphism to projective space only reaches polynomials over the base.

## Main results

* `Stacks.SymGraded.surjective_strZeroSheaf`: **over an affine open the degree-zero structure
  map `Γ(X, V) ⟶ Γ(Sym(E), V)₀` is surjective.**

## References

* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjBundleSurjection
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.SymGraded

/-- **Over an affine open the degree-zero structure map of `Sym(E)` is surjective.** Every
degree-zero element of the graded ring of sections is the image of a function on the open, by
`Stacks.LocallyProjectiveHProjective.exists_strHom_eq`, and
`Stacks.AlgebraicGeometry.ProjBundleSurjection.strZeroSheaf` is that map corestricted to the
degree-zero part. -/
theorem surjective_strZeroSheaf {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    (hqc : IsQuasicoherentPieces E) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (strZeroSheaf (schemeSheafGradedAlgebra E hqc) V) := by
  intro z
  obtain ⟨r, hr⟩ := Stacks.LocallyProjectiveHProjective.exists_strHom_eq E hqc hV z.1 z.2
  exact ⟨r, Subtype.ext
    ((coe_strZeroSheaf_apply (schemeSheafGradedAlgebra E hqc) V r).trans hr)⟩

end Stacks.SymGraded

end
