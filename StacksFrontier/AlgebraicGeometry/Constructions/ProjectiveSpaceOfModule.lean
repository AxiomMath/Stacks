module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraGrading

/-!
# The projective space of a module

For a module `V` over a commutative ring `k`, its projective space is the scheme
`Proj (Sym_k V)`, where the symmetric algebra is graded by its symmetric powers, so that the
elements of `V` have degree one. It is a scheme over `Spec k` through the canonical map to the
spectrum of the degree-zero part.

## Main definitions

* `AlgebraicGeometry.projectiveSpaceOfModule`: the scheme `Proj (Sym_k V)`.
* `AlgebraicGeometry.projectiveSpaceOfModuleToSpec`: its structure morphism to `Spec k`.

## Implementation notes

The degree-`n` homogeneous component is `SymPow.symmetricPower n k V`, the `n`-th power of the
image of the canonical linear map `V → Sym_k V`, and the graded-algebra structure on those
components is `SymmetricAlgebra.gradedAlgebra`; it is found by instance search, so clients may
use Mathlib's `Proj` API directly on `projectiveSpaceOfModule`.

The structure morphism factors through `AlgebraicGeometry.Proj.toSpecZero`, the canonical map to
the spectrum of the degree-zero part, composed with the spectrum of the algebra map
`k → Sym⁰_k V`; the `Over` instance records it so that the `k`-scheme API applies. For that the
ring and the module must lie in one universe, since the base `Spec k` and the total space must.

The source states this for a vector space over a field; the construction needs only a module
over a commutative ring, and is given in that generality.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

open scoped DirectSum

universe u v

section Construction

variable (k : Type u) (V : Type v) [CommRing k] [AddCommGroup V] [Module k V]

/-- The projective space associated to `V`, namely `Proj (Sym_k V)`. -/
public noncomputable abbrev projectiveSpaceOfModule : Scheme :=
  Proj (fun n => SymPow.symmetricPower n k V)

end Construction

section BaseScheme

variable (k V : Type u) [CommRing k] [AddCommGroup V] [Module k V]

/-- The canonical `k`-scheme structure on the projective space of a `k`-module. -/
public noncomputable def projectiveSpaceOfModuleToSpec :
    projectiveSpaceOfModule k V ⟶ Spec (.of k) :=
  Proj.toSpecZero (fun n => SymPow.symmetricPower n k V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k V)))

/-- The projective space of a `k`-module is a scheme over `Spec k`. -/
public noncomputable instance : (projectiveSpaceOfModule k V).Over (Spec (.of k)) where
  hom := projectiveSpaceOfModuleToSpec k V

end BaseScheme

end AlgebraicGeometry
