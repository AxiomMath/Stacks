module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.LocalBound
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain

/-!
# The total colength is bounded by the length of the global sections

Let `I` be a quasi-coherent sheaf of ideals on a scheme `X` over an affine base `Spec A`, and
let `T` be a finite set of closed points equal to the support of `I`. Then the total colength of
`I` along `T` is at most the length over `A` of the global sections of the closed subscheme
`I` cuts out.

The total colength `Stacks.ResolutionOfSurfaces.totalColength` is the sum over `T` of the
lengths of the quotients of the local rings of `X` by the stalks of `I`, which is the right-hand
side of the second inequality of [Stacks, Tag 0AGT]; the left-hand side of that inequality is
the length of the global sections. So the bound below is that inequality, read in the vocabulary
of the total colength.

## Main results

* `Stacks.ResolutionOfSurfaces.totalColength_le_length_globalSections` — the total colength of a
  sheaf of ideals with finite closed support is at most the length over the base ring of the
  global sections of the subscheme it cuts out.

## Implementation notes

The bound is `Stacks.Blowup.Colength.length_globalSections_ge_sum_length_stalkQuotient`, whose
sum is by definition `totalColength I T`. The `A`-algebra structure on the global sections is the
one induced by the composite `I.subscheme ⟶ X ⟶ Spec A`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.ResolutionOfSurfaces

universe u

/-- The total colength of a sheaf of ideals along a finite set of closed points equal to its
support is at most the length, over the base ring of an affine base, of the global sections of
the closed subscheme it cuts out. -/
public theorem totalColength_le_length_globalSections
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (I : X.IdealSheafData) (T : Finset X)
    (hT : (I.support : Set X) = (T : Set X))
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X)) :
    letI : Algebra A Γ(I.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (I.subschemeι ≫ f).appTop).hom.toAlgebra
    totalColength I T ≤ Module.length A Γ(I.subscheme, ⊤) :=
  Stacks.Blowup.Colength.length_globalSections_ge_sum_length_stalkQuotient f I T hT hclosed

end Stacks.ResolutionOfSurfaces

end
