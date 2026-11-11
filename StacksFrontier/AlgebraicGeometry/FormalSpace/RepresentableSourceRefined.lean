module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Formal algebraic spaces along morphisms representable by algebraic spaces: the refined forms

For a morphism `f : X ⟶ Y` of formal algebraic spaces and a property `P` of continuous ring
maps, if `P` holds on every affine étale diagram over `f`, then the atlas of `Y` together with
the atlases of the fibre products of its members with `X` witness that `P` holds after a cover
of the target.

## Main results

* `hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal'`:
  if `P` holds on every affine étale diagram over a morphism of formal algebraic spaces, then
  `P` holds after a cover of the target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Stacks 0ANG, condition (1) implies condition (2).** If `P` holds on every affine étale
diagram over a morphism `f : X ⟶ Y` of formal algebraic spaces, then the atlas of the target
and the atlases of the fibre products of its members with the source witness condition (2).

The fibre products are formal algebraic spaces by **Stacks 0AJ3**, which this library proves
outright for a base which is a formal algebraic space:
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`
asks only that `X`, `Y` and the chart `V` be formal algebraic spaces, which `hX`, `hY` and the
atlas of `Y` give. It therefore supplies the hypothesis `hpb` of
`AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram` with no
standing hypothesis of its own. -/
theorem hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f) :
    HasPropertyAfterTargetCover B S hS C P f :=
  hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS C P f hY
    (fun _ v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v' f hY hV' hX) hf

end AlgebraicGeometry.FormalSpace

end
