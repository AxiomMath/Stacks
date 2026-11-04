module

public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationDescent
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSequenceTerms
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode

/-!
# Vector fields as the derivations of the identity morphism

Two readings of `Der_k(𝒪_X, 𝒪_X)` for a scheme `X` over a field `k` live in this library:

* `Stacks.Curves.SheafDerivation k X` (Stacks 0E66), the vector fields of Section 53.26 of the
  source, in which Stacks 0E67, 0E68 and 0E69 are stated;
* `Deformation.Examples.schemeMorphismDerivations (𝟙 X) (X ↘ Spec k)`, the term
  `Der_k(𝒪_X, f_*𝒪_X)` of Stacks 0E3V at `f = 𝟙_X`, in which the infinitesimal automorphisms of
  `X` (Stacks 0DY9) and hence the tangent space of `Aut(X)` at the identity (Stacks 0E6G) are
  expressed.

They are the same type: both are the derivations of `𝒪_X` relative to the structural map
`(X ↘ Spec k)⁻¹ 𝒪_{Spec k} ⟶ 𝒪_X` with values in `𝒪_X`, and pushing a module forward along the
identity changes nothing on sections. This file records the identification, so that the vanishing
of vector fields of Stacks 0E69 reaches the unramifiedness criterion of Stacks 0E6G — the step
"by Lemma 0E6G it suffices to show that `Der_k(𝒪_X, 𝒪_X) = 0`; this is proven in Lemma 0E69" of
the proof of Stacks 0E7A.

## Main results

* `Stacks.Curves.schemeMorphismDerivationsEquivSheafDerivationOf`: the identification.
* `Stacks.Curves.subsingleton_schemeMorphismDerivations_iff`: vanishing of one is vanishing of the
  other.
* `Stacks.Curves.subsingleton_schemeMorphismDerivations_of_isStableOverAlgClosed`: for a stable
  curve over an algebraically closed field, `Der_k(𝒪_X, 𝒪_X) = 0` in the form Stacks 0E6G consumes,
  from the statement of Stacks 0E69 (an explicit input; unregistered).

## References

* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Deformation.Examples

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] (X : Over (Spec (.of k)))

/-- **`Der_k(𝒪_X, (𝟙_X)_*𝒪_X) = Der_k(𝒪_X, 𝒪_X)`.** The derivations of the identity morphism of a
scheme `X` over `k` (the third term of Stacks 0E3V at `f = 𝟙_X`) are the vector fields of `X`
(Stacks 0E66), definitionally. -/
def schemeMorphismDerivationsEquivSheafDerivationOf :
    schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom ≃ SheafDerivationOf X.hom :=
  Equiv.refl _

/-- `Der_k(𝒪_X, (𝟙_X)_*𝒪_X)` vanishes exactly when `Der_k(𝒪_X, 𝒪_X)` does. -/
theorem subsingleton_schemeMorphismDerivations_iff :
    letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom) ↔
      Subsingleton (SheafDerivation k X.left) :=
  (schemeMorphismDerivationsEquivSheafDerivationOf X).subsingleton_congr

/-- **The vector fields of a stable curve over an algebraically closed field vanish, in the form
Stacks 0E6G consumes.** Let `k` be algebraically closed and `X ⟶ Spec k` proper, connected, of
dimension one, at-worst-nodal, of genus at least two, without rational tails or bridges. Then
`Der_k(𝒪_X, (𝟙_X)_*𝒪_X) = 0`.

The input `hvan` is the statement of Stacks 0E69,
`Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities`, with its conclusion
`D = 0` read as `Subsingleton (SheafDerivation k X)` (the zero vector field is an instance not
available in this file); that theorem gives it as
`⟨fun D₁ D₂ => (h D₁).trans (h D₂).symm⟩`. Unregistered. -/
theorem subsingleton_schemeMorphismDerivations_of_isStableOverAlgClosed
    (hvan : ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] (_ : topologicalKrullDim X = 1)
      (_ : HasAtWorstNodalSingularities k X) (_ : 2 ≤ genus (X ↘ Spec (.of k)))
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
      (_ : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C), Subsingleton (SheafDerivation k X))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAlgClosed k] [IsProper (X ↘ Spec (.of k))]
    [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) :
    Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X) (X ↘ Spec (.of k))) :=
  (subsingleton_schemeMorphismDerivations_iff (Over.mk (X ↘ Spec (.of k)))).2
    (hvan k X hdim hnodal hg htail hbridge)

end Stacks.Curves

end
