module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleSmoothUnramified
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.Basic
public import Mathlib.RingTheory.Etale.Basic

/-!
# The affine criterion for formal étaleness

A morphism `f : X ⟶ S` between **affine** schemes is formally étale exactly when the induced
map on global functions `Γ(S, ⊤) ⟶ Γ(X, ⊤)` is a formally étale ring map.

## Main results

* `AlgebraicGeometry.formallyEtale_iff_globalSectionsMap_formallyEtale`: a morphism of affine
  schemes is formally étale if and only if its map on global functions is.

## References

* [Stacks Project, Tag 02H4](https://stacks.math.columbia.edu/tag/02H4)
* [Stacks Project, Tag 02HG](https://stacks.math.columbia.edu/tag/02HG)
* [Stacks Project, Tag 02HH](https://stacks.math.columbia.edu/tag/02HH)
* [Stacks Project, Tag 02HL](https://stacks.math.columbia.edu/tag/02HL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of affine schemes is formally étale if and only if its pullback map on global
functions is a formally étale ring map. -/
@[stacks 02HL]
theorem formallyEtale_iff_globalSectionsMap_formallyEtale
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) :
    FormallyEtale f ↔ (Scheme.Γ.map f.op).hom.FormallyEtale := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  change FormallyEtale f ↔ Algebra.FormallyEtale Γ(S, ⊤) Γ(X, ⊤)
  rw [formallyEtale_iff_formallySmooth_and_formallyUnramified,
    formallySmooth_iff_appTop_formallySmooth,
    HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified),
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth,
    ← RingHom.formallySmooth_algebraMap, ← RingHom.formallyUnramified_algebraMap]
  simp [RingHom.algebraMap_toAlgebra, and_comm]

end AlgebraicGeometry

end
