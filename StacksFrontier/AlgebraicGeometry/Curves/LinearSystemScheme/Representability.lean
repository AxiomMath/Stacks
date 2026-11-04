module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.Surjectivity

/-!
# `Proj k[T₀, …, Tₙ]` represents the fibre of the Abel map

For a smooth projective curve `X` over an algebraically closed field `k`, an effective Cartier
divisor `D` of degree `d` and a basis `w₀, …, wₙ` of `Γ(X, 𝒪_X(D))`, pulling back the universal
divisor is a bijection, natural in the `k`-scheme `T`, from `k`-morphisms `T ⟶ Proj k[T₀, …, Tₙ]`
to the `T`-points of the fibre of the Abel map over the point of `𝒪_X(D)`
(`Stacks.LinearSystemScheme.abelFibre`).

## Main results

* `Stacks.LinearSystemScheme.familyEquiv`: the bijection.
* `Stacks.LinearSystemScheme.familyEquiv_naturality`: its naturality in `T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange Stacks.Hilbert

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.LinearSystemScheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
  (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  {n : ℕ} (w : letI := baseModule f (Stacks.Divisors.modulesInvertibleSheaf D) ⊤;
    Module.Basis (Fin (n + 1)) Γ(Spec (.of k), ⊤) Γ(Stacks.Divisors.modulesInvertibleSheaf D, ⊤))
  (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
  (hd : invertibleCurveDegree k f hdim (Stacks.Divisors.modulesInvertibleSheaf D) = d)

/-- The family over `T` classified by `g : T ⟶ Q`, as a point of the fibre of the Abel map. -/
def familyPoint {T : Over (Spec (.of k))} (g : T ⟶ projOver k (n := n)) : abelFibre f D d T :=
  ⟨⟨familyOf k f _ w g, isFiniteLocallyFreeOfRank_familyOf k f _ w g hdim hd⟩,
    isLocallyIso_familyOf k f _ w g hdim hd⟩

/-- **The representability bijection.** -/
def familyEquiv (T : Over (Spec (.of k))) : (T ⟶ projOver k (n := n)) ≃ abelFibre f D d T :=
  Equiv.ofBijective (familyPoint k f D w hdim hd)
    ⟨fun g g' h => eq_of_familyOf_eq k f _ w g g'
        (congrArg (fun Z : abelFibre f D d T => Z.1.ideal) h),
      fun Z => by
        obtain ⟨g, hg⟩ := exists_familyOf_eq k f _ w Z.1.ideal Z.1.isFiniteLocallyFreeOfRank Z.2
        exact ⟨g, Subtype.ext (HilbertFamily.ext hg)⟩⟩

/-- **Naturality of the representability bijection**: restricting the family classified by `g`
along `h : T' ⟶ T` classifies the family of `h ≫ g`. -/
theorem familyEquiv_naturality {T T' : Over (Spec (.of k))} (h : T' ⟶ T)
    (g : T ⟶ projOver k (n := n)) :
    (familyEquiv k f D w hdim hd T' (h ≫ g)).1.ideal =
      (familyEquiv k f D w hdim hd T g).1.ideal.comap (familyBaseChangeMap (curveOver f) h) :=
  familyOf_comp k f _ w h g

end Stacks.LinearSystemScheme

end
