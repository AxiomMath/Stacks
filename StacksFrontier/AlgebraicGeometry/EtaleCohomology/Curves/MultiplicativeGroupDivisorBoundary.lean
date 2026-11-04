module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorMiddleExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap

/-!
# `H¹(X, 𝐆_m)` of a smooth curve as a quotient of the global divisors

Let `X` be a smooth curve over an algebraically closed field, with function field `K`, generic
point `j : Spec K ⟶ X` and divisor sequence (Stacks 03RI)

`0 → 𝐆_{m,X} → j_* 𝐆_{m,K} → ⨁_{x ∈ X_0} i_{x,*} 𝐙 → 0`.

Since `H¹(X, j_* 𝐆_{m,K}) = 0` (Stacks 03RK), the connecting map of its long exact sequence
`δ : Γ(X, ⨁_x i_{x,*} 𝐙) → H¹(X, 𝐆_m)` is onto, and its kernel is the image of the second map on
global sections `Γ(X, j_* 𝐆_{m,K}) → Γ(X, ⨁_x i_{x,*} 𝐙)`. This is the cohomological half of the
identification `H¹(X, 𝐆_m) = Div(X)/div(K^*)`: every class is the class of a divisor, and a divisor
has trivial class exactly when it is principal.

Everything is at the coefficient universe `u + 1` and `Ext` universe `u + 1`, which is where the
divisor sequence is exact; `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv` transports to
any larger coefficient universe.

## Main definitions

* `Stacks.EtaleCohomology.divisorBoundary`: the connecting map
  `Γ(X, ⨁_x i_{x,*} 𝐙) → H¹(X, 𝐆_m)`.

## Main results

* `Stacks.EtaleCohomology.surjective_divisorBoundary`: it is surjective.
* `Stacks.EtaleCohomology.divisorBoundary_eq_zero_iff`: its kernel is the image of the second map
  of the divisor sequence on global sections.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK)
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g]

/-- The divisor sequence of Stacks 03RI on a smooth curve, as a short complex of abelian sheaves
on the small étale site at the coefficient universe `u + 1`. -/
abbrev divisorSequence : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk
    (multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X))
    (divisorSequenceSecondMapOfCurve.{u, u + 1} g)
    (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1} g)

/-- **The connecting map of the divisor sequence on global sections**,
`Γ(X, ⨁_x i_{x,*} 𝐙) → H¹(X, 𝐆_m)`: a global section is read as a class in `H⁰` and composed
with the extension class of the divisor sequence. -/
def divisorBoundary :
    ToType ((closedPointDivisorSheaf.{u, u + 1} X).obj.obj (op (Scheme.Etale.mk (𝟙 X)))) →+
      Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 :=
  ((shortExact_divisorSequenceOfCurve g).extClass.postcomp _ (zero_add 1)).comp
    (Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} X)
      (isTerminalEtaleMkId X)).symm.toAddMonoidHom

/-- **Every class of `H¹(X, 𝐆_m)` is the class of a global divisor**: the connecting map of the
divisor sequence is onto, because `H¹(X, j_* 𝐆_{m,K}) = 0` (Stacks 03RK). -/
theorem surjective_divisorBoundary : Function.Surjective (divisorBoundary g) := by
  intro c
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₁ _ (shortExact_divisorSequenceOfCurve g)
    (c : Abelian.Ext _ (divisorSequence g).X₁ 1)
    ((subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_smoothCurve g 1
      le_rfl).elim _ _) (zero_add 1)
  refine ⟨Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} X) (isTerminalEtaleMkId X) x, ?_⟩
  change ((Sheaf.H.equiv₀ _ _).symm (Sheaf.H.equiv₀ _ _ x)).comp _ (zero_add 1) = c
  rwa [AddEquiv.symm_apply_apply]

/-- **A global divisor has trivial class in `H¹(X, 𝐆_m)` exactly when it is the image of a global
section of `j_* 𝐆_{m,K}`** under the second map of the divisor sequence. -/
theorem divisorBoundary_eq_zero_iff
    (s : ToType ((closedPointDivisorSheaf.{u, u + 1} X).obj.obj (op (Scheme.Etale.mk (𝟙 X))))) :
    divisorBoundary g s = 0 ↔ ∃ a, (divisorSequenceSecondMapOfCurve.{u, u + 1} g).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) a = s := by
  have hS := shortExact_divisorSequenceOfCurve g
  constructor
  · intro h
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hS
      ((Sheaf.H.equiv₀ (closedPointDivisorSheaf.{u, u + 1} X) (isTerminalEtaleMkId X)).symm s)
      (zero_add 1) h
    refine ⟨Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X) y, ?_⟩
    rw [Sheaf.H.equiv₀_naturality]
    exact (congrArg (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X)) hy).trans
      (AddEquiv.apply_symm_apply _ _)
  · rintro ⟨a, rfl⟩
    change ((Sheaf.H.equiv₀ _ _).symm _).comp hS.extClass (zero_add 1) = 0
    rw [← Sheaf.H.equiv₀_symm_naturality]
    exact (Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans
      (by rw [hS.comp_extClass, Abelian.Ext.comp_zero])

end Stacks.EtaleCohomology

end
