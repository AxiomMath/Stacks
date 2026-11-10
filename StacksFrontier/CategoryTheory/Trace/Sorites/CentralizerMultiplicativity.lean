module

public import StacksFrontier.CategoryTheory.Trace.Sorites.Coinvariants
public import StacksFrontier.CategoryTheory.Trace.Sorites.Multiplicativity
public import StacksCore.Tactic.StacksAttribute

/-!
# Multiplicativity of the centralizer trace

Let `A` be a commutative ring, `Λ` a ring with a central map from `A`, `G` a finite group and
`Γ` a monoid extension of `G`.  For an element `γ` of `Γ` acting diagonally on the tensor
product of a representation of `Γ` over `A` with one over `Λ`, the trace of `γ` relative to
its centralizer in `G` is the product of the centralizer trace of `γ` on the first factor and
the ordinary trace of `γ` on the second.

## Main definitions

* `MonoidExtensionByNat.diagonalTensorCentralizerTrace` is the centralizer trace of an element
  of the extension monoid acting diagonally on a tensor product.

## Main results

* `MonoidExtensionByNat.diagonalTensorCentralizerTrace_eq` computes that centralizer trace.

## Implementation notes

The identity is the multiplicativity of the group trace of Tag 03UA, applied to the
centralizer of `γ` and to the endomorphisms given by the action of `γ` on each factor.  Since
`A` is commutative, its additive commutator quotient is evaluated in `A` before it acts on the
additive commutator quotient of `Λ`.

## References

* [Stacks Project, Tag 03UC](https://stacks.math.columbia.edu/tag/03UC)
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra

open CategoryTheory.FilteredDerived

open Stacks.Trace.Representation

universe uA uΛ uG uΓ uP uM

namespace Stacks.Trace

/-- The centralizer trace of an element of the extension monoid acting diagonally on the
tensor product of a representation over `A` with a representation over `Λ`. -/
def MonoidExtensionByNat.diagonalTensorCentralizerTrace
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {Γ : Type uΓ} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G] [Finite G] [Monoid Γ]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (E : MonoidExtensionByNat G Γ)
    (ρ : _root_.Representation A Γ P) (σ : _root_.Representation Λ Γ M)
    [Module.Finite A[G] (asModuleNC (restrictedRepresentation E ρ))]
    [Module.Projective A[G] (asModuleNC (restrictedRepresentation E ρ))]
    [Module.Finite Λ M] [Module.Projective Λ M]
    (γ : Γ) : AdditiveCommutatorQuotient Λ := by
  let : AddCommGroup (diagonalTensorProduct A Λ P M) :=
    Module.addCommMonoidToAddCommGroup Λ
  let : Module.Finite Λ[G]
      (asModuleNC (restrictedRepresentation E (Representation.tprodAlgebra ρ σ))) :=
    diagonalAction_module_finite (restrictedRepresentation E ρ)
      (restrictedRepresentation E σ)
  let : Module.Projective Λ[G]
      (asModuleNC (restrictedRepresentation E (Representation.tprodAlgebra ρ σ))) :=
    diagonalAction_module_projective (restrictedRepresentation E ρ)
      (restrictedRepresentation E σ)
  exact E.centralizerTrace (Representation.tprodAlgebra ρ σ) γ

/-- The centralizer trace is multiplicative for the diagonal action on a tensor product. -/
@[stacks 03UC,
  sga "4½ Rapport 5.9" "(5.9.2)",
  sga "5 IIIB 5.12" "special case",
  sga "6 I 8.6" "Punctual (affine) case"]
theorem MonoidExtensionByNat.diagonalTensorCentralizerTrace_eq
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {Γ : Type uΓ} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G] [Finite G] [Monoid Γ]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (E : MonoidExtensionByNat G Γ)
    (ρ : _root_.Representation A Γ P) (σ : _root_.Representation Λ Γ M)
    [Module.Finite A[G] (asModuleNC (restrictedRepresentation E ρ))]
    [Module.Projective A[G] (asModuleNC (restrictedRepresentation E ρ))]
    [Module.Finite Λ M] [Module.Projective Λ M]
    (γ : Γ) :
    E.diagonalTensorCentralizerTrace ρ σ γ =
      commutativeAdditiveCommutatorQuotientEval A (E.centralizerTrace ρ γ) •
        projectiveModuleTrace Λ M (σ γ) := by
  classical
  let : AddCommGroup (diagonalTensorProduct A Λ P M) :=
    Module.addCommMonoidToAddCommGroup Λ
  let H := centralizer E.inclusion γ
  let j : H →* Γ := E.inclusion.comp H.subtype
  let ρH : _root_.Representation A H P := ρ.comp j
  let σH : _root_.Representation Λ H M := σ.comp j
  let : Module.Finite A[H] (asModuleNC ρH) :=
    MonoidExtensionByNat.restricted_module_finite E ρ H
  let : Module.Projective A[H] (asModuleNC ρH) :=
    MonoidExtensionByNat.restricted_module_projective E ρ H
  let u : Module.End A[H] (asModuleNC ρH) :=
    (MonoidExtensionByNat.centralizerEndomorphism E ρ γ).val
  let v : Module.End Λ[H] (asModuleNC σH) :=
    (MonoidExtensionByNat.centralizerEndomorphism E σ γ).val
  have hu : ∀ p : P, u p = ρ γ p :=
    (MonoidExtensionByNat.centralizerEndomorphism E ρ γ).2
  have hv : ∀ m : M, v m = σ γ m :=
    (MonoidExtensionByNat.centralizerEndomorphism E σ γ).2
  let := diagonalAction_module_finite ρH σH
  let := diagonalAction_module_projective ρH σH
  have h := groupTrace_diagonalTensorEndomorphism ρH σH u v
  have hrestrict : groupAlgebraEnd_restrictScalars σH v = σ γ :=
    LinearMap.ext hv
  have hcent : groupTrace A H (asModuleNC ρH) u = E.centralizerTrace ρ γ := rfl
  have hpointwise : ∀ z : diagonalTensorProduct A Λ P M,
      Representation.tprodAlgebra ρ σ γ z =
        (diagonalTensorEndomorphism ρH σH u v).1 z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul p m =>
        rw [(diagonalTensorEndomorphism ρH σH u v).2 p m,
          Representation.tprodAlgebra_apply_tmul, hu, hv]
    | add x y hx hy =>
        exact (map_add (Representation.tprodAlgebra ρ σ γ) x y).trans
          ((congrArg₂ (· + ·) hx hy).trans
            (map_add (diagonalTensorEndomorphism ρH σH u v).1 x y).symm)
  have htensor :
      ((MonoidExtensionByNat.centralizerEndomorphism E
          (Representation.tprodAlgebra ρ σ) γ).val :
        Module.End Λ[H] (asModuleNC (Representation.tprodAlgebra ρH σH))) =
        (diagonalTensorEndomorphism ρH σH u v).1 :=
    LinearMap.ext fun z =>
      ((MonoidExtensionByNat.centralizerEndomorphism E
        (Representation.tprodAlgebra ρ σ) γ).2 z).trans (hpointwise z)
  calc E.diagonalTensorCentralizerTrace ρ σ γ
      = diagonalTensorGroupTrace ρH σH u v :=
        congrArg
          (@groupTrace Λ ↥H _ _ (asModuleNC (Representation.tprodAlgebra ρH σH)) _ _
            (diagonalAction_module_finite ρH σH)
            (diagonalAction_module_projective ρH σH))
          htensor
    _ = commutativeAdditiveCommutatorQuotientEval A
            (groupTrace A H (asModuleNC ρH) u) •
          projectiveModuleTrace Λ M (groupAlgebraEnd_restrictScalars σH v) := h
    _ = commutativeAdditiveCommutatorQuotientEval A (E.centralizerTrace ρ γ) •
          projectiveModuleTrace Λ M (σ γ) := by
        rw [hrestrict, hcent]

end Stacks.Trace
