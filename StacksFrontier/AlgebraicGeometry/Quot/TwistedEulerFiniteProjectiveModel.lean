module

public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerLocallyConstantOfModel
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorTensorInvertible
public import StacksFrontier.AlgebraicGeometry.Quot.InvertibleTwistPower
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# Finite projective models for the twisted modules of a coherent family

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `(T, 𝓕)` an object of `Coh_{X/B}` over an affine test scheme `T = Spec R`.  The
twisted module `𝓖 = 𝓕 ⊗ L_T^{⊗ n}` is again of finite presentation, flat over `T` and with
support proper over `T`, tensoring with the invertible module `L_T^{⊗ n}` changing neither the
geometric stalks up to isomorphism nor the support.  So Stacks 0A1Q applies to `𝓖`: there is a
bounded complex `M^•` of finite projective `R`-modules with `RΓ(X_{T'}, 𝓖_{T'}) ≅ M^• ⊗^𝐋_R R'`
for every affine `T' = Spec R'` over `T`.

Consequently the twisted Euler characteristics `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` are locally
constant on every test scheme, and `Coh^{P, L}_{X/B} ⊆ Coh_{X/B}` is cut out by an open and
closed condition, for every function `P : ℤ → ℤ`.

## Main results

* `CoherentObject.hasFiniteProjectiveDerivedSectionsModel_familyTwistedModule`: the finite
  projective model of the derived sections of `𝓕 ⊗ L_T^{⊗ n}` (Stacks 0A1Q).
* `CoherentObject.isLocallyConstant_twistedEuler`: the twisted Euler characteristics are
  locally constant.
* `CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial`: `Coh^{P, L}_{X/B}` is cut
  out by an open and closed condition.

## References

* [Stacks Project, Tag 0A1Q](https://stacks.math.columbia.edu/tag/0A1Q)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace CoherentObject

variable (L : Modules.{u, u} B S hS D.X.1 D.X.2)
  [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]

include hL in
/-- The pullback `L_T^{⊗ n}` of `L^{⊗ n}` to `X_T` is invertible. -/
theorem isInvertible_familyTwist (A : CoherentObject D) (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS (D.space A.T).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (D.space A.T).1 (D.space A.T).2).O)).property
      ((modulePullback B S hS (baseChangeProjection D.f A.T)).obj
        (invertibleTensorPower B S hS D.X.1 D.X.2 L n)) :=
  isInvertible_modulePullback B S hS _ _

include hL in
/-- The pullback `L_T^{⊗ n}` is étale locally trivial. -/
theorem isLocallyTrivialOnSite_familyTwist (A : CoherentObject D) (n : ℤ) :
    Stacks.SheafOfModules.TensorLocalProperties.IsLocallyTrivialOnSite
      (structureSheaf B S hS (D.space A.T).1 (D.space A.T).2)
      ((modulePullback B S hS (baseChangeProjection D.f A.T)).obj
        (invertibleTensorPower B S hS D.X.1 D.X.2 L n)) :=
  isLocallyTrivialOnSite_of_isInvertible (D.space A.T) _
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ (isInvertible_familyTwist L A n))

include hL in
/-- The twisted module `𝓕 ⊗ L_T^{⊗ n}` is quasi-coherent. -/
theorem isQuasicoherentOnSite_familyTwistedModule (A : CoherentObject D) (n : ℤ) :
    (familyTwistedModule L A n).IsQuasicoherentOnSite :=
  open Stacks.SheafOfModules.TensorLocalProperties in
  (isQuasicoherentOnSite_tensor_iff_of_isLocallyTrivialOnSite
    (structureSheaf B S hS (D.space A.T).1 (D.space A.T).2) A.F _
    (isLocallyTrivialOnSite_familyTwist L A n)).2 A.quasicoherent

include hL in
/-- The twisted module `𝓕 ⊗ L_T^{⊗ n}` is of finite presentation. -/
theorem isFinitePresentation_familyTwistedModule (A : CoherentObject D) (n : ℤ) :
    (familyTwistedModule L A n).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
    (open Stacks.SheafOfModules.TensorLocalProperties in
      (isFinitePresentationOnSite_tensor_iff_of_isLocallyTrivialOnSite
        (structureSheaf B S hS (D.space A.T).1 (D.space A.T).2) A.F _
        (isLocallyTrivialOnSite_familyTwist L A n)).2 A.finitePresentation)

include hL in
/-- The twisted module `𝓕 ⊗ L_T^{⊗ n}` is flat over `T`. -/
theorem isFlatOver_familyTwistedModule (A : CoherentObject D) (n : ℤ) :
    IsFlatOver B S hS (D.space A.T).2 (D.projection A.T).hom (familyTwistedModule L A n) :=
  (isFlatOver_tensor_invertible_iff B S hS (D.space A.T) (D.projection A.T) A.F _
    (isInvertible_familyTwist L A n) A.quasicoherent
    (isQuasicoherentOnSite_familyTwistedModule L A n)).2 A.flat

include hL in
/-- The twisted module `𝓕 ⊗ L_T^{⊗ n}` has support proper over `T`: it has the support of `𝓕`. -/
theorem hasProperSupport_familyTwistedModule (A : CoherentObject D) (n : ℤ) :
    HasProperSupport B S hS (D.space A.T).2 ((schemeSpaceFunctor B S hS).obj A.T.left).2
      (D.projection A.T).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (D.isFinitePresentation_projection A.T).1)
      ((SheafOfModules.toSheaf _).obj (familyTwistedModule L A n)) := by
  obtain ⟨hp, hU, hprop⟩ := A.properSupport
  exact hasProperSupport_congr_support (D.space A.T).2 _ _ _
    (supportOfSheaf_tensor_invertible B S hS (D.space A.T) A.F _
      (isInvertible_familyTwist L A n)).symm ⟨hU, hprop⟩

include hL in
/-- **Stacks 0A1Q for the twisted modules.**  For an object `(T, 𝓕)` of `Coh_{X/B}` over an
affine test scheme `T = Spec R` and `n ∈ ℤ`, the derived sections of `𝓕 ⊗ L_T^{⊗ n}` have a
finite projective model: a bounded complex `M^•` of finite projective `R`-modules with
`RΓ(X_{T'}, (𝓕 ⊗ L_T^{⊗ n})_{T'}) ≅ M^• ⊗^𝐋_R R'` for every affine `T' = Spec R'` over `T`. -/
theorem hasFiniteProjectiveDerivedSectionsModel_familyTwistedModule (A : CoherentObject D)
    [IsAffine A.testScheme] (n : ℤ) :
    HasFiniteProjectiveDerivedSectionsModel A (familyTwistedModule L A n) := by
  obtain ⟨M, a, b, h₁, h₂, h₃, h₄, -, φ, -⟩ :=
    exists_finiteProjective_model_derivedSections (D.projection A.T)
      (D.isFinitePresentation_projection A.T) (familyTwistedModule L A n)
      (isFinitePresentation_familyTwistedModule L A n) (isFlatOver_familyTwistedModule L A n)
      (hasProperSupport_familyTwistedModule L A n)
  refine ⟨M, a, b, h₁, h₂, h₃, h₄, ?_⟩
  intro U' _ g X' f' g' sq
  exact ⟨φ g f' g' sq⟩

include hL in
/-- **The twisted Euler characteristics are locally constant** (Stacks 0A1Q, 0D1Z): for every
object `(T, 𝓕)` of `Coh_{X/B}` and `n ∈ ℤ`, `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant
on `T`. -/
theorem isLocallyConstant_twistedEuler (A : CoherentObject D) (n : ℤ) :
    IsLocallyConstant fun t : A.testScheme => twistedEuler L A t n :=
  isLocallyConstant_twistedEuler_of_model L n
    (fun A' _ => hasFiniteProjectiveDerivedSectionsModel_familyTwistedModule L A' n) A

end CoherentObject

namespace CoherentSituation

/-- **`Coh^{P, L}_{X/B}` is cut out by an open and closed condition** (Stacks 0A1Q): for every
function `P : ℤ → ℤ`, the condition `χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = P(n)` for all `n` and all points
`t` of the test scheme is open and closed on `Coh_{X/B}`. -/
theorem isOpenAndClosedCondition_hasHilbertPolynomial (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) :
    IsOpenAndClosedCondition D (CoherentObject.HasHilbertPolynomial L P) :=
  isOpenAndClosedCondition_hasHilbertPolynomial_of_model L
    (fun A _ n =>
      CoherentObject.hasFiniteProjectiveDerivedSectionsModel_familyTwistedModule L A n) P

end CoherentSituation

end AlgebraicGeometry.Space

end
