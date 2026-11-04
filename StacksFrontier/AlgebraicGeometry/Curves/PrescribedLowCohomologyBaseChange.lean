module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic

/-!
# Twisting an invertible sheaf on a base-changed curve to prescribed low cohomology

Let `k` be a separably closed field, `X` a smooth projective curve over `k`, `K/k` a field
extension and `𝓛` an invertible sheaf on `X_K`. Stacks Tag 0B9Y says there is an invertible
sheaf `𝓛₀` on `X` with

`dim_K H⁰(X_K, 𝓛 ⊗ 𝓛₀|_{X_K}) = 1` and `dim_K H¹(X_K, 𝓛 ⊗ 𝓛₀|_{X_K}) = 0`.

This file defines the twist and the invariant of a descending induction on `dim_K H⁰`, computes
the cohomology of one step of that induction, and carries out the induction given its start and
its step.

## Main definitions

* `AlgebraicGeometry.baseChangeTwist`: the twist `M ⊗_{𝒪_{X'}} p^*L₀` of a module on `X'` by the
  inverse image of a module on `X`.
* `AlgebraicGeometry.HasPrescribedLowCohomology`: vanishing `H¹` together with a
  finite-dimensional `H⁰` of a given dimension.
* `AlgebraicGeometry.PointIdealTwistStep`: the statement that every twist with vanishing `H¹` and
  `H⁰` of dimension `t + 2` admits a short exact sequence down to `i_*i^*` of the twist along a
  closed point `i` at which `H⁰` is one-dimensional, together with a section with nonzero image
  there.
* `AlgebraicGeometry.AmpleTwistStart`: the statement that some twist has vanishing `H¹` and
  nonzero finite-dimensional `H⁰`.

## Main results

* `AlgebraicGeometry.hasPrescribedLowCohomology_of_shortExact`: in a short exact sequence whose
  middle term has vanishing `H¹` and `H⁰` of dimension `t + 1`, and whose right term has
  one-dimensional `H⁰` hit by a global section, the left term has vanishing `H¹` and `H⁰` of
  dimension `t`.
* `AlgebraicGeometry.hasPrescribedLowCohomology_of_pointIdealStep`: one step of the induction
  lowers the dimension of `H⁰` by one.
* `AlgebraicGeometry.exists_hasPrescribedLowCohomology_one`: given the step, some twist has
  vanishing `H¹` and one-dimensional `H⁰`.

## References

* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The twist of a module on the base change by one coming from the base -/

/-- The twist `M ⊗_{𝒪_{X'}} p^*L₀` of a module on `X'` by the inverse image along `p : X' ⟶ X`
of a module on `X`. For `p` the projection of a base change `X' = X_K` this is the sheaf
`𝓛 ⊗_{𝒪_{X_K}} 𝓛₀|_{X_K}`. -/
public def baseChangeTwist {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X'.Modules)
    (L₀ : X.Modules) : X'.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X'.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ X'.presheaf (forget₂ CommRingCat RingCat)
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X')⟩).obj M).obj
    ((Scheme.Modules.pullback p).obj L₀)

/-! ### The invariant carried by the descending induction -/

/-- `M` has *prescribed low cohomology of dimension `t`* over `K` when `H¹(M)` vanishes and
`H⁰(M)` is finite dimensional of dimension `t`, vanishing being
`CategoryTheory.Limits.IsZero`. -/
public structure HasPrescribedLowCohomology (K : Type u) [Field K] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of K)) (M : X'.Modules) (t : ℕ) : Prop where
  /-- The first cohomology vanishes. -/
  isZero_one : IsZero (cohomologyOverField K f' M 1)
  /-- The space of global sections is finite dimensional. -/
  finiteDimensional_zero : FiniteDimensional K (cohomologyOverField K f' M 0)
  /-- The space of global sections has dimension `t`. -/
  finrank_zero : Module.finrank K (cohomologyOverField K f' M 0) = t

/-- Under `AlgebraicGeometry.HasPrescribedLowCohomology`, `dim_K H¹ = 0`. -/
public theorem HasPrescribedLowCohomology.finrank_one {K : Type u} [Field K] {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (.of K)} {M : X'.Modules} {t : ℕ}
    (h : HasPrescribedLowCohomology K f' M t) :
    Module.finrank K (cohomologyOverField K f' M 1) = 0 :=
  have := ModuleCat.subsingleton_of_isZero h.isZero_one
  Module.finrank_zero_of_subsingleton

/-! ### The cohomology of one step -/

/-- Let `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be short exact with `H¹(ℱ₂) = 0` and `H⁰(ℱ₂)` finite dimensional of
dimension `t + 1`, let `dim_K H⁰(ℱ₃) = 1`, and let some class of `H⁰(ℱ₂)` have nonzero image in
`H⁰(ℱ₃)`. Then `H¹(ℱ₁) = 0` and `H⁰(ℱ₁)` is finite dimensional of dimension `t`. -/
public theorem hasPrescribedLowCohomology_of_shortExact (K : Type u) [Field K] {X' : Scheme.{u}}
    (f' : X' ⟶ Spec (.of K)) {S : ShortComplex X'.Modules} (hS : S.ShortExact) (t : ℕ)
    (hmid : HasPrescribedLowCohomology K f' S.X₂ (t + 1))
    (hright : Module.finrank K (cohomologyOverField K f' S.X₃ 0) = 1)
    {a : cohomologyOverField K f' S.X₂ 0}
    (ha : cohomologyOverFieldMap K f' S.g 0 a ≠ 0) :
    HasPrescribedLowCohomology K f' S.X₁ t := by
  obtain ⟨hrk, hvan, hfd⟩ := finrank_cohomologyOverField_zero_add_one_eq_of_shortExact K f' hS
    hmid.finiteDimensional_zero hright hmid.isZero_one ha
  refine ⟨hvan, hfd, ?_⟩
  rw [hmid.finrank_zero] at hrk
  lia

/-! ### The start and the step of the induction -/

section Hypotheses

variable (K : Type u) [Field K] {X X' : Scheme.{u}} (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X)
  (L : X'.Modules)

/-- Whenever a twist of `L` by an invertible sheaf `L₀` on `X` has vanishing `H¹` and `H⁰` of
dimension `t + 2`, there are a closed point `i : Z ⟶ X'`, an invertible sheaf `L₁` on `X` and a
short exact sequence

`0 ⟶ L ⊗ p^*L₁ ⟶ L ⊗ p^*L₀ ⟶ i_*i^*(L ⊗ p^*L₀) ⟶ 0`

such that `dim_K H⁰(Z, i^*(L ⊗ p^*L₀)) = 1` and some class of `H⁰(X', L ⊗ p^*L₀)` has nonzero
image in `H⁰(X', i_*i^*(L ⊗ p^*L₀))`. -/
public def PointIdealTwistStep : Prop :=
  ∀ (L₀ : X.Modules) (t : ℕ), Stacks.Ample.IsInvertibleModule X L₀ →
    HasPrescribedLowCohomology K f' (baseChangeTwist p L L₀) (t + 2) →
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X') (_ : IsClosedImmersion i) (L₁ : X.Modules)
      (α : baseChangeTwist p L L₁ ⟶ baseChangeTwist p L L₀)
      (β : baseChangeTwist p L L₀ ⟶ (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj (baseChangeTwist p L L₀)))
      (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
        Stacks.Ample.IsInvertibleModule X L₁ ∧
        Module.finrank K (cohomologyOverField K (i ≫ f')
            ((Scheme.Modules.pullback i).obj (baseChangeTwist p L L₀)) 0) = 1 ∧
        ∃ a, cohomologyOverFieldMap K f' β 0 a ≠ 0

/-- There is an invertible sheaf `L₀` on `X` whose inverse image twists `L` to a sheaf with
vanishing `H¹` and at least one independent global section. -/
public def AmpleTwistStart : Prop :=
  ∃ (L₀ : X.Modules) (t : ℕ), Stacks.Ample.IsInvertibleModule X L₀ ∧
    HasPrescribedLowCohomology K f' (baseChangeTwist p L L₀) (t + 1)

end Hypotheses

/-! ### One full step, and the descending induction -/

/-- Given `AlgebraicGeometry.PointIdealTwistStep`, if the twist of `L` by an invertible sheaf
`L₀` on `X` has vanishing `H¹` and `H⁰` of dimension `t + 2`, then the twist by some invertible
sheaf `L₁` on `X` has vanishing `H¹` and `H⁰` of dimension `t + 1`. -/
public theorem hasPrescribedLowCohomology_of_pointIdealStep (K : Type u) [Field K]
    {X X' : Scheme.{u}} (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X) (L : X'.Modules)
    (hstep : PointIdealTwistStep K f' p L) (L₀ : X.Modules) (t : ℕ)
    (hL₀ : Stacks.Ample.IsInvertibleModule X L₀)
    (h : HasPrescribedLowCohomology K f' (baseChangeTwist p L L₀) (t + 2)) :
    ∃ L₁ : X.Modules, Stacks.Ample.IsInvertibleModule X L₁ ∧
      HasPrescribedLowCohomology K f' (baseChangeTwist p L L₁) (t + 1) := by
  obtain ⟨Z, i, hi, L₁, α, β, w, hSE, hL₁, hone, a, ha⟩ := hstep L₀ t hL₀ h
  have e := cohomologyOverFieldPushforwardIsoOfIsClosedImmersion K i f'
    ((Scheme.Modules.pullback i).obj (baseChangeTwist p L L₀)) 0
  exact ⟨L₁, hL₁, hasPrescribedLowCohomology_of_shortExact K f' hSE (t + 1) h
    (e.toLinearEquiv.finrank_eq.symm.trans hone) ha⟩

/-- Given `AlgebraicGeometry.PointIdealTwistStep` and one invertible sheaf `L₀` on `X` whose twist
of `L` has vanishing `H¹` and `H⁰` of dimension `t + 1`, there is an invertible sheaf on `X` whose
twist of `L` has vanishing `H¹` and exactly one independent global section. -/
public theorem exists_hasPrescribedLowCohomology_one (K : Type u) [Field K]
    {X X' : Scheme.{u}} (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X) (L : X'.Modules)
    (hstep : PointIdealTwistStep K f' p L) (t : ℕ) (L₀ : X.Modules)
    (hL₀ : Stacks.Ample.IsInvertibleModule X L₀)
    (h : HasPrescribedLowCohomology K f' (baseChangeTwist p L L₀) (t + 1)) :
    ∃ L₁ : X.Modules, Stacks.Ample.IsInvertibleModule X L₁ ∧
      HasPrescribedLowCohomology K f' (baseChangeTwist p L L₁) 1 := by
  induction t generalizing L₀ with
  | zero => exact ⟨L₀, hL₀, h⟩
  | succ t ih =>
      obtain ⟨L₁, hL₁, h₁⟩ :=
        hasPrescribedLowCohomology_of_pointIdealStep K f' p L hstep L₀ t hL₀ h
      exact ih L₁ hL₁ h₁

end AlgebraicGeometry

end
