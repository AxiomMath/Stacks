module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistInjectivity
import all StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistInjectivity
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistVanishing

/-!
# Vanishing of `H¹` on the twists of an invertible sheaf by an exceptional curve

Let `E ⊆ X` be an exceptional curve of the first kind and `ℒ` an invertible `𝒪_X`-module whose
restriction to `E ≅ 𝐏¹` has degree `n ≥ 0`. This file proves assertion (1) of
[Stacks, Tag 0C2J]: if `H¹(X, ℒ) = 0` then `H¹(X, ℒ(iE)) = 0` for `0 ≤ i ≤ n + 1`.

## Main results

* `Stacks.Surfaces.divisorTwist`: the twist `ℒ(iE)`, with
  `Stacks.Surfaces.isInvertible_divisorTwist` and
  `Stacks.Surfaces.nonempty_pullbackDivisorTwistIso`, its degree on `𝐏¹`.
* `Stacks.Surfaces.isZero_rightDerived_one_divisorTwist`: assertion (1) of [Stacks, Tag 0C2J].

## References

* [Stacks Project, Tag 0C2J](https://stacks.math.columbia.edu/tag/0C2J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Divisors
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover twistMultiplicationIso)
open RingedSpaceModuleAdjunction (modulePullback modulePushforward)
open Stacks.SheafOfModules (sheafTensorMonoidal sheafTensorSymmetric)

universe u

namespace Stacks.Surfaces

attribute [local instance] HasDerivedCategory.standard MvPolynomial.gradedAlgebra

attribute [local instance] schemeModulesMonoidal schemeModulesSymmetric

variable {X : Scheme.{u}}

/-! ### The twists `ℒ(iE)` -/

/-- **`ℒ(iE)`, the `i`-fold twist of `ℒ` by the divisor `E`.** Recursively `ℒ(0E) = ℒ` and
`ℒ((i+1)E) = ℒ(iE) ⊗ 𝒪_X(E)`; the index is a natural number because the range `0 ≤ i ≤ n + 1`
of assertion (1) of [Stacks, Tag 0C2J] is a range of non-negative twists. -/
def divisorTwist (E : X.IdealSheafData)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    ℕ → _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
  | 0 => L
  | i + 1 =>
    MonoidalCategory.tensorObj
      (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
      (divisorTwist E L i) (invertibleSheaf' E)

/-- The zeroth twist is `ℒ` itself. -/
theorem divisorTwist_zero (E : X.IdealSheafData)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :
    divisorTwist E L 0 = L := rfl

/-- One more twist is one more tensor factor of `𝒪_X(E)`. -/
theorem divisorTwist_succ (E : X.IdealSheafData)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) (i : ℕ) :
    divisorTwist E L (i + 1) =
      MonoidalCategory.tensorObj
        (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (divisorTwist E L i) (invertibleSheaf' E) := rfl

/-- **Every twist `ℒ(iE)` of an invertible sheaf by an effective Cartier divisor is
invertible**, by induction on `i` from
`Stacks.Surfaces.isInvertible_tensorObj_invertibleSheaf`. -/
theorem isInvertible_divisorTwist (E : X.IdealSheafData) [IsEffectiveCartierDivisor E]
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L] (i : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (divisorTwist E L i) := by
  induction i with
  | zero => rw [divisorTwist_zero]; infer_instance
  | succ i ih =>
    rw [divisorTwist_succ]
    have := ih
    exact isInvertible_tensorObj_invertibleSheaf E (divisorTwist E L i)

/-- **`e^*i^*(ℒ(iE)) ≅ 𝒪(n - i)` when `ℒ|_E` has degree `n`.** Each twist by `E` lowers the
degree on `𝐏¹` by one, because `e^*i^*𝒪_X(E) ≅ 𝒪(-1)`; the step is
`Stacks.Surfaces.pullbackTwistIso` and the induction is on `i`. The conclusion is a `Nonempty`
rather than a chosen isomorphism because nothing below depends on *which* isomorphism the
induction produces. -/
theorem nonempty_pullbackDivisorTwistIso (E : X.IdealSheafData) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ E.subscheme} (hE : E.IsExceptionalCurveOfFirstKind k e)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) {n : ℤ}
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj L) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) (i : ℕ) :
    Nonempty ((modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj (divisorTwist E L i)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (n - i)) := by
  induction i with
  | zero =>
    rw [divisorTwist_zero, Nat.cast_zero, sub_zero]
    exact ⟨hdeg⟩
  | succ i ih =>
    obtain ⟨hi⟩ := ih
    rw [divisorTwist_succ,
      show n - ((i + 1 : ℕ) : ℤ) = (n - (i : ℤ)) + -1 by push_cast; ring]
    exact ⟨pullbackTwistIso E k hE (divisorTwist E L i) hi⟩

/-! ### Assertion (1) of Tag 0C2J -/

/-- **[Stacks, Tag 0C2J], assertion (1).** Let `E ⊆ X` be an exceptional curve of the first kind
on a scheme `X`, let `ℒ` be an invertible `𝒪_X`-module, and let `n` be the degree of `ℒ|_E` as an
invertible module on `𝐏¹`, recorded as an isomorphism `e^*i^*ℒ ≅ 𝒪(n)`. If `H¹(X, ℒ) = 0` and
`0 ≤ n` then

`H¹(X, ℒ(iE)) = 0` for every `0 ≤ i ≤ n + 1`.

The induction is on `i`, along the ideal sequence of `E` twisted by `ℒ((i+1)E)`:

`0 ⟶ ℒ(iE) ⟶ ℒ((i+1)E) ⟶ ℒ((i+1)E)|_E ⟶ 0`,

whose first term is identified by `Stacks.Surfaces.twistedIdealIso` and whose third restricts to
`𝒪(n - i - 1)` on `𝐏¹`. For `i ≤ n` that degree is at least `-1`, so the third term has no `H¹`
by `Stacks.Surfaces.isZero_rightDerived_one_tensorPushforwardUnit`, and the degree-one row of
the long exact sequence forces `H¹` of the middle term to vanish. The hypothesis `0 ≤ n` is the
source's and is carried unchanged; the induction consumes only `i ≤ n + 1`, since the step that
produces `ℒ((j+1)E)` gets the `j ≤ n` it needs from `j + 1 ≤ n + 1`. -/
@[stacks 0C2J "assertion (1): H^1 vanishes on the twists ℒ(iE) for 0 ≤ i ≤ n+1"]
theorem isZero_rightDerived_one_divisorTwist (E : X.IdealSheafData) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ E.subscheme}
    (hE : E.IsExceptionalCurveOfFirstKind k e)
    (L : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {n : ℤ} (_hn : 0 ≤ n)
    (hdeg : (modulePullback e.hom.toLRSHom.toShHom).obj
        ((modulePullback E.subschemeι.toLRSHom.toShHom).obj L) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) n)
    (hL : IsZero (((moduleGlobalSections X).rightDerived 1).obj L))
    (i : ℕ) (hi : (i : ℤ) ≤ n + 1) :
    IsZero (((moduleGlobalSections X).rightDerived 1).obj (divisorTwist E L i)) := by
  have _hcartier := hE.isEffectiveCartierDivisor
  suffices h : ∀ j : ℕ, (j : ℤ) ≤ n + 1 →
      IsZero (((moduleGlobalSections X).rightDerived 1).obj (divisorTwist E L j)) from h i hi
  intro j
  induction j with
  | zero =>
    intro _
    rw [divisorTwist_zero]
    exact hL
  | succ j ih =>
    intro hj
    have hjn : (j : ℤ) ≤ n := by push_cast at hj; omega
    have ihz := ih (by omega)
    have hTinv := isInvertible_divisorTwist E L j
    have hMinv := isInvertible_tensorObj_invertibleSheaf E (divisorTwist E L j)
    obtain ⟨hdegj⟩ := nonempty_pullbackDivisorTwistIso E k hE L hdeg j
    have h₃ := isZero_rightDerived_one_tensorPushforwardUnit E k e
      (MonoidalCategory.tensorObj
        (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (divisorTwist E L j) (invertibleSheaf' E))
      (d := (n - j) + -1) (by omega) (pullbackTwistIso E k hE (divisorTwist E L j) hdegj)
    have h₁ : IsZero (((moduleGlobalSections X).rightDerived 1).obj
        (((idealShortComplex E).map
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).obj
            (MonoidalCategory.tensorObj
              (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
              (divisorTwist E L j) (invertibleSheaf' E)))).X₁)) :=
      IsZero.of_iso ihz (((moduleGlobalSections X).rightDerived 1).mapIso
        (twistedIdealIso E (divisorTwist E L j)))
    have h₂ := isZero_rightDerived_one_X₂
      (Stacks.Cohomology.AmpleH1.shortExact_map_tensorLeft X
        (MonoidalCategory.tensorObj
          (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
          (divisorTwist E L j) (invertibleSheaf' E))
        (idealShortComplex_shortExact E)) h₁ h₃
    rw [divisorTwist_succ]
    exact IsZero.of_iso h₂ (((moduleGlobalSections X).rightDerived 1).mapIso
      (MonoidalCategoryStruct.rightUnitor
        (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
        (MonoidalCategory.tensorObj
          (C := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
          (divisorTwist E L j) (invertibleSheaf' E))).symm)

end Stacks.Surfaces

end
