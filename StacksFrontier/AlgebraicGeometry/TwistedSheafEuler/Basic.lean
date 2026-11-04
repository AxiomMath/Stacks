module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Twists by invertible modules and their Euler characteristics

For a proper scheme `X` over a field `k`, a coherent `𝒪_X`-module `F` and invertible modules
`L₁, …, L_r`, this file defines the twists `F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r}` and the assertion that
the function

`(n₁, …, n_r) ↦ χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`

is a numerical polynomial of total degree at most `dim Supp F`.

## Main definitions

* `Stacks.TwistedSheafEuler.twistStep` and `Stacks.TwistedSheafEuler.twistedSheaf`: the
  successive twists of `F` by `L i ^{⊗ n i}`.
* `Stacks.TwistedSheafEuler.TensorInvertibleCoherent`: the tensor product of a coherent module
  with an invertible module is coherent.
* `Stacks.TwistedSheafEuler.RepresentsEulerCharacteristics`: a rational polynomial takes the
  Euler characteristics of the twists as its values at integral tuples.
* `Stacks.TwistedSheafEuler.IsEulerNumericalPolynomial`: the Euler characteristics of the twists
  are the values of a rational polynomial of total degree at most the dimension of the support.

## Main results

* `MvPolynomial.eq_of_eval_intCast`: a polynomial over `ℚ` is determined by its values at
  integral tuples.
* `Stacks.TwistedSheafEuler.twistedSheaf_isCoherent`: under `TensorInvertibleCoherent`, every
  twist of a coherent module is coherent.
* `Stacks.TwistedSheafEuler.eq_of_representsEulerCharacteristics`: the polynomial representing
  the Euler characteristics of the twists is unique.
* `Stacks.TwistedSheafEuler.topologicalKrullDim_nonneg`: a nonempty space has Krull dimension at
  least `0`.
* `Stacks.TwistedSheafEuler.isEulerNumericalPolynomial_fin_zero`: the case `r = 0`, for `F` of
  nonempty support.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 0BEJ](https://stacks.math.columbia.edu/tag/0BEJ)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MvPolynomial

/-- A rational polynomial is determined by its values at integral tuples. -/
@[sga "6 V 2.6" "partial"]
theorem eq_of_eval_intCast {σ : Type*} {P Q : MvPolynomial σ ℚ}
    (h : ∀ n : σ → ℤ, eval (fun i ↦ (n i : ℚ)) P = eval (fun i ↦ (n i : ℚ)) Q) : P = Q := by
  refine funext_set (fun _ ↦ Set.range ((↑) : ℤ → ℚ))
    (fun _ ↦ Set.infinite_range_of_injective Int.cast_injective) fun x hx ↦ ?_
  choose n hn using fun i ↦ hx i (Set.mem_univ i)
  obtain rfl : x = fun i ↦ ((n i : ℤ) : ℚ) := _root_.funext fun i ↦ (hn i).symm
  exact h n

end MvPolynomial

namespace Stacks.TwistedSheafEuler

universe u

/-! ### The twist of a module by integer powers of a finite family of invertible modules -/

variable {X : Scheme.{u}} {r : ℕ}

/-- One twisting step: tensor `M` with the `m`th tensor power of the invertible module `N`. -/
@[ega "II 4.5.1"]
def twistStep (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] (m : ℤ) (M : X.Modules) :
    X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
    X.presheaf (forget₂ CommRingCat RingCat)
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩).obj M).obj
    (Stacks.Ample.tensorPowModule X N m)

/-- The successive twists of `F` by integer tensor powers of a finite family of invertible
modules, applied in the order of `Fin r`. -/
@[ega "II 4.5.1" "more general"]
def twistedSheaf (F : X.Modules) (L : Fin r → X.Modules)
    [∀ i, Stacks.Ample.IsInvertibleModule X (L i)] (n : Fin r → ℤ) : X.Modules :=
  (List.finRange r).foldl (fun M i ↦ twistStep (L i) (n i) M) F

/-- With no invertible modules there is nothing to twist by. -/
@[simp]
theorem twistedSheaf_fin_zero (F : X.Modules) (L : Fin 0 → X.Modules)
    [∀ i, Stacks.Ample.IsInvertibleModule X (L i)] (n : Fin 0 → ℤ) :
    twistedSheaf F L n = F := rfl

/-! ### Coherence of the iterated twist reduces to a single tensor product -/

/-- The tensor product of a coherent module on `X` with an invertible module is coherent. -/
def TensorInvertibleCoherent (X : Scheme.{u}) : Prop :=
  ∀ (M N : X.Modules), M.IsCoherent → Stacks.Ample.IsInvertibleModule X N →
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
      X.presheaf (forget₂ CommRingCat RingCat)
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩).obj M).obj N).IsCoherent

/-- If the tensor product of a coherent module with an invertible module on `X` is always
coherent, then every twist of a coherent module `F` is coherent. -/
theorem twistedSheaf_isCoherent (hstep : TensorInvertibleCoherent X) (F : X.Modules)
    [F.IsCoherent] (L : Fin r → X.Modules) [∀ i, Stacks.Ample.IsInvertibleModule X (L i)]
    (n : Fin r → ℤ) : (twistedSheaf F L n).IsCoherent := by
  suffices H : ∀ (l : List (Fin r)) (M : X.Modules), M.IsCoherent →
      (l.foldl (fun M i ↦ twistStep (L i) (n i) M) M).IsCoherent from
    H (List.finRange r) F inferInstance
  intro l
  induction l with
  | nil => exact fun M hM ↦ hM
  | cons i l ih =>
      refine fun M hM ↦ ih _ (hstep M _ hM ?_)
      exact Stacks.Ample.isInvertibleModule_tensorPowModule X (L i) (n i)

/-! ### The Euler characteristics of the twists -/

variable (k : Type u) [Field k]

/-- `P` represents the Euler characteristics of the twists of `F`: at every integral tuple `n`
the value of `P` is `χ(X, F ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`. -/
def RepresentsEulerCharacteristics (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    (L : Fin r → X.Modules) [∀ i, Stacks.Ample.IsInvertibleModule X (L i)]
    [∀ n, (twistedSheaf F L n).IsCoherent] (P : MvPolynomial (Fin r) ℚ) : Prop :=
  ∀ n : Fin r → ℤ, MvPolynomial.eval (fun i ↦ (n i : ℚ)) P =
    ((eulerCharacteristic k f (twistedSheaf F L n) : ℤ) : ℚ)

/-- Two rational polynomials whose values at every integral tuple are the Euler characteristics
of the twists of `F` are equal. -/
theorem eq_of_representsEulerCharacteristics (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    (L : Fin r → X.Modules) [∀ i, Stacks.Ample.IsInvertibleModule X (L i)]
    [∀ n, (twistedSheaf F L n).IsCoherent] {P Q : MvPolynomial (Fin r) ℚ}
    (hP : RepresentsEulerCharacteristics k f F L P)
    (hQ : RepresentsEulerCharacteristics k f F L Q) : P = Q :=
  MvPolynomial.eq_of_eval_intCast fun n ↦ (hP n).trans (hQ n).symm

/-- The Euler characteristics of the integral twists of a coherent module on a proper scheme over
a field are the values of a rational polynomial which is zero or whose total degree is at most
the dimension of the support of the module. -/
def IsEulerNumericalPolynomial (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules)
    (L : Fin r → X.Modules) [∀ i, Stacks.Ample.IsInvertibleModule X (L i)]
    [∀ n, (twistedSheaf F L n).IsCoherent] : Prop :=
  ∃ P : MvPolynomial (Fin r) ℚ,
    (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤ topologicalKrullDim (SheafOfModules.supp F)) ∧
      RepresentsEulerCharacteristics k f F L P

/-- The Krull dimension of a nonempty topological space is at least `0`. -/
theorem topologicalKrullDim_nonneg {T : Type*} [TopologicalSpace T] [Nonempty T] :
    (0 : WithBot ℕ∞) ≤ topologicalKrullDim T :=
  have : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {Classical.arbitrary T}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  Order.krullDim_nonneg

/-- With no invertible modules to twist by, the Euler characteristics of the twists of a
coherent module `F` of nonempty support form a numerical polynomial of total degree at most
`dim Supp F`. -/
theorem isEulerNumericalPolynomial_fin_zero (f : X ⟶ Spec (.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (L : Fin 0 → X.Modules)
    [∀ i, Stacks.Ample.IsInvertibleModule X (L i)]
    [∀ n, (twistedSheaf F L n).IsCoherent] (hF : (SheafOfModules.supp F).Nonempty) :
    IsEulerNumericalPolynomial k f F L := by
  refine ⟨MvPolynomial.C ((eulerCharacteristic k f F : ℤ) : ℚ), Or.inr ?_, fun n ↦ ?_⟩
  · have : Nonempty (SheafOfModules.supp F) := Set.nonempty_coe_sort.mpr hF
    rw [MvPolynomial.totalDegree_C]
    simpa using topologicalKrullDim_nonneg (T := (SheafOfModules.supp F : Set X))
  · simp

end Stacks.TwistedSheafEuler

end
