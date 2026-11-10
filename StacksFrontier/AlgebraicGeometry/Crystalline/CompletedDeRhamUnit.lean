module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZero

/-!
# The connection of the structure module, and its de Rham complex

`Crystalline.CompletedDeRham.complex` is the complex `M ⊗^∧_D Ω^*_D` of
[Stacks, Proposition 60.21.3, Tag 07LG], built from a module `M` with a completed connection. This
file defines the connection `∇ x = 1 ⊗ d x` on `M = D` itself and proves that its de Rham complex
is a complex, which is the hypothesis `Crystalline.CompletedDeRham.IsSquareZero`.

## Main definitions

* `Crystalline.CompletedDeRham.unitConnection`: the connection `∇ x = 1 ⊗ d x` on `D` itself,
  for any additive `d : D → Ω` obeying the Leibniz rule.

## Main results

* `Crystalline.CompletedDeRham.differential_differential_unitConnection_tmul` and
  `Crystalline.CompletedDeRham.differential_differential_unitConnection_toCompletedTensor`: the
  square of the de Rham differential of `unitConnection` vanishes on the image of the uncompleted
  tensor product.
* `Crystalline.CompletedDeRham.isSquareZero_unitConnection`: the de Rham complex of the structure
  module is a complex, with no coordinates and no integrability hypothesis.

## Implementation notes

`Crystalline.CompletedDeRham.isSquareZero_of_isIntegrable` deduces `IsSquareZero` from
integrability together with a *finite coordinate expansion* `∇ m = Σ_j θ_j m ⊗ d x_j`. For the
structure module the coordinate operators are the partial derivatives and the expansion is a
genuine extra datum: it is a choice of coordinates on `D`, which the divided power ring does not
carry. With `∇ x = 1 ⊗ d x` the square of the differential computes in four terms,

`∇²(m ⊗ ω) = 1 ⊗ (ω ∧ d m) ∧ d 1 + 1 ⊗ d (ω ∧ d m) + 1 ⊗ (d ω ∧ d m) + m ⊗ d (d ω)`,

of which the first vanishes because `d 1 = 0`, the last because `d ∘ d = 0`, and the middle two
cancel against each other by the graded Leibniz rule `d (ω ∧ η) = - (d ω) ∧ η` for the *closed*
one-form `η = d m`. So the hypotheses are the exterior identities
`Crystalline.CompletedDeRham.IsGradedExterior` of the forms together with `d 1 = 0` and the
closedness of every exact one-form, and no coordinates and no integrability. Both are properties of
the forms rather than choices: they hold for the completed divided power forms of
[Stacks, Tag 07HZ].

No `@[stacks …]` attribute is placed: this is a step inside the proof of
[Stacks, Proposition 60.21.3, Tag 07LG] and not the statement of a tag.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u v

namespace Crystalline

namespace CompletedDeRham

/-! ### The connection of the structure module -/

section UnitConnection

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (dmap : D → Omega)

/-- **The connection `∇ x = 1 ⊗ d x` of the structure module.**  For `M = D` the Leibniz rule
`∇ (f x) = f ∇ x + x ⊗ d f` *is* the product rule for `d`, so the two hypotheses below are all
that a connection on `D` needs. -/
def unitConnection
    (hadd : ∀ x y : D, dmap (x + y) = dmap x + dmap y)
    (hmul : ∀ x y : D, dmap (x * y) = x • dmap y + y • dmap x) :
    CompletedConnection p D Omega dmap D where
  toFun x := toCompletedTensor p D Omega D ((1 : D) ⊗ₜ[D] dmap x)
  map_add' x y := by rw [hadd, TensorProduct.tmul_add, map_add]
  leibniz' f x := by
    have h : f • ((1 : D) ⊗ₜ[D] dmap x) = f ⊗ₜ[D] dmap x := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [smul_eq_mul, hmul, TensorProduct.tmul_add, map_add, ← map_smul, h,
      ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    simp only [smul_eq_mul, mul_one]

/-- The connection `unitConnection` sends `x` to the image of `1 ⊗ d x` in the completed tensor
product. -/
@[simp] theorem unitConnection_apply
    (hadd : ∀ x y : D, dmap (x + y) = dmap x + dmap y)
    (hmul : ∀ x y : D, dmap (x * y) = x • dmap y + y • dmap x) (x : D) :
    unitConnection p D Omega dmap hadd hmul x =
      toCompletedTensor p D Omega D ((1 : D) ⊗ₜ[D] dmap x) := rfl

end UnitConnection

/-! ### The square of its de Rham differential -/

section UnitSquareZero

variable (p : ℕ) (D : Type u) [CommRing D] (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (dmap : D → Om 1)
  (hadd : ∀ x y : D, dmap (x + y) = dmap x + dmap y)
  (hmul : ∀ x y : D, dmap (x * y) = x • dmap y + y • dmap x)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- **The de Rham differential of the structure module on a pure tensor**:
`∇(m ⊗ ω) = 1 ⊗ (ω ∧ d m) + m ⊗ d ω`. -/
theorem differential_unitConnection_tmul (i : ℕ) (m : D) (ω : Om i) :
    differential p D Om wedge deRham D (unitConnection p D (Om 1) dmap hadd hmul) hleib i
        (toCompletedTensor p D (Om i) D (m ⊗ₜ[D] ω)) =
      toCompletedTensor p D (Om (i + 1)) D ((1 : D) ⊗ₜ[D] wedge i ω (dmap m)) +
        toCompletedTensor p D (Om (i + 1)) D (m ⊗ₜ[D] deRham i ω) := by
  rw [differential_of_tmul, unitConnection_apply, wedgeMap_of_tmul]

/-- **The square of the de Rham differential of the structure module vanishes on a pure
tensor.**  Of the four terms the first is killed by `d 1 = 0`, the last by `d ∘ d = 0`, and the
middle two cancel by the graded Leibniz rule against the closed one-form `d m`. -/
theorem differential_differential_unitConnection_tmul
    (hext : IsGradedExterior D Om wedge deRham) (hone : dmap 1 = 0)
    (hclosed : ∀ x : D, deRham 1 (dmap x) = 0) (i : ℕ) (m : D) (ω : Om i) :
    differential p D Om wedge deRham D (unitConnection p D (Om 1) dmap hadd hmul) hleib (i + 1)
      (differential p D Om wedge deRham D (unitConnection p D (Om 1) dmap hadd hmul) hleib i
        (toCompletedTensor p D (Om i) D (m ⊗ₜ[D] ω))) = 0 := by
  rw [differential_unitConnection_tmul, map_add,
    differential_unitConnection_tmul p D Om wedge deRham dmap hadd hmul hleib (i + 1) 1
      (wedge i ω (dmap m)),
    differential_unitConnection_tmul p D Om wedge deRham dmap hadd hmul hleib (i + 1) m
      (deRham i ω), hone, map_zero, TensorProduct.tmul_zero, map_zero, zero_add,
    hext.deRham_deRham, TensorProduct.tmul_zero, map_zero, add_zero, ← map_add,
    ← TensorProduct.tmul_add, hext.deRham_wedge i ω (dmap m) (hclosed m),
    TensorProduct.tmul_zero, map_zero]

/-- The square of the de Rham differential of the structure module vanishes on the image of the
whole uncompleted tensor product `D ⊗_D Ω^i_D`, not only on pure tensors. -/
theorem differential_differential_unitConnection_toCompletedTensor
    (hext : IsGradedExterior D Om wedge deRham) (hone : dmap 1 = 0)
    (hclosed : ∀ x : D, deRham 1 (dmap x) = 0) (i : ℕ) (y : D ⊗[D] Om i) :
    differential p D Om wedge deRham D (unitConnection p D (Om 1) dmap hadd hmul) hleib (i + 1)
      (differential p D Om wedge deRham D (unitConnection p D (Om 1) dmap hadd hmul) hleib i
        (toCompletedTensor p D (Om i) D y)) = 0 := by
  induction y using TensorProduct.inductionOn with
  | tmul m ω =>
    exact differential_differential_unitConnection_tmul p D Om wedge deRham dmap hadd hmul hleib
      hext hone hclosed i m ω
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]

/-- **The de Rham complex of the structure module is a complex.**  This is the hypothesis
`Crystalline.CompletedDeRham.IsSquareZero` of `Crystalline.CompletedDeRham.complex` for the
connection `∇ x = 1 ⊗ d x` on `M = D`, assuming the exterior identities
`Crystalline.CompletedDeRham.IsGradedExterior` of the forms, `d 1 = 0`, and that every exact
one-form is closed. The exterior identities cannot be dropped, by
`Crystalline.CompletedDeRham.SquareZeroExamples.not_isSquareZero`. -/
theorem isSquareZero_unitConnection (hext : IsGradedExterior D Om wedge deRham)
    (hone : dmap 1 = 0) (hclosed : ∀ x : D, deRham 1 (dmap x) = 0) :
    IsSquareZero p D Om wedge deRham D (unitConnection p D (Om 1) dmap hadd hmul) hleib := by
  intro i
  refine AddMonoidHom.ext fun x => ?_
  refine AdicCompletion.ext fun n => ?_
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ n • ⊤ : Submodule D (D ⊗[D] Om i)) (x.val n)
  have hxz : x.val n = (toCompletedTensor p D (Om i) D z).val n := hz.symm
  rw [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, AdicCompletion.val_zero_apply,
    differential_val_congr p D Om wedge deRham D
      (unitConnection p D (Om 1) dmap hadd hmul) hleib (i + 1) n _ _
      (differential_val_congr p D Om wedge deRham D
        (unitConnection p D (Om 1) dmap hadd hmul) hleib i n x _ hxz),
    differential_differential_unitConnection_toCompletedTensor p D Om wedge deRham dmap hadd hmul
      hleib hext hone hclosed i z, AdicCompletion.val_zero_apply]

end UnitSquareZero

end CompletedDeRham

end Crystalline

end
