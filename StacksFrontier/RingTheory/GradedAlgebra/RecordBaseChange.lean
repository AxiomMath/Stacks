module

public import StacksFrontier.RingTheory.GradedAlgebra.SquareZeroRecord

/-!
# How the recorded relation vector changes under base change of the lift

The naturality hypothesis of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` asks that the map `t`
commute with the base change of a lift along a map `V → V'` of test modules. This file proves
the statement that underlies it, and the shape of the answer is the one
`GradedAlgebra.gradedJacobianCokernelFunctor` was built for: the record of the base-changed lift
is the image of the record under `W ⊗ (-)` applied to that map, with no cokernel functoriality
anywhere.

Concretely, let `ρ : Q → Q'` be a ring map over a map of bases `σ : A → A'` carrying the
square-zero ideal `I` into `I'` by `ψ`, compatible with the two reductions to `P`. Then:

* the comparison maps intertwine, `θ' ∘ (ψ ⊗ id_P) = ρ ∘ θ`;
* the record of `(Q', ρ ∘ q)` is `(ψ ⊗ id)` of the record of `(Q, q)`;
* so the class in the cokernel is `W ⊗ (-)` applied to the original class, provided the
  identification of `I'` with `V'` restricts along `ψ` to the given map `V → V'`.

The last of these is the naturality statement, for lifts presented as explicit data.

## Main results

* `MvPolynomial.ringHom_aeval_eq_aeval_map`: naturality of multivariate evaluation along a ring
  map of the coefficients and of the target.
* `GradedAlgebra.map_rTensor_eq_of_ringHom`: the comparison maps intertwine.
* `GradedAlgebra.rTensor_gradedJacobianCokernelRecord`: the cokernel record is natural in the
  module carrying the record.
* `GradedAlgebra.gradedRecord_eq_rTensor_of_ringHom`: the record of the base-changed lift is the
  image of the record.
* `GradedAlgebra.squareZeroRecord_eq_lTensor_of_ringHom`: **the naturality statement**.

## Implementation notes

`MvPolynomial.ringHom_aeval_eq_aeval_map` is the analogue, for a ring map of coefficients, of
`MvPolynomial.hom_aeval_eq_aeval_map`, whose coefficient map is an augmentation
`A →ₐ[k] k`; the proof is the same `MvPolynomial.ringHom_ext`, and neither is an instance of the
other because the target of the coefficient map differs.

The two naturalities of `GradedAlgebra.gradedJacobianCokernelRecord` — in the test module
`V` (`GradedAlgebra.lTensor_gradedJacobianCokernelRecord`) and in the module `N` carrying the
record (here) — are what make the naturality statement a one-line composition once the record
of the base-changed lift is known.

Nothing here is tagged: this is the naturality of `t` in step (vii) of 0DVZ's *proof*, and
Stacks does not tag the steps of a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace MvPolynomial

universe u v

/-- **Naturality of multivariate evaluation along a ring map.** If `ρ : Q → Q'` takes the
constants of `A` to the constants of `A'` along `σ : A → A'` and takes the points `q i` to the
points `q' i`, then it takes the value at `q` of a polynomial over `A` to the value at `q'` of
its coefficientwise image. -/
theorem ringHom_aeval_eq_aeval_map {A A' Q Q' : Type*} [CommRing A] [CommRing A'] [CommRing Q]
    [CommRing Q'] [Algebra A Q] [Algebra A' Q'] (σ : A →+* A') (ρ : Q →+* Q')
    (hconst : ∀ a : A, ρ (algebraMap A Q a) = algebraMap A' Q' (σ a))
    {n : ℕ} {q : Fin n → Q} {q' : Fin n → Q'} (hq : ∀ i, ρ (q i) = q' i)
    (G : MvPolynomial (Fin n) A) :
    ρ (aeval q G) = aeval q' (MvPolynomial.map σ G) := by
  have hcomp : ρ.comp (aeval q : MvPolynomial (Fin n) A →ₐ[A] Q).toRingHom =
      ((aeval q' : MvPolynomial (Fin n) A' →ₐ[A'] Q').toRingHom).comp (MvPolynomial.map σ) :=
    MvPolynomial.ringHom_ext (fun a => by simpa using hconst a) fun i => by simpa using hq i
  exact DFunLike.congr_fun hcomp G

end MvPolynomial

namespace GradedAlgebra

universe u v t

variable {k : Type u} {P : Type v} [Field k] [CommRing P] [Algebra k P]

section Intertwine

variable {A A' Q Q' : Type*} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A']
  [CommRing Q] [Algebra A Q] [CommRing Q'] [Algebra A' Q']

/-- **The comparison maps intertwine along a base change of the lift.** If `ρ : Q → Q'` is
compatible with the two reductions to `P` and carries the action of `b ∈ I` into the action of
`ψ b ∈ I'`, then `θ' ∘ (ψ ⊗ id_P) = ρ ∘ θ`: both send `b ⊗ₜ π y` to `(ψ b) • ρ y`. -/
theorem map_rTensor_eq_of_ringHom {I : Ideal A} {I' : Ideal A'} (π : Q →+* P) (π' : Q' →+* P)
    (hπsurj : Function.Surjective π) (θ : (↥I) ⊗[k] P →+ Q) (θ' : (↥I') ⊗[k] P →+ Q')
    (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hθ' : ∀ (b : ↥I') (y : Q'), θ' (b ⊗ₜ π' y) = (b : A') • y)
    (ρ : Q →+* Q') (ψ : (↥I) →ₗ[k] (↥I')) (hρπ : ∀ y, π' (ρ y) = π y)
    (hρsmul : ∀ (b : ↥I) (y : Q), ((ψ b : A')) • ρ y = ρ ((b : A) • y))
    (ξ : (↥I) ⊗[k] P) : θ' (LinearMap.rTensor P ψ ξ) = ρ (θ ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => rw [map_zero (LinearMap.rTensor P ψ), map_zero θ', map_zero θ, map_zero ρ]
  | tmul b m =>
      obtain ⟨y, rfl⟩ := hπsurj m
      rw [LinearMap.rTensor_tmul, hθ b y, ← hρπ y, hθ' (ψ b) (ρ y), hρsmul]
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη, map_add θ, map_add ρ]

end Intertwine

section CokernelRecord

variable {N N' V : Type*} [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N']
  [AddCommGroup V] [Module k V]

/-- A map of the module carrying the records commutes with taking coordinates. -/
theorem piRight_rTensor (ψ : N →ₗ[k] N') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Mi : ι → Type*) [∀ i, AddCommGroup (Mi i)] [∀ i, Module k (Mi i)]
    (ξ : N ⊗[k] ((i : ι) → Mi i)) (i : ι) :
    TensorProduct.piRight k k N' Mi (LinearMap.rTensor ((i : ι) → Mi i) ψ ξ) i =
      LinearMap.rTensor (Mi i) ψ (TensorProduct.piRight k k N Mi ξ i) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul b p =>
      have hL : TensorProduct.piRight k k N' Mi
          (LinearMap.rTensor ((i : ι) → Mi i) ψ (b ⊗ₜ p)) i = ψ b ⊗ₜ p i := rfl
      have hR : TensorProduct.piRight k k N Mi (b ⊗ₜ p) i = b ⊗ₜ p i := rfl
      rw [hL, hR, LinearMap.rTensor_tmul]
  | add ξ η hξ hη => simp only [map_add, Pi.add_apply, hξ, hη]

/-- Assembling a family of records commutes with a map of the module carrying them. -/
theorem piRight_symm_rTensor (ψ : N →ₗ[k] N') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Mi : ι → Type*) [∀ i, AddCommGroup (Mi i)] [∀ i, Module k (Mi i)]
    (g : (i : ι) → N ⊗[k] Mi i) :
    (TensorProduct.piRight k k N' Mi).symm (fun i => LinearMap.rTensor (Mi i) ψ (g i)) =
      LinearMap.rTensor ((i : ι) → Mi i) ψ ((TensorProduct.piRight k k N Mi).symm g) := by
  refine (TensorProduct.piRight k k N' Mi).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  refine funext fun i => ?_
  rw [piRight_rTensor ψ Mi _ i, LinearEquiv.apply_symm_apply]

/-- `recordSwap` along a map of the module carrying the record. -/
theorem recordSwap_comp_rTensor (ψ : N →ₗ[k] N') (φ' : N' →ₗ[k] V) (M : Type*)
    [AddCommGroup M] [Module k M] :
    recordSwap φ' M ∘ₗ LinearMap.rTensor M ψ = recordSwap (φ' ∘ₗ ψ) M := by
  refine TensorProduct.ext' fun b m => ?_
  rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, recordSwap_tmul, recordSwap_tmul,
    LinearMap.comp_apply]

/-- **The cokernel record is natural in the module carrying the record**: pushing the records
forward along `ψ : N → N'` and then identifying `N'` with the test module is the same as
identifying `N` with the test module along the composite. -/
theorem rTensor_gradedJacobianCokernelRecord (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (ψ : N →ₗ[k] N') (φ' : N' →ₗ[k] V)
    (g : (j : Fin r) → N ⊗[k] ↥(grading (e j))) :
    gradedJacobianCokernelRecord grading hx F hF φ'
        (fun j => LinearMap.rTensor ↥(grading (e j)) ψ (g j)) =
      gradedJacobianCokernelRecord grading hx F hF (φ' ∘ₗ ψ) g := by
  have e1 : gradedJacobianCokernelRecord grading hx F hF φ'
        (fun j => LinearMap.rTensor ↥(grading (e j)) ψ (g j)) =
      LinearMap.rTensor V (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF)))
        (recordSwap φ' ((j : Fin r) → ↥(grading (e j)))
          ((TensorProduct.piRight k k N' fun j : Fin r => ↥(grading (e j))).symm
            fun j => LinearMap.rTensor ↥(grading (e j)) ψ (g j))) := rfl
  have e2 : gradedJacobianCokernelRecord grading hx F hF (φ' ∘ₗ ψ) g =
      LinearMap.rTensor V (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF)))
        (recordSwap (φ' ∘ₗ ψ) ((j : Fin r) → ↥(grading (e j)))
          ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm g)) := rfl
  have e3 : recordSwap φ' ((j : Fin r) → ↥(grading (e j)))
        (LinearMap.rTensor ((j : Fin r) → ↥(grading (e j))) ψ
          ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm g)) =
      recordSwap (φ' ∘ₗ ψ) ((j : Fin r) → ↥(grading (e j)))
        ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm g) := by
    rw [← LinearMap.comp_apply, recordSwap_comp_rTensor]
  rw [e1, e2, piRight_symm_rTensor ψ (fun j : Fin r => ↥(grading (e j))) g, e3]

end CokernelRecord

section SquareZero

variable {M M' : Type*} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
  [AddCommGroup M'] [Module k M'] [Module kᵐᵒᵖ M'] [IsCentralScalar k M']
  {Q Q' : Type t} [CommRing Q] [Algebra (TrivSqZeroExt k M) Q] [CommRing Q']
  [Algebra (TrivSqZeroExt k M') Q']

/-- **The record of the base-changed lift is the image of the record.** With the comparison maps
intertwined, the unique record of the obstruction of `(Q', ρ ∘ q)` is the image under
`ψ ⊗ id` of the record of `(Q, q)`. -/
theorem gradedRecord_eq_rTensor_of_ringHom (gradingP : ℕ → Submodule k P)
    (gradingQ' : ℕ → Submodule (TrivSqZeroExt k M') Q') [GradedAlgebra gradingP]
    [GradedAlgebra gradingQ'] [∀ e', Module.Flat (TrivSqZeroExt k M') ↥(gradingQ' e')]
    (π : Q →+* P) (π' : Q' →+* P) (hπsurj : Function.Surjective π)
    (hπ'mem : ∀ (e' : ℕ) (y : Q'), y ∈ gradingQ' e' → π' y ∈ gradingP e')
    (hπ'smul : ∀ (a : TrivSqZeroExt k M') (y : Q'), π' (a • y) = TrivSqZeroExt.fst a • π' y)
    (hπ'surj : Function.Surjective π')
    (hπ'ker : ∀ y : Q', π' y = 0 ↔
      y ∈ RingHom.ker (TrivSqZeroExt.fstHom k k M') • (⊤ : Submodule (TrivSqZeroExt k M') Q'))
    (θ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q),
      θ (b ⊗ₜ π y) = (b : TrivSqZeroExt k M) • y)
    (θ' : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M')) ⊗[k] P →+ Q')
    (hθ' : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M'))) (y : Q'),
      θ' (b ⊗ₜ π' y) = (b : TrivSqZeroExt k M') • y)
    (ρ : Q →+* Q')
    (ψ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) →ₗ[k]
      ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M')))
    (hρπ : ∀ y, π' (ρ y) = π y)
    (hρsmul : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q),
      ((ψ b : TrivSqZeroExt k M')) • ρ y = ρ ((b : TrivSqZeroExt k M) • y))
    {n r : ℕ} {e : Fin r → ℕ} {q : Fin n → Q} (F : Fin r → MvPolynomial (Fin n) k)
    (hρaeval : ∀ j, ρ (aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M)) (F j))) =
      aeval (fun i => ρ (q i))
        (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M')) (F j)))
    {g : (j : Fin r) → ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] ↥(gradingP (e j))}
    {g' : (j : Fin r) → ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M')) ⊗[k] ↥(gradingP (e j))}
    (hg : ∀ j, θ (LinearMap.lTensor _ (gradingP (e j)).subtype (g j)) =
      -aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M)) (F j)))
    (hg' : ∀ j, θ' (LinearMap.lTensor _ (gradingP (e j)).subtype (g' j)) =
      -aeval (fun i => ρ (q i))
        (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M')) (F j))) :
    g' = fun j => LinearMap.rTensor ↥(gradingP (e j)) ψ (g j) := by
  have hinj' := injective_lTensor_subtype_record gradingP gradingQ'
    (TrivSqZeroExt.fstHom k k M') π' (RingHom.ker (TrivSqZeroExt.fstHom k k M'))
    TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπ'mem hπ'smul hπ'surj hπ'ker θ' hθ'
  refine funext fun j => ?_
  have hswap : LinearMap.lTensor _ (gradingP (e j)).subtype
        (LinearMap.rTensor ↥(gradingP (e j)) ψ (g j)) =
      LinearMap.rTensor P ψ (LinearMap.lTensor _ (gradingP (e j)).subtype (g j)) := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.comp_apply,
      LinearMap.rTensor_comp_lTensor]
  have key : θ' (LinearMap.lTensor _ (gradingP (e j)).subtype (g' j)) =
      θ' (LinearMap.lTensor _ (gradingP (e j)).subtype
        (LinearMap.rTensor ↥(gradingP (e j)) ψ (g j))) := by
    rw [hg' j, hswap, map_rTensor_eq_of_ringHom π π' hπsurj θ θ' hθ hθ' ρ ψ hρπ hρsmul, hg j,
      map_neg, hρaeval j]
  exact hinj' (e j) key

/-- **The naturality statement.** If the identification of `I'` with the new test module
restricts along `ψ` to the given map `V → V'`, then the element recorded by the base-changed
lift is `W ⊗ (-)` applied to the element recorded by the original lift. This is the hypothesis
`ht` of `Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` for lifts
presented as explicit data.

No functoriality of a cokernel is used: the record is pushed along `ψ` on the left factor by
`GradedAlgebra.rTensor_gradedJacobianCokernelRecord`, and the identification is changed on the
right factor by `GradedAlgebra.lTensor_gradedJacobianCokernelRecord`. -/
theorem squareZeroRecord_eq_lTensor_of_ringHom (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule (TrivSqZeroExt k M) Q)
    (gradingQ' : ℕ → Submodule (TrivSqZeroExt k M') Q') [GradedAlgebra gradingP]
    [GradedAlgebra gradingQ] [GradedAlgebra gradingQ']
    [Module.Flat (TrivSqZeroExt k M) Q]
    [∀ e', Module.Flat (TrivSqZeroExt k M) ↥(gradingQ e')]
    [∀ e', Module.Flat (TrivSqZeroExt k M') ↥(gradingQ' e')]
    (π : Q →+* P) (π' : Q' →+* P)
    (hπmem : ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → π y ∈ gradingP e')
    (hπsmul : ∀ (a : TrivSqZeroExt k M) (y : Q), π (a • y) = TrivSqZeroExt.fst a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔
      y ∈ RingHom.ker (TrivSqZeroExt.fstHom k k M) • (⊤ : Submodule (TrivSqZeroExt k M) Q))
    (hπ'mem : ∀ (e' : ℕ) (y : Q'), y ∈ gradingQ' e' → π' y ∈ gradingP e')
    (hπ'smul : ∀ (a : TrivSqZeroExt k M') (y : Q'), π' (a • y) = TrivSqZeroExt.fst a • π' y)
    (hπ'surj : Function.Surjective π')
    (hπ'ker : ∀ y : Q', π' y = 0 ↔
      y ∈ RingHom.ker (TrivSqZeroExt.fstHom k k M') • (⊤ : Submodule (TrivSqZeroExt k M') Q'))
    (θ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q),
      θ (b ⊗ₜ π y) = (b : TrivSqZeroExt k M) • y)
    (θ' : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M')) ⊗[k] P →+ Q')
    (hθ' : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M'))) (y : Q'),
      θ' (b ⊗ₜ π' y) = (b : TrivSqZeroExt k M') • y)
    (ρ : Q →+* Q')
    (ψ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) →ₗ[k]
      ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M')))
    (hρπ : ∀ y, π' (ρ y) = π y)
    (hρsmul : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q),
      ((ψ b : TrivSqZeroExt k M')) • ρ y = ρ ((b : TrivSqZeroExt k M) • y))
    (hρmem : ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → ρ y ∈ gradingQ' e')
    (f : M →ₗ[k] M')
    (hψf : (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M')).toLinearMap ∘ₗ ψ =
      f ∘ₗ (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)).toLinearMap)
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ gradingP (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (hF0 : ∀ j, aeval x (F j) = 0)
    (hρaeval : ∀ (q : Fin n → Q) (j : Fin r),
      ρ (aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M)) (F j))) =
        aeval (fun i => ρ (q i))
          (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M')) (F j)))
    {w : (((j : Fin r) → ↥(gradingP (e j))) ⧸
      LinearMap.range (gradedJacobian gradingP hx F hF)) ⊗[k] M}
    {w' : (((j : Fin r) → ↥(gradingP (e j))) ⧸
      LinearMap.range (gradedJacobian gradingP hx F hF)) ⊗[k] M'}
    (hw : ∀ q : Fin n → Q, (∀ i, q i ∈ gradingQ (d i)) → (∀ i, π (q i) = x i) →
      ∀ g : (j : Fin r) → ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] ↥(gradingP (e j)),
        (∀ j, θ (LinearMap.lTensor _ (gradingP (e j)).subtype (g j)) =
          -aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M)) (F j))) →
        gradedJacobianCokernelRecord gradingP hx F hF
          (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)).toLinearMap g = w)
    (hw' : ∀ q : Fin n → Q', (∀ i, q i ∈ gradingQ' (d i)) → (∀ i, π' (q i) = x i) →
      ∀ g : (j : Fin r) → ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M')) ⊗[k] ↥(gradingP (e j)),
        (∀ j, θ' (LinearMap.lTensor _ (gradingP (e j)).subtype (g j)) =
          -aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M')) (F j))) →
        gradedJacobianCokernelRecord gradingP hx F hF
          (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M')).toLinearMap g = w') :
    w' = LinearMap.lTensor _ f w := by
  obtain ⟨q, hqmem, hq⟩ := exists_homogeneous_lift_generators gradingP gradingQ π hπmem hπsurj
    d x hx
  obtain ⟨g, hg⟩ := exists_gradedRecord gradingP gradingQ (TrivSqZeroExt.fstHom k k M) π
    (RingHom.ker (TrivSqZeroExt.fstHom k k M)) TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπmem hπsmul hπsurj hπker θ hθ hqmem hq
    F hF hF0
  have hqmem' : ∀ i, ρ (q i) ∈ gradingQ' (d i) := fun i => hρmem _ _ (hqmem i)
  have hq' : ∀ i, π' (ρ (q i)) = x i := fun i => (hρπ (q i)).trans (hq i)
  obtain ⟨g', hg'⟩ := exists_gradedRecord gradingP gradingQ' (TrivSqZeroExt.fstHom k k M') π'
    (RingHom.ker (TrivSqZeroExt.fstHom k k M')) TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπ'mem hπ'smul hπ'surj hπ'ker θ' hθ'
    (q := fun i => ρ (q i)) hqmem' hq' F hF hF0
  have hgg : g' = fun j => LinearMap.rTensor ↥(gradingP (e j)) ψ (g j) :=
    gradedRecord_eq_rTensor_of_ringHom gradingP gradingQ' π π' hπsurj hπ'mem hπ'smul hπ'surj
      hπ'ker θ hθ θ' hθ' ρ ψ hρπ hρsmul F (fun j => hρaeval q j) hg hg'
  rw [← hw' (fun i => ρ (q i)) hqmem' hq' g' hg', ← hw q hqmem hq g hg, hgg,
    rTensor_gradedJacobianCokernelRecord gradingP hx F hF ψ _ g, hψf,
    ← lTensor_gradedJacobianCokernelRecord gradingP hx F hF _ f g]

end SquareZero

end GradedAlgebra

end
