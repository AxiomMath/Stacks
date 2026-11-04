module

public import StacksFrontier.Algebra.TrivSqZeroExtKernel
public import StacksFrontier.RingTheory.GradedAlgebra.LiftRecordInvariant

/-!
# The record of a lift over a square-zero extension, as a single well-defined element

Specialise the lifting machinery to the base `A = k[M] = TrivSqZeroExt k M`, which is the base
at which the tangent space of a deformation category is evaluated (Stacks 06IB). There the
augmentation is `TrivSqZeroExt.fstHom`, its kernel `I` is square zero, splits off and is `M`
itself (`StacksFrontier/Algebra/TrivSqZeroExtKernel.lean`), so every hypothesis of the lifting
results is discharged and the record of a lift `Q` is an element of `W ⊗[k] M` for `W` the
cokernel of the graded Jacobian.

The two statements below are what makes that element well defined and what pins down its
dependence on `Q`:

* **one element for every choice**: there is a single `w ∈ W ⊗[k] M` which *every* family of
  homogeneous lifts of the generators and *every* record of the resulting obstructions
  produces;
* **isomorphism invariance**: isomorphic lifts produce the same `w`.

Together these are the whole of the map `t` of the proof of Stacks 0DVZ
(`examples-defos.tex:683`) at the level of algebra: a lift of `P` over `k[M]` has a canonical
element of `W ⊗[k] M` attached to it, depending on the lift only through its isomorphism class.
What is left of `t` is the passage from an object of the deformation category to this data and
the descent of the map through `Deformation.isomorphismClasses`.

## Main results

* `GradedAlgebra.exists_squareZeroRecord`: a single element of `W ⊗[k] M` is produced by every
  choice of lifted generators and every record of the obstructions.
* `GradedAlgebra.squareZeroRecord_eq_of_algEquiv`: isomorphic lifts produce the same element.

## Implementation notes

Both statements are propositions, deliberately: the element is produced by `Classical.choose`
from `GradedAlgebra.exists_gradedRecord` and that choice must not leak into the statement, so
the element is existentially quantified and characterised by what every choice gives. A
consumer defines its map by choosing the witness.

Nothing here is tagged: this is the construction of `t` in step (vii) of 0DVZ's *proof*, and
Stacks does not tag the steps of a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace GradedAlgebra

universe u v t

variable {k : Type u} {P : Type v} {M : Type*} {Q : Type t} [Field k] [CommRing P] [Algebra k P]
  [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
  [CommRing Q] [Algebra (TrivSqZeroExt k M) Q]

/-- **The record of a lift over a square-zero extension is one element of `W ⊗[k] M`.** Every
family of homogeneous lifts `q` of the generators, and every record `g` of the resulting
obstructions, produces the *same* element: the class of the vector `(g j)` in the cokernel of
the graded Jacobian, tensored with `M`.

This is the well-definedness the proof of Stacks 0DVZ needs in order to speak of "the" element
of `W` attached to a deformation over `k[M]`; the two choices it eliminates are the two
ambiguities of the source's step (vii), the lifted relations (through injectivity of the
comparison map) and the lifted generators (through the change-of-generators formula). -/
theorem exists_squareZeroRecord (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule (TrivSqZeroExt k M) Q) [GradedAlgebra gradingP]
    [GradedAlgebra gradingQ] [Module.Flat (TrivSqZeroExt k M) Q]
    [∀ e', Module.Flat (TrivSqZeroExt k M) ↥(gradingQ e')] (π : Q →+* P)
    (hπmem : ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → π y ∈ gradingP e')
    (hπsmul : ∀ (a : TrivSqZeroExt k M) (y : Q), π (a • y) = TrivSqZeroExt.fst a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔
      y ∈ RingHom.ker (TrivSqZeroExt.fstHom k k M) • (⊤ : Submodule (TrivSqZeroExt k M) Q))
    (θ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q),
      θ (b ⊗ₜ π y) = (b : TrivSqZeroExt k M) • y)
    (hθinj : Function.Injective θ)
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ gradingP (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (hF0 : ∀ j, aeval x (F j) = 0) :
    ∃ w : (((j : Fin r) → ↥(gradingP (e j))) ⧸
      LinearMap.range (gradedJacobian gradingP hx F hF)) ⊗[k] M,
      ∀ q : Fin n → Q, (∀ i, q i ∈ gradingQ (d i)) → (∀ i, π (q i) = x i) →
        ∀ g : (j : Fin r) → ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] ↥(gradingP (e j)),
          (∀ j, θ (LinearMap.lTensor _ (gradingP (e j)).subtype (g j)) =
            -aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M)) (F j))) →
          gradedJacobianCokernelRecord gradingP hx F hF
            (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)).toLinearMap g = w := by
  obtain ⟨q₀, hq₀mem, hq₀⟩ := exists_homogeneous_lift_generators gradingP gradingQ π hπmem
    hπsurj d x hx
  obtain ⟨g₀, hg₀⟩ := exists_gradedRecord gradingP gradingQ (TrivSqZeroExt.fstHom k k M) π
    (RingHom.ker (TrivSqZeroExt.fstHom k k M)) TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπmem hπsmul hπsurj hπker θ hθ hq₀mem hq₀
    F hF hF0
  refine ⟨gradedJacobianCokernelRecord gradingP hx F hF
    (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)).toLinearMap g₀, fun q hqmem hq g hg => ?_⟩
  exact gradedJacobianCokernelRecord_eq_of_record gradingP gradingQ
    (TrivSqZeroExt.fstHom k k M) π (RingHom.ker (TrivSqZeroExt.fstHom k k M))
    TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπmem hπsmul hπsurj hπker θ hθ hθinj hx F hF
    hq₀mem hq₀ hqmem hq hg₀ hg _

/-- **Isomorphic lifts record the same element of `W ⊗[k] M`.** The witnesses of
`exists_squareZeroRecord` for two lifts related by an isomorphism of graded `k[M]`-algebras over
`P` agree, because such an isomorphism carries one family of lifted generators to another and
the records are then literally equal (`GradedAlgebra.gradedRecord_eq_of_algEquiv`).

This is the last of the three things the proof of Stacks 0DVZ needs of the map `t`: that it is
defined on isomorphism classes. -/
theorem squareZeroRecord_eq_of_algEquiv {Q' : Type t} [CommRing Q']
    [Algebra (TrivSqZeroExt k M) Q'] (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule (TrivSqZeroExt k M) Q)
    (gradingQ' : ℕ → Submodule (TrivSqZeroExt k M) Q') [GradedAlgebra gradingP]
    [GradedAlgebra gradingQ] [GradedAlgebra gradingQ']
    [Module.Flat (TrivSqZeroExt k M) Q] [Module.Flat (TrivSqZeroExt k M) Q']
    [∀ e', Module.Flat (TrivSqZeroExt k M) ↥(gradingQ e')]
    [∀ e', Module.Flat (TrivSqZeroExt k M) ↥(gradingQ' e')]
    (π : Q →+* P) (π' : Q' →+* P)
    (hπmem : ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → π y ∈ gradingP e')
    (hπsmul : ∀ (a : TrivSqZeroExt k M) (y : Q), π (a • y) = TrivSqZeroExt.fst a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔
      y ∈ RingHom.ker (TrivSqZeroExt.fstHom k k M) • (⊤ : Submodule (TrivSqZeroExt k M) Q))
    (hπ'mem : ∀ (e' : ℕ) (y : Q'), y ∈ gradingQ' e' → π' y ∈ gradingP e')
    (hπ'smul : ∀ (a : TrivSqZeroExt k M) (y : Q'), π' (a • y) = TrivSqZeroExt.fst a • π' y)
    (hπ'surj : Function.Surjective π')
    (hπ'ker : ∀ y : Q', π' y = 0 ↔
      y ∈ RingHom.ker (TrivSqZeroExt.fstHom k k M) • (⊤ : Submodule (TrivSqZeroExt k M) Q'))
    (θ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q),
      θ (b ⊗ₜ π y) = (b : TrivSqZeroExt k M) • y)
    (θ' : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] P →+ Q')
    (hθ' : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q'),
      θ' (b ⊗ₜ π' y) = (b : TrivSqZeroExt k M) • y)
    (Φ : Q ≃ₐ[TrivSqZeroExt k M] Q') (hΦπ : ∀ y, π' (Φ y) = π y)
    (hΦmem : ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → Φ y ∈ gradingQ' e')
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ gradingP (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (hF0 : ∀ j, aeval x (F j) = 0)
    {w w' : (((j : Fin r) → ↥(gradingP (e j))) ⧸
      LinearMap.range (gradedJacobian gradingP hx F hF)) ⊗[k] M}
    (hw : ∀ q : Fin n → Q, (∀ i, q i ∈ gradingQ (d i)) → (∀ i, π (q i) = x i) →
      ∀ g : (j : Fin r) → ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] ↥(gradingP (e j)),
        (∀ j, θ (LinearMap.lTensor _ (gradingP (e j)).subtype (g j)) =
          -aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M)) (F j))) →
        gradedJacobianCokernelRecord gradingP hx F hF
          (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)).toLinearMap g = w)
    (hw' : ∀ q : Fin n → Q', (∀ i, q i ∈ gradingQ' (d i)) → (∀ i, π' (q i) = x i) →
      ∀ g : (j : Fin r) → ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] ↥(gradingP (e j)),
        (∀ j, θ' (LinearMap.lTensor _ (gradingP (e j)).subtype (g j)) =
          -aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k M)) (F j))) →
        gradedJacobianCokernelRecord gradingP hx F hF
          (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)).toLinearMap g = w') :
    w' = w := by
  obtain ⟨q, hqmem, hq⟩ := exists_homogeneous_lift_generators gradingP gradingQ π hπmem hπsurj
    d x hx
  obtain ⟨g, hg⟩ := exists_gradedRecord gradingP gradingQ (TrivSqZeroExt.fstHom k k M) π
    (RingHom.ker (TrivSqZeroExt.fstHom k k M)) TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπmem hπsmul hπsurj hπker θ hθ hqmem hq
    F hF hF0
  have hΦqmem : ∀ i, Φ (q i) ∈ gradingQ' (d i) := fun i => hΦmem _ _ (hqmem i)
  have hΦq : ∀ i, π' (Φ (q i)) = x i := fun i => (hΦπ (q i)).trans (hq i)
  obtain ⟨g', hg'⟩ := exists_gradedRecord gradingP gradingQ'
    (TrivSqZeroExt.fstHom k k M) π' (RingHom.ker (TrivSqZeroExt.fstHom k k M))
    TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπ'mem hπ'smul hπ'surj hπ'ker θ' hθ'
    hΦqmem hΦq F hF hF0
  have hinj' := injective_lTensor_subtype_record gradingP gradingQ'
    (TrivSqZeroExt.fstHom k k M) π' (RingHom.ker (TrivSqZeroExt.fstHom k k M))
    TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom hπ'mem hπ'smul hπ'surj hπ'ker θ' hθ'
  have hgg : g' = g := gradedRecord_eq_of_algEquiv gradingP
    (RingHom.ker (TrivSqZeroExt.fstHom k k M)) π π' hπsurj Φ hΦπ θ hθ θ' hθ' hinj' F hg hg'
  rw [← hw' _ hΦqmem hΦq g' hg', ← hw q hqmem hq g hg, hgg]

end GradedAlgebra

end
