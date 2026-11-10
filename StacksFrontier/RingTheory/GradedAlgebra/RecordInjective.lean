module

public import StacksFrontier.RingTheory.GradedAlgebra.RecordDeterminesLift
public import StacksFrontier.RingTheory.GradedAlgebra.SquareZeroRecord

/-!
# Lifts with the same recorded class are isomorphic

`GradedAlgebra.exists_algEquiv_of_record_eq` identifies two lifts whose recorded *vectors* are
equal. The map `t` of the proof of the tangent-space half of Stacks 0DVZ
(`examples-defos.tex:683`) records not the vector but its class in `W ⊗[k] M`, `W` being the
cokernel of the graded Jacobian, so injectivity of `t` needs the converse of the
well-definedness: two vectors with the same class differ by the image of the Jacobian, and that
difference is realised by a change of the lifted generators.

Both halves are here. The first is right exactness of `- ⊗ V`, which turns
`GradedAlgebra.gradedJacobianCokernelRecord_eq_of_sub_eq_sum` into an equivalence when the
identification of the recording module with the test module is an isomorphism. The second is
the change-of-generators formula read backwards: given the difference, replace `q i` by
`q i + θ (p i)` and the record moves by exactly that amount.

The conclusion, `GradedAlgebra.exists_algEquiv_of_squareZeroRecord_eq`, is the injectivity
statement of 0DVZ's step (viii) for lifts presented as explicit data: if two lifts of `P` over
`k[M]` record the same element of `W ⊗[k] M`, they are isomorphic as graded `k[M]`-algebras
over `P`.

## Main definitions

* `GradedAlgebra.recordSwapEquiv`: `GradedAlgebra.recordSwap` along an isomorphism, as an
  isomorphism.

## Main results

* `GradedAlgebra.comparison_mem_smul_top`: the comparison map lands in `I • Q`.
* `GradedAlgebra.exists_sub_eq_sum_of_gradedJacobianCokernelRecord_eq`: two records with the
  same class differ by the image of the graded Jacobian.
* `GradedAlgebra.exists_algEquiv_of_squareZeroRecord_eq`: **two lifts recording the same
  element of `W ⊗[k] M` are isomorphic.**

## Implementation notes

Right exactness is `rTensor_exact` applied to `Function.Exact J mkQ`, which holds by
definition of `W` — no flatness is used and no `Submodule.subtype` detour is needed, because
the exact sequence may be taken to end in the Jacobian itself rather than in its range.

Nothing here is tagged: this is step (viii) of 0DVZ's *proof*, and Stacks does not tag the steps
of a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace GradedAlgebra

universe u v t

section Comparison

variable {k : Type u} {A P Q : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing P]
  [Algebra k P] [CommRing Q] [Algebra A Q]

/-- **The comparison map lands in `I • Q`.** Every elementary tensor is `b ⊗ₜ π y` for some `y`
by surjectivity of the reduction, and goes to `b • y`. -/
theorem comparison_mem_smul_top (π : Q →+* P) (I : Ideal A) (θ : (↥I) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y) (hπsurj : Function.Surjective π)
    (ξ : (↥I) ⊗[k] P) : θ ξ ∈ I • (⊤ : Submodule A Q) := by
  induction ξ using TensorProduct.inductionOn with
  | tmul b m =>
      obtain ⟨y, rfl⟩ := hπsurj m
      rw [hθ b y]
      exact Submodule.smul_mem_smul b.2 Submodule.mem_top
  | add ξ η hξ hη => rw [map_add]; exact Submodule.add_mem _ hξ hη

end Comparison

section Exactness

variable {k : Type u} {P : Type v} [Field k] [CommRing P] [Algebra k P]
  {N V : Type*} [AddCommGroup N] [Module k N] [AddCommGroup V] [Module k V]

/-- `GradedAlgebra.recordSwap` along an isomorphism of the recording module with the test
module is itself an isomorphism. -/
def recordSwapEquiv (φ : N ≃ₗ[k] V) (M : Type*) [AddCommGroup M] [Module k M] :
    N ⊗[k] M ≃ₗ[k] M ⊗[k] V :=
  (TensorProduct.comm k N M).trans (TensorProduct.congr (LinearEquiv.refl k M) φ)

/-- `recordSwapEquiv` is `recordSwap`. -/
theorem recordSwapEquiv_apply (φ : N ≃ₗ[k] V) (M : Type*) [AddCommGroup M] [Module k M]
    (ξ : N ⊗[k] M) : recordSwapEquiv φ M ξ = recordSwap φ.toLinearMap M ξ := by
  induction ξ using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη]

/-- **Two records with the same class differ by the image of the graded Jacobian.** This is the
converse of `GradedAlgebra.gradedJacobianCokernelRecord_eq_of_sub_eq_sum`, and it holds because
`- ⊗ V` is right exact and the identification of the recording module with the test module is
an isomorphism. -/
theorem exists_sub_eq_sum_of_gradedJacobianCokernelRecord_eq (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (φ : N ≃ₗ[k] V)
    (g g' : (j : Fin r) → N ⊗[k] ↥(grading (e j)))
    (hrec : gradedJacobianCokernelRecord grading hx F hF φ.toLinearMap g' =
      gradedJacobianCokernelRecord grading hx F hF φ.toLinearMap g) :
    ∃ p : (i : Fin n) → N ⊗[k] ↥(grading (d i)),
      ∀ j, g' j - g j =
        -∑ i : Fin n, LinearMap.lTensor N (gradedJacobianEntry grading hx F hF i j) (p i) := by
  have hexact : Function.Exact (gradedJacobian grading hx F hF)
      (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF))) := by
    intro y
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range
  have hex := rTensor_exact V hexact (Submodule.mkQ_surjective _)
  have hzero : LinearMap.rTensor V
      (Submodule.mkQ (LinearMap.range (gradedJacobian grading hx F hF)))
      (recordSwap φ.toLinearMap ((j : Fin r) → ↥(grading (e j)))
        ((TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm (g' - g))) = 0 := by
    have hsub : gradedJacobianCokernelRecord grading hx F hF φ.toLinearMap (g' - g) = 0 := by
      rw [map_sub, hrec, sub_self]
    exact hsub
  obtain ⟨ζ, hζ⟩ := (hex _).mp hzero
  obtain ⟨ζ, rfl⟩ := (recordSwapEquiv φ _).surjective ζ
  have hassemble : LinearMap.lTensor N (gradedJacobian grading hx F hF) ζ =
      (TensorProduct.piRight k k N fun j : Fin r => ↥(grading (e j))).symm (g' - g) := by
    refine (recordSwapEquiv φ ((j : Fin r) → ↥(grading (e j)))).injective ?_
    rw [recordSwapEquiv_apply, recordSwapEquiv_apply, ← LinearMap.comp_apply,
      recordSwap_comp_lTensor, LinearMap.comp_apply, ← recordSwapEquiv_apply]
    exact hζ
  refine ⟨fun i => -TensorProduct.piRight k k N (fun i' : Fin n => ↥(grading (d i'))) ζ i,
    fun j => ?_⟩
  have hcoord := piRight_lTensor_gradedJacobian grading hx F hF ζ j
  rw [hassemble, LinearEquiv.apply_symm_apply, Pi.sub_apply] at hcoord
  simp only [map_neg, Finset.sum_neg_distrib]
  rw [hcoord, neg_neg]

end Exactness

section SquareZero

variable {k : Type u} {P : Type v} {M : Type*} {Q Q' : Type t} [Field k] [CommRing P]
  [Algebra k P] [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
  [CommRing Q] [Algebra (TrivSqZeroExt k M) Q] [CommRing Q'] [Algebra (TrivSqZeroExt k M) Q']

/-- **Two lifts recording the same element of `W ⊗[k] M` are isomorphic.** This is the
injectivity statement of step (viii) of the proof of Stacks 0DVZ, for lifts presented as
explicit data: the recorded class determines the lift up to an isomorphism of graded
`k[M]`-algebras compatible with the reductions to `P`.

The proof changes the lifted generators of the first lift by the element of `I ⊗[k] P_{d i}`
which right exactness produces from the equality of the classes; after that change the two
*vectors* are equal, and `GradedAlgebra.exists_algEquiv_of_record_eq` applies. -/
theorem exists_algEquiv_of_squareZeroRecord_eq (gradingP : ℕ → Submodule k P)
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
    (hθinj : Function.Injective θ)
    (θ' : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M)) ⊗[k] P →+ Q')
    (hθ' : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k M))) (y : Q'),
      θ' (b ⊗ₜ π' y) = (b : TrivSqZeroExt k M) • y)
    (hθ'inj : Function.Injective θ')
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ gradingP (d i))
    (hxsurj : Function.Surjective (aeval x : MvPolynomial (Fin n) k →ₐ[k] P))
    (F : Fin r → MvPolynomial (Fin n) k) (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j))
    (hF0 : ∀ j, aeval x (F j) = 0)
    (hxker : ∀ G : MvPolynomial (Fin n) k, aeval x G = 0 → G ∈ Ideal.span (Set.range F))
    {w : (((j : Fin r) → ↥(gradingP (e j))) ⧸
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
          (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)).toLinearMap g = w) :
    ∃ Φ : Q ≃ₐ[TrivSqZeroExt k M] Q',
      (∀ y, π' (Φ y) = π y) ∧
      ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → Φ y ∈ gradingQ' e' := by
  have hIsq := TrivSqZeroExt.ker_fstHom_mul_self_eq_bot (R := k) (M := M)
  have hIker := TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom (R := k) (M := M)
  have hεI : ∀ a : TrivSqZeroExt k M, TrivSqZeroExt.fstHom k k M a = 0 →
      a ∈ RingHom.ker (TrivSqZeroExt.fstHom k k M) := fun _ h => h
  have hInil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k M)) :=
    ⟨2, by rw [pow_two, hIsq]; rfl⟩
  -- the two lifts, with their generators and records
  obtain ⟨q, hqmem, hq⟩ := exists_homogeneous_lift_generators gradingP gradingQ π hπmem hπsurj
    d x hx
  obtain ⟨g, hg⟩ := exists_gradedRecord gradingP gradingQ (TrivSqZeroExt.fstHom k k M) π _
    hIsq hIker hπmem hπsmul hπsurj hπker θ hθ hqmem hq F hF hF0
  obtain ⟨q', hq'mem, hq'⟩ := exists_homogeneous_lift_generators gradingP gradingQ' π' hπ'mem
    hπ'surj d x hx
  obtain ⟨g', hg'⟩ := exists_gradedRecord gradingP gradingQ' (TrivSqZeroExt.fstHom k k M) π' _
    hIsq hIker hπ'mem hπ'smul hπ'surj hπ'ker θ' hθ' hq'mem hq' F hF hF0
  -- the difference of the two records is the image of the Jacobian
  obtain ⟨p, hp⟩ := exists_sub_eq_sum_of_gradedJacobianCokernelRecord_eq gradingP hx F hF
    (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := M)) g g'
    ((hw' q' hq'mem hq' g' hg').trans (hw q hqmem hq g hg).symm)
  -- the corrected generators
  have hpmem : ∀ i, θ (LinearMap.lTensor _ (gradingP (d i)).subtype (p i)) ∈ gradingQ (d i) := by
    intro i
    obtain ⟨θdi, hcompat, -, -⟩ := exists_addMonoidHom_tmul_smul_grading gradingP gradingQ
      (TrivSqZeroExt.fstHom k k M) π _ hIsq hIker hπmem hπsmul hπsurj hπker θ hθ (d i)
    rw [← hcompat]
    exact (θdi (p i)).2
  have hptop : ∀ i, θ (LinearMap.lTensor _ (gradingP (d i)).subtype (p i)) ∈
      RingHom.ker (TrivSqZeroExt.fstHom k k M) • (⊤ : Submodule (TrivSqZeroExt k M) Q) :=
    fun i => comparison_mem_smul_top π _ θ hθ hπsurj _
  have hpzero : ∀ i, π (θ (LinearMap.lTensor _ (gradingP (d i)).subtype (p i))) = 0 :=
    fun i => (hπker _).mpr (hptop i)
  set q'' : Fin n → Q :=
    fun i => q i + θ (LinearMap.lTensor _ (gradingP (d i)).subtype (p i)) with hq''def
  have hq''mem : ∀ i, q'' i ∈ gradingQ (d i) :=
    fun i => Submodule.add_mem _ (hqmem i) (hpmem i)
  have hq''red : ∀ i, π (q'' i) = x i := by
    intro i
    rw [hq''def, map_add, hpzero i, add_zero, hq i]
  have hq''diff : ∀ i, q'' i - q i =
      θ (LinearMap.lTensor _ (gradingP (d i)).subtype (p i)) := fun i => by rw [hq''def]; ring
  obtain ⟨g'', hg''⟩ := exists_gradedRecord gradingP gradingQ (TrivSqZeroExt.fstHom k k M) π _
    hIsq hIker hπmem hπsmul hπsurj hπker θ hθ hq''mem hq''red F hF hF0
  -- after the change of generators the two vectors agree
  have hinj := injective_lTensor_subtype_record gradingP gradingQ
    (TrivSqZeroExt.fstHom k k M) π _ hIsq hIker hπmem hπsmul hπsurj hπker θ hθ
  have hchange : ∀ j, g'' j - g j =
      -∑ i : Fin n, LinearMap.lTensor _ (gradedJacobianEntry gradingP hx F hF i j) (p i) :=
    fun j => sub_eq_sum_lTensor_gradedJacobianEntry_of_lift_relation gradingP hx F hF
      (TrivSqZeroExt.fstHom k k M) π _ θ hθ hθinj hIsq hπsmul hπsurj hinj hq
      (fun i => (hq''diff i) ▸ hptop i) hg hg'' (fun i => (hq''diff i).symm) j
  have hgg : g'' = g' := by
    refine funext fun j => ?_
    have h := (hchange j).trans (hp j).symm
    exact sub_left_injective h
  -- the two presentations, and the isomorphism
  have hq''surj := surjective_aeval_of_lift (TrivSqZeroExt.fstHom k k M) π _
    hπsmul (fun y hy => (hπker y).mp hy) hInil hxsurj hq''red
  have hq'surj := surjective_aeval_of_lift (TrivSqZeroExt.fstHom k k M) π' _
    hπ'smul (fun y hy => (hπ'ker y).mp hy) hInil hxsurj hq'
  choose Flift hFlhom hFlmap hFlval using fun j => exists_homogeneous_lift_relation gradingP
    gradingQ (TrivSqZeroExt.fstHom k k M) π _ hπmem hπsmul (fun y hy => (hπker y).mp hy) hIsq
    (fun _ h => h) hx hxsurj hq''mem hq''red (hF j) (hF0 j)
  choose Flift' hFl'hom hFl'map hFl'val using fun j => exists_homogeneous_lift_relation gradingP
    gradingQ' (TrivSqZeroExt.fstHom k k M) π' _ hπ'mem hπ'smul
    (fun y hy => (hπ'ker y).mp hy) hIsq (fun _ h => h) hx hxsurj hq'mem hq' (hF j) (hF0 j)
  obtain ⟨Φ, -, hΦπ, hΦmem⟩ := exists_algEquiv_of_record_eq gradingQ gradingQ'
    (TrivSqZeroExt.fstHom k k M) π π' _ hIsq (fun _ h => h) hπsmul hπ'smul θ hθ hθinj θ' hθ'
    hθ'inj hxker hq''red hq' hq''mem hq'mem hq''surj hq'surj Flift Flift' hFlmap hFlval
    hFl'map hFl'val
    (G := fun j => LinearMap.lTensor _ (gradingP (e j)).subtype (g' j))
    (fun j => by rw [← hgg]; exact hg'' j) hg'
  exact ⟨Φ, hΦπ, hΦmem⟩

end SquareZero

end GradedAlgebra

end
