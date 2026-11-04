module

public import StacksFrontier.RingTheory.GradedAlgebra.GradedJacobianRecord

/-!
# The recorded relation vector of a lift, and its independence of every choice

Let `P` be a graded `k`-algebra with a weighted graded presentation `k[X_1, …, X_n] → P`,
`X_i ↦ x i`, with relations `F j` weighted homogeneous of weighted degree `e j`, and let `Q` be
a graded algebra over a `k`-algebra `A` with an augmentation `ε : A →ₐ[k] k`, a square-zero
ideal `I ⊇ ker ε` and a reduction `π : Q → P` exhibiting `P` as `Q/IQ`.

A choice of homogeneous lifts `q i ∈ Q_{d i}` of the generators `x i` determines, for each
relation, the obstruction `aeval q F_j^{can}` to the canonical coefficientwise lift of `F j`
being a relation of `Q`. This file assembles the three statements the proof of the
tangent-space half of Stacks 0DVZ (`examples-defos.tex:683`) makes about the vector of those
obstructions:

* the obstruction is a homogeneous element of `I • Q_{e j}`, hence has a unique **graded
  record** `g j ∈ I ⊗[k] P_{e j}`;
* the class of the vector `(g j)` in `W ⊗[k] V` does not depend on the chosen lifts `q` of the
  generators, `W` being the cokernel of the graded Jacobian;
* the vector itself does not depend on the lift `Q` beyond its isomorphism class: an
  isomorphism of graded `A`-algebras over `P` carries one record to the other, unchanged.

Together these are the whole of steps (vii) and (viii) of 0DVZ's proof, for a lift presented as
explicit data rather than as an object of the deformation category.

## Main results

* `GradedAlgebra.mem_smul_grading_of_map_eq_zero`: a homogeneous element killed by the
  reduction lies in `I • Q_e`.
* `GradedAlgebra.aeval_map_algebraMap_mem_smul_grading`: the obstruction to a canonical lift
  being a relation lies in `I • Q_e`.
* `GradedAlgebra.exists_gradedRecord`: the graded record of the obstruction vector exists.
* `GradedAlgebra.gradedJacobianCokernelRecord_eq_of_record`: independence of the chosen lifts
  of the generators.
* `GradedAlgebra.gradedRecord_eq_of_algEquiv`: invariance under an isomorphism of lifts.

## Implementation notes

The comparison map `θ : I ⊗[k] P → Q` is carried as a parameter together with its
characterising property `θ (b ⊗ₜ π y) = b • y` and its injectivity, rather than constructed
here; `Ideal.exists_addMonoidHom_tmul_smul` provides one, and carrying it avoids making a
choice of set-theoretic section canonical. The graded records are then the unique preimages of
`GradedAlgebra.existsUnique_lTensor_subtype_record`.

Invariance under an isomorphism `Φ : Q ≃ₐ[A] Q'` needs no new computation: `θ' = Φ ∘ θ`,
because both sides send `b ⊗ₜ π y` to `b • Φ y`, and `aeval (Φ ∘ q) = Φ ∘ aeval q`.

Nothing here is tagged: these are steps of 0DVZ's *proof*, and Stacks does not tag the steps of
a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace GradedAlgebra

universe u v w t

section CommRingBase

variable {k : Type u} {A : Type v} {P : Type w} {Q : Type t}
  [CommRing k] [CommRing A] [Algebra k A] [CommRing P] [Algebra k P] [CommRing Q] [Algebra A Q]

/-- **A homogeneous element killed by the reduction lies in `I • Q_e`.** The kernel of `π` is
`I • Q`, whose degree-`e` part is `I • Q_e` by
`DirectSum.coe_decompose_mem_smul_grading`. -/
theorem mem_smul_grading_of_map_eq_zero (gradingQ : ℕ → Submodule A Q) [GradedAlgebra gradingQ]
    (π : Q →+* P) (I : Ideal A)
    (hπker : ∀ y : Q, π y = 0 → y ∈ I • (⊤ : Submodule A Q))
    {e' : ℕ} {z : Q} (hz : z ∈ gradingQ e') (h0 : π z = 0) : z ∈ I • gradingQ e' := by
  have h2 := DirectSum.coe_decompose_mem_smul_grading (ℳ := gradingQ) (hπker _ h0) e'
  rwa [DirectSum.decompose_of_mem_same gradingQ hz] at h2

/-- **The obstruction to a canonical lift being a relation lies in `I • Q_e`.** The canonical
coefficientwise lift of a relation `F` of weighted degree `e` has value at `q` a homogeneous
element of degree `e` whose reduction is `aeval x F = 0`. -/
theorem aeval_map_algebraMap_mem_smul_grading (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule A Q) [GradedAlgebra gradingP] [GradedAlgebra gradingQ]
    (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπker : ∀ y : Q, π y = 0 → y ∈ I • (⊤ : Submodule A Q))
    {n : ℕ} {d : Fin n → ℕ} {x : Fin n → P} {q : Fin n → Q}
    (hqmem : ∀ i, q i ∈ gradingQ (d i)) (hq : ∀ i, π (q i) = x i)
    {e' : ℕ} {G : MvPolynomial (Fin n) k} (hG : IsWeightedHomogeneous d G e')
    (hG0 : aeval x G = 0) :
    aeval q (MvPolynomial.map (algebraMap k A) G) ∈ I • gradingQ e' := by
  have hconst := map_algebraMap_of_smul ε π hπsmul
  have hmem : aeval q (MvPolynomial.map (algebraMap k A) G) ∈ gradingQ e' :=
    aeval_mem_grading_of_isWeightedHomogeneous gradingQ hqmem (hG.map _)
  have hzker : π (aeval q (MvPolynomial.map (algebraMap k A) G)) = 0 := by
    rw [MvPolynomial.hom_aeval_eq_aeval_map ε π hconst hq, MvPolynomial.map_map_algebraMap, hG0]
  exact mem_smul_grading_of_map_eq_zero gradingQ π I hπker hmem hzker

/-- **The graded record of the obstruction vector exists.** For each relation `F j` there is a
unique `g j ∈ I ⊗[k] P_{e j}` with `θ (g j) = -aeval q F_j^{can}`; this is the vector Stacks
0DVZ calls `(g_1, …, g_m)`.

The sign is the source's: `F_{ε, j} = F_j^{can} + ε G_j` is a relation of `Q`, so the record of
`ε G_j` is minus the obstruction of the canonical lift. -/
theorem exists_gradedRecord (gradingP : ℕ → Submodule k P) (gradingQ : ℕ → Submodule A Q)
    [GradedAlgebra gradingP] [GradedAlgebra gradingQ] (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A)
    [∀ e', Module.Flat A ↥(gradingQ e')] (hIsq : I * I = ⊥)
    (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I)
    (hπmem : ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → π y ∈ gradingP e')
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔ y ∈ I • (⊤ : Submodule A Q))
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    {n r : ℕ} {d : Fin n → ℕ} {e : Fin r → ℕ} {x : Fin n → P} {q : Fin n → Q}
    (hqmem : ∀ i, q i ∈ gradingQ (d i)) (hq : ∀ i, π (q i) = x i)
    (F : Fin r → MvPolynomial (Fin n) k) (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j))
    (hF0 : ∀ j, aeval x (F j) = 0) :
    ∃ g : (j : Fin r) → (↥I) ⊗[k] ↥(gradingP (e j)),
      ∀ j, θ (LinearMap.lTensor (↥I) (gradingP (e j)).subtype (g j)) =
        -aeval q (MvPolynomial.map (algebraMap k A) (F j)) := by
  choose g hg -- the records, one for each relation
    using fun j => (existsUnique_lTensor_subtype_record gradingP gradingQ ε π I hIsq hIker
      hπmem hπsmul hπsurj hπker θ hθ
      (z := -aeval q (MvPolynomial.map (algebraMap k A) (F j)))
      (Submodule.neg_mem _ (aeval_map_algebraMap_mem_smul_grading gradingP gradingQ ε π I
        hπsmul (fun y hy => (hπker y).mp hy) hqmem hq (hF j) (hF0 j)))).exists
  exact ⟨g, hg⟩

/-- **The record is unchanged by an isomorphism of lifts.** An isomorphism `Φ : Q ≃ₐ[A] Q'` of
graded `A`-algebras compatible with the reductions carries the comparison map `θ` of `Q` to
that of `Q'`, and the obstruction of `q` to the obstruction of `Φ ∘ q`; so the two records are
*equal*, not merely equal modulo the Jacobian. -/
theorem gradedRecord_eq_of_algEquiv {Q' : Type t} [CommRing Q'] [Algebra A Q']
    (gradingP : ℕ → Submodule k P) [GradedAlgebra gradingP] (I : Ideal A)
    (π : Q →+* P) (π' : Q' →+* P) (hπsurj : Function.Surjective π)
    (Φ : Q ≃ₐ[A] Q') (hΦπ : ∀ y, π' (Φ y) = π y)
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (θ' : (↥I) ⊗[k] P →+ Q') (hθ' : ∀ (b : ↥I) (y : Q'), θ' (b ⊗ₜ π' y) = (b : A) • y)
    (hinj' : ∀ e' : ℕ, Function.Injective fun ξ : (↥I) ⊗[k] ↥(gradingP e') =>
      θ' (LinearMap.lTensor (↥I) (gradingP e').subtype ξ))
    {n r : ℕ} {e : Fin r → ℕ} {q : Fin n → Q} (F : Fin r → MvPolynomial (Fin n) k)
    {g : (j : Fin r) → (↥I) ⊗[k] ↥(gradingP (e j))}
    {g' : (j : Fin r) → (↥I) ⊗[k] ↥(gradingP (e j))}
    (hg : ∀ j, θ (LinearMap.lTensor (↥I) (gradingP (e j)).subtype (g j)) =
      -aeval q (MvPolynomial.map (algebraMap k A) (F j)))
    (hg' : ∀ j, θ' (LinearMap.lTensor (↥I) (gradingP (e j)).subtype (g' j)) =
      -aeval (fun i => Φ (q i)) (MvPolynomial.map (algebraMap k A) (F j))) :
    g' = g := by
  have hθΦ : ∀ ξ : (↥I) ⊗[k] P, θ' ξ = Φ (θ ξ) := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul b m =>
        obtain ⟨y, rfl⟩ := hπsurj m
        rw [hθ b y, ← hΦπ y, hθ' b (Φ y), map_smul]
    | add ξ η hξ hη => rw [map_add, map_add, hξ, hη, map_add]
  have haeval : ∀ G : MvPolynomial (Fin n) A, Φ (aeval q G) = aeval (fun i => Φ (q i)) G :=
    fun G => DFunLike.congr_fun (MvPolynomial.comp_aeval q Φ.toAlgHom) G
  refine funext fun j => ?_
  have key : θ' (LinearMap.lTensor (↥I) (gradingP (e j)).subtype (g' j)) =
      θ' (LinearMap.lTensor (↥I) (gradingP (e j)).subtype (g j)) := by
    rw [hg' j, ← haeval, hθΦ, hg j, map_neg]
  exact hinj' (e j) key

end CommRingBase

section FieldBase

variable {k : Type u} {P : Type v} {A Q : Type*} [Field k] [CommRing P] [Algebra k P]
  [CommRing A] [Algebra k A] [CommRing Q] [Algebra A Q]

/-- **The recorded class in `W ⊗[k] V` does not depend on the chosen lifts of the
generators.** Two families of homogeneous lifts of the generators differ by elements of `I • Q`,
so their records differ by the image of the graded Jacobian — the change-of-generators formula
`GradedAlgebra.sub_eq_sum_lTensor_gradedJacobianEntry_of_lift_relation` — which dies in the
cokernel.

This is the independence Stacks 0DVZ asserts when it passes from the vector `(g_1, …, g_m)` to
its class in `W`. -/
theorem gradedJacobianCokernelRecord_eq_of_record (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule A Q) [GradedAlgebra gradingP] [GradedAlgebra gradingQ]
    (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A) [∀ e', Module.Flat A ↥(gradingQ e')]
    (hIsq : I * I = ⊥) (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I)
    (hπmem : ∀ (e' : ℕ) (y : Q), y ∈ gradingQ e' → π y ∈ gradingP e')
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔ y ∈ I • (⊤ : Submodule A Q))
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hθinj : Function.Injective θ)
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ gradingP (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j))
    {q q' : Fin n → Q} (hqmem : ∀ i, q i ∈ gradingQ (d i)) (hq : ∀ i, π (q i) = x i)
    (hq'mem : ∀ i, q' i ∈ gradingQ (d i)) (hq' : ∀ i, π (q' i) = x i)
    {g g' : (j : Fin r) → (↥I) ⊗[k] ↥(gradingP (e j))}
    (hg : ∀ j, θ (LinearMap.lTensor (↥I) (gradingP (e j)).subtype (g j)) =
      -aeval q (MvPolynomial.map (algebraMap k A) (F j)))
    (hg' : ∀ j, θ (LinearMap.lTensor (↥I) (gradingP (e j)).subtype (g' j)) =
      -aeval q' (MvPolynomial.map (algebraMap k A) (F j)))
    {V : Type*} [AddCommGroup V] [Module k V] (φ : (↥I) →ₗ[k] V) :
    gradedJacobianCokernelRecord gradingP hx F hF φ g' =
      gradedJacobianCokernelRecord gradingP hx F hF φ g := by
  have hdiffmem : ∀ i, q' i - q i ∈ I • gradingQ (d i) := fun i =>
    mem_smul_grading_of_map_eq_zero gradingQ π I (fun y hy => (hπker y).mp hy)
      (Submodule.sub_mem _ (hq'mem i) (hqmem i))
      (by rw [map_sub, hq', hq, sub_self])
  choose p hp -- the records of the differences of the two families of lifts
    using fun i => (existsUnique_lTensor_subtype_record gradingP gradingQ ε π I hIsq hIker
      hπmem hπsmul hπsurj hπker θ hθ (hdiffmem i)).exists
  have hqq : ∀ i, q' i - q i ∈ I • (⊤ : Submodule A Q) := fun i =>
    Submodule.smul_mono le_rfl le_top (hdiffmem i)
  have hinj := injective_lTensor_subtype_record gradingP gradingQ ε π I hIsq hIker hπmem
    hπsmul hπsurj hπker θ hθ
  exact gradedJacobianCokernelRecord_eq_of_sub_eq_sum gradingP hx F hF φ
    fun j => sub_eq_sum_lTensor_gradedJacobianEntry_of_lift_relation gradingP hx F hF ε π I θ
      hθ hθinj hIsq hπsmul hπsurj hinj hq hqq hg hg' hp j

end FieldBase

end GradedAlgebra

end
