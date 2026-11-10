module

public import StacksFrontier.RingTheory.GradedAlgebra.LiftRelationVariation

/-!
# The graded refinement of the square-zero comparison map

`Ideal.exists_addMonoidHom_tmul_smul` identifies `I ⊗[k] P` with `I • Q` for a graded
`A`-algebra `Q` with reduction `π : Q → P`, an augmentation `ε : A →ₐ[k] k` and a square-zero
ideal `I ⊇ ker ε`. The proof of the tangent-space half of Stacks 0DVZ
(`examples-defos.tex:683`) needs that identification **degreewise**: the correction term of the
lift of a relation of weighted degree `e j` is an element of `I • Q_{e j}`, and the source
records it as an element of `P_{e j}`, not merely of `P`, because the target of the record is
the product `P_{e_1} ⊕ … ⊕ P_{e_m}` of graded pieces.

This file supplies that refinement. For each degree `e` the same construction applied to the
pair `(Q_e, P_e)` gives a comparison map `I ⊗[k] P_e → Q_e`, and the point of the statement
below is the **compatibility** of that map with the ungraded one: the composite
`I ⊗[k] P_e → Q_e ↪ Q` is the ungraded `θ` precomposed with `I ⊗ (P_e ↪ P)`. Consequently the
ungraded record of an element of `I • Q_e` has a unique preimage in `I ⊗[k] P_e`, and the
change-of-generators formula of `GradedAlgebra.sub_eq_sum_lTensor_mulRight_of_lift_relation`
holds already between those preimages, with the ungraded multiplication maps replaced by the
entries of `GradedAlgebra.gradedJacobian`.

## Main results

* `Submodule.mem_smul_top_subtype_iff`: membership in `I • ⊤` of a submodule read in the
  ambient module.
* `GradedAlgebra.exists_addMonoidHom_tmul_smul_grading`: the degreewise comparison map, with
  its compatibility with the ungraded one, its injectivity and its image.
* `GradedAlgebra.injective_lTensor_subtype_record`: the ungraded record determines the graded
  one.
* `GradedAlgebra.existsUnique_lTensor_subtype_record`: an element of `I • Q_e` has a unique
  record in `I ⊗[k] P_e`.
* `GradedAlgebra.gradedJacobianEntry`: the `(i, j)` entry of the graded Jacobian as a map
  `P_{d i} → P_{e j}`.
* `GradedAlgebra.sub_eq_sum_lTensor_gradedJacobianEntry_of_lift_relation`: the
  change-of-generators formula between graded records.

## Implementation notes

The degreewise map is produced by `Ideal.exists_addMonoidHom_tmul_smul` itself, applied to the
restriction of `π` to the degree-`e` pieces; the two hypotheses of that application which are
not inherited verbatim are surjectivity in degree `e`, which is
`DirectSum.exists_mem_map_eq_of_surjective`, and the description of the kernel in degree `e`,
which is `DirectSum.coe_decompose_mem_smul_grading`. Flatness is required of the graded pieces
rather than of `Q`, which is what the deformation-theoretic application supplies (the pieces
are finite projective over the base).

Nothing here is tagged: this is the graded bookkeeping of step (vii) of the *proof* of
Stacks 0DVZ, and Stacks does not tag the steps of a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open DirectSum MvPolynomial TensorProduct

namespace Submodule

/-- An element of a submodule `N` lies in `I • ⊤` of `N` exactly when it lies in `I • N` as an
element of the ambient module. -/
theorem mem_smul_top_subtype_iff {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (N : Submodule A M) (z : ↥N) :
    z ∈ I • (⊤ : Submodule A ↥N) ↔ (z : M) ∈ I • N := by
  have hmap : (I • (⊤ : Submodule A ↥N)).map N.subtype = I • N := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← hmap]
  exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨y, hy, hyz⟩ => (Subtype.ext hyz : y = z) ▸ hy⟩

end Submodule

namespace GradedAlgebra

universe u v w t

variable {k : Type u} {A : Type v} {P : Type w} {Q : Type t}
  [CommRing k] [CommRing A] [Algebra k A] [CommRing P] [Algebra k P] [CommRing Q] [Algebra A Q]

/-- **The degreewise square-zero comparison map.** Under the hypotheses of
`Ideal.exists_addMonoidHom_tmul_smul` — an augmentation `ε : A →ₐ[k] k`, a square-zero ideal
`I` containing `ker ε` and a reduction `π : Q → P` with kernel `I • Q` — and with the graded
pieces of `Q` flat over `A`, the comparison map refines to each degree: there is an additive
map `I ⊗[k] P_e → Q_e` which is injective, has image `I • Q_e`, and whose composite with the
inclusion `Q_e ↪ Q` is the ungraded `θ` precomposed with `I ⊗ (P_e ↪ P)`.

The compatibility is the whole point: it is what makes the ungraded record of an element of
`I • Q_e` lie in `I ⊗[k] P_e`, which is where the proof of Stacks 0DVZ records the correction
term of a lifted relation. -/
theorem exists_addMonoidHom_tmul_smul_grading (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule A Q) [GradedAlgebra gradingP] [GradedAlgebra gradingQ]
    (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A) [∀ e, Module.Flat A ↥(gradingQ e)]
    (hIsq : I * I = ⊥) (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I)
    (hπmem : ∀ (e : ℕ) (y : Q), y ∈ gradingQ e → π y ∈ gradingP e)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔ y ∈ I • (⊤ : Submodule A Q))
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y) (e : ℕ) :
    ∃ θe : (↥I) ⊗[k] ↥(gradingP e) →+ ↥(gradingQ e),
      (∀ ξ, ((θe ξ : ↥(gradingQ e)) : Q) =
        θ (LinearMap.lTensor (↥I) (gradingP e).subtype ξ)) ∧
      Function.Injective θe ∧
      ∀ z ∈ I • gradingQ e, ∃ ξ, ((θe ξ : ↥(gradingQ e)) : Q) = z := by
  classical
  let πe : ↥(gradingQ e) →+ ↥(gradingP e) :=
    AddMonoidHom.mk' (fun y => ⟨π y, hπmem e y y.2⟩) fun y y' => Subtype.ext (map_add π _ _)
  have hπesurj : Function.Surjective πe := by
    intro m
    obtain ⟨y, hy, hym⟩ := DirectSum.exists_mem_map_eq_of_surjective
      (ℳ := gradingQ) (𝒩 := gradingP) π.toAddMonoidHom hπmem hπsurj m.2
    exact ⟨⟨y, hy⟩, Subtype.ext hym⟩
  have hπeker : ∀ y : ↥(gradingQ e), πe y = 0 ↔ y ∈ I • (⊤ : Submodule A ↥(gradingQ e)) := by
    intro y
    rw [Submodule.mem_smul_top_subtype_iff]
    refine ⟨fun h => ?_,
      fun h => Subtype.ext ((hπker _).mpr (Submodule.smul_mono le_rfl le_top h))⟩
    have h1 := DirectSum.coe_decompose_mem_smul_grading (ℳ := gradingQ)
      ((hπker _).mp (congrArg Subtype.val h)) e
    rwa [DirectSum.decompose_of_mem_same gradingQ y.2] at h1
  obtain ⟨θe, hθe, hθeinj, -, hθesurj⟩ :=
    Ideal.exists_addMonoidHom_tmul_smul (M := ↥(gradingP e)) (N := ↥(gradingQ e))
      ε πe I hIsq hIker (fun a y => Subtype.ext (hπsmul a y)) hπesurj hπeker
  refine ⟨θe, fun ξ => ?_, hθeinj, fun z hz => ?_⟩
  · induction ξ using TensorProduct.inductionOn with
    | tmul b m =>
        obtain ⟨y, rfl⟩ := hπesurj m
        rw [hθe b y, LinearMap.lTensor_tmul, Submodule.coe_smul]
        exact (hθ b y).symm
    | add ξ η hξ hη =>
        rw [map_add, map_add, Submodule.coe_add, hξ, hη, map_add]
  · have hzmem : z ∈ gradingQ e := Submodule.smul_le_right hz
    obtain ⟨ξ, hξ⟩ := hθesurj ⟨z, hzmem⟩
      ((Submodule.mem_smul_top_subtype_iff I (gradingQ e) ⟨z, hzmem⟩).mpr hz)
    exact ⟨ξ, congrArg Subtype.val hξ⟩

/-- **The ungraded record determines the graded one.** The composite of the ungraded comparison
map `θ` with `I ⊗ (P_e ↪ P)` is injective, so an element of `I • Q_e` has at most one record in
`I ⊗[k] P_e`. In particular `I ⊗ (P_e ↪ P)` is itself injective, which is why no flatness of
`I` over `k` is needed. -/
theorem injective_lTensor_subtype_record (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule A Q) [GradedAlgebra gradingP] [GradedAlgebra gradingQ]
    (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A) [∀ e, Module.Flat A ↥(gradingQ e)]
    (hIsq : I * I = ⊥) (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I)
    (hπmem : ∀ (e : ℕ) (y : Q), y ∈ gradingQ e → π y ∈ gradingP e)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔ y ∈ I • (⊤ : Submodule A Q))
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y) (e : ℕ) :
    Function.Injective fun ξ : (↥I) ⊗[k] ↥(gradingP e) =>
      θ (LinearMap.lTensor (↥I) (gradingP e).subtype ξ) := by
  obtain ⟨θe, hcompat, hθeinj, -⟩ := exists_addMonoidHom_tmul_smul_grading gradingP gradingQ
    ε π I hIsq hIker hπmem hπsmul hπsurj hπker θ hθ e
  exact fun ξ η h => hθeinj (Subtype.ext (by rwa [hcompat, hcompat]))

/-- **An element of `I • Q_e` has a unique record in `I ⊗[k] P_e`.** This is the statement the
proof of Stacks 0DVZ uses when it writes that the vector `(g_1, …, g_m)` lies in
`P_{e_1} ⊕ … ⊕ P_{e_m}`. -/
theorem existsUnique_lTensor_subtype_record (gradingP : ℕ → Submodule k P)
    (gradingQ : ℕ → Submodule A Q) [GradedAlgebra gradingP] [GradedAlgebra gradingQ]
    (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A) [∀ e, Module.Flat A ↥(gradingQ e)]
    (hIsq : I * I = ⊥) (hIker : ∀ a : A, a - algebraMap k A (ε a) ∈ I)
    (hπmem : ∀ (e : ℕ) (y : Q), y ∈ gradingQ e → π y ∈ gradingP e)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y)
    (hπsurj : Function.Surjective π)
    (hπker : ∀ y : Q, π y = 0 ↔ y ∈ I • (⊤ : Submodule A Q))
    (θ : (↥I) ⊗[k] P →+ Q) (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    {e : ℕ} {z : Q} (hz : z ∈ I • gradingQ e) :
    ∃! ξ : (↥I) ⊗[k] ↥(gradingP e),
      θ (LinearMap.lTensor (↥I) (gradingP e).subtype ξ) = z := by
  obtain ⟨θe, hcompat, hθeinj, hθesurj⟩ := exists_addMonoidHom_tmul_smul_grading gradingP
    gradingQ ε π I hIsq hIker hπmem hπsmul hπsurj hπker θ hθ e
  obtain ⟨ξ, hξ⟩ := hθesurj z hz
  exact ⟨ξ, (hcompat ξ).symm.trans hξ,
    fun η hη => hθeinj (Subtype.ext ((hcompat η).trans (hη.trans hξ.symm)))⟩

end GradedAlgebra

namespace GradedAlgebra

open MvPolynomial

universe u v

variable {k : Type u} {P : Type v} [Field k] [CommRing P] [Algebra k P]

/-- **The `(i, j)` entry of the graded Jacobian**, as a `k`-linear map from the single graded
piece `P_{d i}` to the single graded piece `P_{e j}`: multiplication by
`(∂F_j/∂X_i)(x)`. It is `GradedAlgebra.gradedJacobianTerm` precomposed with the `i`-th
coordinate inclusion, so no new degree bookkeeping is needed. -/
noncomputable def gradedJacobianEntry (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (i : Fin n) (j : Fin r) :
    grading (d i) →ₗ[k] grading (e j) :=
  LinearMap.codRestrict (grading (e j))
    (LinearMap.mulRight k (aeval x (pderiv i (F j))) ∘ₗ (grading (d i)).subtype)
    fun p => mul_aeval_pderiv_mem_grading grading hx (hF j) i p.2

/-- The defining formula of `gradedJacobianEntry`. -/
@[simp]
theorem gradedJacobianEntry_apply_coe (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (i : Fin n) (j : Fin r)
    (p : ↥(grading (d i))) :
    ((gradedJacobianEntry grading hx F hF i j p : ↥(grading (e j))) : P) =
      (p : P) * aeval x (pderiv i (F j)) :=
  rfl

/-- The entry of the graded Jacobian is the restriction of multiplication by
`(∂F_j/∂X_i)(x)`, which is the map appearing in the ungraded change-of-generators formula
`GradedAlgebra.sub_eq_sum_lTensor_mulRight_of_lift_relation`. -/
theorem subtype_comp_gradedJacobianEntry (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j)) (i : Fin n) (j : Fin r) :
    (grading (e j)).subtype ∘ₗ gradedJacobianEntry grading hx F hF i j =
      LinearMap.mulRight k (aeval x (pderiv i (F j))) ∘ₗ (grading (d i)).subtype :=
  rfl

variable {A Q : Type*} [CommRing A] [Algebra k A] [CommRing Q] [Algebra A Q]

/-- **The change-of-generators formula between graded records.** Exactly
`GradedAlgebra.sub_eq_sum_lTensor_mulRight_of_lift_relation`, but between the graded records
`gvec j, gvec' j ∈ I ⊗[k] P_{e j}` and `pvec i ∈ I ⊗[k] P_{d i}` of
`GradedAlgebra.existsUnique_lTensor_subtype_record`, with the ungraded multiplication maps
replaced by the entries of the graded Jacobian. This is the form in which the formula says
that the recorded vector is well defined modulo the image of `GradedAlgebra.gradedJacobian`.

The injectivity hypothesis is supplied by
`GradedAlgebra.injective_lTensor_subtype_record`. -/
theorem sub_eq_sum_lTensor_gradedJacobianEntry_of_lift_relation (grading : ℕ → Submodule k P)
    [GradedAlgebra grading] {n r : ℕ} {x : Fin n → P} {d : Fin n → ℕ} {e : Fin r → ℕ}
    (hx : ∀ i, x i ∈ grading (d i)) (F : Fin r → MvPolynomial (Fin n) k)
    (hF : ∀ j, IsWeightedHomogeneous d (F j) (e j))
    (ε : A →ₐ[k] k) (π : Q →+* P) (I : Ideal A) (θ : (↥I) ⊗[k] P →+ Q)
    (hθ : ∀ (b : ↥I) (y : Q), θ (b ⊗ₜ π y) = (b : A) • y)
    (hθinj : Function.Injective θ) (hIsq : I * I = ⊥)
    (hπsmul : ∀ (a : A) (y : Q), π (a • y) = ε a • π y) (hπsurj : Function.Surjective π)
    (hinj : ∀ e' : ℕ, Function.Injective fun ξ : (↥I) ⊗[k] ↥(grading e') =>
      θ (LinearMap.lTensor (↥I) (grading e').subtype ξ))
    {q q' : Fin n → Q} (hq : ∀ i, π (q i) = x i)
    (hqq : ∀ i, q' i - q i ∈ I • (⊤ : Submodule A Q))
    {gvec gvec' : (j : Fin r) → (↥I) ⊗[k] ↥(grading (e j))}
    {pvec : (i : Fin n) → (↥I) ⊗[k] ↥(grading (d i))}
    (hg : ∀ j, θ (LinearMap.lTensor (↥I) (grading (e j)).subtype (gvec j)) =
      -aeval q (MvPolynomial.map (algebraMap k A) (F j)))
    (hg' : ∀ j, θ (LinearMap.lTensor (↥I) (grading (e j)).subtype (gvec' j)) =
      -aeval q' (MvPolynomial.map (algebraMap k A) (F j)))
    (hp : ∀ i, θ (LinearMap.lTensor (↥I) (grading (d i)).subtype (pvec i)) = q' i - q i)
    (j : Fin r) :
    gvec' j - gvec j =
      -∑ i : Fin n, LinearMap.lTensor (↥I) (gradedJacobianEntry grading hx F hF i j) (pvec i) := by
  have hungraded := sub_eq_sum_lTensor_mulRight_of_lift_relation (P := P) (F := F)
    (g := fun j' => LinearMap.lTensor (↥I) (grading (e j')).subtype (gvec j'))
    (g' := fun j' => LinearMap.lTensor (↥I) (grading (e j')).subtype (gvec' j'))
    (p := fun i => LinearMap.lTensor (↥I) (grading (d i)).subtype (pvec i))
    ε π I θ hθ hθinj hIsq hπsmul hπsurj hq hqq hg hg' hp j
  have inner : LinearMap.lTensor (↥I) (grading (e j)).subtype
        (-∑ i : Fin n,
          LinearMap.lTensor (↥I) (gradedJacobianEntry grading hx F hF i j) (pvec i)) =
      -∑ i : Fin n, LinearMap.lTensor (↥I) (LinearMap.mulRight k (aeval x (pderiv i (F j))))
        (LinearMap.lTensor (↥I) (grading (d i)).subtype (pvec i)) := by
    rw [map_neg, map_sum]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, subtype_comp_gradedJacobianEntry,
      LinearMap.lTensor_comp, LinearMap.comp_apply]
  refine hinj (e j) ?_
  dsimp only
  rw [map_sub, hungraded, inner]

end GradedAlgebra

end
