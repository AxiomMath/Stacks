module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialFirstTwistFiber
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialTwistFiber

/-!
# The associated-sheaf functor on `Proj` is not monoidal

Let `S = k[x, y, z]` be graded by the weights `1`, `2` and `3`. Multiplication gives a canonical
map `S(1)₍z₎ ⊗_{S₍z₎} S(2)₍z₎ → S(3)₍z₎` of the degree-zero localized twists at `z`, and it is
not an isomorphism: the fibres at the vertex ideal have dimensions `2 · 2 = 4` on the left and
`1` on the right.

## Main definitions

* `Stacks.WeightedPolynomialSituation.localizedTwistTensorMap`: multiplication
  `S(1)₍z₎ ⊗ S(2)₍z₎ → S(3)₍z₎`.

## Main results

* `Stacks.WeightedPolynomialSituation.localizedTwist_mul_le`: products of fractions of the first
  and second twists lie in the third twist, which is what makes the map above exist.
* `Stacks.WeightedPolynomialSituation.localizedTwistTensorMap_tmul`: on pure tensors the map
  multiplies the fractions.
* `Stacks.WeightedPolynomialSituation.not_bijective_localizedTwistTensorMap`: it is not
  bijective.

## Implementation notes

The codomain of the multiplication map is the third localized twist itself, not merely the
ambient localization `S_z`; that is what makes the dimension count of the fibres at the vertex
ideal applicable. The three fibre dimensions are
`WeightedPolynomialSituation.finrank_firstTwistLocalization_fiber`,
`Stacks.WeightedPolynomialSituation.finrank_secondTwistLocalization_quotient_vertexIdeal` and
`Stacks.WeightedPolynomialSituation.finrank_thirdTwistLocalization_quotient_vertexIdeal`; the
first is stated over the residue field and the other two over the quotient by the maximal ideal,
so the two fields are compared by `finrank_tensor_baseChange_of_algEquiv` below.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.WeightedPolynomialSituation

private theorem finrank_tensor_baseChange_of_algEquiv
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    (eKL : K ≃ₐ[K] L) (M : Type*) [AddCommGroup M] [Module R M] :
    Module.finrank K (TensorProduct R K M) = Module.finrank L (TensorProduct R L M) := by
  let equiv : TensorProduct R K M ≃ₗ[K] TensorProduct R L M :=
    TensorProduct.AlgebraTensorModule.congr eKL.toLinearEquiv (LinearEquiv.refl R M)
  have hK := equiv.finrank_eq
  have hKL := lift_rank_eq_of_equiv_equiv eKL.toRingEquiv.toRingHom
    (AddEquiv.refl (TensorProduct R L M)) eKL.toRingEquiv.bijective (by
      intro r x
      change r • x = eKL r • x
      have hr : eKL r = algebraMap K L r := by simpa using eKL.commutes r
      simp [hr])
  have hdim := congrArg Cardinal.toNat hKL
  exact hK.trans (by simpa [Module.finrank] using hdim)

/-- Base change of a module to `R ⧸ I` has the same rank as its quotient by `I • ⊤`. -/
private theorem finrank_tensor_quotient_eq_finrank_quotient_smul
    {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    Module.finrank (R ⧸ I) (TensorProduct R (R ⧸ I) M) =
      Module.finrank (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
  ((TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).finrank_eq

/-- Products of fractions in the first and second twists lie in the third twist. -/
public theorem localizedTwist_mul_le (E : WeightedPolynomialSituation) :
    E.firstTwistLocalization * E.secondTwistLocalization ≤ E.localizedTwist 3 := by
  let L := Localization (Submonoid.powers E.z)
  let g₁ : Set L := {z | ∃ (i e : ℕ) (p : E.S),
    (e : ℤ) = (i * 3 : ℕ) + 1 ∧ p ∈ E.naturalGrading e ∧
      z = Localization.mk p ⟨E.z ^ i, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) i⟩}
  let g₂ : Set L := {z | ∃ (j e : ℕ) (p : E.S),
    (e : ℤ) = (j * 3 : ℕ) + 2 ∧ p ∈ E.naturalGrading e ∧
      z = Localization.mk p ⟨E.z ^ j, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) j⟩}
  let g₃ : Set L := {z | ∃ (k e : ℕ) (p : E.S),
    (e : ℤ) = (k * 3 : ℕ) + 3 ∧ p ∈ E.naturalGrading e ∧
      z = Localization.mk p ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩}
  let : IsScalarTower E.R L L := IsScalarTower.right
  change (Submodule.span E.R g₁) * (Submodule.span E.R g₂) ≤ Submodule.span E.R g₃
  rw [Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, ei, p, he₁, hp, rfl⟩, _, ⟨j, ej, q, he₂, hq, rfl⟩, rfl⟩
  have he₁' : ei = i * 3 + 1 := by exact_mod_cast he₁
  have he₂' : ej = j * 3 + 2 := by exact_mod_cast he₂
  have hdeg : ei + ej = 3 * (i + j) + 3 := by omega
  have hprod : p * q ∈ E.naturalGrading (3 * (i + j) + 3) := by
    simpa [hdeg] using (SetLike.mul_mem_graded hp hq)
  apply Submodule.subset_span
  refine ⟨i + j, 3 * (i + j) + 3, p * q, ?_, hprod, ?_⟩
  · exact_mod_cast (by ring : 3 * (i + j) + 3 = (i + j) * 3 + 3)
  · beta_reduce
    rw [Localization.mk_mul]
    congr 1
    apply Subtype.ext
    simp [pow_add]

/-- The canonical multiplication map on degree-zero localized twists. -/
public noncomputable def localizedTwistTensorMap (E : WeightedPolynomialSituation) :
    E.firstTwistLocalization ⊗[E.R] E.secondTwistLocalization →ₗ[E.R] E.localizedTwist 3 :=
  (Submodule.inclusion (localizedTwist_mul_le E)).comp
    (Submodule.mulMap' E.firstTwistLocalization E.secondTwistLocalization)

/-- On pure tensors the canonical map multiplies the localized fractions. -/
public theorem localizedTwistTensorMap_tmul (E : WeightedPolynomialSituation)
    (m : E.firstTwistLocalization) (n : E.secondTwistLocalization) :
    ((localizedTwistTensorMap E) (m ⊗ₜ[E.R] n) : Localization (Submonoid.powers E.z)) =
      m.1 * n.1 := by
  simp [localizedTwistTensorMap, Submodule.val_mulMap'_tmul]

/-- **Stacks Project, Tag 01ML.** The canonical multiplication map
`M₍z₎ ⊗_{S₍z₎} N₍z₎ → S(3)₍z₎` is not an isomorphism: the fibres at the vertex ideal have
dimensions `2 · 2 = 4` on the left and `1` on the right.

This is the conclusion the source's own argument reaches.  The remark's headline — that the sheaf
morphism of Tag 01MK,
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafTensorMap`, is therefore not
an isomorphism — is a further step, over the stalk of the tensor sheaf at the point of `D₊(z)` cut
out by the vertex ideal, and is still not taken here.  The headline itself is proved, from a
different witness, by `Stacks.EvenWeightProj.not_isIso_associatedModuleSheafTensorMap`. -/
public theorem not_bijective_localizedTwistTensorMap (E : WeightedPolynomialSituation) :
    ¬ Function.Bijective (localizedTwistTensorMap E) := by
  intro hbij
  let : E.vertexIdeal.IsMaximal := vertexIdeal_isMaximal E
  let K := E.R ⧸ E.vertexIdeal
  let : Field K := Ideal.Quotient.field E.vertexIdeal
  let L := E.vertexIdeal.ResidueField
  let residueEquiv : K ≃ₐ[K] L :=
    AlgEquiv.ofBijective (Algebra.ofId K L)
      (Ideal.bijective_algebraMap_quotient_residueField E.vertexIdeal)
  let A := E.firstTwistLocalization
  let B := E.secondTwistLocalization
  let C := E.localizedTwist 3
  let e : A ⊗[E.R] B ≃ₗ[E.R] C := LinearEquiv.ofBijective (localizedTwistTensorMap E) hbij
  let eTensor : TensorProduct E.R K (A ⊗[E.R] B) ≃ₗ[K] TensorProduct E.R K C :=
    LinearEquiv.baseChange E.R K _ _ e
  have hsrc : Module.finrank K (TensorProduct E.R K (A ⊗[E.R] B)) = 4 := by
    let d : TensorProduct E.R K (A ⊗[E.R] B) ≃ₗ[K]
        (TensorProduct E.R K A) ⊗[K] (TensorProduct E.R K B) :=
      TensorProduct.AlgebraTensorModule.distribBaseChange E.R K A B
    have hA : Module.finrank K (TensorProduct E.R K A) = 2 := by
      rw [finrank_tensor_baseChange_of_algEquiv residueEquiv A]
      simpa [L, A] using finrank_firstTwistLocalization_fiber E
    have hB : Module.finrank K (TensorProduct E.R K B) = 2 := by
      simpa [K, B] using (finrank_tensor_quotient_eq_finrank_quotient_smul E.vertexIdeal B).trans
        (finrank_secondTwistLocalization_quotient_vertexIdeal E)
    rw [d.finrank_eq, Module.finrank_tensorProduct, hA, hB]
  have htgt : Module.finrank K (TensorProduct E.R K C) = 1 := by
    simpa [K, C] using (finrank_tensor_quotient_eq_finrank_quotient_smul E.vertexIdeal C).trans
      (finrank_thirdTwistLocalization_quotient_vertexIdeal E)
  have hdim := eTensor.finrank_eq
  rw [hsrc, htgt] at hdim
  norm_num at hdim

end Stacks.WeightedPolynomialSituation

end
