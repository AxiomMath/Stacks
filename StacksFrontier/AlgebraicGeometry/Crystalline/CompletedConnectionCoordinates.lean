module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeHom
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFreeFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsExist
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsUnique
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorSumComplete
public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# The coordinate operators of a completed connection against a finite basis

Let `Ω` be a `D`-module with a finite basis `b`, and let `∇ : M → M ⊗̂_D Ω` be a completed
connection on a `p`-adically complete module.  The canonical map `M ⊗_D Ω → M ⊗̂_D Ω` is then
bijective (`Crystalline.bijective_toCompletedTensor_of_finite_basis`), so `∇ m` has coordinates
in `M`: these are the **coordinate operators** `θ_j`, `Crystalline.coordOp`, with
`∇ m = ∑_j θ_j(m) ⊗ b j`.  This module records what the comparison of
[Stacks, Lemma 60.17.5, Tag 07L5] uses of them:

* they realise the coordinate expansion and are the only operators that do
  (`Crystalline.isCoordinateExpansion_coordOp`, `Crystalline.eq_coordOp_of_isCoordinateExpansion`);
* they are additive and obey the Leibniz rule `θ_j(a m) = a θ_j(m) + ∂_j(a) m`, where
  `∂_j a` is the `j`-th coordinate of `d a`;
* a horizontal map commutes with them, and conversely a linear map commuting with them is
  horizontal (`Crystalline.coordOp_map`, `Crystalline.horizontal_of_coordOp`);
* the four conditions of a `Crystalline.Pair` are carried along a horizontal linear equivalence
  (`Crystalline.Pair.ofHorizontalEquiv`).

It also proves the density principle that pins maps out of `p`-adic completions:
`Crystalline.addMonoidHom_ext_adicCompletion`.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u uI

namespace Crystalline

/-! ### Additive maps out of a `p`-adic completion -/

section Ext

variable (p : ℕ) {R S : Type u} [CommRing R] [CommRing S] {X Y : Type u} [AddCommGroup X]
  [Module R X] [AddCommGroup Y] [Module S Y]

/-- An element of a `p`-adic completion differs from the image of a representative of its level
`n` by an element of `(p)^n` times the completion. -/
theorem sub_of_mem_pow_smul_top (z : AdicCompletion (pAdicIdeal (A := R) p) X) (n : ℕ) (t : X)
    (ht : z.val n = Submodule.Quotient.mk t) :
    z - AdicCompletion.of (pAdicIdeal (A := R) p) X t ∈
      (pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R (AdicCompletion (pAdicIdeal (A := R) p) X)) := by
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    map_sub, AdicCompletion.eval_apply, AdicCompletion.eval_of, ht]
  exact sub_self _

/-- **Two additive maps out of a `p`-adic completion into a `p`-adically separated module agree
as soon as they agree on the image of the uncompleted module**: an element differs from the image
of a representative by an element of `p^n`, which both maps carry into `p^n`. -/
theorem addMonoidHom_ext_adicCompletion (hY : IsHausdorff (pAdicIdeal (A := S) p) Y)
    {f g : AdicCompletion (pAdicIdeal (A := R) p) X →+ Y}
    (h : ∀ x : X, f (AdicCompletion.of (pAdicIdeal (A := R) p) X x) =
      g (AdicCompletion.of (pAdicIdeal (A := R) p) X x)) : f = g := by
  ext z
  rw [← sub_eq_zero]
  refine hY.haus _ fun n ↦ ?_
  rw [SModEq.sub_mem, sub_zero]
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
  have hz := sub_of_mem_pow_smul_top p z n t ht.symm
  have hf := PAdicCompletion.map_mem_pow_smul_top p R S (f - g) n hz
  have : f z - g z = (f - g) (z - AdicCompletion.of (pAdicIdeal (A := R) p) X t) := by
    rw [map_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, h t, sub_self, sub_zero]
  rw [this]
  exact hf

end Ext

/-! ### The coordinate operators -/

section Coordinates

variable (p : ℕ) {D : Type u} [CommRing D] {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] {ι : Type uI} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι D Omega)
  {d : D → Omega} {M : Type u} [AddCommGroup M] [Module D M]
  (hM : IsPAdicallyComplete p D M) (nabla : CompletedConnection p D Omega d M)

/-- **The completed tensor product is the uncompleted one** against a finite basis of `Ω`, for a
`p`-adically complete module. -/
def completedTensorEquivOfBasis : (M ⊗[D] Omega) ≃ₗ[D] CompletedTensor p D Omega M :=
  LinearEquiv.ofBijective (toCompletedTensor p D Omega M)
    (bijective_toCompletedTensor_of_finite_basis p D Omega M b hM)

omit [DecidableEq ι] in
/-- The equivalence `Crystalline.completedTensorEquivOfBasis` is the canonical map. -/
@[simp] theorem completedTensorEquivOfBasis_apply (z : M ⊗[D] Omega) :
    completedTensorEquivOfBasis p b hM z = toCompletedTensor p D Omega M z := rfl

/-- **The `j`-th coordinate operator** of a completed connection against a finite basis: the
`j`-th coordinate of `∇ m`, read in the uncompleted tensor product. -/
def coordOp (j : ι) (m : M) : M :=
  tensorCoordinate b j ((completedTensorEquivOfBasis p b hM).symm (nabla m))

/-- **The connection is the sum of its coordinates**: `∇ m = ∑_j θ_j(m) ⊗ b j`. -/
theorem nabla_eq_sum_coordOp (m : M) :
    nabla m = toCompletedTensor p D Omega M (∑ j, coordOp p b hM nabla j m ⊗ₜ[D] b j) := by
  simp only [coordOp]
  rw [sum_tensorCoordinate_tmul b, ← completedTensorEquivOfBasis_apply p b hM,
    LinearEquiv.apply_symm_apply]

/-- The coordinate operators realise the coordinate expansion. -/
theorem isCoordinateExpansion_coordOp {dx : ι → Omega} (hdx : ∀ i, dx i = b i) :
    IsCoordinateExpansion p D Omega dx nabla (coordOp p b hM nabla) := by
  intro m
  let := completedTensorTopology p D Omega M
  have hz : ∑ i, toCompletedTensor p D Omega M (coordOp p b hM nabla i m ⊗ₜ[D] dx i) =
      nabla m := by
    simp only [hdx]
    rw [← map_sum, ← nabla_eq_sum_coordOp]
  exact hz ▸ hasSum_fintype _

/-- **The coordinate operators are the only ones realising the coordinate expansion.** -/
theorem eq_coordOp_of_isCoordinateExpansion {dx : ι → Omega} (hdx : ∀ i, dx i = b i)
    {theta : ι → (M → M)} (hco : IsCoordinateExpansion p D Omega dx nabla theta) :
    theta = coordOp p b hM nabla :=
  eq_of_isCoordinateExpansion p D Omega M hco (isCoordinateExpansion_coordOp p b hM nabla hdx) b
    hdx hM.toIsHausdorff

/-- The coordinate operators are additive. -/
theorem coordOp_add (j : ι) (m m' : M) :
    coordOp p b hM nabla j (m + m') = coordOp p b hM nabla j m + coordOp p b hM nabla j m' := by
  simp only [coordOp, nabla.map_add, map_add]

/-- The `j`-th coordinate of `m ⊗ ω` is `(b.repr ω j) • m`. -/
theorem tensorCoordinate_tmul (j : ι) (m : M) (omega : Omega) :
    tensorCoordinate b j (m ⊗ₜ[D] omega) = b.repr omega j • m := by
  conv_lhs => rw [← b.sum_repr omega, TensorProduct.tmul_sum]
  rw [map_sum, Finset.sum_eq_single j]
  · rw [TensorProduct.tmul_smul, map_smul, tensorCoordinate_tmul_basis_self]
  · intro i _ hij
    rw [TensorProduct.tmul_smul, map_smul, tensorCoordinate_tmul_basis_of_ne b hij, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The Leibniz rule for the coordinate operators**: `θ_j(a m) = a θ_j(m) + ∂_j(a) m`, with
`∂_j a` the `j`-th coordinate of `d a`. -/
theorem coordOp_smul (j : ι) (a : D) (m : M) :
    coordOp p b hM nabla j (a • m) =
      a • coordOp p b hM nabla j m + b.repr (d a) j • m := by
  simp only [coordOp, nabla.leibniz, map_add, map_smul]
  rw [← completedTensorEquivOfBasis_apply p b hM, LinearEquiv.symm_apply_apply,
    tensorCoordinate_tmul]

/-- The coordinate operators carry `p^n M` into itself. -/
theorem coordOp_mem_pPowSmul (j : ι) {n : ℕ} {m : M} (h : m ∈ pPowSmul p D M n) :
    coordOp p b hM nabla j m ∈ pPowSmul p D M n :=
  map_mem_pPowSmul p D M (coordOp_add p b hM nabla j) h

variable {N : Type u} [AddCommGroup N] [Module D N] (hN : IsPAdicallyComplete p D N)
  (nablaN : CompletedConnection p D Omega d N)

/-- **A horizontal map commutes with the coordinate operators.** -/
theorem coordOp_map (φ : M →ₗ[D] N)
    (hφ : ∀ m, nablaN (φ m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega))) (nabla m)) (j : ι) (m : M) :
    coordOp p b hN nablaN j (φ m) = φ (coordOp p b hM nabla j m) := by
  have h1 : nablaN (φ m) = toCompletedTensor p D Omega N
      (TensorProduct.map φ LinearMap.id
        ((completedTensorEquivOfBasis p b hM).symm (nabla m))) := by
    have hz : nabla m = toCompletedTensor p D Omega M
        ((completedTensorEquivOfBasis p b hM).symm (nabla m)) :=
      ((completedTensorEquivOfBasis p b hM).apply_symm_apply _).symm
    rw [hφ]
    conv_lhs => rw [hz]
    exact AdicCompletion.map_of (pAdicIdeal (A := D) p)
      (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega))) _
  simp only [coordOp]
  rw [h1, ← completedTensorEquivOfBasis_apply p b hN, LinearEquiv.symm_apply_apply]
  generalize (completedTensorEquivOfBasis p b hM).symm (nabla m) = z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x omega => simp [tensorCoordinate_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- **A linear map commuting with the coordinate operators is horizontal.** -/
theorem horizontal_of_coordOp (φ : M →ₗ[D] N)
    (hφ : ∀ j m, coordOp p b hN nablaN j (φ m) = φ (coordOp p b hM nabla j m)) (m : M) :
    nablaN (φ m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map φ (LinearMap.id (R := D) (M := Omega))) (nabla m) := by
  rw [nabla_eq_sum_coordOp p b hN nablaN, nabla_eq_sum_coordOp p b hM nabla,
    AdicCompletion.map_of]
  congr 1
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [TensorProduct.map_tmul, hφ]; rfl

end Coordinates

/-! ### The four conditions along a horizontal equivalence -/

section Transfer

variable (p : ℕ) {D : Type u} [CommRing D] {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] {ι : Type uI} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι D Omega)
  {dx : ι → Omega} (hdx : ∀ i, dx i = b i) {d : D → Omega}

/-- **A completed connection on a `p`-adically complete module which is carried to a pair by a
horizontal linear equivalence is a pair**: the coordinate operators of the two are conjugate
(`Crystalline.coordOp_map`), so integrability and topological quasi-nilpotence pass across. -/
def Pair.ofHorizontalEquiv (P : Pair.{u, u, uI, u} p D Omega dx d) {N : Type u}
    [AddCommGroup N] [Module D N] (hN : IsPAdicallyComplete p D N)
    (nablaN : CompletedConnection p D Omega d N) (e : P.carrier ≃ₗ[D] N)
    (he : ∀ m, nablaN (e m) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e.toLinearMap (LinearMap.id (R := D) (M := Omega))) (P.nabla m)) :
    Pair.{u, u, uI, u} p D Omega dx d where
  carrier := N
  isPAdicallyComplete := hN
  nabla := nablaN
  hasCoordinateOperators := ⟨_, isCoordinateExpansion_coordOp p b hN nablaN hdx⟩
  isIntegrable := by
    intro theta hco i j
    have hθ := eq_coordOp_of_isCoordinateExpansion p b hN nablaN hdx hco
    subst hθ
    have hP := P.isIntegrable _ (isCoordinateExpansion_coordOp p b P.isPAdicallyComplete P.nabla
      hdx) i j
    funext x
    obtain ⟨m, rfl⟩ := e.surjective x
    have hc := coordOp_map p b P.isPAdicallyComplete P.nabla hN nablaN e.toLinearMap he
    simp only [Function.comp_apply, LinearEquiv.coe_coe] at hc ⊢
    rw [hc, hc, hc, hc]
    exact congrArg e (congrFun hP m)
  isTopologicallyQuasiNilpotent := by
    intro theta hco x
    have hθ := eq_coordOp_of_isCoordinateExpansion p b hN nablaN hdx hco
    subst hθ
    obtain ⟨m, rfl⟩ := e.surjective x
    refine (P.isTopologicallyQuasiNilpotent _ (isCoordinateExpansion_coordOp p b
      P.isPAdicallyComplete P.nabla hdx) m).subset fun q hq ↦ ⟨hq.1, fun hmem ↦ hq.2 ?_⟩
    have hc := coordOp_map p b P.isPAdicallyComplete P.nabla hN nablaN e.toLinearMap he q.1
    have hiter : ∀ k : ℕ, (coordOp p b hN nablaN q.1)^[k] (e m) =
        e ((coordOp p b P.isPAdicallyComplete P.nabla q.1)^[k] m) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        exact hc _
    rw [hiter]
    rw [← pPowSmul_one] at hmem ⊢
    exact map_mem_pPowSmul_of_addMonoidHom p e.toLinearMap.toAddMonoidHom hmem

/-- The carrier of `Crystalline.Pair.ofHorizontalEquiv` is the given module. -/
@[simp] theorem Pair.ofHorizontalEquiv_carrier (P : Pair.{u, u, uI, u} p D Omega dx d)
    {N : Type u} [AddCommGroup N] [Module D N] (hN : IsPAdicallyComplete p D N)
    (nablaN : CompletedConnection p D Omega d N) (e : P.carrier ≃ₗ[D] N) (he) :
    (Pair.ofHorizontalEquiv p b hdx P hN nablaN e he).carrier = N := rfl

end Transfer

end Crystalline

end
