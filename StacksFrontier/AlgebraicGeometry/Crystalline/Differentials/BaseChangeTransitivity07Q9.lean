module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionsHorizontal
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.ColumnAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex

/-!
# Transitivity of the completed base change of de Rham complexes

Let `p` be an integer and let `D → D'` be a map of commutative rings.  For a `D`-module `M` with a
completed connection, `Crystalline.CompletedDeRham.baseChangeComplexHom` is the base change map
`M ⊗^∧_D Ω^*_D ⟶ M' ⊗^∧_{D'} Ω^*_{D'}`, `M' = (D' ⊗_D M)^∧`.  This file shows that this map is
determined, up to isomorphism of its target, by any *semilinear comparison* `μ : M → N` whose
`D'`-linearisation `(D' ⊗_D M)^∧ → N` is bijective, and deduces the transitivity of the
construction along `D → D₁ → D₂`:

`(D₂ ⊗_D M)^∧ ≅ (D₂ ⊗_{D₁} (D₁ ⊗_D M)^∧)^∧`,

horizontally for the base-changed connections, and the base change map along `D → D₂` is, up to
this isomorphism, the composite of the base change maps along `D → D₁` and `D₁ → D₂`.

## Main definitions

* `Crystalline.CompletedDeRham.comparisonComplexHom07Q9` — the morphism of complexes
  `M ⊗^∧_D Ω^*_D ⟶ N ⊗^∧_{D'} Ω'^*` induced by a semilinear horizontal map `μ : M → N` and a
  semilinear comparison of forms, whose components are
  `Crystalline.CompletedDeRham.comparisonValues`.
* `Crystalline.CompletedDeRham.linearize07Q9` — the linearisation `(D' ⊗_D M)^∧ → N`,
  `b ⊗ m ↦ τ b • μ m`, of a map `μ : M → N` into a complete module, semilinear over a ring map
  `τ : D' → D''`.
* `Crystalline.CompletedDeRham.IsBaseChange07Q9` — the linearisation is bijective.
* `Crystalline.CompletedDeRham.baseChangeComplexIso07Q9` — for such a `μ`, the target of the base
  change map is isomorphic to `N ⊗^∧_{D'} Ω'^*`.
* `Crystalline.CompletedDeRham.transitivityInclusion07Q9` — `m ↦ 1 ⊗ (1 ⊗ m)`.
* `Crystalline.CompletedDeRham.transitivityEquiv07Q9` — the transitivity isomorphism.

## Main results

* `Crystalline.CompletedDeRham.comparisonComplexHom07Q9_comp` — comparisons compose.
* `Crystalline.CompletedDeRham.isIso_comparisonComplexHom07Q9` — a comparison with an inverse
  comparison is an isomorphism.
* `Crystalline.CompletedDeRham.baseChangeComplexHom_eq_comparisonComplexHom07Q9` — the base
  change map is the comparison of the inclusion `m ↦ 1 ⊗ m`.
* `Crystalline.CompletedDeRham.linearize07Q9_horizontal` — the linearisation of a horizontal map
  is horizontal for the base-changed connection.
* `Crystalline.CompletedDeRham.baseChangeComplexHom_comp_baseChangeComplexIso07Q9` — the base
  change map followed by `baseChangeComplexIso07Q9` is the comparison of `μ`.
* `Crystalline.CompletedDeRham.isBaseChange07Q9_transitivityInclusion` — transitivity.
* `Crystalline.CompletedDeRham.transitivityEquiv07Q9_horizontal` — the transitivity isomorphism
  is horizontal.
* `Crystalline.CompletedDeRham.baseChangeComplexHom_trans07Q9` — the arrow identity
  `baseChangeComplexHom (D → D₂) ≅ baseChangeComplexHom (D → D₁) ≫ baseChangeComplexHom (D₁ → D₂)`.

## References

* [Stacks Project, Remark 60.17.4, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

namespace CompletedDeRham

/-- A `p`-adic completion is `p`-adically complete: the ideal `(p)` is principal. -/
instance instIsAdicCompletePAdic07Q9 (p : ℕ) (R : Type*) [CommRing R] (Y : Type*)
    [AddCommGroup Y] [Module R Y] :
    IsAdicComplete (pAdicIdeal (A := R) p) (AdicCompletion (pAdicIdeal (A := R) p) Y) :=
  AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _)

/-- Comparisons along mutually inverse data are mutually inverse on completed tensor products:
both are completions, and the uncompleted maps agree on pure tensors. -/
private theorem comparisonValues_comp_eq_self07Q9 (p : ℕ) {R S : Type u} [CommRing R]
    [CommRing S] (σ : R →+* S) (σ' : S →+* R) {X Y : Type u} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module S Y] (mu : X →ₛₗ[σ] Y) (mu' : Y →ₛₗ[σ'] X)
    (OmR : ℕ → Type u) [∀ i, AddCommGroup (OmR i)] [∀ i, Module R (OmR i)]
    (OmS : ℕ → Type u) [∀ i, AddCommGroup (OmS i)] [∀ i, Module S (OmS i)]
    (psi : ∀ i, OmR i →ₛₗ[σ] OmS i) (psi' : ∀ i, OmS i →ₛₗ[σ'] OmR i)
    (h₁ : ∀ m, mu' (mu m) = m) (h₃ : ∀ i ω, psi' i (psi i ω) = ω) (i : ℕ)
    (x : CompletedTensor p R (OmR i) X) :
    comparisonValues p S R σ' Y X mu' OmS OmR psi' i
        (comparisonValues p R S σ X Y mu OmR OmS psi i x) = x := by
  refine adicCompletionMapₛₗ_comp_eq_self (TensorProduct.map mu (psi i))
    (TensorProduct.map mu' (psi' i)) (map_pAdicIdeal_le p σ) (map_pAdicIdeal_le p σ')
    (fun y ↦ ?_) x
  induction y using TensorProduct.inductionOn with
  | tmul m ω =>
    change mu' (mu m) ⊗ₜ[R] psi' i (psi i ω) = m ⊗ₜ[R] ω
    rw [h₁, h₃]
  | add a b ha hb => simp only [map_add, ha, hb]

/-! ### Semilinear comparisons as morphisms of complexes -/

section ComparisonHom

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] (σ : D →+* D')
  (M : Type u) [AddCommGroup M] [Module D M] (N : Type u) [AddCommGroup N] [Module D' N]
  (mu : M →ₛₗ[σ] N)
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[σ] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} {d' : D' → Om' 1}
  (nabla : CompletedConnection p D (Om 1) d M)
  (nabla' : CompletedConnection p D' (Om' 1) d' N)
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq' : IsSquareZero p D' Om' wedge' deRham' N nabla' hleib')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))
  (hnabla : ∀ m : M, nabla' (mu m) = comparisonValues p D D' σ M N mu Om Om' psi 1 (nabla m))

/-- **The morphism of complexes `M ⊗^∧_D Ω^*_D ⟶ N ⊗^∧_{D'} Ω'^*` induced by a semilinear
horizontal map `μ : M → N` and a semilinear comparison `ψ` of the forms**: in degree `i` it is
the completion of `m ⊗ ω ↦ μ m ⊗ ψ_i ω`, `Crystalline.CompletedDeRham.comparisonValues`, and it
commutes with the differentials by `Crystalline.CompletedDeRham.differential_comparisonValues`. -/
def comparisonComplexHom07Q9 :
    complex p D Om wedge deRham M nabla hleib hsq ⟶
      complex p D' Om' wedge' deRham' N nabla' hleib' hsq' :=
  CochainComplex.ofHom
    (fun i ↦ AddCommGrpCat.ofHom (comparisonValues p D D' σ M N mu Om Om' psi i).toAddMonoidHom)
    (fun i ↦ by
      rw [complex_d, complex_d]
      exact AddCommGrpCat.ext fun x ↦ differential_comparisonValues p D D' σ M N mu Om Om' psi
        wedge wedge' deRham deRham' nabla nabla' hleib hleib' hpsi_wedge hpsi_deRham hnabla i x)

/-- The components of `Crystalline.CompletedDeRham.comparisonComplexHom07Q9` are the comparisons
`Crystalline.CompletedDeRham.comparisonValues`. -/
theorem comparisonComplexHom07Q9_f (i : ℕ) :
    (comparisonComplexHom07Q9 p D D' σ M N mu Om Om' psi wedge wedge' deRham deRham' nabla
        nabla' hleib hleib' hsq hsq' hpsi_wedge hpsi_deRham hnabla).f i =
      AddCommGrpCat.ofHom (comparisonValues p D D' σ M N mu Om Om' psi i).toAddMonoidHom :=
  rfl

/-- The comparison of completed tensor products of a composite is the composite of the
comparisons: both are completions, and the uncompleted maps agree on pure tensors. -/
theorem comparisonValues_comp07Q9 (D'' : Type u) [CommRing D''] (σ₂ : D' →+* D'')
    (σ₃ : D →+* D'') (N'' : Type u) [AddCommGroup N''] [Module D'' N''] (mu₂ : N →ₛₗ[σ₂] N'')
    (mu₃ : M →ₛₗ[σ₃] N'') (Om'' : ℕ → Type u) [∀ i, AddCommGroup (Om'' i)]
    [∀ i, Module D'' (Om'' i)] (psi₂ : ∀ i, Om' i →ₛₗ[σ₂] Om'' i)
    (psi₃ : ∀ i, Om i →ₛₗ[σ₃] Om'' i) (hmu : ∀ m, mu₃ m = mu₂ (mu m))
    (hpsi : ∀ i ω, psi₃ i ω = psi₂ i (psi i ω)) (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    comparisonValues p D' D'' σ₂ N N'' mu₂ Om' Om'' psi₂ i
        (comparisonValues p D D' σ M N mu Om Om' psi i x) =
      comparisonValues p D D'' σ₃ M N'' mu₃ Om Om'' psi₃ i x := by
  refine (adicCompletionMapₛₗ_comp_apply (TensorProduct.map mu (psi i))
    (TensorProduct.map mu₂ (psi₂ i)) (TensorProduct.map mu₃ (psi₃ i)) (map_pAdicIdeal_le p σ)
    (map_pAdicIdeal_le p σ₂) (map_pAdicIdeal_le p σ₃) (fun y ↦ ?_) x).symm
  induction y using TensorProduct.inductionOn with
  | tmul m ω =>
    change mu₃ m ⊗ₜ[D''] psi₃ i ω = mu₂ (mu m) ⊗ₜ[D''] psi₂ i (psi i ω)
    rw [hmu, hpsi]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **Comparisons compose**: the composite of the comparisons along `σ : D → D'` and
`σ₂ : D' → D''` is the comparison along any `σ₃` whose module map and forms maps are the
composites. -/
theorem comparisonComplexHom07Q9_comp (D'' : Type u) [CommRing D''] (σ₂ : D' →+* D'')
    (σ₃ : D →+* D'') (N'' : Type u) [AddCommGroup N''] [Module D'' N''] (mu₂ : N →ₛₗ[σ₂] N'')
    (mu₃ : M →ₛₗ[σ₃] N'') (Om'' : ℕ → Type u) [∀ i, AddCommGroup (Om'' i)]
    [∀ i, Module D'' (Om'' i)] (psi₂ : ∀ i, Om' i →ₛₗ[σ₂] Om'' i)
    (psi₃ : ∀ i, Om i →ₛₗ[σ₃] Om'' i) (wedge'' : ∀ i, Om'' i →ₗ[D''] Om'' 1 →ₗ[D''] Om'' (i + 1))
    (deRham'' : ∀ i, Om'' i →+ Om'' (i + 1)) {d'' : D'' → Om'' 1}
    (nabla'' : CompletedConnection p D'' (Om'' 1) d'' N'')
    (hleib'' : IsGradedLeibniz D'' Om'' wedge'' deRham'' d'')
    (hsq'' : IsSquareZero p D'' Om'' wedge'' deRham'' N'' nabla'' hleib'')
    (hpsi_wedge₂ : ∀ (i : ℕ) (ω : Om' i) (η : Om' 1),
      psi₂ (i + 1) (wedge' i ω η) = wedge'' i (psi₂ i ω) (psi₂ 1 η))
    (hpsi_deRham₂ : ∀ (i : ℕ) (ω : Om' i), psi₂ (i + 1) (deRham' i ω) = deRham'' i (psi₂ i ω))
    (hnabla₂ : ∀ n : N, nabla'' (mu₂ n) =
      comparisonValues p D' D'' σ₂ N N'' mu₂ Om' Om'' psi₂ 1 (nabla' n))
    (hpsi_wedge₃ : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
      psi₃ (i + 1) (wedge i ω η) = wedge'' i (psi₃ i ω) (psi₃ 1 η))
    (hpsi_deRham₃ : ∀ (i : ℕ) (ω : Om i), psi₃ (i + 1) (deRham i ω) = deRham'' i (psi₃ i ω))
    (hnabla₃ : ∀ m : M, nabla'' (mu₃ m) =
      comparisonValues p D D'' σ₃ M N'' mu₃ Om Om'' psi₃ 1 (nabla m))
    (hmu : ∀ m, mu₃ m = mu₂ (mu m)) (hpsi : ∀ i ω, psi₃ i ω = psi₂ i (psi i ω)) :
    comparisonComplexHom07Q9 p D D' σ M N mu Om Om' psi wedge wedge' deRham deRham' nabla
        nabla' hleib hleib' hsq hsq' hpsi_wedge hpsi_deRham hnabla ≫
      comparisonComplexHom07Q9 p D' D'' σ₂ N N'' mu₂ Om' Om'' psi₂ wedge' wedge'' deRham'
        deRham'' nabla' nabla'' hleib' hleib'' hsq' hsq'' hpsi_wedge₂ hpsi_deRham₂ hnabla₂ =
    comparisonComplexHom07Q9 p D D'' σ₃ M N'' mu₃ Om Om'' psi₃ wedge wedge'' deRham deRham''
        nabla nabla'' hleib hleib'' hsq hsq'' hpsi_wedge₃ hpsi_deRham₃ hnabla₃ := by
  ext i : 1
  refine AddCommGrpCat.ext fun x ↦ ?_
  exact comparisonValues_comp07Q9 p D D' σ M N mu Om Om' psi D'' σ₂ σ₃ N'' mu₂ mu₃ Om'' psi₂
    psi₃ hmu hpsi i x

/-- **A comparison with an inverse comparison is an isomorphism of complexes.**  In each degree
the comparison along the inverse data is an inverse, both composites being completions of the
identity. -/
theorem isIso_comparisonComplexHom07Q9 (σ' : D' →+* D) (mu' : N →ₛₗ[σ'] M)
    (psi' : ∀ i, Om' i →ₛₗ[σ'] Om i) (h₁ : ∀ m, mu' (mu m) = m) (h₂ : ∀ n, mu (mu' n) = n)
    (h₃ : ∀ i ω, psi' i (psi i ω) = ω) (h₄ : ∀ i ω, psi i (psi' i ω) = ω) :
    IsIso (comparisonComplexHom07Q9 p D D' σ M N mu Om Om' psi wedge wedge' deRham deRham'
      nabla nabla' hleib hleib' hsq hsq' hpsi_wedge hpsi_deRham hnabla) := by
  suffices h : ∀ i, IsIso ((comparisonComplexHom07Q9 p D D' σ M N mu Om Om' psi wedge wedge'
      deRham deRham' nabla nabla' hleib hleib' hsq hsq' hpsi_wedge hpsi_deRham hnabla).f i) from
    HomologicalComplex.Hom.isIso_of_components _
  intro i
  refine ⟨AddCommGrpCat.ofHom
      (comparisonValues p D' D σ' N M mu' Om' Om psi' i).toAddMonoidHom, ?_, ?_⟩
  · exact AddCommGrpCat.ext fun x ↦
      comparisonValues_comp_eq_self07Q9 p σ σ' mu mu' Om Om' psi psi' h₁ h₃ i x
  · exact AddCommGrpCat.ext fun x ↦
      comparisonValues_comp_eq_self07Q9 p σ' σ mu' mu Om' Om psi' psi h₂ h₄ i x

end ComparisonHom


/-! ### The linearisation of a semilinear map out of `M` -/

section Linearize

variable (p : ℕ) {D : Type u} [CommRing D] {D' : Type u} [CommRing D'] [Algebra D D']
  {D'' : Type u} [CommRing D''] (τ : D' →+* D'') {ρ : D →+* D''}
  (hρ : ∀ x : D, ρ x = τ (algebraMap D D' x))
  {M : Type u} [AddCommGroup M] [Module D M] {N : Type u} [AddCommGroup N] [Module D'' N]
  (mu : M →ₛₗ[ρ] N)

include hρ in
/-- The pairing `(b, m) ↦ τ b • μ m` is balanced over `D`. -/
theorem linearizePairing07Q9_balanced (c : D) (b : D') (m : M) :
    τ (c • b) • mu m = τ b • mu (c • m) := by
  rw [mu.map_smulₛₗ, hρ, Algebra.smul_def, map_mul, mul_smul, smul_comm]

/-- **The linearisation `D' ⊗_D M → N`, `b ⊗ m ↦ τ b • μ m`**, of a map `μ : M → N` semilinear
over `ρ = τ ∘ (D → D')`, as an additive map. -/
def linearizeTensorAdd07Q9 : D' ⊗[D] M →+ N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b ↦ AddMonoidHom.mk' (fun m ↦ τ b • mu m)
        (fun m m' ↦ by rw [map_add, smul_add]))
      (fun b b' ↦ AddMonoidHom.ext fun m ↦ by
        simp only [map_add, add_smul, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]))
    (fun c b m ↦ linearizePairing07Q9_balanced τ hρ mu c b m)

/-- The linearisation on a pure tensor. -/
@[simp] theorem linearizeTensorAdd07Q9_tmul (b : D') (m : M) :
    linearizeTensorAdd07Q9 τ hρ mu (b ⊗ₜ m) = τ b • mu m :=
  rfl

/-- **The linearisation `D' ⊗_D M → N`, `b ⊗ m ↦ τ b • μ m`**, semilinear over `τ`. -/
def linearizeTensor07Q9 : D' ⊗[D] M →ₛₗ[τ] N where
  toFun := linearizeTensorAdd07Q9 τ hρ mu
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      rw [TensorProduct.smul_tmul', linearizeTensorAdd07Q9_tmul, linearizeTensorAdd07Q9_tmul,
        smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The semilinear linearisation on a pure tensor. -/
@[simp] theorem linearizeTensor07Q9_tmul (b : D') (m : M) :
    linearizeTensor07Q9 τ hρ mu (b ⊗ₜ m) = τ b • mu m :=
  rfl

variable [IsAdicComplete (pAdicIdeal (A := D'') p) N]

/-- **The linearisation `(D' ⊗_D M)^∧ → N`, `b ⊗ m ↦ τ b • μ m`**, of a map `μ : M → N`
semilinear over `ρ = τ ∘ (D → D')` into a `p`-adically complete module: the completion of
`Crystalline.CompletedDeRham.linearizeTensor07Q9`, read back in `N`. -/
def linearize07Q9 : CompletedConnection.baseChangeCarrier p D D' M →ₛₗ[τ] N :=
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p) N).symm.toLinearMap.comp
    (adicCompletionMapₛₗ (linearizeTensor07Q9 τ hρ mu) (map_pAdicIdeal_le p τ))

/-- The linearisation on the image of the uncompleted tensor product. -/
theorem linearize07Q9_of (t : D' ⊗[D] M) :
    linearize07Q9 p τ hρ mu (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) t) =
      linearizeTensor07Q9 τ hρ mu t := by
  change (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p) N).symm
      (adicCompletionMapₛₗ (linearizeTensor07Q9 τ hρ mu) (map_pAdicIdeal_le p τ)
        (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) t)) = _
  rw [adicCompletionMapₛₗ_of, AdicCompletion.ofLinearEquiv_symm_of]

/-- **The linearisation extends `μ`**: it carries `1 ⊗ m` to `μ m`. -/
theorem linearize07Q9_baseChangeInclusion (m : M) :
    linearize07Q9 p τ hρ mu (CompletedConnection.baseChangeInclusion p D D' M m) = mu m := by
  rw [CompletedConnection.baseChangeInclusion_apply, linearize07Q9_of, linearizeTensor07Q9_tmul,
    map_one, one_smul]

/-- **The linearisation is the only extension of `μ`**: an additive map out of `(D' ⊗_D M)^∧`,
semilinear over `τ`, which carries `1 ⊗ m` to `μ m`, is the linearisation. -/
theorem eq_linearize07Q9 (g : CompletedConnection.baseChangeCarrier p D D' M →+ N)
    (hg : ∀ (c : D') x, g (c • x) = τ c • g x)
    (h0 : ∀ m, g (CompletedConnection.baseChangeInclusion p D D' M m) = mu m)
    (x : CompletedConnection.baseChangeCarrier p D D' M) : g x = linearize07Q9 p τ hρ mu x := by
  let e := AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p) N
  let G : CompletedConnection.baseChangeCarrier p D D' M →+
      AdicCompletion (pAdicIdeal (A := D'') p) N :=
    e.toLinearMap.toAddMonoidHom.comp (g - (linearize07Q9 p τ hρ mu).toAddMonoidHom)
  have hG : G x = 0 := by
    refine eq_zero_of_baseChangeInclusion p τ G (fun c y ↦ ?_) (fun m ↦ ?_) x
    · change e (g (c • y) - linearize07Q9 p τ hρ mu (c • y)) =
        τ c • e (g y - linearize07Q9 p τ hρ mu y)
      rw [hg, map_smulₛₗ, ← smul_sub, map_smul]
    · change e (g _ - linearize07Q9 p τ hρ mu _) = 0
      rw [h0, linearize07Q9_baseChangeInclusion, sub_self, map_zero]
  exact sub_eq_zero.mp (e.injective (hG.trans (map_zero e).symm))

end Linearize

/-- An additive endomorphism of `(D' ⊗_D M)^∧`, linear over `D'`, which fixes every `1 ⊗ m` is
the identity. -/
private theorem eq_self_of_baseChangeInclusion07Q9 (p : ℕ) {D D' : Type u} [CommRing D]
    [CommRing D'] [Algebra D D'] {M : Type u} [AddCommGroup M] [Module D M]
    (f : CompletedConnection.baseChangeCarrier p D D' M →+
      CompletedConnection.baseChangeCarrier p D D' M)
    (hf : ∀ (c : D') x, f (c • x) = c • f x)
    (h0 : ∀ m, f (CompletedConnection.baseChangeInclusion p D D' M m) =
      CompletedConnection.baseChangeInclusion p D D' M m)
    (x : CompletedConnection.baseChangeCarrier p D D' M) : f x = x :=
  (eq_linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl)
    (CompletedConnection.baseChangeInclusion p D D' M) f hf h0 x).trans
  (eq_linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl)
    (CompletedConnection.baseChangeInclusion p D D' M) (AddMonoidHom.id _) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) x).symm


/-! ### The linearisation is horizontal -/

section Horizontal

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] (τ : D' →+* D'') (ρ : D →+* D'')
  (hρ : ∀ x : D, ρ x = τ (algebraMap D D' x))
  (M : Type u) [AddCommGroup M] [Module D M] (N : Type u) [AddCommGroup N] [Module D'' N]
  [IsAdicComplete (pAdicIdeal (A := D'') p) N] (mu : M →ₛₗ[ρ] N)
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (Om'' : ℕ → Type u) [∀ i, AddCommGroup (Om'' i)] [∀ i, Module D'' (Om'' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i) (psi'' : ∀ i, Om' i →ₛₗ[τ] Om'' i)
  (psiρ : ∀ i, Om i →ₛₗ[ρ] Om'' i) (hpsiρ : ∀ i ω, psiρ i ω = psi'' i (psi i ω))
  {d : D → Om 1} (d' : D' → Om' 1) {d'' : D'' → Om'' 1}
  (nabla : CompletedConnection p D (Om 1) d M)
  (nablaN : CompletedConnection p D'' (Om'' 1) d'' N)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hd'' : ∀ b : D', psi'' 1 (d' b) = d'' (τ b))
  (hmu : ∀ m : M, nablaN (mu m) = comparisonValues p D D'' ρ M N mu Om Om'' psiρ 1 (nabla m))

include hpsiρ hd'' hmu in
/-- **The linearisation of a horizontal map is horizontal**: if `μ : M → N` carries `∇` to `∇_N`,
then its linearisation `(D' ⊗_D M)^∧ → N` carries the base-changed connection to `∇_N`.  On
`b ⊗ m` both sides are `τ b • μ_*(∇ m) + μ m ⊗ d (τ b)`, by the Leibniz rule of `∇_N` and the
formula for the base-changed connection; both sides are additive maps between `p`-adic
completions, so this suffices. -/
theorem linearize07Q9_horizontal (x : CompletedConnection.baseChangeCarrier p D D' M) :
    nablaN (linearize07Q9 p τ hρ mu x) =
      comparisonValues p D' D'' τ (CompletedConnection.baseChangeCarrier p D D' M) N
        (linearize07Q9 p τ hρ mu) Om' Om'' psi'' 1
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
          hd'leib hpsi1 x) := by
  let F : CompletedConnection.baseChangeCarrier p D D' M →+ CompletedTensor p D'' (Om'' 1) N :=
    AddMonoidHom.mk' (fun x ↦ nablaN (linearize07Q9 p τ hρ mu x))
      (fun x y ↦ by rw [map_add, nablaN.map_add])
  let G : CompletedConnection.baseChangeCarrier p D D' M →+ CompletedTensor p D'' (Om'' 1) N :=
    AddMonoidHom.mk' (fun x ↦ comparisonValues p D' D'' τ
        (CompletedConnection.baseChangeCarrier p D D' M) N (linearize07Q9 p τ hρ mu) Om' Om''
        psi'' 1 (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
          hd'leib hpsi1 x))
      (fun x y ↦ by rw [CompletedConnection.map_add, map_add])
  have hFG : F = G := by
    refine adicCompletion_addMonoidHom_ext_of_of p (fun t ↦ ?_)
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | tmul b m =>
      have hc := comparisonValues_comp07Q9 p D D' (algebraMap D D') M
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChangeInclusion p D D' M) Om Om' psi D'' τ ρ N
        (linearize07Q9 p τ hρ mu) mu Om'' psi'' psiρ
        (fun m ↦ (linearize07Q9_baseChangeInclusion p τ hρ mu m).symm) hpsiρ 1 (nabla m)
      change nablaN (linearize07Q9 p τ hρ mu _) = comparisonValues p D' D'' τ _ N _ Om' Om'' psi''
        1 (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
          hd'leib hpsi1 _)
      rw [linearize07Q9_of, linearizeTensor07Q9_tmul, nablaN.leibniz, hmu,
        CompletedConnection.baseChange_of_tmul, map_add, map_smulₛₗ,
        CompletedConnection.correction_apply, comparisonValues_of_tmul,
        linearize07Q9_baseChangeInclusion, hd'']
      congr 2
      exact hc.symm
  exact DFunLike.congr_fun hFG x

end Horizontal

/-! ### The base change map is a comparison -/

section BaseChangeHom

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) (nabla : CompletedConnection p D (Om 1) d M)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
  (hpsi_deRham : ∀ (i : ℕ) (omega : Om i),
    psi (i + 1) (deRham i omega) = deRham' i (psi i omega))
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq' : IsSquareZero p D' Om' wedge' deRham'
    (CompletedConnection.baseChangeCarrier p D D' M)
    (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
      hpsi1) hleib')

/-- The base-changed connection is horizontal for the inclusion `m ↦ 1 ⊗ m`, in the form asked
by `Crystalline.CompletedDeRham.comparisonComplexHom07Q9`. -/
theorem baseChange_inclusion07Q9 (m : M) :
    CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib hpsi1
        (CompletedConnection.baseChangeInclusion p D D' M m) =
      comparisonValues p D D' (algebraMap D D') M
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChangeInclusion p D D' M) Om Om' psi 1 (nabla m) :=
  CompletedConnection.baseChange_inclusion p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
    hd'leib hpsi1 m

include hpsi_wedge hpsi_deRham in
/-- **The base change map of completed de Rham complexes is the comparison of the inclusion
`m ↦ 1 ⊗ m`.** -/
theorem baseChangeComplexHom_eq_comparisonComplexHom07Q9 :
    baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla hd'add hd'leib
        hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq' =
      comparisonComplexHom07Q9 p D D' (algebraMap D D') M
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChangeInclusion p D D' M) Om Om' psi wedge wedge' deRham
        deRham' nabla
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) hleib hleib' hsq hsq' hpsi_wedge hpsi_deRham
        (baseChange_inclusion07Q9 p D D' M Om Om' psi d' nabla hd'add hd'leib hpsi1) :=
  rfl

end BaseChangeHom

/-! ### The base change map followed by a linearisation -/

section LinearizeComplex

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] (τ : D' →+* D'') (ρ : D →+* D'')
  (hρ : ∀ x : D, ρ x = τ (algebraMap D D' x))
  (M : Type u) [AddCommGroup M] [Module D M] (N : Type u) [AddCommGroup N] [Module D'' N]
  [IsAdicComplete (pAdicIdeal (A := D'') p) N] (mu : M →ₛₗ[ρ] N)
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (Om'' : ℕ → Type u) [∀ i, AddCommGroup (Om'' i)] [∀ i, Module D'' (Om'' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i) (psi'' : ∀ i, Om' i →ₛₗ[τ] Om'' i)
  (psiρ : ∀ i, Om i →ₛₗ[ρ] Om'' i) (hpsiρ : ∀ i ω, psiρ i ω = psi'' i (psi i ω))
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (wedge'' : ∀ i, Om'' i →ₗ[D''] Om'' 1 →ₗ[D''] Om'' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  (deRham'' : ∀ i, Om'' i →+ Om'' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) {d'' : D'' → Om'' 1}
  (nabla : CompletedConnection p D (Om 1) d M)
  (nablaN : CompletedConnection p D'' (Om'' 1) d'' N)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hd'' : ∀ b : D', psi'' 1 (d' b) = d'' (τ b))
  (hmu : ∀ m : M, nablaN (mu m) = comparisonValues p D D'' ρ M N mu Om Om'' psiρ 1 (nabla m))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hleib'' : IsGradedLeibniz D'' Om'' wedge'' deRham'' d'')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))
  (hpsi''_wedge : ∀ (i : ℕ) (ω : Om' i) (η : Om' 1),
    psi'' (i + 1) (wedge' i ω η) = wedge'' i (psi'' i ω) (psi'' 1 η))
  (hpsi''_deRham : ∀ (i : ℕ) (ω : Om' i), psi'' (i + 1) (deRham' i ω) = deRham'' i (psi'' i ω))
  (hpsiρ_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psiρ (i + 1) (wedge i ω η) = wedge'' i (psiρ i ω) (psiρ 1 η))
  (hpsiρ_deRham : ∀ (i : ℕ) (ω : Om i), psiρ (i + 1) (deRham i ω) = deRham'' i (psiρ i ω))
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq' : IsSquareZero p D' Om' wedge' deRham'
    (CompletedConnection.baseChangeCarrier p D D' M)
    (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
      hpsi1) hleib')
  (hsqN : IsSquareZero p D'' Om'' wedge'' deRham'' N nablaN hleib'')

include hpsiρ in
/-- **The base change map followed by the comparison of a linearisation** is the comparison of
the map `μ` itself: `M ⊗^∧_D Ω^* ⟶ M' ⊗^∧_{D'} Ω'^* ⟶ N ⊗^∧_{D''} Ω''^*` is the completion of
`m ⊗ ω ↦ μ m ⊗ ψ ω`. -/
theorem baseChangeComplexHom_comp_linearize07Q9 :
    baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla hd'add hd'leib
        hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq' ≫
      comparisonComplexHom07Q9 p D' D'' τ (CompletedConnection.baseChangeCarrier p D D' M) N
        (linearize07Q9 p τ hρ mu) Om' Om'' psi'' wedge' wedge'' deRham' deRham''
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) nablaN hleib' hleib'' hsq' hsqN hpsi''_wedge hpsi''_deRham
        (linearize07Q9_horizontal p D D' D'' τ ρ hρ M N mu Om Om' Om'' psi psi'' psiρ hpsiρ d'
          nabla nablaN hd'add hd'leib hpsi1 hd'' hmu) =
    comparisonComplexHom07Q9 p D D'' ρ M N mu Om Om'' psiρ wedge wedge'' deRham deRham''
      nabla nablaN hleib hleib'' hsq hsqN hpsiρ_wedge hpsiρ_deRham hmu := by
  rw [baseChangeComplexHom_eq_comparisonComplexHom07Q9]
  exact comparisonComplexHom07Q9_comp p D D' (algebraMap D D') M
    (CompletedConnection.baseChangeCarrier p D D' M)
    (CompletedConnection.baseChangeInclusion p D D' M) Om Om' psi wedge wedge' deRham deRham'
    nabla _ hleib hleib' hsq hsq' hpsi_wedge hpsi_deRham _ D'' τ ρ N (linearize07Q9 p τ hρ mu)
    mu Om'' psi'' psiρ wedge'' deRham'' nablaN hleib'' hsqN hpsi''_wedge hpsi''_deRham _
    hpsiρ_wedge hpsiρ_deRham hmu (fun m ↦ (linearize07Q9_baseChangeInclusion p τ hρ mu m).symm)
    hpsiρ

end LinearizeComplex

/-! ### Transitivity -/

section Transitivity

variable (p : ℕ) (D : Type u) [CommRing D] (D₁ : Type u) [CommRing D₁] (D₂ : Type u)
  [CommRing D₂] [Algebra D D₁] [Algebra D₁ D₂] [Algebra D D₂] [IsScalarTower D D₁ D₂]
  (M : Type u) [AddCommGroup M] [Module D M]

/-- The composite inclusion `M → (D₂ ⊗_{D₁} (D₁ ⊗_D M)^∧)^∧`, `m ↦ 1 ⊗ (1 ⊗ m)`, semilinear over
`D → D₂`. -/
def transitivityInclusion07Q9 :
    M →ₛₗ[algebraMap D D₂] CompletedConnection.baseChangeCarrier p D₁ D₂
      (CompletedConnection.baseChangeCarrier p D D₁ M) where
  toFun m := CompletedConnection.baseChangeInclusion p D₁ D₂ _
    (CompletedConnection.baseChangeInclusion p D D₁ M m)
  map_add' m n := by rw [map_add, map_add]
  map_smul' c m := by
    rw [map_smulₛₗ, map_smulₛₗ, IsScalarTower.algebraMap_apply D D₁ D₂ c]

/-- The composite inclusion, as a formula. -/
theorem transitivityInclusion07Q9_apply (m : M) :
    transitivityInclusion07Q9 p D D₁ D₂ M m =
      CompletedConnection.baseChangeInclusion p D₁ D₂ _
        (CompletedConnection.baseChangeInclusion p D D₁ M m) :=
  rfl

/-- **The transitivity map** `(D₂ ⊗_D M)^∧ → (D₂ ⊗_{D₁} (D₁ ⊗_D M)^∧)^∧`, `b ⊗ m ↦ b ⊗ (1 ⊗ m)`:
the linearisation of `Crystalline.CompletedDeRham.transitivityInclusion07Q9`. -/
def transitivityMap07Q9 :
    CompletedConnection.baseChangeCarrier p D D₂ M →ₗ[D₂]
      CompletedConnection.baseChangeCarrier p D₁ D₂
        (CompletedConnection.baseChangeCarrier p D D₁ M) :=
  linearize07Q9 (D := D) p (RingHom.id D₂) (fun _ ↦ rfl) (transitivityInclusion07Q9 p D D₁ D₂ M)

/-- The structure map `(D₁ ⊗_D M)^∧ → (D₂ ⊗_D M)^∧`, `b ⊗ m ↦ b ⊗ m`, semilinear over
`D₁ → D₂`. -/
def towerInclusion07Q9 :
    CompletedConnection.baseChangeCarrier p D D₁ M →ₛₗ[algebraMap D₁ D₂]
      CompletedConnection.baseChangeCarrier p D D₂ M :=
  linearize07Q9 p (algebraMap D₁ D₂) (IsScalarTower.algebraMap_apply D D₁ D₂)
    (CompletedConnection.baseChangeInclusion p D D₂ M)

/-- **The inverse transitivity map** `(D₂ ⊗_{D₁} (D₁ ⊗_D M)^∧)^∧ → (D₂ ⊗_D M)^∧`,
`b ⊗ x ↦ b • x`. -/
def transitivityInverse07Q9 :
    CompletedConnection.baseChangeCarrier p D₁ D₂
        (CompletedConnection.baseChangeCarrier p D D₁ M) →ₗ[D₂]
      CompletedConnection.baseChangeCarrier p D D₂ M :=
  linearize07Q9 (D := D₁) p (RingHom.id D₂) (fun _ ↦ rfl) (towerInclusion07Q9 p D D₁ D₂ M)

/-- The transitivity map extends the composite inclusion. -/
theorem transitivityMap07Q9_baseChangeInclusion (m : M) :
    transitivityMap07Q9 p D D₁ D₂ M (CompletedConnection.baseChangeInclusion p D D₂ M m) =
      transitivityInclusion07Q9 p D D₁ D₂ M m :=
  linearize07Q9_baseChangeInclusion (D := D) p (RingHom.id D₂) (fun _ ↦ rfl)
    (transitivityInclusion07Q9 p D D₁ D₂ M) m

/-- The transitivity map undoes the structure map `(D₁ ⊗_D M)^∧ → (D₂ ⊗_D M)^∧`. -/
theorem transitivityMap07Q9_towerInclusion (x : CompletedConnection.baseChangeCarrier p D D₁ M) :
    transitivityMap07Q9 p D D₁ D₂ M (towerInclusion07Q9 p D D₁ D₂ M x) =
      CompletedConnection.baseChangeInclusion p D₁ D₂ _ x := by
  have h1 := eq_linearize07Q9 p (algebraMap D₁ D₂) (IsScalarTower.algebraMap_apply D D₁ D₂)
    (transitivityInclusion07Q9 p D D₁ D₂ M)
    ((transitivityMap07Q9 p D D₁ D₂ M).toAddMonoidHom.comp
      (towerInclusion07Q9 p D D₁ D₂ M).toAddMonoidHom)
    (fun c y ↦ by
      change transitivityMap07Q9 p D D₁ D₂ M (towerInclusion07Q9 p D D₁ D₂ M (c • y)) =
        algebraMap D₁ D₂ c • transitivityMap07Q9 p D D₁ D₂ M (towerInclusion07Q9 p D D₁ D₂ M y)
      rw [(towerInclusion07Q9 p D D₁ D₂ M).map_smulₛₗ, map_smul])
    (fun m ↦ by
      change transitivityMap07Q9 p D D₁ D₂ M (towerInclusion07Q9 p D D₁ D₂ M _) = _
      rw [towerInclusion07Q9, linearize07Q9_baseChangeInclusion,
        transitivityMap07Q9_baseChangeInclusion]) x
  have h2 := eq_linearize07Q9 p (algebraMap D₁ D₂) (IsScalarTower.algebraMap_apply D D₁ D₂)
    (transitivityInclusion07Q9 p D D₁ D₂ M)
    (CompletedConnection.baseChangeInclusion p D₁ D₂ _).toAddMonoidHom
    (fun c y ↦ (CompletedConnection.baseChangeInclusion p D₁ D₂ _).map_smulₛₗ c y)
    (fun m ↦ rfl) x
  exact h1.trans h2.symm

/-- The inverse transitivity map undoes the transitivity map. -/
theorem transitivityInverse07Q9_transitivityMap07Q9
    (x : CompletedConnection.baseChangeCarrier p D D₂ M) :
    transitivityInverse07Q9 p D D₁ D₂ M (transitivityMap07Q9 p D D₁ D₂ M x) = x := by
  refine eq_self_of_baseChangeInclusion07Q9 p
    ((transitivityInverse07Q9 p D D₁ D₂ M).toAddMonoidHom.comp
      (transitivityMap07Q9 p D D₁ D₂ M).toAddMonoidHom)
    (fun c y ↦ by
      change transitivityInverse07Q9 p D D₁ D₂ M (transitivityMap07Q9 p D D₁ D₂ M (c • y)) =
        c • transitivityInverse07Q9 p D D₁ D₂ M (transitivityMap07Q9 p D D₁ D₂ M y)
      rw [map_smul, map_smul])
    (fun m ↦ by
      change transitivityInverse07Q9 p D D₁ D₂ M (transitivityMap07Q9 p D D₁ D₂ M _) = _
      rw [transitivityMap07Q9_baseChangeInclusion, transitivityInclusion07Q9_apply,
        transitivityInverse07Q9, linearize07Q9_baseChangeInclusion, towerInclusion07Q9,
        linearize07Q9_baseChangeInclusion]) x

/-- The transitivity map undoes the inverse transitivity map. -/
theorem transitivityMap07Q9_transitivityInverse07Q9
    (x : CompletedConnection.baseChangeCarrier p D₁ D₂
      (CompletedConnection.baseChangeCarrier p D D₁ M)) :
    transitivityMap07Q9 p D D₁ D₂ M (transitivityInverse07Q9 p D D₁ D₂ M x) = x := by
  refine eq_self_of_baseChangeInclusion07Q9 p
    ((transitivityMap07Q9 p D D₁ D₂ M).toAddMonoidHom.comp
      (transitivityInverse07Q9 p D D₁ D₂ M).toAddMonoidHom)
    (fun c y ↦ by
      change transitivityMap07Q9 p D D₁ D₂ M (transitivityInverse07Q9 p D D₁ D₂ M (c • y)) =
        c • transitivityMap07Q9 p D D₁ D₂ M (transitivityInverse07Q9 p D D₁ D₂ M y)
      rw [map_smul, map_smul])
    (fun y ↦ by
      change transitivityMap07Q9 p D D₁ D₂ M (transitivityInverse07Q9 p D D₁ D₂ M _) = _
      rw [transitivityInverse07Q9, linearize07Q9_baseChangeInclusion,
        transitivityMap07Q9_towerInclusion]) x

/-- **Transitivity of the completed base change**:
`(D₂ ⊗_D M)^∧ ≅ (D₂ ⊗_{D₁} (D₁ ⊗_D M)^∧)^∧`, `b ⊗ m ↦ b ⊗ (1 ⊗ m)`, linearly over `D₂`. -/
def transitivityEquiv07Q9 :
    CompletedConnection.baseChangeCarrier p D D₂ M ≃ₗ[D₂]
      CompletedConnection.baseChangeCarrier p D₁ D₂
        (CompletedConnection.baseChangeCarrier p D D₁ M) :=
  LinearEquiv.ofLinearMap (transitivityMap07Q9 p D D₁ D₂ M) (transitivityInverse07Q9 p D D₁ D₂ M)
    (LinearMap.ext (transitivityMap07Q9_transitivityInverse07Q9 p D D₁ D₂ M))
    (LinearMap.ext (transitivityInverse07Q9_transitivityMap07Q9 p D D₁ D₂ M))

/-- The transitivity isomorphism on `1 ⊗ m` is `1 ⊗ (1 ⊗ m)`. -/
theorem transitivityEquiv07Q9_baseChangeInclusion (m : M) :
    transitivityEquiv07Q9 p D D₁ D₂ M (CompletedConnection.baseChangeInclusion p D D₂ M m) =
      CompletedConnection.baseChangeInclusion p D₁ D₂ _
        (CompletedConnection.baseChangeInclusion p D D₁ M m) :=
  transitivityMap07Q9_baseChangeInclusion p D D₁ D₂ M m

end Transitivity

/-! ### Base change along a map with bijective linearisation -/

section BaseChangeIso

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (M : Type u) [AddCommGroup M] [Module D M] (N : Type u) [AddCommGroup N] [Module D' N]
  [IsAdicComplete (pAdicIdeal (A := D') p) N] (mu : M →ₛₗ[algebraMap D D'] N)

/-- **`μ : M → N` exhibits `N` as the completed base change of `M`**: the linearisation
`(D' ⊗_D M)^∧ → N`, `b ⊗ m ↦ b • μ m`, is bijective. -/
def IsBaseChange07Q9 : Prop :=
  Function.Bijective (linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl) mu)

/-- The inclusion `m ↦ 1 ⊗ m` exhibits `(D' ⊗_D M)^∧` as the completed base change of `M`: its
linearisation is the identity. -/
theorem isBaseChange07Q9_baseChangeInclusion :
    IsBaseChange07Q9 p D D' M (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChangeInclusion p D D' M) := by
  have h : ∀ x, linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl)
      (CompletedConnection.baseChangeInclusion p D D' M) x = x := fun x ↦
    eq_self_of_baseChangeInclusion07Q9 p
      (linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl)
        (CompletedConnection.baseChangeInclusion p D D' M)).toAddMonoidHom
      (fun _ _ ↦ by simp) (linearize07Q9_baseChangeInclusion p _ _ _) x
  exact ⟨fun x y hxy ↦ by rwa [h, h] at hxy, fun y ↦ ⟨y, h y⟩⟩

/-- The transitivity map is bijective. -/
theorem isBaseChange07Q9_transitivityInclusion (D₁ : Type u) [CommRing D₁] (D₂ : Type u)
    [CommRing D₂] [Algebra D D₁] [Algebra D₁ D₂] [Algebra D D₂] [IsScalarTower D D₁ D₂] :
    IsBaseChange07Q9 p D D₂ M _ (transitivityInclusion07Q9 p D D₁ D₂ M) :=
  (transitivityEquiv07Q9 p D D₁ D₂ M).bijective

variable (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1)
  (nabla : CompletedConnection p D (Om 1) d M)
  (nablaN : CompletedConnection p D' (Om' 1) d' N)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hmu : ∀ m : M, nablaN (mu m) =
    comparisonValues p D D' (algebraMap D D') M N mu Om Om' psi 1 (nabla m))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq' : IsSquareZero p D' Om' wedge' deRham'
    (CompletedConnection.baseChangeCarrier p D D' M)
    (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
      hpsi1) hleib')
  (hsqN : IsSquareZero p D' Om' wedge' deRham' N nablaN hleib')

/-- The linearisation of a horizontal `μ` is horizontal, in the form asked by
`Crystalline.CompletedDeRham.comparisonComplexHom07Q9`. -/
theorem linearize07Q9_horizontal' (hmu : ∀ m : M, nablaN (mu m) =
      comparisonValues p D D' (algebraMap D D') M N mu Om Om' psi 1 (nabla m))
    (x : CompletedConnection.baseChangeCarrier p D D' M) :
    nablaN (linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl) mu x) =
      comparisonValues p D' D' (RingHom.id D') (CompletedConnection.baseChangeCarrier p D D' M)
        N (linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl) mu) Om' Om'
        (fun _ ↦ LinearMap.id) 1
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add
          hd'leib hpsi1 x) :=
  linearize07Q9_horizontal p D D' D' (RingHom.id D') (algebraMap D D') (fun _ ↦ rfl) M N mu Om
    Om' Om' psi (fun _ ↦ LinearMap.id) psi (fun _ _ ↦ rfl) d' nabla nablaN hd'add hd'leib hpsi1
    (fun _ ↦ rfl) hmu x

/-- **The target of the base change map is the de Rham complex of any base change**: for
`μ : M → N` horizontal with bijective linearisation, the linearisation induces an isomorphism
`M' ⊗^∧_{D'} Ω'^* ≅ N ⊗^∧_{D'} Ω'^*`. -/
def baseChangeComplexIso07Q9 (h : IsBaseChange07Q9 p D D' M N mu) :
    complex p D' Om' wedge' deRham' (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
          hpsi1) hleib' hsq' ≅
      complex p D' Om' wedge' deRham' N nablaN hleib' hsqN :=
  haveI := isIso_comparisonComplexHom07Q9 p D' D' (RingHom.id D')
    (CompletedConnection.baseChangeCarrier p D D' M) N
    (linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl) mu) Om' Om'
    (fun _ ↦ LinearMap.id) wedge' wedge' deRham' deRham' _ nablaN hleib' hleib' hsq' hsqN
    (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (linearize07Q9_horizontal' p D D' M N mu Om Om' psi d' nabla nablaN hd'add hd'leib hpsi1 hmu)
    (RingHom.id D') (LinearEquiv.ofBijective _ h).symm.toLinearMap (fun _ ↦ LinearMap.id)
    (fun x ↦ (LinearEquiv.ofBijective _ h).symm_apply_apply x)
    (fun y ↦ (LinearEquiv.ofBijective _ h).apply_symm_apply y) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  asIso (comparisonComplexHom07Q9 p D' D' (RingHom.id D')
    (CompletedConnection.baseChangeCarrier p D D' M) N
    (linearize07Q9 (D := D) p (RingHom.id D') (fun _ ↦ rfl) mu) Om' Om'
    (fun _ ↦ LinearMap.id) wedge' wedge' deRham' deRham' _ nablaN hleib' hleib' hsq' hsqN
    (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (linearize07Q9_horizontal' p D D' M N mu Om Om' psi d' nabla nablaN hd'add hd'leib hpsi1 hmu))

/-- **The base change map followed by `baseChangeComplexIso07Q9` is the comparison of `μ`.** -/
theorem baseChangeComplexHom_comp_baseChangeComplexIso07Q9 (h : IsBaseChange07Q9 p D D' M N mu) :
    baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla hd'add hd'leib
        hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq' ≫
      (baseChangeComplexIso07Q9 p D D' M N mu Om Om' psi wedge' deRham' d' nabla nablaN hd'add
        hd'leib hpsi1 hmu hleib' hsq' hsqN h).hom =
    comparisonComplexHom07Q9 p D D' (algebraMap D D') M N mu Om Om' psi wedge wedge' deRham
      deRham' nabla nablaN hleib hleib' hsq hsqN hpsi_wedge hpsi_deRham hmu :=
  baseChangeComplexHom_comp_linearize07Q9 p D D' D' (RingHom.id D') (algebraMap D D')
    (fun _ ↦ rfl) M N mu Om Om' Om' psi (fun _ ↦ LinearMap.id) psi (fun _ _ ↦ rfl) wedge wedge'
    wedge' deRham deRham' deRham' d' nabla nablaN hd'add hd'leib hpsi1 (fun _ ↦ rfl) hmu hleib
    hleib' hleib' hpsi_wedge hpsi_deRham (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) hpsi_wedge
    hpsi_deRham hsq hsq' hsqN

/-- **The base change map is isomorphic, as an arrow, to the comparison of any base change
`μ`.** -/
def baseChangeArrowIso07Q9 (h : IsBaseChange07Q9 p D D' M N mu) :
    Arrow.mk (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla
        hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq') ≅
      Arrow.mk (comparisonComplexHom07Q9 p D D' (algebraMap D D') M N mu Om Om' psi wedge wedge'
        deRham deRham' nabla nablaN hleib hleib' hsq hsqN hpsi_wedge hpsi_deRham hmu) :=
  Arrow.isoMk (Iso.refl _)
    (baseChangeComplexIso07Q9 p D D' M N mu Om Om' psi wedge' deRham' d' nabla nablaN hd'add
      hd'leib hpsi1 hmu hleib' hsq' hsqN h) (by
    simp only [Arrow.mk_hom, Iso.refl_hom, Category.id_comp]
    exact (baseChangeComplexHom_comp_baseChangeComplexIso07Q9 p D D' M N mu Om Om' psi wedge
      wedge' deRham deRham' d' nabla nablaN hd'add hd'leib hpsi1 hmu hleib hleib' hpsi_wedge
      hpsi_deRham hsq hsq' hsqN h).symm)

end BaseChangeIso

/-! ### The arrow identity of transitivity -/

section TransitivityArrow

variable (p : ℕ) (D : Type u) [CommRing D] (D₁ : Type u) [CommRing D₁] (D₂ : Type u)
  [CommRing D₂] [Algebra D D₁] [Algebra D₁ D₂] [Algebra D D₂] [IsScalarTower D D₁ D₂]
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om₁ : ℕ → Type u) [∀ i, AddCommGroup (Om₁ i)] [∀ i, Module D₁ (Om₁ i)]
  (Om₂ : ℕ → Type u) [∀ i, AddCommGroup (Om₂ i)] [∀ i, Module D₂ (Om₂ i)]
  (psi₁ : ∀ i, Om i →ₛₗ[algebraMap D D₁] Om₁ i) (psi₂ : ∀ i, Om₁ i →ₛₗ[algebraMap D₁ D₂] Om₂ i)
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D₂] Om₂ i) (hpsi : ∀ i ω, psi i ω = psi₂ i (psi₁ i ω))
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge₁ : ∀ i, Om₁ i →ₗ[D₁] Om₁ 1 →ₗ[D₁] Om₁ (i + 1))
  (wedge₂ : ∀ i, Om₂ i →ₗ[D₂] Om₂ 1 →ₗ[D₂] Om₂ (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham₁ : ∀ i, Om₁ i →+ Om₁ (i + 1))
  (deRham₂ : ∀ i, Om₂ i →+ Om₂ (i + 1))
  {d : D → Om 1} (d₁ : D₁ → Om₁ 1) (d₂ : D₂ → Om₂ 1)
  (nabla : CompletedConnection p D (Om 1) d M)
  (hd₁add : ∀ x y : D₁, d₁ (x + y) = d₁ x + d₁ y)
  (hd₁leib : ∀ x y : D₁, d₁ (x * y) = x • d₁ y + y • d₁ x)
  (hd₂add : ∀ x y : D₂, d₂ (x + y) = d₂ x + d₂ y)
  (hd₂leib : ∀ x y : D₂, d₂ (x * y) = x • d₂ y + y • d₂ x)
  (hpsi₁1 : ∀ x : D, psi₁ 1 (d x) = d₁ (algebraMap D D₁ x))
  (hpsi₂1 : ∀ x : D₁, psi₂ 1 (d₁ x) = d₂ (algebraMap D₁ D₂ x))
  (hpsi1 : ∀ x : D, psi 1 (d x) = d₂ (algebraMap D D₂ x))

/-- The connection of the twice base-changed module `(D₂ ⊗_{D₁} (D₁ ⊗_D M)^∧)^∧`. -/
abbrev transitivityConnection07Q9 :
    CompletedConnection p D₂ (Om₂ 1) d₂ (CompletedConnection.baseChangeCarrier p D₁ D₂
      (CompletedConnection.baseChangeCarrier p D D₁ M)) :=
  CompletedConnection.baseChange p D₁ D₂ (CompletedConnection.baseChangeCarrier p D D₁ M)
    (Om₁ 1) (Om₂ 1) d₂ (psi₂ 1)
    (CompletedConnection.baseChange p D D₁ M (Om 1) (Om₁ 1) d₁ (psi₁ 1) nabla hd₁add hd₁leib
      hpsi₁1) hd₂add hd₂leib hpsi₂1

include hpsi in
/-- **The composite inclusion `m ↦ 1 ⊗ (1 ⊗ m)` is horizontal** for the twice base-changed
connection. -/
theorem transitivityInclusion07Q9_horizontal (m : M) :
    transitivityConnection07Q9 p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ d₁ d₂ nabla hd₁add hd₁leib
        hd₂add hd₂leib hpsi₁1 hpsi₂1 (transitivityInclusion07Q9 p D D₁ D₂ M m) =
      comparisonValues p D D₂ (algebraMap D D₂) M _ (transitivityInclusion07Q9 p D D₁ D₂ M) Om
        Om₂ psi 1 (nabla m) := by
  rw [transitivityInclusion07Q9_apply, CompletedConnection.baseChange_inclusion,
    CompletedConnection.baseChange_inclusion]
  exact comparisonValues_comp07Q9 p D D₁ (algebraMap D D₁) M _
    (CompletedConnection.baseChangeInclusion p D D₁ M) Om Om₁ psi₁ D₂ (algebraMap D₁ D₂)
    (algebraMap D D₂) _ (CompletedConnection.baseChangeInclusion p D₁ D₂ _)
    (transitivityInclusion07Q9 p D D₁ D₂ M) Om₂ psi₂ psi (fun _ ↦ rfl) hpsi 1 (nabla m)

include hpsi in
/-- **The transitivity isomorphism is horizontal**: it carries the connection of `(D₂ ⊗_D M)^∧`
to that of `(D₂ ⊗_{D₁} (D₁ ⊗_D M)^∧)^∧`. -/
theorem transitivityEquiv07Q9_horizontal (x : CompletedConnection.baseChangeCarrier p D D₂ M) :
    transitivityConnection07Q9 p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ d₁ d₂ nabla hd₁add hd₁leib
        hd₂add hd₂leib hpsi₁1 hpsi₂1 (transitivityEquiv07Q9 p D D₁ D₂ M x) =
      comparisonValues p D₂ D₂ (RingHom.id D₂) _ _
        (transitivityEquiv07Q9 p D D₁ D₂ M).toLinearMap Om₂ Om₂ (fun _ ↦ LinearMap.id) 1
        (CompletedConnection.baseChange p D D₂ M (Om 1) (Om₂ 1) d₂ (psi 1) nabla hd₂add hd₂leib
          hpsi1 x) :=
  linearize07Q9_horizontal' p D D₂ M _ (transitivityInclusion07Q9 p D D₁ D₂ M) Om Om₂ psi d₂ nabla
    _ hd₂add hd₂leib hpsi1
    (transitivityInclusion07Q9_horizontal p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ psi hpsi d₁ d₂ nabla
      hd₁add hd₁leib hd₂add hd₂leib hpsi₁1 hpsi₂1) x

variable (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib₁ : IsGradedLeibniz D₁ Om₁ wedge₁ deRham₁ d₁)
  (hleib₂ : IsGradedLeibniz D₂ Om₂ wedge₂ deRham₂ d₂)
  (hpsi₁_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi₁ (i + 1) (wedge i ω η) = wedge₁ i (psi₁ i ω) (psi₁ 1 η))
  (hpsi₁_deRham : ∀ (i : ℕ) (ω : Om i), psi₁ (i + 1) (deRham i ω) = deRham₁ i (psi₁ i ω))
  (hpsi₂_wedge : ∀ (i : ℕ) (ω : Om₁ i) (η : Om₁ 1),
    psi₂ (i + 1) (wedge₁ i ω η) = wedge₂ i (psi₂ i ω) (psi₂ 1 η))
  (hpsi₂_deRham : ∀ (i : ℕ) (ω : Om₁ i), psi₂ (i + 1) (deRham₁ i ω) = deRham₂ i (psi₂ i ω))
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge₂ i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham₂ i (psi i ω))
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq₁ : IsSquareZero p D₁ Om₁ wedge₁ deRham₁ (CompletedConnection.baseChangeCarrier p D D₁ M)
    (CompletedConnection.baseChange p D D₁ M (Om 1) (Om₁ 1) d₁ (psi₁ 1) nabla hd₁add hd₁leib
      hpsi₁1) hleib₁)
  (hsq₁₂ : IsSquareZero p D₂ Om₂ wedge₂ deRham₂ _
    (transitivityConnection07Q9 p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ d₁ d₂ nabla hd₁add hd₁leib
      hd₂add hd₂leib hpsi₁1 hpsi₂1) hleib₂)
  (hsq₂ : IsSquareZero p D₂ Om₂ wedge₂ deRham₂ (CompletedConnection.baseChangeCarrier p D D₂ M)
    (CompletedConnection.baseChange p D D₂ M (Om 1) (Om₂ 1) d₂ (psi 1) nabla hd₂add hd₂leib
      hpsi1) hleib₂)

include hpsi in
/-- The composite of the base change maps along `D → D₁` and `D₁ → D₂` is the comparison of the
composite inclusion `m ↦ 1 ⊗ (1 ⊗ m)`. -/
theorem baseChangeComplexHom_comp_baseChangeComplexHom07Q9 :
    baseChangeComplexHom p D D₁ M Om Om₁ psi₁ wedge wedge₁ deRham deRham₁ d₁ nabla hd₁add
        hd₁leib hpsi₁1 hleib hleib₁ hpsi₁_wedge hpsi₁_deRham hsq hsq₁ ≫
      baseChangeComplexHom p D₁ D₂ (CompletedConnection.baseChangeCarrier p D D₁ M) Om₁ Om₂ psi₂
        wedge₁ wedge₂ deRham₁ deRham₂ d₂
        (CompletedConnection.baseChange p D D₁ M (Om 1) (Om₁ 1) d₁ (psi₁ 1) nabla hd₁add hd₁leib
          hpsi₁1) hd₂add hd₂leib hpsi₂1 hleib₁ hleib₂ hpsi₂_wedge hpsi₂_deRham hsq₁ hsq₁₂ =
    comparisonComplexHom07Q9 p D D₂ (algebraMap D D₂) M _ (transitivityInclusion07Q9 p D D₁ D₂ M)
      Om Om₂ psi wedge wedge₂ deRham deRham₂ nabla _ hleib hleib₂ hsq hsq₁₂ hpsi_wedge
      hpsi_deRham
      (transitivityInclusion07Q9_horizontal p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ psi hpsi d₁ d₂ nabla
        hd₁add hd₁leib hd₂add hd₂leib hpsi₁1 hpsi₂1) := by
  rw [baseChangeComplexHom_eq_comparisonComplexHom07Q9,
    baseChangeComplexHom_eq_comparisonComplexHom07Q9]
  exact comparisonComplexHom07Q9_comp p D D₁ (algebraMap D D₁) M _ _ Om Om₁ psi₁ wedge wedge₁
    deRham deRham₁ nabla _ hleib hleib₁ hsq hsq₁ hpsi₁_wedge hpsi₁_deRham _ D₂ (algebraMap D₁ D₂)
    (algebraMap D D₂) _ _ _ Om₂ psi₂ psi wedge₂ deRham₂ _ hleib₂ hsq₁₂ hpsi₂_wedge hpsi₂_deRham _
    hpsi_wedge hpsi_deRham _ (fun _ ↦ rfl) hpsi

include hpsi in
/-- **The arrow identity of transitivity**: the base change map along `D → D₂` is isomorphic,
as an arrow, to the composite of the base change maps along `D → D₁` and `D₁ → D₂`, through the
transitivity isomorphism `Crystalline.CompletedDeRham.transitivityEquiv07Q9` of their
targets. -/
def baseChangeComplexHom_trans07Q9 :
    Arrow.mk (baseChangeComplexHom p D D₂ M Om Om₂ psi wedge wedge₂ deRham deRham₂ d₂ nabla
        hd₂add hd₂leib hpsi1 hleib hleib₂ hpsi_wedge hpsi_deRham hsq hsq₂) ≅
      Arrow.mk (baseChangeComplexHom p D D₁ M Om Om₁ psi₁ wedge wedge₁ deRham deRham₁ d₁ nabla
          hd₁add hd₁leib hpsi₁1 hleib hleib₁ hpsi₁_wedge hpsi₁_deRham hsq hsq₁ ≫
        baseChangeComplexHom p D₁ D₂ (CompletedConnection.baseChangeCarrier p D D₁ M) Om₁ Om₂
          psi₂ wedge₁ wedge₂ deRham₁ deRham₂ d₂
          (CompletedConnection.baseChange p D D₁ M (Om 1) (Om₁ 1) d₁ (psi₁ 1) nabla hd₁add
            hd₁leib hpsi₁1) hd₂add hd₂leib hpsi₂1 hleib₁ hleib₂ hpsi₂_wedge hpsi₂_deRham hsq₁
          hsq₁₂) :=
  baseChangeArrowIso07Q9 p D D₂ M _ (transitivityInclusion07Q9 p D D₁ D₂ M) Om Om₂ psi wedge
      wedge₂ deRham deRham₂ d₂ nabla _ hd₂add hd₂leib hpsi1
      (transitivityInclusion07Q9_horizontal p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ psi hpsi d₁ d₂ nabla
        hd₁add hd₁leib hd₂add hd₂leib hpsi₁1 hpsi₂1) hleib hleib₂ hpsi_wedge hpsi_deRham hsq hsq₂
      hsq₁₂ (isBaseChange07Q9_transitivityInclusion p D M D₁ D₂) ≪≫
    eqToIso (by
      rw [baseChangeComplexHom_comp_baseChangeComplexHom07Q9 p D D₁ D₂ M Om Om₁ Om₂ psi₁ psi₂ psi
        hpsi wedge wedge₁ wedge₂ deRham deRham₁ deRham₂ d₁ d₂ nabla hd₁add hd₁leib hd₂add hd₂leib
        hpsi₁1 hpsi₂1 hleib hleib₁ hleib₂ hpsi₁_wedge hpsi₁_deRham hpsi₂_wedge hpsi₂_deRham
        hpsi_wedge hpsi_deRham hsq hsq₁ hsq₁₂])

end TransitivityArrow

/-! ### Invariance under isomorphisms of the data -/

section Invariance

variable (p : ℕ) {D : Type u} [CommRing D] {D' : Type u} [CommRing D'] [Algebra D D']
  {D₀ : Type u} [CommRing D₀] {D₀' : Type u} [CommRing D₀'] [Algebra D₀ D₀']
  (e : D ≃+* D₀) (e' : D' ≃+* D₀') (he : ∀ x, e' (algebraMap D D' x) = algebraMap D₀ D₀' (e x))
  {M : Type u} [AddCommGroup M] [Module D M] {M₀ : Type u} [AddCommGroup M₀] [Module D₀ M₀]
  (mu : M →ₛₗ[(e : D →+* D₀)] M₀) (muInv : M₀ →ₛₗ[(e.symm : D₀ →+* D)] M)
  (hmu₁ : ∀ m, muInv (mu m) = m) (hmu₂ : ∀ m, mu (muInv m) = m)

include he in
/-- The inverse isomorphisms are compatible with the structure maps. -/
theorem algebraMap_symm07Q9 (x : D₀) :
    e'.symm (algebraMap D₀ D₀' x) = algebraMap D D' (e.symm x) := by
  rw [RingEquiv.symm_apply_eq, he, RingEquiv.apply_symm_apply]

/-- The map `(D' ⊗_D M)^∧ → (D₀' ⊗_{D₀} M₀)^∧` induced by isomorphisms of the data,
`b ⊗ m ↦ e' b ⊗ μ m`. -/
def baseChangeCarrierMap07Q9 :
    CompletedConnection.baseChangeCarrier p D D' M →ₛₗ[(e' : D' →+* D₀')]
      CompletedConnection.baseChangeCarrier p D₀ D₀' M₀ :=
  linearize07Q9 p (e' : D' →+* D₀') (ρ := (algebraMap D₀ D₀').comp (e : D →+* D₀))
    (fun x ↦ (he x).symm)
    (semilinearComp (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀) mu)

/-- The map induced by isomorphisms of the data carries `1 ⊗ m` to `1 ⊗ μ m`. -/
theorem baseChangeCarrierMap07Q9_baseChangeInclusion (m : M) :
    baseChangeCarrierMap07Q9 p e e' he mu (CompletedConnection.baseChangeInclusion p D D' M m) =
      CompletedConnection.baseChangeInclusion p D₀ D₀' M₀ (mu m) :=
  linearize07Q9_baseChangeInclusion p _ _ _ m

include hmu₁ in
/-- The map induced by the inverse data undoes the map induced by the data. -/
theorem baseChangeCarrierMap07Q9_symm_apply (x : CompletedConnection.baseChangeCarrier p D D' M) :
    baseChangeCarrierMap07Q9 p e.symm e'.symm
        (algebraMap_symm07Q9 e e' he) muInv
        (baseChangeCarrierMap07Q9 p e e' he mu x) = x := by
  refine eq_self_of_baseChangeInclusion07Q9 p
    ((baseChangeCarrierMap07Q9 p e.symm e'.symm
        (algebraMap_symm07Q9 e e' he)
        muInv).toAddMonoidHom.comp (baseChangeCarrierMap07Q9 p e e' he mu).toAddMonoidHom)
    (fun c y ↦ by
      change baseChangeCarrierMap07Q9 p e.symm e'.symm (algebraMap_symm07Q9 e e' he) muInv
          (baseChangeCarrierMap07Q9 p e e' he mu (c • y)) =
        c • baseChangeCarrierMap07Q9 p e.symm e'.symm (algebraMap_symm07Q9 e e' he) muInv
          (baseChangeCarrierMap07Q9 p e e' he mu y)
      rw [map_smulₛₗ, map_smulₛₗ]
      simp)
    (fun m ↦ by
      change baseChangeCarrierMap07Q9 p e.symm e'.symm (algebraMap_symm07Q9 e e' he) muInv
        (baseChangeCarrierMap07Q9 p e e' he mu _) = _
      rw [baseChangeCarrierMap07Q9_baseChangeInclusion,
        baseChangeCarrierMap07Q9_baseChangeInclusion, hmu₁]) x

variable (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (Om₀ : ℕ → Type u) [∀ i, AddCommGroup (Om₀ i)] [∀ i, Module D₀ (Om₀ i)]
  (Om₀' : ℕ → Type u) [∀ i, AddCommGroup (Om₀' i)] [∀ i, Module D₀' (Om₀' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i) (psi₀ : ∀ i, Om₀ i →ₛₗ[algebraMap D₀ D₀'] Om₀' i)
  (phi : ∀ i, Om i →ₛₗ[(e : D →+* D₀)] Om₀ i) (phiInv : ∀ i, Om₀ i →ₛₗ[(e.symm : D₀ →+* D)] Om i)
  (phi' : ∀ i, Om' i →ₛₗ[(e' : D' →+* D₀')] Om₀' i)
  (phi'Inv : ∀ i, Om₀' i →ₛₗ[(e'.symm : D₀' →+* D')] Om' i)
  (hphi₁ : ∀ i ω, phiInv i (phi i ω) = ω) (hphi₂ : ∀ i ω, phi i (phiInv i ω) = ω)
  (hphi'₁ : ∀ i ω, phi'Inv i (phi' i ω) = ω) (hphi'₂ : ∀ i ω, phi' i (phi'Inv i ω) = ω)
  (hcomm : ∀ i ω, phi' i (psi i ω) = psi₀ i (phi i ω))
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (wedge₀ : ∀ i, Om₀ i →ₗ[D₀] Om₀ 1 →ₗ[D₀] Om₀ (i + 1))
  (wedge₀' : ∀ i, Om₀' i →ₗ[D₀'] Om₀' 1 →ₗ[D₀'] Om₀' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  (deRham₀ : ∀ i, Om₀ i →+ Om₀ (i + 1)) (deRham₀' : ∀ i, Om₀' i →+ Om₀' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) {d₀ : D₀ → Om₀ 1} (d₀' : D₀' → Om₀' 1)
  (nabla : CompletedConnection p D (Om 1) d M) (nabla₀ : CompletedConnection p D₀ (Om₀ 1) d₀ M₀)
  (hnabla : ∀ m, nabla₀ (mu m) = comparisonValues p D D₀ (e : D →+* D₀) M M₀ mu Om Om₀ phi 1
    (nabla m))
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hd₀'add : ∀ x y : D₀', d₀' (x + y) = d₀' x + d₀' y)
  (hd₀'leib : ∀ x y : D₀', d₀' (x * y) = x • d₀' y + y • d₀' x)
  (hpsi₀1 : ∀ x : D₀, psi₀ 1 (d₀ x) = d₀' (algebraMap D₀ D₀' x))
  (hphi'd : ∀ b : D', phi' 1 (d' b) = d₀' (e' b))

/-- The comparison of forms along `D → D₀'`, the composite `ψ₀ ∘ φ = φ' ∘ ψ`. -/
def invarianceForms07Q9 (i : ℕ) :
    Om i →ₛₗ[(algebraMap D₀ D₀').comp (e : D →+* D₀)] Om₀' i :=
  semilinearComp (psi₀ i) (phi i)

include hnabla in
/-- The composite `m ↦ 1 ⊗ μ m` is horizontal. -/
theorem invarianceInclusion07Q9_horizontal (m : M) :
    CompletedConnection.baseChange p D₀ D₀' M₀ (Om₀ 1) (Om₀' 1) d₀' (psi₀ 1) nabla₀ hd₀'add
        hd₀'leib hpsi₀1
        (semilinearComp (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀) mu m) =
      comparisonValues p D D₀' ((algebraMap D₀ D₀').comp (e : D →+* D₀)) M _
        (semilinearComp (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀) mu) Om Om₀'
        (invarianceForms07Q9 e Om Om₀ Om₀' psi₀ phi) 1 (nabla m) := by
  rw [semilinearComp_apply, CompletedConnection.baseChange_inclusion, hnabla]
  exact comparisonValues_comp07Q9 p D D₀ (e : D →+* D₀) M M₀ mu Om Om₀ phi D₀'
    (algebraMap D₀ D₀') _ _ (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀) _ Om₀' psi₀ _
    (fun _ ↦ rfl) (fun _ _ ↦ rfl) 1 (nabla m)

include hcomm hnabla hphi'd in
/-- The map induced by isomorphisms of the data is horizontal. -/
theorem baseChangeCarrierMap07Q9_horizontal
    (x : CompletedConnection.baseChangeCarrier p D D' M) :
    CompletedConnection.baseChange p D₀ D₀' M₀ (Om₀ 1) (Om₀' 1) d₀' (psi₀ 1) nabla₀ hd₀'add
        hd₀'leib hpsi₀1 (baseChangeCarrierMap07Q9 p e e' he mu x) =
      comparisonValues p D' D₀' (e' : D' →+* D₀') _ _ (baseChangeCarrierMap07Q9 p e e' he mu) Om'
        Om₀' phi' 1 (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla
          hd'add hd'leib hpsi1 x) :=
  linearize07Q9_horizontal p D D' D₀' (e' : D' →+* D₀') _ (fun x ↦ (he x).symm) M _
    (semilinearComp (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀) mu) Om Om' Om₀' psi
    phi' (invarianceForms07Q9 e Om Om₀ Om₀' psi₀ phi) (fun i ω ↦ (hcomm i ω).symm) d' nabla _
    hd'add hd'leib hpsi1 hphi'd
    (invarianceInclusion07Q9_horizontal p e mu Om Om₀ Om₀' psi₀ phi d₀' nabla nabla₀ hnabla
      hd₀'add hd₀'leib hpsi₀1) x

variable (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hleib₀ : IsGradedLeibniz D₀ Om₀ wedge₀ deRham₀ d₀)
  (hleib₀' : IsGradedLeibniz D₀' Om₀' wedge₀' deRham₀' d₀')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))
  (hpsi₀_wedge : ∀ (i : ℕ) (ω : Om₀ i) (η : Om₀ 1),
    psi₀ (i + 1) (wedge₀ i ω η) = wedge₀' i (psi₀ i ω) (psi₀ 1 η))
  (hpsi₀_deRham : ∀ (i : ℕ) (ω : Om₀ i), psi₀ (i + 1) (deRham₀ i ω) = deRham₀' i (psi₀ i ω))
  (hphi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    phi (i + 1) (wedge i ω η) = wedge₀ i (phi i ω) (phi 1 η))
  (hphi_deRham : ∀ (i : ℕ) (ω : Om i), phi (i + 1) (deRham i ω) = deRham₀ i (phi i ω))
  (hphi'_wedge : ∀ (i : ℕ) (ω : Om' i) (η : Om' 1),
    phi' (i + 1) (wedge' i ω η) = wedge₀' i (phi' i ω) (phi' 1 η))
  (hphi'_deRham : ∀ (i : ℕ) (ω : Om' i), phi' (i + 1) (deRham' i ω) = deRham₀' i (phi' i ω))
  (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
  (hsq' : IsSquareZero p D' Om' wedge' deRham' (CompletedConnection.baseChangeCarrier p D D' M)
    (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
      hpsi1) hleib')
  (hsq₀ : IsSquareZero p D₀ Om₀ wedge₀ deRham₀ M₀ nabla₀ hleib₀)
  (hsq₀' : IsSquareZero p D₀' Om₀' wedge₀' deRham₀'
    (CompletedConnection.baseChangeCarrier p D₀ D₀' M₀)
    (CompletedConnection.baseChange p D₀ D₀' M₀ (Om₀ 1) (Om₀' 1) d₀' (psi₀ 1) nabla₀ hd₀'add
      hd₀'leib hpsi₀1) hleib₀')

include hmu₁ hmu₂ hphi₁ hphi₂ hphi'₁ hphi'₂ hcomm hphi'd in
/-- **Invariance of the base change map under isomorphisms of the data**: isomorphisms
`D ≅ D₀`, `D' ≅ D₀'` compatible with the structure maps, a horizontal isomorphism `M ≅ M₀` and
isomorphisms of the forms compatible with the comparisons `ψ`, `ψ₀`, the wedge products and the
de Rham differentials, induce an isomorphism, in the arrow category, between the base change maps
`M ⊗^∧_D Ω^* ⟶ M' ⊗^∧_{D'} Ω'^*` and `M₀ ⊗^∧_{D₀} Ω₀^* ⟶ M₀' ⊗^∧_{D₀'} Ω₀'^*`. -/
def baseChangeArrowIsoOfIso07Q9 :
    Arrow.mk (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla
        hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq') ≅
      Arrow.mk (baseChangeComplexHom p D₀ D₀' M₀ Om₀ Om₀' psi₀ wedge₀ wedge₀' deRham₀ deRham₀'
        d₀' nabla₀ hd₀'add hd₀'leib hpsi₀1 hleib₀ hleib₀' hpsi₀_wedge hpsi₀_deRham hsq₀ hsq₀') :=
  haveI hα := isIso_comparisonComplexHom07Q9 p D D₀ (e : D →+* D₀) M M₀ mu Om Om₀ phi wedge
    wedge₀ deRham deRham₀ nabla nabla₀ hleib hleib₀ hsq hsq₀ hphi_wedge hphi_deRham hnabla
    (e.symm : D₀ →+* D) muInv phiInv hmu₁ hmu₂ hphi₁ hphi₂
  haveI hβ := isIso_comparisonComplexHom07Q9 p D' D₀' (e' : D' →+* D₀') _ _
    (baseChangeCarrierMap07Q9 p e e' he mu) Om' Om₀' phi' wedge' wedge₀' deRham' deRham₀' _ _
    hleib' hleib₀' hsq' hsq₀' hphi'_wedge hphi'_deRham
    (baseChangeCarrierMap07Q9_horizontal p e e' he mu Om Om' Om₀ Om₀' psi psi₀ phi phi' hcomm d'
      d₀' nabla nabla₀ hnabla hd'add hd'leib hpsi1 hd₀'add hd₀'leib hpsi₀1 hphi'd)
    (e'.symm : D₀' →+* D')
    (baseChangeCarrierMap07Q9 p e.symm e'.symm (algebraMap_symm07Q9 e e' he) muInv)
    phi'Inv (baseChangeCarrierMap07Q9_symm_apply p e e' he mu muInv hmu₁)
    (baseChangeCarrierMap07Q9_symm_apply p e.symm e'.symm (algebraMap_symm07Q9 e e' he) muInv mu
      hmu₂) hphi'₁ hphi'₂
  Arrow.isoMk (asIso (comparisonComplexHom07Q9 p D D₀ (e : D →+* D₀) M M₀ mu Om Om₀ phi wedge
      wedge₀ deRham deRham₀ nabla nabla₀ hleib hleib₀ hsq hsq₀ hphi_wedge hphi_deRham hnabla))
    (asIso (comparisonComplexHom07Q9 p D' D₀' (e' : D' →+* D₀') _ _
      (baseChangeCarrierMap07Q9 p e e' he mu) Om' Om₀' phi' wedge' wedge₀' deRham' deRham₀' _ _
      hleib' hleib₀' hsq' hsq₀' hphi'_wedge hphi'_deRham
      (baseChangeCarrierMap07Q9_horizontal p e e' he mu Om Om' Om₀ Om₀' psi psi₀ phi phi' hcomm
        d' d₀' nabla nabla₀ hnabla hd'add hd'leib hpsi1 hd₀'add hd₀'leib hpsi₀1 hphi'd))) (by
    simp only [Arrow.mk_hom, asIso_hom]
    rw [baseChangeComplexHom_eq_comparisonComplexHom07Q9 p D₀ D₀' M₀,
      comparisonComplexHom07Q9_comp p D D₀ (e : D →+* D₀) M M₀ mu Om Om₀ phi wedge wedge₀ deRham
        deRham₀ nabla nabla₀ hleib hleib₀ hsq hsq₀ hphi_wedge hphi_deRham hnabla D₀'
        (algebraMap D₀ D₀') ((algebraMap D₀ D₀').comp (e : D →+* D₀)) _
        (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀)
        (semilinearComp (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀) mu) Om₀'
        psi₀ (invarianceForms07Q9 e Om Om₀ Om₀' psi₀ phi) wedge₀' deRham₀' _ hleib₀' hsq₀'
        hpsi₀_wedge hpsi₀_deRham _
        (fun i ω η ↦ by
          simp only [invarianceForms07Q9, semilinearComp_apply, hphi_wedge, hpsi₀_wedge])
        (fun i ω ↦ by
          simp only [invarianceForms07Q9, semilinearComp_apply, hphi_deRham, hpsi₀_deRham])
        (invarianceInclusion07Q9_horizontal p e mu Om Om₀ Om₀' psi₀ phi d₀' nabla nabla₀ hnabla
          hd₀'add hd₀'leib hpsi₀1) (fun _ ↦ rfl) (fun _ _ ↦ rfl)]
    exact (baseChangeComplexHom_comp_linearize07Q9 p D D' D₀' (e' : D' →+* D₀') _
      (fun x ↦ (he x).symm) M _
      (semilinearComp (CompletedConnection.baseChangeInclusion p D₀ D₀' M₀) mu) Om Om' Om₀'
      psi phi' (invarianceForms07Q9 e Om Om₀ Om₀' psi₀ phi) (fun i ω ↦ (hcomm i ω).symm) wedge
      wedge' wedge₀' deRham deRham' deRham₀' d' nabla _ hd'add hd'leib hpsi1 hphi'd _ hleib hleib'
      hleib₀' hpsi_wedge hpsi_deRham hphi'_wedge hphi'_deRham _ _ hsq hsq' hsq₀').symm)

end Invariance

end CompletedDeRham

end Crystalline

end
