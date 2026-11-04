module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.ColumnAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex

/-!
# The complexes `M ⊗^∧_D Ω^*_D` of isomorphic data are isomorphic

Let `e : D ≃+* D'` be a ring isomorphism, together with a semilinear isomorphism of modules
`M → M'` and one of graded forms `Ω^i → Ω'^i` in each degree, each presented as a semilinear map
with a semilinear inverse, compatible with the wedge products, with the de Rham differentials of
the forms and with the two connections. Then the two complexes `M ⊗^∧_D Ω^*_D` and
`M' ⊗^∧_{D'} Ω'^*_{D'}` of [Stacks, Proposition 60.21.3, Tag 07LG] are isomorphic, through the
degreewise comparison `Crystalline.CompletedDeRham.comparisonValues`, and so have the same
cohomology in every degree. A connection on `M` also transports along such an identification to a
connection on `M'`.

## Main definitions

Everything lives in the namespace `Crystalline.CompletedDeRham`.

* `isoValuesFwd` and `isoValuesBwd` — the degreewise comparisons in the two directions.
* `comparisonIsoValues` — **the degree-`i` comparison as an isomorphism of abelian groups.**
* `comparisonComplexIso` — **the two complexes are isomorphic.**
* `comparisonHomologyIso` — hence their cohomology agrees in every degree.
* `transportConnection` — the connection on `M'` transported from one on `M`.

## Main results

* `isoValues_bwd_fwd` and `isoValues_fwd_bwd` — the two comparisons are mutually inverse.
* `surjective_isoValuesFwd` — the degreewise comparison is surjective.
* `isSquareZero_comparison` — **the square-zero hypothesis transports** along the comparison.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct

universe v w uD uD'

namespace Crystalline

namespace CompletedDeRham

section SemilinearIso

variable (p : ℕ) {D : Type uD} [CommRing D] {D' : Type uD'} [CommRing D'] (e : D ≃+* D')
  {M : Type w} [AddCommGroup M] [Module D M] {M' : Type w} [AddCommGroup M'] [Module D' M']
  (mu : M →ₛₗ[(e : D →+* D')] M') (muInv : M' →ₛₗ[(e.symm : D' →+* D)] M)
  {Om : ℕ → Type v} [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  {Om' : ℕ → Type v} [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[(e : D →+* D')] Om' i)
  (psiInv : ∀ i, Om' i →ₛₗ[(e.symm : D' →+* D)] Om i)

/-- The forward degreewise comparison `M ⊗̂_D Ω^i → M' ⊗̂_{D'} Ω'^i`. -/
public abbrev isoValuesFwd (i : ℕ) :
    CompletedTensor p D (Om i) M →ₛₗ[(e : D →+* D')] CompletedTensor p D' (Om' i) M' :=
  comparisonValues p D D' (e : D →+* D') M M' mu Om Om' psi i

/-- The backward degreewise comparison, built from the inverse ring isomorphism and the inverse
module and forms isomorphisms. -/
public abbrev isoValuesBwd (i : ℕ) :
    CompletedTensor p D' (Om' i) M' →ₛₗ[(e.symm : D' →+* D)] CompletedTensor p D (Om i) M :=
  comparisonValues p D' D (e.symm : D' →+* D) M' M muInv Om' Om psiInv i

variable (hmu : ∀ m : M, muInv (mu m) = m) (hmu' : ∀ m' : M', mu (muInv m') = m')
  (hpsi : ∀ (i : ℕ) (ω : Om i), psiInv i (psi i ω) = ω)
  (hpsi' : ∀ (i : ℕ) (ω : Om' i), psi i (psiInv i ω) = ω)

include hmu hpsi in
/-- **The backward comparison undoes the forward one.** -/
public theorem isoValues_bwd_fwd (i : ℕ) (z : CompletedTensor p D (Om i) M) :
    isoValuesBwd p e muInv psiInv i (isoValuesFwd p e mu psi i z) = z := by
  refine adicCompletionMapₛₗ_comp_eq_self (TensorProduct.map mu (psi i))
    (TensorProduct.map muInv (psiInv i))
    (map_pAdicIdeal_le p (e : D →+* D')) (map_pAdicIdeal_le p (e.symm : D' →+* D)) ?_ z
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m ω =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul]
    show muInv (mu m) ⊗ₜ[D] psiInv i (psi i ω) = m ⊗ₜ[D] ω
    rw [hmu, hpsi]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

include hmu' hpsi' in
/-- **The forward comparison undoes the backward one.** -/
public theorem isoValues_fwd_bwd (i : ℕ) (z : CompletedTensor p D' (Om' i) M') :
    isoValuesFwd p e mu psi i (isoValuesBwd p e muInv psiInv i z) = z :=
  isoValues_bwd_fwd p e.symm muInv mu psiInv psi hmu' hpsi' i z

include hmu' hpsi' in
/-- **The degreewise comparison is surjective.** -/
public theorem surjective_isoValuesFwd (i : ℕ) :
    Function.Surjective (isoValuesFwd p e mu psi i) :=
  fun z => ⟨isoValuesBwd p e muInv psiInv i z,
    isoValues_fwd_bwd p e mu muInv psi psiInv hmu' hpsi' i z⟩

include hmu hmu' hpsi hpsi' in
/-- **The degree-`i` comparison of the two complexes, as an isomorphism of abelian groups.** -/
public def comparisonIsoValues (i : ℕ) :
    AddCommGrpCat.of (CompletedTensor p D (Om i) M) ≅
      AddCommGrpCat.of (CompletedTensor p D' (Om' i) M') where
  hom := AddCommGrpCat.ofHom (isoValuesFwd p e mu psi i).toAddMonoidHom
  inv := AddCommGrpCat.ofHom (isoValuesBwd p e muInv psiInv i).toAddMonoidHom
  hom_inv_id :=
    AddCommGrpCat.ext (isoValues_bwd_fwd p e mu muInv psi psiInv hmu hpsi i)
  inv_hom_id :=
    AddCommGrpCat.ext (isoValues_fwd_bwd p e mu muInv psi psiInv hmu' hpsi' i)

include hmu hmu' hpsi hpsi' in
/-- The forward direction of the degreewise comparison isomorphism is the forward comparison. -/
@[simp] public theorem comparisonIsoValues_hom (i : ℕ) :
    (comparisonIsoValues p e mu muInv psi psiInv hmu hmu' hpsi hpsi' i).hom =
      AddCommGrpCat.ofHom (isoValuesFwd p e mu psi i).toAddMonoidHom :=
  rfl

variable (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {dm : D → Om 1} {dm' : D' → Om' 1}
  (nabla : CompletedConnection p D (Om 1) dm M)
  (nabla' : CompletedConnection p D' (Om' 1) dm' M')
  (hleib : IsGradedLeibniz D Om wedge deRham dm)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' dm')
  (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (eta : Om 1),
    psi (i + 1) (wedge i ω eta) = wedge' i (psi i ω) (psi 1 eta))
  (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))
  (hnabla : ∀ m : M, nabla' (mu m) = isoValuesFwd p e mu psi 1 (nabla m))

include hmu' hpsi' hpsi_wedge hpsi_deRham hnabla in
/-- **The square-zero hypothesis transports along the comparison**: if the differential of
`M ⊗^∧_D Ω^*_D` squares to zero, so does that of `M' ⊗^∧_{D'} Ω'^*_{D'}`. -/
public theorem isSquareZero_comparison
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib) :
    IsSquareZero p D' Om' wedge' deRham' M' nabla' hleib' := by
  intro i
  refine AddMonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := surjective_isoValuesFwd p e mu muInv psi psiInv hmu' hpsi' i y
  show differential p D' Om' wedge' deRham' M' nabla' hleib' (i + 1)
      (differential p D' Om' wedge' deRham' M' nabla' hleib' i
        (isoValuesFwd p e mu psi i x)) = 0
  rw [differential_comparisonValues p D D' (e : D →+* D') M M' mu Om Om' psi wedge wedge'
      deRham deRham' nabla nabla' hleib hleib' hpsi_wedge hpsi_deRham hnabla i x,
    differential_comparisonValues p D D' (e : D →+* D') M M' mu Om Om' psi wedge wedge'
      deRham deRham' nabla nabla' hleib hleib' hpsi_wedge hpsi_deRham hnabla (i + 1)
      (differential p D Om wedge deRham M nabla hleib i x),
    show differential p D Om wedge deRham M nabla hleib (i + 1)
        (differential p D Om wedge deRham M nabla hleib i x) = 0 from
      DFunLike.congr_fun (hsq i) x,
    map_zero]

include hmu hmu' hpsi hpsi' hpsi_wedge hpsi_deRham hnabla in
/-- **The complexes `M ⊗^∧_D Ω^*_D` and `M' ⊗^∧_{D'} Ω'^*_{D'}` of isomorphic data are
isomorphic**, in degree `i` by `Crystalline.CompletedDeRham.comparisonIsoValues`. -/
public def comparisonComplexIso
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : IsSquareZero p D' Om' wedge' deRham' M' nabla' hleib') :
    complex p D Om wedge deRham M nabla hleib hsq ≅
      complex p D' Om' wedge' deRham' M' nabla' hleib' hsq' := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => comparisonIsoValues p e mu muInv psi psiInv hmu hmu' hpsi hpsi' i) ?_
  intro i j hij
  change i + 1 = j at hij
  subst hij
  rw [complex_d p D Om wedge deRham M nabla hleib hsq i,
    complex_d p D' Om' wedge' deRham' M' nabla' hleib' hsq' i,
    comparisonIsoValues_hom p e mu muInv psi psiInv hmu hmu' hpsi hpsi',
    comparisonIsoValues_hom p e mu muInv psi psiInv hmu hmu' hpsi hpsi']
  exact AddCommGrpCat.ext fun x => differential_comparisonValues p D D' (e : D →+* D') M M' mu
    Om Om' psi wedge wedge' deRham deRham' nabla nabla' hleib hleib' hpsi_wedge hpsi_deRham hnabla
    i x

include hmu hmu' hpsi hpsi' hpsi_wedge hpsi_deRham hnabla in
/-- **The cohomology of the two complexes agrees in every degree.** -/
public def comparisonHomologyIso
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : IsSquareZero p D' Om' wedge' deRham' M' nabla' hleib') (j : ℕ) :
    (complex p D Om wedge deRham M nabla hleib hsq).homology j ≅
      (complex p D' Om' wedge' deRham' M' nabla' hleib' hsq').homology j :=
  HomologicalComplex.homologyMapIso
    (comparisonComplexIso p e mu muInv psi psiInv hmu hmu' hpsi hpsi' wedge wedge' deRham
      deRham' nabla nabla' hleib hleib' hpsi_wedge hpsi_deRham hnabla hsq hsq') j

end SemilinearIso

/-! ### The transported connection -/

section TransportConnection

variable (p : ℕ) {D : Type uD} [CommRing D] {D' : Type uD'} [CommRing D'] (e : D ≃+* D')
  {M : Type w} [AddCommGroup M] [Module D M] {M' : Type w} [AddCommGroup M'] [Module D' M']
  (mu : M →ₛₗ[(e : D →+* D')] M') (muInv : M' →ₛₗ[(e.symm : D' →+* D)] M)
  {Om : ℕ → Type v} [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  {Om' : ℕ → Type v} [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[(e : D →+* D')] Om' i)
  (dm : D → Om 1) (dm' : D' → Om' 1)
  (nabla : CompletedConnection p D (Om 1) dm M)

/-- **The connection transported along an identification of the data**: the connection on `M'`
sending `m'` to the image of `∇ (μ⁻¹ m')`, for an identification of the forms carrying
`d : D → Ω¹` to `d' : D' → Ω'¹` (the hypothesis `hdm`). -/
public def transportConnection (hmu' : ∀ m' : M', mu (muInv m') = m')
    (hdm : ∀ f : D, psi 1 (dm f) = dm' (e f)) :
    CompletedConnection p D' (Om' 1) dm' M' where
  toFun m' := isoValuesFwd p e mu psi 1 (nabla (muInv m'))
  map_add' m' n' := by
    rw [map_add, nabla.map_add, map_add]
  leibniz' a m' := by
    show isoValuesFwd p e mu psi 1 (nabla (muInv (a • m'))) =
      a • isoValuesFwd p e mu psi 1 (nabla (muInv m')) +
        toCompletedTensor p D' (Om' 1) M' (m' ⊗ₜ[D'] dm' a)
    rw [muInv.map_smulₛₗ, nabla.leibniz, map_add,
      (isoValuesFwd p e mu psi 1).map_smulₛₗ,
      comparisonValues_of_tmul p D D' (e : D →+* D') M M' mu Om Om' psi 1,
      hdm, hmu']
    simp

/-- The transported connection sends `μ m` to the image of `∇ m` under the identification of the
completed tensor products of `M` and `M'` with the one-forms. -/
@[simp] public theorem transportConnection_apply (hmu : ∀ m : M, muInv (mu m) = m)
    (hmu' : ∀ m' : M', mu (muInv m') = m') (hdm : ∀ f : D, psi 1 (dm f) = dm' (e f)) (m : M) :
    transportConnection p e mu muInv psi dm dm' nabla hmu' hdm (mu m) =
      isoValuesFwd p e mu psi 1 (nabla m) := by
  show isoValuesFwd p e mu psi 1 (nabla (muInv (mu m))) = _
  rw [hmu]

end TransportConnection

end CompletedDeRham

end Crystalline

end
