module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.Tactic.TFAE
import StacksCore.Tactic.StacksAttribute

/-!
# The universal factorization map is étale away from the resultant

Let `R` be a ring and `n = m + k`. The universal factorization map
`R[a₀, …, aₙ₋₁] → S = R[b₀, …, bₘ₋₁] ⊗[R] R[c₀, …, cₖ₋₁]` sends the coefficients of the
generic monic polynomial of degree `n` to those of the product `g h` of the generic monic
polynomials `g = xᵐ + bₘ₋₁ xᵐ⁻¹ + ⋯ + b₀` and `h = xᵏ + cₖ₋₁ xᵏ⁻¹ + ⋯ + c₀`. Writing `aⱼ(b, c)` for
the coefficient of `xʲ` in `g h`, so that `S = R[a][b, c]/(aⱼ(b, c) - aⱼ)`, the matrix of partial
derivatives of these relations with respect to the `b`'s and `c`'s is the Sylvester matrix of
`g` and `h`, the transpose of the matrix of the linear map `(p, q) ↦ g q + h p`, and its
determinant `Δ` is the resultant `Res(g, h)`.

Consequently, for a prime `q ⊂ S` the following are equivalent: `R[a] → S` is étale at `q`;
`Δ ∉ q`; the images of `g` and `h` in `κ(q)[x]` are coprime. In particular `R[a] → S[1/Δ]` is
étale.

## Main results

* `MvPolynomial.ker_aeval_universalFactorizationMap`: `S = R[a][b, c]/(aⱼ(b, c) - aⱼ)`.
* `MvPolynomial.pderiv_universalFactorizationMap_eq_sylvester`: the matrix of partial
  derivatives is the Sylvester matrix.
* `MvPolynomial.aeval_pderiv_universalFactorizationMap_eq_transpose_toMatrix_sylvesterMap`:
  in `S`, it is the transpose of the matrix of `(p, q) ↦ g q + h p`.
* `MvPolynomial.aeval_det_pderiv_universalFactorizationMap`: its determinant is `Res(g, h)`.
* `MvPolynomial.tfae_universalFactorizationMap_etale`: étale at `q` ⇔ `Δ ∉ q` ⇔ `g`, `h` coprime
  in `κ(q)[x]`.
* `MvPolynomial.exists_mulVec_sylvester_map_eq_zero_iff`: over `κ(q)` the Sylvester matrix has a
  nonzero kernel if and only if the images of `g` and `h` have a common nonunit factor.
* `MvPolynomial.etale_localizationAway_resultant_universalFactorizationMap`: `R[a] → S[1/Δ]` is
  étale.
* `MvPolynomial.isEtaleAt_universalFactorizationMap_iff`: `R[a] → S` is étale at `q` in the sense
  of `Algebra.IsEtaleAt` if and only if `Δ ∉ q`.
* `Algebra.PreSubmersivePresentation.isUnit_jacobian_of_formallyUnramified`: the Jacobian of a
  pre-submersive presentation of a formally unramified algebra is a unit.

## Implementation notes

The degrees `m`, `k` may be zero. As in `MvPolynomial.universalFactorizationMap`, the variables are
indexed by increasing degree: `bᵢ` is the coefficient of `xⁱ` in `g` (the source's `b_{m-i}`), and
similarly for `c` and `a`. With this indexing the matrix of partial derivatives is the source's
matrix with its rows reversed within the `b`- and `c`-blocks and its columns reversed, and the
Sylvester matrix and resultant are `Polynomial.sylvester` and `Polynomial.resultant`. Reordering
the rows and columns to the source's order multiplies the determinant by `(-1)ᵐᵏ`; the sign of the
resultant is a matter of convention, and none of the conditions on primes depends on it. The
relations are taken as `aⱼ(b, c) - aⱼ`, as in the source;
`MvPolynomial.universalFactorizationMapPresentation` uses their negatives. In
`Polynomial.sylvesterMap` the summands of the source are swapped: the pair `(p, q)` with
`deg p < m`, `deg q < k` is sent to `g q + h p`. Étaleness at `q` means that `R[a] → S_f` is étale
for some `f ∉ q`.

## References

* [Stacks Project, Tag 00UA](https://stacks.math.columbia.edu/tag/00UA)
-/

@[expose] public section

open MvPolynomial
open scoped Matrix TensorProduct

namespace Algebra.PreSubmersivePresentation

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The Jacobian of a pre-submersive presentation, with finitely many relations, of a formally
unramified algebra is a unit. -/
theorem isUnit_jacobian_of_formallyUnramified [Finite σ] [FormallyUnramified R S]
    (P : PreSubmersivePresentation R S ι σ) : IsUnit P.jacobian := by
  classical
  cases nonempty_fintype σ
  have hc : Function.Surjective P.toExtension.cotangentComplex := fun v ↦
    (Extension.exact_cotangentComplex_toKaehler (P := P.toExtension) v).mp
      (Subsingleton.elim _ _)
  have haux : Function.Surjective P.cotangentComplexAux :=
    (Finsupp.linearEquivFunOnFinite S S σ).surjective.comp <|
      (Finsupp.comapDomain_surjective P.map_inj).comp <|
        P.cotangentSpaceBasis.repr.surjective.comp hc
  have key : ∀ y ∈ Ideal.span (Set.range P.relation),
      (fun i ↦ aeval P.val (pderiv (P.map i) y)) ∈ LinearMap.range P.aevalDifferential := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨Pi.single j 1, funext fun i ↦ P.aevalDifferential_single j i⟩
    | zero => exact ⟨0, by ext; simp⟩
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext i
      simp
    | smul a x hx' hx =>
      have h0 : aeval P.val x = 0 := by
        rw [← RingHom.mem_ker, ← Generators.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
        exact hx'
      convert Submodule.smul_mem _ (aeval P.val a) hx using 1
      ext i
      simp [Derivation.leibniz, h0]
  have hsurj : Function.Surjective P.aevalDifferential := by
    intro v
    obtain ⟨c, rfl⟩ := haux v
    obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective c
    obtain ⟨w, hw⟩ := key x.1 (P.span_range_relation_eq_ker ▸ x.2)
    exact ⟨w, hw.trans (funext fun i ↦ (P.cotangentComplexAux_apply x i).symm)⟩
  rw [isUnit_jacobian_iff_aevalDifferential_bijective]
  exact OrzechProperty.bijective_of_surjective_endomorphism _ hsurj

end Algebra.PreSubmersivePresentation

namespace Polynomial

/-- The image of the free monic polynomial of degree `n` under any ring map has degree at most
`n`. -/
theorem natDegree_map_freeMonic_le {R S : Type*} [CommRing R] [Semiring S] (n : ℕ)
    (f : MvPolynomial (Fin n) R →+* S) : ((freeMonic R n).map f).natDegree ≤ n := by
  refine natDegree_map_le.trans ?_
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton]
  · exact (natDegree_freeMonic R n).le

end Polynomial

namespace MvPolynomial

variable (R : Type*) [CommRing R] (n m k : ℕ) (hn : n = m + k)

local notation "𝓢" => MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R

/-- The generic monic polynomial `g = xᵐ + bₘ₋₁ xᵐ⁻¹ + ⋯ + b₀` over `S`. -/
local notation "𝐠" => Polynomial.map (Algebra.TensorProduct.includeLeftRingHom :
  MvPolynomial (Fin m) R →+* 𝓢) (Polynomial.freeMonic R m)

/-- The generic monic polynomial `h = xᵏ + cₖ₋₁ xᵏ⁻¹ + ⋯ + c₀` over `S`. -/
local notation "𝐡" => Polynomial.map (AlgHom.toRingHom (Algebra.TensorProduct.includeRight :
  MvPolynomial (Fin k) R →ₐ[R] 𝓢)) (Polynomial.freeMonic R k)

/-- The `R[a]`-algebra map `R[a][b, c] → S` sending `bᵢ ↦ bᵢ` and `cⱼ ↦ cⱼ` is surjective. -/
@[stacks 00UA "The symbolic presentation `S = R[b, c]/(a_k(b, c) - a_k)`: the map from
`R[b, c]` is surjective."]
theorem surjective_aeval_universalFactorizationMap :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Function.Surjective (aeval (R := MvPolynomial (Fin n) R) (S₁ := 𝓢)
      (Sum.elim (fun i ↦ X i ⊗ₜ[R] 1) fun j ↦ 1 ⊗ₜ[R] X j)) :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  (universalFactorizationMapPresentation R n m k hn).algebraMap_surjective

/-- The kernel of `R[a][b, c] → S` is generated by the relations `aⱼ(b, c) - aⱼ`, where
`aⱼ(b, c)` is the image of `aⱼ` written as a polynomial in the `b`'s and `c`'s. -/
@[stacks 00UA "The symbolic presentation `S = R[b, c]/(a_k(b, c) - a_k)`: the kernel. The
polynomial `a_k(b, c)` is the image of `a_k` under `R[a] → S ≃ R[b, c]`."]
theorem ker_aeval_universalFactorizationMap :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    RingHom.ker (aeval (R := MvPolynomial (Fin n) R) (S₁ := 𝓢)
      (Sum.elim (fun i ↦ X i ⊗ₜ[R] 1) fun j ↦ 1 ⊗ₜ[R] X j)) =
    Ideal.span (Set.range fun j : Fin n ↦
      (tensorEquivSum R (Fin m) (Fin k) R (universalFactorizationMap R n m k hn (X j))).map C -
        C (X j)) := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  refine (ker_eval₂Hom_universalFactorizationMap R n m k hn).trans (le_antisymm ?_ ?_) <;>
    rw [Ideal.span_le] <;> rintro _ ⟨j, rfl⟩ <;> dsimp only <;> rw [← neg_sub] <;>
    exact neg_mem (Ideal.subset_span ⟨j, rfl⟩)

/-- The matrix of partial derivatives of the relations `aⱼ(b, c) - aⱼ` with respect to the
variables `bᵢ`, `cⱼ` is the transpose of the Sylvester matrix of the generic monic polynomials
`g` and `h` over `R[a][b, c]`. Its rows are indexed by the variables and its columns by the
relations. -/
@[stacks 00UA "The matrix of partial derivatives is the Sylvester matrix of `g` and `h`.
Mathlib's `Polynomial.sylvester` is the transpose of the source's matrix, and the variables are
ordered by increasing degree; see the module docstring."]
theorem pderiv_universalFactorizationMap_eq_sylvester :
    (Matrix.of fun (i : Fin m ⊕ Fin k) (j : Fin n) ↦ pderiv i
      ((tensorEquivSum R (Fin m) (Fin k) R (universalFactorizationMap R n m k hn (X j))).map C -
        C (X j))) =
    ((Polynomial.sylvester
      ((Polynomial.freeMonic R m).map ((mapAlgHom (Algebra.ofId R (MvPolynomial (Fin n) R))).comp
        (rename Sum.inl)).toRingHom)
      ((Polynomial.freeMonic R k).map ((mapAlgHom (Algebra.ofId R (MvPolynomial (Fin n) R))).comp
        (rename Sum.inr)).toRingHom) m k).submatrix (finCongr hn) finSumFinEquiv)ᵀ := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have hJ := universalFactorizationMapPresentation_jacobiMatrix R n m k hn
  ext i j : 1
  have h := congr($hJ ((finCongr hn).symm (finSumFinEquiv i)) j)
  have hmap : (universalFactorizationMapPresentation R n m k hn).map
      ((finCongr hn).symm (finSumFinEquiv i)) = i := by
    simp [universalFactorizationMapPresentation_map]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hmap] at h
  rw [Matrix.of_apply, ← neg_sub, map_neg]
  refine (congr(-$h)).trans ?_
  simp only [Matrix.neg_apply, Matrix.transpose_apply, Matrix.reindex_apply, neg_neg,
    Matrix.submatrix_apply]
  congr 1

/-- The image in `S[x]` of the generic polynomial with coefficients the `bᵢ` in `R[a][b, c]` is
`g`. -/
private theorem map_aeval_freeMonic_inl :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    ((Polynomial.freeMonic R m).map ((mapAlgHom (Algebra.ofId R (MvPolynomial (Fin n) R))).comp
        (rename Sum.inl)).toRingHom).map (aeval (R := MvPolynomial (Fin n) R) (S₁ := 𝓢)
      (Sum.elim (fun i ↦ X i ⊗ₜ[R] 1) fun j ↦ 1 ⊗ₜ[R] X j)).toRingHom = 𝐠 := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  rw [Polynomial.map_map]
  congr 1
  ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]

/-- The image in `S[x]` of the generic polynomial with coefficients the `cⱼ` in `R[a][b, c]` is
`h`. -/
private theorem map_aeval_freeMonic_inr :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    ((Polynomial.freeMonic R k).map ((mapAlgHom (Algebra.ofId R (MvPolynomial (Fin n) R))).comp
        (rename Sum.inr)).toRingHom).map (aeval (R := MvPolynomial (Fin n) R) (S₁ := 𝓢)
      (Sum.elim (fun i ↦ X i ⊗ₜ[R] 1) fun j ↦ 1 ⊗ₜ[R] X j)).toRingHom = 𝐡 := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  rw [Polynomial.map_map]
  congr 1
  ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]

/-- In `S`, the matrix of partial derivatives of the relations `aⱼ(b, c) - aⱼ` is the transpose
of the matrix of the `S`-linear map `S[x]_{<m} × S[x]_{<k} → S[x]_{<m+k}`,
`(p, q) ↦ g q + h p`, in the monomial bases. -/
@[stacks 00UA "The Sylvester matrix is the transpose of the matrix of the linear map
`S[x]_{<m} ⊕ S[x]_{<n} → S[x]_{<n+m}`, `a ⊕ b ↦ ag + bh`, stated for the matrix of partial
derivatives with entries in `S`. Mathlib's `Polynomial.sylvesterMap` lists the two summands in
the other order; see the module docstring."]
theorem aeval_pderiv_universalFactorizationMap_eq_transpose_toMatrix_sylvesterMap :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (Matrix.of fun (i : Fin m ⊕ Fin k) (j : Fin n) ↦
      aeval (R := MvPolynomial (Fin n) R) (S₁ := 𝓢)
        (Sum.elim (fun i ↦ X i ⊗ₜ[R] 1) fun j ↦ 1 ⊗ₜ[R] X j) (pderiv i
          ((tensorEquivSum R (Fin m) (Fin k) R
            (universalFactorizationMap R n m k hn (X j))).map C - C (X j)))) =
    ((LinearMap.toMatrix
      (((Polynomial.degreeLT.basis 𝓢 m).prod (Polynomial.degreeLT.basis 𝓢 k)).reindex
        finSumFinEquiv)
      (Polynomial.degreeLT.basis 𝓢 (m + k))
      (Polynomial.sylvesterMap 𝐠 𝐡 (Polynomial.natDegree_map_freeMonic_le m _)
        (Polynomial.natDegree_map_freeMonic_le k _))).submatrix (finCongr hn) finSumFinEquiv)ᵀ := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  ext i j : 1
  have h := congr($(pderiv_universalFactorizationMap_eq_sylvester R n m k hn) i j)
  rw [Polynomial.toMatrix_sylvesterMap']
  simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply] at h ⊢
  rw [h, ← map_aeval_freeMonic_inl R n m k hn, ← map_aeval_freeMonic_inr R n m k hn,
    Polynomial.sylvester_map_map]
  rfl

/-- The determinant `Δ` of the matrix of partial derivatives of the relations `aⱼ(b, c) - aⱼ`,
with the variables `b₀, …, bₘ₋₁, c₀, …, cₖ₋₁` in this order, is in `S` the resultant
`Res(g, h)`. -/
@[stacks 00UA "The determinant `Δ` of the matrix of partial derivatives is the resultant
`Res_x(g, h)`."]
theorem aeval_det_pderiv_universalFactorizationMap :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    aeval (R := MvPolynomial (Fin n) R) (S₁ := 𝓢)
      (Sum.elim (fun i ↦ X i ⊗ₜ[R] 1) fun j ↦ 1 ⊗ₜ[R] X j)
      (Matrix.of fun i j : Fin n ↦ pderiv (finSumFinEquiv.symm (finCongr hn i))
        ((tensorEquivSum R (Fin m) (Fin k) R
          (universalFactorizationMap R n m k hn (X j))).map C - C (X j))).det =
    Polynomial.resultant 𝐠 𝐡 := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  set P := universalFactorizationMapPresentation R n m k hn
  have hM : (Matrix.of fun i j : Fin n ↦ pderiv (finSumFinEquiv.symm (finCongr hn i))
      ((tensorEquivSum R (Fin m) (Fin k) R
        (universalFactorizationMap R n m k hn (X j))).map C - C (X j))) = -P.jacobiMatrix := by
    ext i j : 1
    rw [Matrix.neg_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply, Matrix.of_apply,
      ← map_neg]
    exact congr_arg _ (neg_sub _ _).symm
  have hJ : aeval (R := MvPolynomial (Fin n) R) (S₁ := 𝓢)
      (Sum.elim (fun i ↦ X i ⊗ₜ[R] 1) fun j ↦ 1 ⊗ₜ[R] X j) P.jacobiMatrix.det =
      (-1) ^ n * Polynomial.resultant 𝐠 𝐡 :=
    P.jacobian_eq_jacobiMatrix_det.symm.trans
      (universalFactorizationMapPresentation_jacobian R n m k hn)
  rw [hM, Matrix.det_neg, map_mul, hJ, Fintype.card_fin, map_pow, map_neg, map_one, ← mul_assoc,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- `R[a] → S[1/Δ]` is étale, where `Δ = Res(g, h)`. -/
@[stacks 00UA "The conclusion: `R → S[1/Δ] = S[1/Res_x(g, h)]` is étale."]
theorem etale_localizationAway_resultant_universalFactorizationMap :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.Etale (MvPolynomial (Fin n) R) (Localization.Away (Polynomial.resultant 𝐠 𝐡)) := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  set Δ := Polynomial.resultant 𝐠 𝐡
  have hΔ : IsUnit (algebraMap 𝓢 (Localization.Away Δ) Δ) :=
    IsLocalization.Away.algebraMap_isUnit _
  let P : Algebra.SubmersivePresentation (MvPolynomial (Fin n) R) (Localization.Away Δ) _ _ :=
    { toPreSubmersivePresentation :=
        .comp (.localizationAway (Localization.Away Δ) Δ)
          (universalFactorizationMapPresentation R n m k hn)
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian,
          universalFactorizationMapPresentation_jacobian, Algebra.smul_def, map_mul, map_pow,
          map_neg, map_one]
        exact ((isUnit_neg_one.pow n).mul hΔ).mul hΔ }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) R)
      (Localization.Away Δ) :=
    ⟨_, _, _, inferInstance, P, by
      simp only [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, P]
      simp [Algebra.Presentation.dimension, hn]⟩
  infer_instance

/-- If `R[a] → S_f` is étale for some `f ∉ q`, then `Δ = Res(g, h) ∉ q`. -/
private theorem resultant_notMem_of_etale (q : Ideal 𝓢) [q.IsPrime] (f : 𝓢) (hf : f ∉ q) :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.Etale (MvPolynomial (Fin n) R) (Localization.Away f) →
      Polynomial.resultant 𝐠 𝐡 ∉ q := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  intro _
  have hu := ((Algebra.PreSubmersivePresentation.localizationAway (Localization.Away f) f).comp
    (universalFactorizationMapPresentation R n m k hn)).isUnit_jacobian_of_formallyUnramified
  rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    universalFactorizationMapPresentation_jacobian, Algebra.smul_def, map_mul] at hu
  have hΔ := (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hu).1).2
  have hq : (q.map (algebraMap 𝓢 (Localization.Away f))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf)
  exact fun hmem ↦ hq.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmem) hΔ)

/-- For a prime `q` of `S` the following are equivalent: `R[a] → S` is étale at `q`, that is,
`R[a] → S_f` is étale for some `f ∉ q`; `Δ = Res(g, h) ∉ q`; the images of `g` and `h` in
`κ(q)[x]` are coprime. -/
@[stacks 00UA "For a prime `q ⊂ S`: (1) `R → S` is étale at `q`, (2) `Δ = Res_x(g, h) ∉ q`,
(3) the images of `g, h` in `κ(q)[x]` are relatively prime, are equivalent. Étale at `q` is the
source's definition, `∃ f ∉ q, Algebra.Etale R (Localization.Away f)`."]
theorem tfae_universalFactorizationMap_etale (q : Ideal 𝓢) [q.IsPrime] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    List.TFAE [∃ f ∉ q, Algebra.Etale (MvPolynomial (Fin n) R) (Localization.Away f),
      Polynomial.resultant 𝐠 𝐡 ∉ q,
      IsCoprime (𝐠.map (algebraMap 𝓢 q.ResidueField)) (𝐡.map (algebraMap 𝓢 q.ResidueField))] := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  tfae_have 1 → 2 := fun ⟨f, hf, h⟩ ↦ resultant_notMem_of_etale R n m k hn q f hf h
  tfae_have 2 → 1 := fun h ↦
    ⟨_, h, etale_localizationAway_resultant_universalFactorizationMap R n m k hn⟩
  tfae_have 2 ↔ 3 := by
    have hg : (𝐠).Monic := (Polynomial.monic_freeMonic R m).map _
    have hh : (𝐡).Monic := (Polynomial.monic_freeMonic R k).map _
    rw [← Polynomial.isUnit_resultant_iff_isCoprime (hg.map _), isUnit_iff_ne_zero,
      hg.natDegree_map, hh.natDegree_map, Polynomial.resultant_map_map, Ne,
      Ideal.algebraMap_residueField_eq_zero]
  tfae_finish

/-- For a prime `q` of `S`, the Sylvester matrix of the images of `g` and `h` in `κ(q)[x]` has a
nonzero kernel if and only if these images have a common factor which is not a unit. -/
@[stacks 00UA "The reason given for (2) ⇔ (3): the image of the Sylvester matrix in
`Mat(n + m, κ(q))` has a kernel if and only if `ḡ, h̄` have a factor in common. Mathlib's
`Polynomial.sylvester` is the transpose of the source's matrix; a square matrix over a field and
its transpose have a nonzero kernel simultaneously."]
theorem exists_mulVec_sylvester_map_eq_zero_iff (q : Ideal 𝓢) [q.IsPrime] :
    (∃ v ≠ 0, Polynomial.sylvester (𝐠.map (algebraMap 𝓢 q.ResidueField))
      (𝐡.map (algebraMap 𝓢 q.ResidueField)) m k *ᵥ v = 0) ↔
    ∃ d, d ∣ 𝐠.map (algebraMap 𝓢 q.ResidueField) ∧ d ∣ 𝐡.map (algebraMap 𝓢 q.ResidueField) ∧
      ¬IsUnit d := by
  set φ := algebraMap 𝓢 q.ResidueField
  have : Nontrivial R := (φ.comp (algebraMap R 𝓢)).domain_nontrivial
  have hg : (𝐠.map φ).Monic := ((Polynomial.monic_freeMonic R m).map _).map _
  have hres : Polynomial.resultant (𝐠.map φ) (𝐡.map φ) m k =
      Polynomial.resultant (𝐠.map φ) (𝐡.map φ) := by
    rw [Polynomial.resultant, Polynomial.map_map, Polynomial.map_map,
      (Polynomial.monic_freeMonic R m).natDegree_map,
      (Polynomial.monic_freeMonic R k).natDegree_map, Polynomial.natDegree_freeMonic,
      Polynomial.natDegree_freeMonic]
    rfl
  rw [Matrix.exists_mulVec_eq_zero_iff]
  change Polynomial.resultant (𝐠.map φ) (𝐡.map φ) m k = 0 ↔ _
  rw [hres, Polynomial.resultant_eq_zero_iff, ← isRelPrime_iff_isCoprime]
  simp [hg.ne_zero, IsRelPrime]

/-- `R[a] → S` is étale at a prime `q` of `S` in the sense of `Algebra.IsEtaleAt` if and only if
`Δ = Res(g, h) ∉ q`. -/
@[stacks 00UA "(1) ⇔ (2), with étale at `q` read as Mathlib's `Algebra.IsEtaleAt`, which agrees
with the source's definition since `S` is of finite presentation over `R`."]
theorem isEtaleAt_universalFactorizationMap_iff (q : Ideal 𝓢) [q.IsPrime] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.IsEtaleAt (MvPolynomial (Fin n) R) q ↔ Polynomial.resultant 𝐠 𝐡 ∉ q := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) R) 𝓢 :=
    finitePresentation_universalFactorizationMap R n m k hn
  have := etale_localizationAway_resultant_universalFactorizationMap R n m k hn
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf, h⟩ := Algebra.exists_etale_of_isEtaleAt (R := MvPolynomial (Fin n) R) q
    exact resultant_notMem_of_etale R n m k hn q f hf h
  · exact Algebra.basicOpen_subset_etaleLocus_iff.mpr inferInstance
      (show (⟨q, ‹_›⟩ : PrimeSpectrum 𝓢) ∈ PrimeSpectrum.basicOpen _ from h)

end MvPolynomial
