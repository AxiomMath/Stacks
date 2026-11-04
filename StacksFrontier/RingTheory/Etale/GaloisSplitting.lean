module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Fixed
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Splitting a finite étale algebra by a finite Galois extension

Let `k` be a field and `A` a finite étale `k`-algebra, that is, a finite product of finite
separable field extensions of `k`. The proof of Stacks 0FHQ chooses a finite Galois extension
`L/k` containing each factor of `A` and uses the decomposition

`A ⊗_k L = ∏_{σ ∈ Σ} L`, `Σ = Hom_k(A, L)`, `a ⊗ b ↦ (σ(a) b)_σ`.

This file proves both facts.

* `Stacks.FiniteEtaleSplitting.exists_isGalois_splits`: there is a finite Galois extension
  `L/k` in which the minimal polynomial of every element of `A` splits; equivalently every
  factor of `A` embeds into `L`.
* `Stacks.FiniteEtaleSplitting.splitHom`: the `k`-algebra map `A ⊗_k L → ∏_{σ ∈ Σ} L`,
  `a ⊗ b ↦ (σ(a) b)_σ`.
* `Stacks.FiniteEtaleSplitting.natCard_algHom`: `|Σ| = [A : k]` when every minimal polynomial
  splits in `L`.
* `Stacks.FiniteEtaleSplitting.splitHom_bijective`, `Stacks.FiniteEtaleSplitting.splitEquiv`:
  under the same hypothesis the map is an isomorphism.

## Implementation notes

Surjectivity of `A ⊗_k L → L^Σ` is Dedekind's independence of characters
(`linearIndependent_toLinearMap`): the image is an `L`-subspace containing the vectors
`(σ(a))_σ`, and a linear form on `L^Σ` vanishing on all of them is a relation
`∑_σ c_σ σ = 0`. The count `|Σ| = [A : k]` comes from writing `A = ∏_i K_i` with `K_i` finite
separable fields: each `K_i` has `[K_i : k]` embeddings into `L`
(`AlgHom.natCard_of_splits`), and composing them with the projections gives
`∑_i [K_i : k] = [A : k]` distinct elements of `Σ`; the reverse inequality is
`AlgHom.card_algHom_le_finrank`. Both sides then have dimension `[A : k] [L : k]` over `k`.

## Relation to the field case

For a finite separable field extension `k'/k` and a normal `K/k` into which `k'` embeds, base
already has the decomposition `Stacks.FieldTheory.tensorPiEquiv'` of `k' ⊗_k K`
(`StacksFrontier/FieldTheory/SeparableTensorSplitting.lean`, used for Tag 0FVS). The present file
is the generalization the proof of Tag 0FHQ needs, to a finite étale algebra `A`, a finite
product of such fields, which is not a field and does not embed into `L`; the hypothesis is
that every minimal polynomial over `k` of an element of `A` splits in `L`. The field case is not
reproved separately here: the count `|Hom_k(A, L)| = [A : k]` is reduced to Mathlib's
`AlgHom.natCard_of_splits` on the factors, and the decomposition itself is proved once, for `A`.
Base's `tensorPiEquiv'` is the special case `A = k'` (normality of `K` giving the splitting
hypothesis), with the factors of the tensor product in the order `k' ⊗_k K` used here.

## References

* [Stacks Project, Tag 0FHQ](https://stacks.math.columbia.edu/tag/0FHQ)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Polynomial

universe u v w

namespace Stacks.FiniteEtaleSplitting

variable (k : Type u) [Field k]

/-! ### A Galois extension splitting a finite étale algebra -/

/-- If `g ≠ 0` splits after base change, then so does every divisor of `g`. -/
private theorem splits_map_of_dvd {L : Type*} [Field L] {f g : k[X]} (φ : k →+* L) (hg : g ≠ 0)
    (hfg : f ∣ g) (h : (g.map φ).Splits) : (f.map φ).Splits :=
  h.of_dvd (Polynomial.map_ne_zero hg) (Polynomial.map_dvd _ hfg)

/-- A finite product of finite separable field extensions of `k` is split by a finite Galois
extension of `k`: the splitting field of the product of the minimal polynomials of primitive
elements of the factors. -/
theorem exists_isGalois_splits_pi {I : Type v} [Finite I] (K : I → Type v) [∀ i, Field (K i)]
    [∀ i, Algebra k (K i)] [∀ i, FiniteDimensional k (K i)] [∀ i, Algebra.IsSeparable k (K i)] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L) (_ : IsGalois k L),
      ∀ a : ∀ i, K i, ((minpoly k a).map (algebraMap k L)).Splits := by
  classical
  have : Fintype I := Fintype.ofFinite I
  let pb (i : I) : PowerBasis k (K i) := Field.powerBasisOfFiniteOfSeparable k (K i)
  have hint (i : I) : IsIntegral k (pb i).gen := Algebra.IsIntegral.isIntegral _
  let J : Finset k[X] := Finset.univ.image fun i ↦ minpoly k (pb i).gen
  have hJ (q : k[X]) (hq : q ∈ J) : ∃ i, minpoly k (pb i).gen = q := by
    simpa [J] using hq
  let p : k[X] := ∏ q ∈ J, q
  have hpsep : p.Separable := by
    refine Polynomial.separable_prod' (fun q hq r hr hqr ↦ ?_) (fun q hq ↦ ?_)
    · obtain ⟨i, rfl⟩ := hJ q hq
      obtain ⟨j, rfl⟩ := hJ r hr
      rw [Irreducible.coprime_iff_not_dvd (minpoly.irreducible (hint i))]
      intro hdvd
      exact hqr (Polynomial.eq_of_monic_of_associated (minpoly.monic (hint i))
        (minpoly.monic (hint j))
        ((minpoly.irreducible (hint i)).associated_of_dvd (minpoly.irreducible (hint j)) hdvd))
    · obtain ⟨i, rfl⟩ := hJ q hq
      exact Algebra.IsSeparable.isSeparable k (pb i).gen
  let L := SplittingField p
  have : IsGalois k L := IsGalois.of_separable_splitting_field hpsep
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq ↦ by
    obtain ⟨i, rfl⟩ := hJ q hq
    exact minpoly.ne_zero (hint i)
  have hgen (i : I) : ((minpoly k (pb i).gen).map (algebraMap k L)).Splits :=
    splits_map_of_dvd k _ hp0 (Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i))) (SplittingField.splits p)
  have hcomp (i : I) (x : K i) : ((minpoly k x).map (algebraMap k L)).Splits := by
    have hdeg : ((minpoly k (pb i).gen).map (algebraMap k L)).degree ≠ 0 := by
      rw [Polynomial.degree_map]
      exact (minpoly.degree_pos (hint i)).ne'
    obtain ⟨y, hy⟩ := (hgen i).exists_eval_eq_zero hdeg
    let f : K i →ₐ[k] L := (pb i).lift y (by simpa [Polynomial.aeval_def, Polynomial.eval_map]
      using hy)
    rw [← minpoly.algHom_eq f f.injective x]
    exact IsGalois.splits k (f x)
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, fun a ↦ ?_⟩
  let q : k[X] := ∏ i, minpoly k (a i)
  have hq : Polynomial.aeval a q = 0 := by
    ext i
    show Pi.evalAlgHom k K i (Polynomial.aeval a q) = 0
    rw [← Polynomial.aeval_algHom_apply, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval k (a i))
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (a i))
  have hqs : (q.map (algebraMap k L)).Splits := by
    rw [Polynomial.map_prod]
    exact Polynomial.Splits.prod fun i _ ↦ hcomp i (a i)
  exact splits_map_of_dvd k _ hq0 (minpoly.dvd k a hq) hqs

variable (A : Type v) [CommRing A] [Algebra k A]

/-- A finite étale `k`-algebra is a finite product of finite separable field extensions, whose
projections `A → K i` are surjective. -/
private theorem exists_algEquiv_pi_surjective [Module.Finite k A] [Algebra.Etale k A] :
    ∃ (I : Type v) (_ : Fintype I) (K : I → Type v) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, FiniteDimensional k (K i))
      (_ : ∀ i, Algebra.IsSeparable k (K i)) (e : A ≃ₐ[k] ∀ i, K i),
      ∀ i, Function.Surjective ((Pi.evalAlgHom k K i).comp e.toAlgHom) := by
  classical
  obtain ⟨I, _, K, _, _, e, hK⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod k A).mp inferInstance
  have : Fintype I := Fintype.ofFinite I
  have hπ (i : I) : Function.Surjective ((Pi.evalAlgHom k K i).comp e.toAlgHom) :=
    fun x ↦ ⟨e.symm (Pi.single i x), by simp⟩
  exact ⟨I, inferInstance, K, inferInstance, inferInstance,
    fun i ↦ Module.Finite.of_surjective
      ((Pi.evalAlgHom k K i).comp e.toAlgHom).toLinearMap (hπ i), hK, e, hπ⟩

/-- **A finite étale algebra over `k` is split by a finite Galois extension of `k`**: there is a
finite Galois `L/k` in which the minimal polynomial of every element of `A` splits. -/
theorem exists_isGalois_splits [Module.Finite k A] [Algebra.Etale k A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L) (_ : IsGalois k L),
      ∀ a : A, ((minpoly k a).map (algebraMap k L)).Splits := by
  obtain ⟨I, _, K, _, _, _, _, e, -⟩ := exists_algEquiv_pi_surjective k A
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isGalois_splits_pi k K
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    fun a ↦ by simpa only [minpoly.algEquiv_eq e a] using hL (e a)⟩

/-! ### The comparison map -/

variable (L : Type w) [Field L] [Algebra k L]

/-- **The comparison map `A ⊗_k L → ∏_{σ ∈ Hom_k(A, L)} L`, `a ⊗ b ↦ (σ(a) b)_σ`.** -/
def splitHom : A ⊗[k] L →ₐ[k] ((A →ₐ[k] L) → L) :=
  AlgHom.pi fun σ ↦ Algebra.TensorProduct.lift σ (AlgHom.id k L) fun _ _ ↦ Commute.all _ _

/-- The comparison map sends `a ⊗ b` to the family `(σ a * b)_σ`. -/
@[simp]
theorem splitHom_tmul (a : A) (b : L) : splitHom k A L (a ⊗ₜ b) = fun σ ↦ σ a * b := by
  ext σ
  simp [splitHom]

variable {k A L}

/-- If every minimal polynomial of an element of `A` splits in `L`, then so does that of every
element of a factor `A → K` of `A`. -/
private theorem splits_of_surjective {K : Type*} [Field K] [Algebra k K] [Module.Finite k A]
    (π : A →ₐ[k] K) (hπ : Function.Surjective π)
    (hsplit : ∀ a : A, ((minpoly k a).map (algebraMap k L)).Splits) (x : K) :
    ((minpoly k x).map (algebraMap k L)).Splits := by
  obtain ⟨a, rfl⟩ := hπ x
  have ha : IsIntegral k a := Algebra.IsIntegral.isIntegral a
  exact splits_map_of_dvd k _ (minpoly.ne_zero ha)
    (minpoly.dvd k (π a) (by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]))
    (hsplit a)

variable (k A L) in
/-- **`|Hom_k(A, L)| = [A : k]`** for a finite étale `A` all of whose minimal polynomials split
in `L`. -/
theorem natCard_algHom [Module.Finite k A] [Algebra.Etale k A]
    (hsplit : ∀ a : A, ((minpoly k a).map (algebraMap k L)).Splits) :
    Nat.card (A →ₐ[k] L) = Module.finrank k A := by
  classical
  refine le_antisymm (card_algHom_le_finrank k A L) ?_
  obtain ⟨I, _, K, _, _, _, _, e, hπ⟩ := exists_algEquiv_pi_surjective k A
  let π (i : I) : A →ₐ[k] K i := (Pi.evalAlgHom k K i).comp e.toAlgHom
  let ι : (Σ i, K i →ₐ[k] L) → (A →ₐ[k] L) := fun p ↦ p.2.comp (π p.1)
  have hι : Function.Injective ι := by
    rintro ⟨i, τ⟩ ⟨j, τ'⟩ h
    have hij : i = j := by
      by_contra hne
      have h1 : π i (e.symm (Pi.single i 1)) = 1 := by simp [π]
      have h2 : π j (e.symm (Pi.single i 1)) = 0 := by
        simp [π, Pi.single_eq_of_ne (Ne.symm hne)]
      have := congrArg (fun f : A →ₐ[k] L ↦ f (e.symm (Pi.single i 1))) h
      change τ (π i _) = τ' (π j _) at this
      rw [h1, h2, map_one, map_zero] at this
      exact one_ne_zero this
    subst hij
    have : τ = τ' := AlgHom.ext fun x ↦ by
      obtain ⟨a, rfl⟩ := hπ i x
      exact congrArg (fun f : A →ₐ[k] L ↦ f a) h
    subst this
    rfl
  have hcard : Nat.card (Σ i, K i →ₐ[k] L) = Module.finrank k A := by
    rw [Nat.card_sigma, e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact AlgHom.natCard_of_splits k (K i) L (splits_of_surjective (π i) (hπ i) hsplit)
  rw [← hcard]
  exact Nat.card_le_card_of_injective ι hι

/-- The image of `A ⊗_k L → L^Σ` is stable under multiplication by `L` acting diagonally. -/
private theorem smul_mem_range_splitHom (l : L) (y : (A →ₐ[k] L) → L)
    (hy : y ∈ Set.range (splitHom k A L)) : l • y ∈ Set.range (splitHom k A L) := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨x * (1 ⊗ₜ l), ?_⟩
  rw [map_mul, splitHom_tmul]
  ext σ
  simp [mul_comm]

variable [Module.Finite k A]

/-- **Dedekind's independence of characters, as a surjectivity statement**: the vectors
`(σ(a))_σ`, `a ∈ A`, span `L^Σ` over `L`; hence `A ⊗_k L → L^Σ` is surjective. -/
theorem splitHom_surjective : Function.Surjective (splitHom k A L) := by
  classical
  have : Fintype (A →ₐ[k] L) := Fintype.ofFinite _
  let V : Submodule L ((A →ₐ[k] L) → L) :=
    Submodule.span L (Set.range fun a : A ↦ fun σ : A →ₐ[k] L ↦ σ a)
  have hV : V = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := V.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
    let c : (A →ₐ[k] L) → L := fun σ ↦ f (Pi.single σ 1)
    have hfc (y : (A →ₐ[k] L) → L) : f y = ∑ σ, c σ * y σ := by
      conv_lhs => rw [show y = ∑ σ, y σ • Pi.single σ 1 by ext τ; simp [Finset.sum_apply,
        Pi.single_apply]]
      simp [c, map_sum, map_smul, mul_comm]
    have hrel : ∑ σ, c σ • (σ : A →ₐ[k] L).toLinearMap = 0 := by
      ext a
      have := hle (Submodule.subset_span ⟨a, rfl⟩)
      rw [LinearMap.mem_ker, hfc] at this
      simpa [LinearMap.sum_apply] using this
    have hc : c = 0 := funext (Fintype.linearIndependent_iff.mp
      (linearIndependent_toLinearMap k A L) c hrel)
    exact hf0 (LinearMap.pi_ext' fun σ ↦ LinearMap.ext_ring (by
      simpa [c] using congrFun hc σ))
  intro y
  have hy : y ∈ V := hV ▸ Submodule.mem_top
  refine Submodule.span_induction (p := fun y _ ↦ y ∈ Set.range (splitHom k A L)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, rfl⟩
    exact ⟨a ⊗ₜ 1, by rw [splitHom_tmul]; simp⟩
  · exact ⟨0, map_zero _⟩
  · rintro _ _ _ _ ⟨x, rfl⟩ ⟨x', rfl⟩
    exact ⟨x + x', map_add _ _ _⟩
  · intro l y _ hy
    exact smul_mem_range_splitHom l y hy

variable [Algebra.Etale k A] [FiniteDimensional k L]

/-- **`A ⊗_k L → ∏_{σ ∈ Hom_k(A, L)} L` is an isomorphism** when every minimal polynomial of an
element of `A` splits in `L`. -/
theorem splitHom_bijective (hsplit : ∀ a : A, ((minpoly k a).map (algebraMap k L)).Splits) :
    Function.Bijective (splitHom k A L) := by
  classical
  have : Fintype (A →ₐ[k] L) := Fintype.ofFinite _
  refine ⟨?_, splitHom_surjective⟩
  have hrank : Module.finrank k (A ⊗[k] L) = Module.finrank k ((A →ₐ[k] L) → L) := by
    rw [Module.finrank_tensorProduct, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_algHom k A L hsplit, smul_eq_mul]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := (splitHom k A L).toLinearMap)).mpr splitHom_surjective

/-- **The splitting `A ⊗_k L ≅ ∏_{σ ∈ Hom_k(A, L)} L`**, `a ⊗ b ↦ (σ(a) b)_σ`. -/
def splitEquiv (hsplit : ∀ a : A, ((minpoly k a).map (algebraMap k L)).Splits) :
    A ⊗[k] L ≃ₐ[k] ((A →ₐ[k] L) → L) :=
  AlgEquiv.ofBijective (splitHom k A L) (splitHom_bijective hsplit)

/-- The splitting isomorphism `splitEquiv` agrees with the comparison map `splitHom`. -/
@[simp]
theorem splitEquiv_apply (hsplit : ∀ a : A, ((minpoly k a).map (algebraMap k L)).Splits)
    (x : A ⊗[k] L) : splitEquiv hsplit x = splitHom k A L x := rfl

end Stacks.FiniteEtaleSplitting

end
