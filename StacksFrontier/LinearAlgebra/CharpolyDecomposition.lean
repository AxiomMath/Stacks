module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic polynomials along decompositions and extensions of scalars

Two elementary facts on characteristic polynomials of endomorphisms of finite-dimensional vector
spaces, phrased through explicit maps (as they arise on the cohomology of sheaves, where the maps
come from morphisms of sheaves and no isomorphism of vector spaces is given):

* `LinearMap.charpoly_eq_prod_of_retractions`: if `W` is the direct sum of the `Wᵢ` through maps
  `ιᵢ : Wᵢ → W`, `πᵢ : W → Wᵢ` with `πᵢ ιᵢ = 1`, `πᵢ ιⱼ = 0` for `i ≠ j` and `∑ ιᵢ πᵢ = 1`, and
  `F ιᵢ = ιᵢ Fᵢ`, then `charpoly F = ∏ charpoly Fᵢ`;
* `LinearMap.charpoly_eq_map_of_scalarExtension`: if `W` is an `E'`-vector space and
  `Ψ : V → W` is `E`-semilinear with `W = E' ⊗_E V` through `Ψ` (witnessed by projections
  `prₜ : W → V` dual to an `E`-basis `c` of `E'`) and `F_W Ψ = Ψ F_V`, then
  `charpoly F_W = (charpoly F_V).map (algebraMap E E')`.

Both are used for the purity of the fibres of a direct sum in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Matrix.charpoly_blockDiagonal'`.
* `LinearMap.charpoly_eq_prod_of_retractions`.
* `LinearMap.charpoly_eq_map_of_scalarExtension`.
-/

@[expose] public noncomputable section

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {o : Type*} [Fintype o] [LinearOrder o]
  {m : o → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

omit [Fintype o] [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] in
/-- A diagonal block of a block diagonal matrix is the block, reindexed. -/
theorem toSquareBlock_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) R) (a : o) :
    (blockDiagonal' M).toSquareBlock Sigma.fst a =
      reindex (Equiv.sigmaSubtype a).symm (Equiv.sigmaSubtype a).symm (M a) := by
  ext ⟨⟨i, x⟩, hx⟩ ⟨⟨j, y⟩, hy⟩
  simp only at hx hy
  subst hx hy
  simp [toSquareBlock_def, blockDiagonal'_apply_eq, Equiv.sigmaSubtype]

/-- **The characteristic polynomial of a block diagonal matrix is the product of those of its
blocks.** -/
theorem charpoly_blockDiagonal' (M : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' M).charpoly = ∏ i, (M i).charpoly := by
  rw [(blockTriangular_blockDiagonal' M).charpoly]
  simp only [toSquareBlock_blockDiagonal', charpoly_reindex]
  refine Finset.prod_subset (Finset.subset_univ _) fun a _ ha => ?_
  have : IsEmpty (m a) := ⟨fun x => ha (Finset.mem_image.2 ⟨⟨a, x⟩, Finset.mem_univ _, rfl⟩)⟩
  exact charpoly_isEmpty

end Matrix

namespace LinearMap

section Retractions

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {o : Type*} [Fintype o]
  [LinearOrder o] {Wi : o → Type*} [∀ i, AddCommGroup (Wi i)]
  [∀ i, Module K (Wi i)] [∀ i, FiniteDimensional K (Wi i)]
  (ι : ∀ i, Wi i →ₗ[K] W) (π : ∀ i, W →ₗ[K] Wi i) (hπι : ∀ i v, π i (ι i v) = v)
  (hπι' : ∀ i j, i ≠ j → ∀ v, π i (ι j v) = 0) (hsum : ∀ w, ∑ i, ι i (π i w) = w)

include hπι hπι' hsum in
/-- The images under the `ιᵢ` of bases of the `Wᵢ` form a basis of `W`. -/
def retractionsBasis :
    Module.Basis (Σ i, Fin (Module.finrank K (Wi i))) K W :=
  Module.Basis.mk (v := fun x => ι x.1 (Module.finBasis K (Wi x.1) x.2))
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg ⟨j, a⟩
      have h := congrArg (π j) hg
      rw [Fintype.sum_sigma, map_sum, map_zero] at h
      rw [Finset.sum_eq_single j (fun i _ hij => by
          simp only [map_sum, map_smul, hπι' j i (Ne.symm hij), smul_zero, Finset.sum_const_zero])
        (by simp)] at h
      simp only [map_sum, map_smul, hπι] at h
      exact Fintype.linearIndependent_iff.1 (Module.finBasis K (Wi j)).linearIndependent
        (fun a => g ⟨j, a⟩) h a)
    (by
      intro w _
      rw [← hsum w]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← (Module.finBasis K (Wi i)).sum_repr (π i w), map_sum]
      exact Submodule.sum_mem _ fun a _ => by
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, a⟩, rfl⟩))

include hπι hπι' hsum in
/-- **The characteristic polynomial along a decomposition into a direct sum.**  If
`ιᵢ : Wᵢ → W`, `πᵢ : W → Wᵢ` exhibit `W` as the direct sum of the `Wᵢ` and `F ιᵢ = ιᵢ Fᵢ`, then
`charpoly F = ∏ charpoly Fᵢ`. -/
theorem charpoly_eq_prod_of_retractions [FiniteDimensional K W] (F : W →ₗ[K] W)
    (Fi : ∀ i, Wi i →ₗ[K] Wi i) (hF : ∀ i v, F (ι i v) = ι i (Fi i v)) :
    F.charpoly = ∏ i, (Fi i).charpoly := by
  set b := retractionsBasis ι π hπι hπι' hsum
  let M : ∀ i, Matrix (Fin (Module.finrank K (Wi i))) (Fin (Module.finrank K (Wi i))) K :=
    fun i => LinearMap.toMatrix (Module.finBasis K (Wi i)) (Module.finBasis K (Wi i)) (Fi i)
  have hF' : F = Matrix.toLin b b (Matrix.blockDiagonal' M) := by
    refine b.ext fun ⟨i, a⟩ => ?_
    rw [Matrix.toLin_self]
    simp only [b, retractionsBasis, Module.Basis.mk_apply]
    rw [hF, ← (Module.finBasis K (Wi i)).sum_repr (Fi i _), map_sum, Fintype.sum_sigma,
      Finset.sum_eq_single i (fun j _ hji => Finset.sum_eq_zero fun c _ => by
        rw [Matrix.blockDiagonal'_apply_ne M c a hji, zero_smul]) (by simp)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.blockDiagonal'_apply_eq, map_smul]
    simp only [M, LinearMap.toMatrix_apply]
  rw [hF', Matrix.charpoly_toLin, Matrix.charpoly_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => LinearMap.charpoly_toMatrix _ _

end Retractions

section ScalarExtension

variable {E E' : Type*} [Field E] [Field E'] [Algebra E E'] {V W : Type*} [AddCommGroup V]
  [Module E V] [FiniteDimensional E V] [AddCommGroup W] [Module E' W]
  {s : Type*} [Fintype s] [DecidableEq s]
  (c : Module.Basis s E E') (Ψ : V →+ W)
  (hΨ : ∀ (e : E) (v : V), Ψ (e • v) = algebraMap E E' e • Ψ v) (pr : s → W →+ V)
  (hpr : ∀ t u v, pr t (c u • Ψ v) = if t = u then v else 0)
  (hsum : ∀ w, ∑ t, c t • Ψ (pr t w) = w)

include hΨ hpr hsum in
/-- The images under `Ψ` of a basis of `V` form a basis of `W`. -/
def scalarExtensionBasis : Module.Basis (Fin (Module.finrank E V)) E' W :=
  Module.Basis.mk (v := fun j => Ψ (Module.finBasis E V j))
    (by
      classical
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      have hexp : ∀ e' : E', ∀ w : W, e' • w = ∑ t, algebraMap E E' (c.repr e' t) • c t • w :=
        fun e' w => by
          conv_lhs => rw [← c.sum_repr e']
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Algebra.smul_def, mul_smul]
      have hg' : ∑ t, c t • Ψ (∑ i, c.repr (g i) t • Module.finBasis E V i) = 0 := by
        rw [← hg]
        simp only [map_sum, hΨ, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hexp (g i)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [smul_comm]
      have hz : ∀ u, ∑ i, c.repr (g i) u • Module.finBasis E V i = 0 := fun u => by
        have h := congrArg (pr u) hg'
        rw [map_sum, map_zero] at h
        simp only [hpr] at h
        simpa using h
      have h0 : ∀ u, c.repr (g j) u = 0 := fun u =>
        Fintype.linearIndependent_iff.1 (Module.finBasis E V).linearIndependent _ (hz u) j
      exact c.repr.injective (Finsupp.ext fun u => by rw [h0 u]; simp))
    (by
      intro w _
      rw [← hsum w]
      refine Submodule.sum_mem _ fun t _ => ?_
      refine Submodule.smul_mem _ _ ?_
      rw [← (Module.finBasis E V).sum_repr (pr t w), map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [hΨ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

include hΨ hpr hsum in
/-- **The characteristic polynomial after an extension of scalars.**  If `Ψ : V → W` exhibits
the `E'`-vector space `W` as `E' ⊗_E V` (with projections `prₜ` dual to an `E`-basis `c` of `E'`)
and `F_W Ψ = Ψ F_V`, then `charpoly F_W = (charpoly F_V).map (algebraMap E E')`. -/
theorem charpoly_eq_map_of_scalarExtension [FiniteDimensional E' W] (FV : V →ₗ[E] V)
    (FW : W →ₗ[E'] W) (hF : ∀ v, FW (Ψ v) = Ψ (FV v)) :
    FW.charpoly = FV.charpoly.map (algebraMap E E') := by
  set b := scalarExtensionBasis c Ψ hΨ pr hpr hsum
  set A := LinearMap.toMatrix (Module.finBasis E V) (Module.finBasis E V) FV
  have hF' : FW = Matrix.toLin b b (A.map (algebraMap E E')) := by
    refine b.ext fun j => ?_
    rw [Matrix.toLin_self]
    simp only [b, scalarExtensionBasis, Module.Basis.mk_apply]
    rw [hF, ← (Module.finBasis E V).sum_repr (FV _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΨ, Matrix.map_apply]
    simp only [A, LinearMap.toMatrix_apply]
  rw [hF', Matrix.charpoly_toLin, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

end ScalarExtension

end LinearMap

end
