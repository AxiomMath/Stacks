module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.FreeTensorPowMatrixUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixAlgebraLocalConj

/-!
# The overlap step of Tag 0A2L: the tensor power of an automorphism fixes Saltman's projector

Let `T` be a scheme, let `d = n + 1`, and let `Ψ` be an automorphism of the sheaf of `d × d`
matrices over `𝒪_T`. Its `d`-fold tensor power is an automorphism of
`Mat_d(𝒪_T)^{⊗ d} ≅ 𝓗om(𝒪_T^{d ^ d}, 𝒪_T^{d ^ d})`, and the content of this file is that **it
fixes Saltman's projector `altProjFree`.**

This is the agreement of two trivialisations on an overlap, in the form
`CategoryTheory.MonoidalClosed.curry'_comp_inv_hom_eq_iff` reduces it to: two isomorphisms
`A ≅ 𝓗om(F, F)` of sheaves of algebras read an endomorphism `f` of `F` as the same point of `A`
exactly when the comparison automorphism `a⁻¹ ≫ b` fixes `f`. On an overlap the comparison
automorphism is the `d`-fold tensor power of an automorphism of `Mat_d`, and the endomorphism is
the projector.

The proof is local. Every step before the last is a dictionary computation over
`R₀ T = End (𝒪_T)`: the tensor power acts factorwise on tensors of endomorphisms
(`pointMap_natTensorPowEndConj`), a matrix unit of the big algebra is a tensor of matrix units of
the small one (`conj_natTensorPowFreeIso_uncurry'_matIncl`), so the matrix of the image of a
matrix unit is an entrywise product (`pointMatrix_conj_natTensorPowEndConj`), and a morphism acts
on all matrices as the combination of the images of the matrix units
(`freeDualMatrix_pointMap`). The last step is where the locality enters: `R₀ T` is separated
(`unitEnd_eq_of_cover`), and on a Zariski neighbourhood of any point Skolem--Noether makes `Ψ`
conjugation by one invertible matrix `u` of sections
(`exists_sectionPointMatrix_eq_conj`), whereupon the entrywise product becomes conjugation by the
`d`-fold Kronecker power of `u` (`Matrix.tensorPow_mul_single_mul_tensorPow_apply`) and
`Matrix.tensorPow_mul_altProj_mul_tensorPow` -- the determinants the two sides pick up cancel --
finishes.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.pointMatrix_conj_natTensorPowEndConj`: the matrix of the
  image of a matrix unit under the `d`-fold tensor power of an automorphism of `Mat_d(𝒪_T)` is
  the entrywise product of the matrices of the images of the matrix units of `Mat_d(𝒪_T)`.
* `Stacks.EtaleCohomology.BrauerScheme.pointMap_natTensorPowEndConj_altProjFree`: **the `d`-fold
  tensor power of an automorphism of `Mat_d(𝒪_T)` fixes Saltman's projector.**

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules Opposite

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

variable {T : Scheme.{u}}

/-- Reindexing a square matrix over `Fin d → Fin d` along `ULift.down`. -/
def uliftMat {d : ℕ} {K : Type*} (M : Matrix (Fin d → Fin d) (Fin d → Fin d) K) :
    Matrix (ULift.{u, 0} (Fin d → Fin d)) (ULift.{u, 0} (Fin d → Fin d)) K :=
  M.submatrix ULift.down ULift.down

/-- The entry of `uliftMat M` at `(k, l)` is the entry of `M` at `(k.down, l.down)`. -/
@[simp]
theorem uliftMat_apply {d : ℕ} {K : Type*} (M : Matrix (Fin d → Fin d) (Fin d → Fin d) K)
    (k l : ULift.{u, 0} (Fin d → Fin d)) : uliftMat M k l = M k.down l.down := rfl

/-- Reindexing along `ULift.down` is multiplicative. -/
theorem uliftMat_mul {d : ℕ} {K : Type*} [CommRing K]
    (M N : Matrix (Fin d → Fin d) (Fin d → Fin d) K) :
    uliftMat.{u} (M * N) = uliftMat.{u} M * uliftMat.{u} N := by
  funext k l
  rw [uliftMat_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact (Equiv.sum_comp (Equiv.ulift.{u, 0} (α := Fin d → Fin d))
    fun p => M k.down p * N p l.down).symm

/-- Reindexing a matrix unit along `ULift.down` gives the matrix unit of the reindexed type. -/
theorem uliftMat_single {d : ℕ} {K : Type*} [CommRing K] (c e : Fin d → Fin d) :
    uliftMat.{u} (Matrix.single c e (1 : K))
      = Matrix.single (ULift.up.{u, 0} c) (ULift.up.{u, 0} e) (1 : K) := by
  funext k l
  rw [uliftMat_apply, Matrix.single_apply, Matrix.single_apply]
  refine if_congr ⟨fun h => ⟨congrArg ULift.up h.1, congrArg ULift.up h.2⟩,
    fun h => ⟨congrArg ULift.down h.1, congrArg ULift.down h.2⟩⟩ rfl rfl

/-- Reindexing along `ULift.down` turns a triple product into a triple product. -/
theorem uliftMat_mul_mul {d : ℕ} {K : Type*} [CommRing K]
    (A M B : Matrix (Fin d → Fin d) (Fin d → Fin d) K) :
    uliftMat.{u} A * uliftMat.{u} M * uliftMat.{u} B = uliftMat.{u} (A * M * B) := by
  rw [uliftMat_mul, uliftMat_mul]

/-- A matrix unit conjugated by two reindexed matrices is the reindex of the conjugate. -/
theorem uliftMat_mul_single_mul {d : ℕ} {K : Type*} [CommRing K]
    (A B : Matrix (Fin d → Fin d) (Fin d → Fin d) K) (c e : Fin d → Fin d) :
    uliftMat.{u} A * Matrix.single (ULift.up.{u, 0} c) (ULift.up.{u, 0} e) (1 : K)
        * uliftMat.{u} B
      = uliftMat.{u} (A * Matrix.single c e (1 : K) * B) := by
  rw [← uliftMat_single, uliftMat_mul_mul]

/-- The conjugate, by the identification of the `(n+1)`-fold tensor power of `𝒪_T^{n+1}` with
the free sheaf of rank `(n+1) ^ (n+1)`, of the `(n+1)`-fold tensor power of an automorphism of
`Mat_{n+1}(𝒪_T)`. -/
def natTensorPowEndConjFree (T : Scheme.{u}) (n : ℕ)
    (Ψ : matrixAlgebra T (n + 1) ≅ matrixAlgebra T (n + 1)) :
    endAlgebra (freeModule T (ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)))) ≅
      endAlgebra (freeModule T (ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)))) :=
  (endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))).symm ≪≫
    natTensorPowEndConj (isFiniteLocallyFree_free (ULift.{u, 0} (Fin (n + 1)))) Ψ n ≪≫
    endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))

/-- **The matrix of the image of a matrix unit under the `(n+1)`-fold tensor power of an
automorphism of `Mat_{n+1}(𝒪_T)` is the entrywise product** of the matrices of the images of the
matrix units of `Mat_{n+1}(𝒪_T)`. -/
theorem pointMatrix_conj_natTensorPowEndConj (T : Scheme.{u}) (n : ℕ)
    (Ψ : matrixAlgebra T (n + 1) ≅ matrixAlgebra T (n + 1))
    (c e k l : Fin (n + 1) → Fin (n + 1)) :
    pointMatrix (natTensorPowEndConjFree T n Ψ).hom
        (ULift.up.{u, 0} c, ULift.up.{u, 0} e) (ULift.up.{u, 0} k) (ULift.up.{u, 0} l)
      = ∏ j, pointMatrix Ψ.hom (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j))
          (ULift.up.{u, 0} (k j)) (ULift.up.{u, 0} (l j)) := by
  have hstep₁ : MonoidalClosed.pointMap
        (endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))).inv
        (MonoidalClosed.uncurry' (matIncl (S := T)
          (ULift.up.{u, 0} c, ULift.up.{u, 0} e)))
      = natTensorPowFam (n + 1) fun j => MonoidalClosed.uncurry' (matIncl (S := T)
          (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j))) := by
    rw [endAlgebraCongr, MonoidalClosed.internalEndCongr_inv,
      MonoidalClosed.pointMap_internalEndCongr]
    exact conj_natTensorPowFreeIso_uncurry'_matIncl T (n + 1) (n + 1) c e
  have hstep₂ := pointMap_natTensorPowEndConj
    (isFiniteLocallyFree_free (S := T) (ULift.{u, 0} (Fin (n + 1)))) Ψ n
    (fun j => MonoidalClosed.uncurry' (matIncl (S := T)
      (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j))))
  have hmain : MonoidalClosed.pointMap (natTensorPowEndConjFree T n Ψ).hom
        (MonoidalClosed.uncurry' (matIncl (S := T)
          (ULift.up.{u, 0} c, ULift.up.{u, 0} e)))
      = (natTensorPowFreeIso T (n + 1) (n + 1)).inv ≫ (natTensorPowFam (n + 1)
          fun j => MonoidalClosed.pointMap Ψ.hom (MonoidalClosed.uncurry' (matIncl (S := T)
            (ULift.up.{u, 0} (c j), ULift.up.{u, 0} (e j))))) ≫
          (natTensorPowFreeIso T (n + 1) (n + 1)).hom := by
    change MonoidalClosed.pointMap
        ((endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))).inv ≫
          (natTensorPowEndConj (isFiniteLocallyFree_free
            (ULift.{u, 0} (Fin (n + 1)))) Ψ n).hom ≫
          (endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))).hom) _ = _
    rw [MonoidalClosed.pointMap_trans, MonoidalClosed.pointMap_trans, hstep₁, hstep₂,
      endAlgebraCongr, MonoidalClosed.pointMap_internalEndCongr]
  rw [pointMatrix, hmain, freeDualMatrix_eq_freeEndMatrixEquiv T (Fin (n + 1) → Fin (n + 1)),
    freeEndMatrixEquiv_natTensorPowFam T (n + 1) (n + 1) _ k l]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [pointMatrix, freeDualMatrix_eq_freeEndMatrixEquiv T (Fin (n + 1))]

/-- **THE OVERLAP STEP OF [Stacks, Tag 0A2L]: the `(n+1)`-fold tensor power of an automorphism of
`Mat_{n+1}(𝒪_T)` fixes Saltman's projector.** -/
theorem pointMap_natTensorPowEndConj_altProjFree (T : Scheme.{u}) (n : ℕ)
    (Ψ : matrixAlgebra T (n + 1) ≅ matrixAlgebra T (n + 1)) :
    MonoidalClosed.pointMap (natTensorPowEndConjFree T n Ψ).hom (altProjFree T (n + 1))
      = altProjFree T (n + 1) := by
  refine freeDualMatrix_injective ?_
  rw [freeDualMatrix_pointMap]
  funext k l
  have hd : freeDualMatrix (altProjFree T (n + 1))
      = uliftMat.{u} (Matrix.altProj (R₀ T) (n := Fin (n + 1))) := by
    funext p q
    rw [freeDualMatrix_altProjFree, uliftMat_apply]
  rw [hd]
  refine unitEnd_eq_of_cover fun x => ?_
  obtain ⟨V, hxV, u, hu⟩ := exists_sectionPointMatrix_eq_conj Ψ x
  refine ⟨V, hxV, ?_⟩
  set φ := unitEndValueHom T V with hφ
  have hmapconj : ∀ κ : ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)) ×
        ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)),
      (pointMatrix (natTensorPowEndConjFree T n Ψ).hom κ).map φ
        = uliftMat.{u} (Matrix.tensorPow (u : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, V)))
            * Matrix.single κ.1 κ.2 (1 : Γ(T, V))
            * uliftMat.{u} (Matrix.tensorPow
              ((u⁻¹ : (Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, V))ˣ) :
                Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, V))) := by
    rintro ⟨⟨c⟩, ⟨e⟩⟩
    funext p q
    obtain ⟨p'⟩ := p
    obtain ⟨q'⟩ := q
    rw [Matrix.map_apply, pointMatrix_conj_natTensorPowEndConj T n Ψ c e p' q', map_prod]
    refine Eq.trans (Finset.prod_congr rfl fun j (_ : j ∈ Finset.univ) =>
      hu (c j) (e j) (p' j) (q' j)) ?_
    rw [uliftMat_mul_single_mul, uliftMat_apply,
      Matrix.tensorPow_mul_single_mul_tensorPow_apply]
  have hfin : Stacks.Matrix.unitCombination
        (fun κ => (pointMatrix (natTensorPowEndConjFree T n Ψ).hom κ).map φ)
        ((uliftMat.{u} (Matrix.altProj (R₀ T) (n := Fin (n + 1)))).map φ)
      = (uliftMat.{u} (Matrix.altProj (R₀ T) (n := Fin (n + 1)))).map φ := by
    rw [Stacks.Matrix.unitCombination_eq_conj
      (fun κ => (pointMatrix (natTensorPowEndConjFree T n Ψ).hom κ).map φ) hmapconj]
    have hmapalt : (uliftMat.{u} (Matrix.altProj (R₀ T) (n := Fin (n + 1)))).map φ
        = uliftMat.{u} (Matrix.altProj Γ(T, V) (n := Fin (n + 1))) := by
      funext p q
      exact congrFun (congrFun (Matrix.map_altProj (n := Fin (n + 1)) φ) p.down) q.down
    rw [hmapalt, uliftMat_mul_mul, Matrix.tensorPow_mul_altProj_mul_tensorPow (u.mul_inv)]
  have hentry := congrFun (congrFun (Stacks.Matrix.unitCombination_map
    (W := pointMatrix (natTensorPowEndConjFree T n Ψ).hom) φ
    (uliftMat.{u} (Matrix.altProj (R₀ T) (n := Fin (n + 1))))) k) l
  exact hentry.trans (congrFun (congrFun hfin k) l)

end Stacks.EtaleCohomology.BrauerScheme

end

end
