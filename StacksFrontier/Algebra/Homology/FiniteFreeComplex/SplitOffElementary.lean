module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Complexes of finite free modules and splitting off elementary complexes

This file defines `FreeComplex`, a `ℤ`-indexed complex of finite free modules given by ranks and
matrices, its associated `HomologicalComplex`, the elementary identity complex `T^{(i)}`, and
block-diagonal sums, and proves that a complex whose differential `φ_i` has an invertible matrix
coefficient splits off `T^{(i)}` (Stacks, Tag 00MT).
-/

@[expose] public section

open CategoryTheory Limits

/-- A complex of finite free `R`-modules, given by a rank function `n : ℤ → ℕ` and differential
matrices `d i : Matrix (Fin (n i)) (Fin (n (i+1))) R` (the map `R^{n (i+1)} → R^{n i}` in the
standard bases), subject to the complex condition `d i * d (i+1) = 0`. -/
structure FreeComplex (R : Type*) [CommRing R] where
  n : ℤ → ℕ
  d : (i : ℤ) → Matrix (Fin (n i)) (Fin (n (i + 1))) R
  dd : ∀ i, (d i) * (d (i + 1)) = 0

namespace FreeComplex
variable {R : Type*} [CommRing R]

/-- The honest homological complex (chain complex indexed by `ℤ`, differentials lowering degree
by one) associated to a `FreeComplex`. The term in degree `i` is the finite free module
`R^{n i}`, and the differentials are given by the matrices `d`. -/
@[implicit_reducible]
noncomputable def toComplex (C : FreeComplex R) :
    HomologicalComplex (ModuleCat R) (ComplexShape.down ℤ) where
  X i := ModuleCat.of R (Fin (C.n i) → R)
  d i j := if h : i = j + 1 then
      ModuleCat.ofHom ((Matrix.toLin' (C.d j)).comp (LinearEquiv.toLinearMap
        (LinearEquiv.funCongrLeft R R (finCongr (by rw [h]))))) else 0
  shape i j hij := by rw [dite_eq_right]; intro h; exact hij (by simp [ComplexShape.down, h])
  d_comp_d' i j k hij hjk := by
    have hij' : i = j + 1 := by simpa [ComplexShape.down, eq_comm] using hij
    have hjk' : j = k + 1 := by simpa [ComplexShape.down, eq_comm] using hjk
    subst hij' hjk'
    rw [dite_eq_left rfl, dite_eq_left rfl]
    apply ModuleCat.hom_ext
    ext x
    have hrefl : ∀ α : Type, LinearEquiv.funCongrLeft R R (Equiv.refl α)
        = LinearEquiv.refl R (α → R) := by intro α; ext f y; simp [LinearEquiv.funCongrLeft]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, finCongr_refl, hrefl,
      LinearEquiv.refl_toLinearMap, LinearMap.id_coe, id_eq]
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, C.dd k, map_zero]; rfl

/-- Rank function of the elementary identity complex `T^{(i)}`: rank `1` in degrees `i` and
`i - 1`, and `0` elsewhere. -/
def elemRank (i : ℤ) : ℤ → ℕ := fun j => if j = i ∨ j = i - 1 then 1 else 0

/-- The elementary identity complex `T^{(i)}_•`, i.e. `… → 0 → R --id--> R → 0 → …`
concentrated in degrees `i` and `i - 1`, with the identity map as differential
`R = X i → X (i-1) = R`. -/
@[implicit_reducible]
noncomputable def elementaryComplex (R : Type*) [CommRing R] (i : ℤ) : FreeComplex R where
  n := elemRank i
  d t := if t = i - 1 then
      (Matrix.of fun (_ : Fin (elemRank i t)) (_ : Fin (elemRank i (t + 1))) => (1 : R)) else 0
  dd t := by
    by_cases h1 : t = i - 1
    · subst h1
      have h2 : elemRank i (i - 1 + 1 + 1) = 0 := by simp only [elemRank]; rw [ite_eq_right]; omega
      apply Matrix.ext; intro a b
      exact (finCongr h2 b).elim0
    · rw [ite_eq_right h1]; simp

/-- The differential `φ_i : R^{n_i} → R^{n_{i-1}}` of `C` (represented by the matrix `d (i-1)`,
recalling `n (i-1+1) = n i`) *has an invertible matrix coefficient*: some entry of its matrix is
a unit of `R`. -/
def HasInvertibleCoeff (C : FreeComplex R) (i : ℤ) : Prop :=
  ∃ (k : Fin (C.n (i - 1))) (j : Fin (C.n (i - 1 + 1))), IsUnit (C.d (i - 1) k j)

/-- The differential `C.toComplex.d (t+1) t`, as a linear map, is `Matrix.toLin' (C.d t)`. -/
lemma toComplex_d_succ (C : FreeComplex R) (t : ℤ) (x : Fin (C.n (t + 1)) → R) :
    (C.toComplex.d (t+1) t).hom x = Matrix.toLin' (C.d t) x := by
  have hrefl : ∀ α : Type, LinearEquiv.funCongrLeft R R (Equiv.refl α)
      = LinearEquiv.refl R (α → R) := by intro α; ext f y; simp [LinearEquiv.funCongrLeft]
  simp only [toComplex, dite_eq_left, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    finCongr_refl, hrefl, LinearEquiv.refl_toLinearMap, LinearMap.id_coe, id_eq]

/-- Degreewise `R`-linear equivalences intertwining the differentials give an isomorphism of the
associated complexes. -/
noncomputable def linIso (C D : FreeComplex R)
    (e : (t : ℤ) → (Fin (C.n t) → R) ≃ₗ[R] (Fin (D.n t) → R))
    (hcomm : ∀ t, (Matrix.toLin' (D.d t)).comp (e (t + 1)).toLinearMap
      = (e t).toLinearMap.comp (Matrix.toLin' (C.d t))) :
    C.toComplex ≅ D.toComplex := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun t => (LinearEquiv.toModuleIso (e t))) ?_
  intro a b hab
  have hab' : a = b + 1 := by simpa [ComplexShape.down, eq_comm] using hab
  subst hab'
  apply ModuleCat.hom_ext
  ext x
  change (D.toComplex.d (b+1) b).hom ((e (b+1)) x) = (e b) ((C.toComplex.d (b+1) b).hom x)
  rw [toComplex_d_succ D b ((e (b+1)) x), toComplex_d_succ C b x]
  have := LinearMap.congr_fun (hcomm b) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
  exact this

/-- The block-diagonal ("direct sum") of two free complexes: ranks add, differentials are
block-diagonal via the standard identification `Fin (a + b) ≃ Fin a ⊕ Fin b`. -/
@[implicit_reducible]
noncomputable def combine (A B : FreeComplex R) : FreeComplex R where
  n j := A.n j + B.n j
  d t := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (A.d t) 0 0 (B.d t))
  dd t := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
      A.dd, B.dd, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.fromBlocks_zero,
      Matrix.submatrix_zero]
    rfl

/-- The linear equivalence `(Fin (a + b) → R) ≃ₗ (Fin a → R) × (Fin b → R)`. -/
noncomputable def splitLEquiv (a b : ℕ) :
    (Fin (a + b) → R) ≃ₗ[R] ((Fin a → R) × (Fin b → R)) :=
  (LinearEquiv.funCongrLeft R R (finSumFinEquiv (m := a) (n := b))).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R)

end FreeComplex

open FreeComplex

/-- The complex associated to the block-diagonal sum `combine A B` is isomorphic to the biproduct
of the complexes associated to `A` and `B`. -/
lemma combine_toComplex_iso_biprod {R : Type*} [CommRing R] (A B : FreeComplex R) :
    Nonempty ((combine A B).toComplex ≅ A.toComplex ⊞ B.toComplex) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun t => (splitLEquiv (A.n t) (B.n t)).toModuleIso
      ≪≫ (ModuleCat.biprodIsoProd (A.toComplex.X t) (B.toComplex.X t)).symm
      ≪≫ (HomologicalComplex.biprodXIso A.toComplex B.toComplex t).symm) ?_⟩
  intro a b hab
  have hab' : a = b + 1 := by simpa [ComplexShape.down, eq_comm] using hab
  subst hab'
  have hmatfst : ∀ (a' b' : ℕ) (MA : Matrix (Fin a') (Fin (A.n (b+1))) R)
      (MB : Matrix (Fin b') (Fin (B.n (b+1))) R) (x : Fin (A.n (b+1) + B.n (b+1)) → R),
      (Matrix.toLin' MA) ((splitLEquiv (A.n (b+1)) (B.n (b+1)) x)).fst
        = (splitLEquiv a' b'
            ((Matrix.toLin' (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks MA 0 0 MB))) x)).fst := by
    intro a' b' MA MB x
    funext r
    simp only [splitLEquiv, LinearEquiv.trans_apply, LinearEquiv.sumArrowLequivProdArrow_apply_fst,
      LinearEquiv.funCongrLeft_apply, Matrix.toLin'_apply, Matrix.reindex_apply,
      Matrix.submatrix_mulVec_equiv, LinearMap.funLeft_apply, Function.comp_apply,
      Matrix.fromBlocks_mulVec, Equiv.symm_apply_apply, Sum.elim_inl, Matrix.mulVec,
      Matrix.zero_mulVec, add_zero]
    rfl
  have hmatsnd : ∀ (a' b' : ℕ) (MA : Matrix (Fin a') (Fin (A.n (b+1))) R)
      (MB : Matrix (Fin b') (Fin (B.n (b+1))) R) (x : Fin (A.n (b+1) + B.n (b+1)) → R),
      (Matrix.toLin' MB) ((splitLEquiv (A.n (b+1)) (B.n (b+1)) x)).snd
        = (splitLEquiv a' b'
            ((Matrix.toLin' (Matrix.reindex finSumFinEquiv finSumFinEquiv
              (Matrix.fromBlocks MA 0 0 MB))) x)).snd := by
    intro a' b' MA MB x
    funext r
    simp only [splitLEquiv, LinearEquiv.trans_apply, LinearEquiv.sumArrowLequivProdArrow_apply_snd,
      LinearEquiv.funCongrLeft_apply, Matrix.toLin'_apply, Matrix.reindex_apply,
      Matrix.submatrix_mulVec_equiv, LinearMap.funLeft_apply, Function.comp_apply,
      Matrix.fromBlocks_mulVec, Equiv.symm_apply_apply, Sum.elim_inr, Matrix.mulVec,
      Matrix.zero_mulVec, zero_add]
    rfl
  rw [← cancel_mono (HomologicalComplex.biprodXIso A.toComplex B.toComplex b).hom]
  have hxinv_fst : ∀ t : ℤ, (HomologicalComplex.biprodXIso A.toComplex B.toComplex t).inv
      ≫ (biprod.fst (X := A.toComplex) (Y := B.toComplex)).f t = biprod.fst := by
    intro t
    rw [← HomologicalComplex.biprodXIso_hom_fst, Iso.inv_hom_id_assoc]
  have hxinv_snd : ∀ t : ℤ, (HomologicalComplex.biprodXIso A.toComplex B.toComplex t).inv
      ≫ (biprod.snd (X := A.toComplex) (Y := B.toComplex)).f t = biprod.snd := by
    intro t
    rw [← HomologicalComplex.biprodXIso_hom_snd, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext
  · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_fst]
    rw [← (biprod.fst (X := A.toComplex) (Y := B.toComplex)).comm (b+1) b]
    simp only [Iso.trans_hom, Category.assoc, Iso.symm_hom,
      reassoc_of% (hxinv_fst (b+1)),
      reassoc_of% ModuleCat.biprodIsoProd_inv_comp_fst,
      hxinv_fst b, ModuleCat.biprodIsoProd_inv_comp_fst]
    apply ModuleCat.hom_ext
    ext x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.toModuleIso_hom]
    change (A.toComplex.d (b+1) b).hom ((splitLEquiv (A.n (b+1)) (B.n (b+1)) x).fst)
      = (splitLEquiv (A.n b) (B.n b) ((combine A B).toComplex.d (b+1) b x)).fst
    rw [toComplex_d_succ A b, toComplex_d_succ (combine A B) b]
    exact hmatfst (A.n b) (B.n b) (A.d b) (B.d b) x
  · simp only [Category.assoc, HomologicalComplex.biprodXIso_hom_snd]
    rw [← (biprod.snd (X := A.toComplex) (Y := B.toComplex)).comm (b+1) b]
    simp only [Iso.trans_hom, Category.assoc, Iso.symm_hom,
      reassoc_of% (hxinv_snd (b+1)),
      reassoc_of% ModuleCat.biprodIsoProd_inv_comp_snd,
      hxinv_snd b, ModuleCat.biprodIsoProd_inv_comp_snd]
    apply ModuleCat.hom_ext
    ext x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.toModuleIso_hom]
    change (B.toComplex.d (b+1) b).hom ((splitLEquiv (A.n (b+1)) (B.n (b+1)) x).snd)
      = (splitLEquiv (A.n b) (B.n b) ((combine A B).toComplex.d (b+1) b x)).snd
    rw [toComplex_d_succ B b, toComplex_d_succ (combine A B) b]
    exact hmatsnd (A.n b) (B.n b) (A.d b) (B.d b) x

/-- Given degreewise invertible change-of-basis matrices `P t`, the complex `C` is isomorphic to
any complex `D` with the same ranks (`hn`) whose differentials are conjugate:
`P t * C.d t = (D.d t)|_{cast} * P (t+1)`. -/
lemma freeComplex_changeOfBasis {R : Type*} [CommRing R] (C D : FreeComplex R)
    (hn : ∀ t, D.n t = C.n t)
    (P : (t : ℤ) → Matrix (Fin (C.n t)) (Fin (C.n t)) R)
    (hP : ∀ t, Invertible (P t))
    (hconj : ∀ t, (P t) * (C.d t)
      = (D.d t).submatrix (Fin.cast (hn t).symm) (Fin.cast (hn (t + 1)).symm) * (P (t + 1))) :
    Nonempty (C.toComplex ≅ D.toComplex) := by
  refine ⟨FreeComplex.linIso C D
    (fun t => ((P t).toLinearEquiv' (hP t)).trans
      (LinearEquiv.funCongrLeft R R (finCongr (hn t)))) ?_⟩
  intro t
  have hPe : ∀ s, ((P s).toLinearEquiv' (hP s)).toLinearMap = Matrix.toLin' (P s) := fun s => rfl
  have hfc : ∀ s, (LinearEquiv.funCongrLeft R R (finCongr (hn s))).toLinearMap
      = LinearMap.funLeft R R (finCongr (hn s)) := fun s => rfl
  change (Matrix.toLin' (D.d t)).comp
      (((P (t+1)).toLinearEquiv' (hP (t+1))).trans
        (LinearEquiv.funCongrLeft R R (finCongr (hn (t+1))))).toLinearMap
    = (((P t).toLinearEquiv' (hP t)).trans
        (LinearEquiv.funCongrLeft R R (finCongr (hn t)))).toLinearMap.comp (Matrix.toLin' (C.d t))
  rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans, hPe, hPe, hfc, hfc]
  rw [LinearMap.comp_assoc, ← Matrix.toLin'_mul, hconj t]
  rw [show (Fin.cast (hn (t+1)).symm) = ⇑(finCongr (hn (t+1)).symm) from rfl]
  rw [Matrix.toLin'_mul, Matrix.toLin'_submatrix, finCongr_symm]
  have hcancel : (LinearMap.funLeft R R (finCongr (hn t))).comp
      (LinearMap.funLeft R R (Fin.cast (hn t).symm))
      = LinearMap.id := by
    rw [← LinearMap.funLeft_comp]
    have : (Fin.cast (hn t).symm) ∘ (finCongr (hn t)) = id := by
      funext y; simp [finCongr_apply]
    rw [this]
    ext g i; simp
  simp only [← LinearMap.comp_assoc, hcancel, LinearMap.id_comp]

open Matrix in
/-- Clearing the first row and column of a block matrix whose `(0,0)` block has been scaled to the
identity yields `fromBlocks 1 0 0 M`. -/
private lemma pivot_block_algebra {R : Type*} [CommRing R] {p q : ℕ}
    (v11 : Matrix (Fin 1) (Fin 1) R)
    (v12 : Matrix (Fin 1) (Fin (q - 1)) R)
    (v21 : Matrix (Fin (p - 1)) (Fin 1) R)
    (v22 : Matrix (Fin (p - 1)) (Fin (q - 1)) R)
    (b : R) (hba : (b • (1 : Matrix (Fin 1) (Fin 1) R)) * v11 = 1) :
    (fromBlocks (1:Matrix (Fin 1) (Fin 1) R) 0 (-v21) (1:Matrix (Fin (p-1)) (Fin (p-1)) R))
      * (fromBlocks (b • (1 : Matrix (Fin 1) (Fin 1) R)) 0 0 (1:Matrix (Fin (p-1)) (Fin (p-1)) R))
      * (fromBlocks v11 v12 v21 v22)
      * (fromBlocks (1:Matrix (Fin 1) (Fin 1) R) (-(b • v12)) 0 (1:Matrix (Fin (q-1)) (Fin (q-1))
          R))
      = fromBlocks 1 0 0 (v22 - v21 * (b • v12)) := by
  have hv : b • v11 = 1 := by rw [← hba, Matrix.smul_mul, Matrix.one_mul]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.smul_mul, Matrix.mul_assoc, hba]
  congr 1
  · rw [neg_add_cancel]
  · rw [neg_add_cancel]
  · rw [neg_add_cancel, Matrix.zero_mul, zero_add, sub_eq_add_neg, Matrix.neg_mul, add_comm]

/-- A permutation matrix has unit determinant. -/
private lemma perm_isUnit_det {R : Type*} [CommRing R] {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    IsUnit (σ.permMatrix R).det := by
  rw [Matrix.det_permutation]
  exact (Int.isUnit_iff.mpr (by rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h|h <;>
    simp [h])).map (Int.castRingHom R)

open Matrix in
/-- A matrix `u` with a unit entry can be normalized by invertible row and column changes of basis
to block-diagonal form: there are `P` and `Q` with unit determinant and a block `M` such that
`P * u * Q`, reindexed along `Fin 1 ⊕ Fin (p-1) ≃ Fin p` and `Fin 1 ⊕ Fin (q-1) ≃ Fin q`, equals
`fromBlocks 1 0 0 M`. -/
lemma exists_pivot_block_split {R : Type*} [CommRing R] {p q : ℕ}
    (u : Matrix (Fin p) (Fin q) R) (k : Fin p) (j : Fin q) (hu : IsUnit (u k j)) :
    ∃ (hp : 1 ≤ p) (hq : 1 ≤ q) (P : Matrix (Fin p) (Fin p) R) (Q : Matrix (Fin q) (Fin q) R)
      (M : Matrix (Fin (p - 1)) (Fin (q - 1)) R),
      IsUnit P.det ∧ IsUnit Q.det ∧
      (P * u * Q).submatrix
          (fun x => Fin.cast (by omega : 1 + (p - 1) = p) (finSumFinEquiv x))
          (fun y => Fin.cast (by omega : 1 + (q - 1) = q) (finSumFinEquiv y))
        = Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 M := by
  have hp : 1 ≤ p := by have := k.isLt; omega
  have hq : 1 ≤ q := by have := j.isLt; omega
  refine ⟨hp, hq, ?_⟩
  obtain ⟨b, hba⟩ := hu.exists_left_inv
  set eP : Fin 1 ⊕ Fin (p-1) ≃ Fin p := finSumFinEquiv.trans (finCongr (by omega)) with hePdef
  set eQ : Fin 1 ⊕ Fin (q-1) ≃ Fin q := finSumFinEquiv.trans (finCongr (by omega)) with heQdef
  set σ : Equiv.Perm (Fin p) := Equiv.swap ⟨0, by omega⟩ k with hσdef
  set τ : Equiv.Perm (Fin q) := Equiv.swap ⟨0, by omega⟩ j with hτdef
  set Pperm := σ.permMatrix R with hPpdef
  set Qperm := τ.permMatrix R with hQpdef
  set v : Matrix (Fin 1 ⊕ Fin (p-1)) (Fin 1 ⊕ Fin (q-1)) R
    := (Pperm * u * Qperm).submatrix eP eQ with hvdef
  have hentry : v (Sum.inl 0) (Sum.inl 0) = u k j := by
    have h1 : (Pperm * u * Qperm) (eP (Sum.inl 0)) (eQ (Sum.inl 0))
        = u (σ (eP (Sum.inl 0))) (τ.symm (eQ (Sum.inl 0))) := by
      rw [hPpdef, hQpdef, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix]
      rw [Matrix.mul_assoc, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
      simp [Matrix.submatrix_apply]
    rw [hvdef, Matrix.submatrix_apply, h1]
    have heP : eP (Sum.inl 0) = (⟨0, by omega⟩ : Fin p) := by
      rw [hePdef]; simp [finSumFinEquiv_apply_left]; rfl
    have heQ : eQ (Sum.inl 0) = (⟨0, by omega⟩ : Fin q) := by
      rw [heQdef]; simp [finSumFinEquiv_apply_left]; rfl
    rw [heP, heQ, hσdef, hτdef]
    simp [Equiv.swap_apply_left]
  have hba' : (b • (1 : Matrix (Fin 1) (Fin 1) R)) * v.toBlocks₁₁ = 1 := by
    ext a c
    fin_cases a; fin_cases c
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.toBlocks₁₁]
    rw [Fin.sum_univ_one]
    simp only [Matrix.of_apply]
    change b • (1:R) * v (Sum.inl 0) (Sum.inl 0) = 1
    rw [hentry, smul_eq_mul, mul_one, hba]
  set Lscale : Matrix (Fin 1 ⊕ Fin (p-1)) (Fin 1 ⊕ Fin (p-1)) R
    := fromBlocks (b • (1 : Matrix (Fin 1) (Fin 1) R)) 0 0 1 with hLscaledef
  set Lclear : Matrix (Fin 1 ⊕ Fin (p-1)) (Fin 1 ⊕ Fin (p-1)) R
    := fromBlocks 1 0 (-v.toBlocks₂₁) 1 with hLcleardef
  set Rclear : Matrix (Fin 1 ⊕ Fin (q-1)) (Fin 1 ⊕ Fin (q-1)) R
    := fromBlocks 1 (-(b • v.toBlocks₁₂)) 0 1 with hRcleardef
  set Lall := Lclear * Lscale with hLalldef
  set Pleft := Lall.submatrix eP.symm eP.symm with hPleftdef
  set Rright := Rclear.submatrix eQ.symm eQ.symm with hRrightdef
  refine ⟨Pleft * Pperm, Qperm * Rright,
    v.toBlocks₂₂ - v.toBlocks₂₁ * (b • v.toBlocks₁₂), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    apply IsUnit.mul
    · rw [hPleftdef, Matrix.det_submatrix_equiv_self, hLalldef, Matrix.det_mul,
        hLcleardef, hLscaledef, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
      simp only [det_unique, one_apply_eq, det_one, mul_one, Fin.default_eq_zero, Fin.isValue,
        Matrix.smul_apply, smul_eq_mul, one_mul]
      exact IsUnit.of_mul_eq_one _ hba
    · rw [hPpdef]; exact perm_isUnit_det σ
  · rw [Matrix.det_mul]
    apply IsUnit.mul
    · rw [hQpdef]; exact perm_isUnit_det τ
    · rw [hRrightdef, Matrix.det_submatrix_equiv_self, hRcleardef, det_fromBlocks_zero₂₁]
      simp
  · have hreindex : ((Pleft * Pperm) * u * (Qperm * Rright)).submatrix eP eQ
        = Lall * v * Rclear := by
      have hP : Pleft.submatrix eP eP = Lall := by
        rw [hPleftdef]; simp [Matrix.submatrix_submatrix]
      have hR : Rright.submatrix eQ eQ = Rclear := by
        rw [hRrightdef]; simp [Matrix.submatrix_submatrix]
      rw [hvdef]
      rw [show (Pleft * Pperm) * u * (Qperm * Rright)
            = Pleft * (Pperm * u * Qperm) * Rright by simp only [Matrix.mul_assoc]]
      rw [← hP, ← hR]
      simp only [Matrix.submatrix_mul_equiv]
    change ((Pleft * Pperm) * u * (Qperm * Rright)).submatrix (⇑eP) (⇑eQ) = _
    rw [hreindex, hLalldef, hLcleardef, hLscaledef, hRcleardef]
    have key := pivot_block_algebra v.toBlocks₁₁ v.toBlocks₁₂ v.toBlocks₂₁ v.toBlocks₂₂ b hba'
    rw [fromBlocks_toBlocks v] at key
    exact key

/-- Block-clearing (ROW): if a block matrix `fromBlocks 1 0 0 M` left-multiplies `Y` to zero,
then the top (`inl`) row-block of `Y` vanishes. -/
private lemma split_data_clearRow {R : Type*} [CommRing R] {a c d : ℕ}
    (M : Matrix (Fin a) (Fin c) R) (Y : Matrix (Fin 1 ⊕ Fin c) (Fin 1 ⊕ Fin d) R)
    (h : (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 M) * Y = 0) :
    Y.toBlocks₁₁ = 0 ∧ Y.toBlocks₁₂ = 0 := by
  rw [← Matrix.fromBlocks_toBlocks Y, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_zero,
    Matrix.fromBlocks_inj] at h
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero] at h
  exact ⟨h.1, h.2.1⟩

/-- Block-clearing (COLUMN): if `Y` right-multiplied by `fromBlocks 1 0 0 M` is zero,
then the left (`inl`) column-block of `Y` vanishes. -/
private lemma split_data_clearCol {R : Type*} [CommRing R] {a c d : ℕ}
    (M : Matrix (Fin c) (Fin a) R) (Y : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin c) R)
    (h : Y * (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 M) = 0) :
    Y.toBlocks₁₁ = 0 ∧ Y.toBlocks₂₁ = 0 := by
  rw [← Matrix.fromBlocks_toBlocks Y, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_zero,
    Matrix.fromBlocks_inj] at h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add] at h
  exact ⟨h.1, h.2.2.1⟩

/-- Block-clearing (ROW), C'-first ordering: if `fromBlocks M 0 0 1` left-multiplies `Y` to
zero, then the bottom (`inr`) row-blocks of `Y` vanish. -/
private lemma split_data_clearRow' {R : Type*} [CommRing R] {a c d f : ℕ}
    (M : Matrix (Fin a) (Fin c) R) (Y : Matrix (Fin c ⊕ Fin 1) (Fin d ⊕ Fin f) R)
    (h : (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin 1) (Fin 1) R)) * Y = 0) :
    Y.toBlocks₂₁ = 0 ∧ Y.toBlocks₂₂ = 0 := by
  rw [← Matrix.fromBlocks_toBlocks Y, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_zero,
    Matrix.fromBlocks_inj] at h
  simp only [Matrix.one_mul, Matrix.zero_mul, zero_add] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- Block-clearing (COLUMN), C'-first ordering: if `Y` right-multiplied by `fromBlocks M 0 0 1`
is zero, then the right (`inr`) column-blocks of `Y` vanish. -/
private lemma split_data_clearCol' {R : Type*} [CommRing R] {a c d f : ℕ}
    (M : Matrix (Fin c) (Fin a) R) (Y : Matrix (Fin d ⊕ Fin f) (Fin c ⊕ Fin 1) R)
    (h : Y * (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin 1) (Fin 1) R)) = 0) :
    Y.toBlocks₁₂ = 0 ∧ Y.toBlocks₂₂ = 0 := by
  rw [← Matrix.fromBlocks_toBlocks Y, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_zero,
    Matrix.fromBlocks_inj] at h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add] at h
  exact ⟨h.2.1, h.2.2.2⟩

/-- The `sumComm` block-swap of `fromBlocks 1 0 0 M` is `fromBlocks M 0 0 1`. -/
private lemma split_data_swap {R : Type*} [CommRing R] {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) :
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 M).submatrix
      (Equiv.sumComm (Fin a) (Fin 1)) (Equiv.sumComm (Fin b) (Fin 1))
      = Matrix.fromBlocks M 0 0 1 := by
  ext x y
  rcases x with x|x <;> rcases y with y|y <;>
    simp [Matrix.submatrix_apply, Equiv.sumComm, Matrix.fromBlocks]

/-- The inverse of a permutation matrix is the permutation matrix of the inverse. -/
private lemma permMatrix_inv {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix R)⁻¹ = Equiv.Perm.permMatrix R σ⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

/-- Let `P`, `Q` be matrices with unit determinant such that `P * C.d (i-1) * Q` is
block-diagonal `fromBlocks 1 0 0 M`. Then there are a complex `C'` with the ranks of `C`
decremented at `i` and `i - 1`, with `(combine C' (elementaryComplex R i)).n t = C.n t` for all
`t`, and degreewise matrices `Pmat t` with unit determinant conjugating the differentials of `C`
into those of `combine C' (elementaryComplex R i)`. -/
lemma freeComplex_split_data {R : Type*} [CommRing R] (C : FreeComplex R) (i : ℤ)
    (hi : 1 ≤ C.n (i - 1 + 1)) (him1 : 1 ≤ C.n (i - 1))
    (P : Matrix (Fin (C.n (i - 1))) (Fin (C.n (i - 1))) R)
    (Q : Matrix (Fin (C.n (i - 1 + 1))) (Fin (C.n (i - 1 + 1))) R)
    (M : Matrix (Fin (C.n (i - 1) - 1)) (Fin (C.n (i - 1 + 1) - 1)) R)
    (hPdet : IsUnit P.det) (hQdet : IsUnit Q.det)
    (hblock : (P * C.d (i - 1) * Q).submatrix
        (fun x => Fin.cast (by omega : 1 + (C.n (i - 1) - 1) = C.n (i - 1)) (finSumFinEquiv x))
        (fun y => Fin.cast (by omega : 1 + (C.n (i - 1 + 1) - 1) = C.n (i - 1 + 1))
          (finSumFinEquiv y))
      = Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 M) :
    ∃ (C' : FreeComplex R) (Pmat : (t : ℤ) → Matrix (Fin (C.n t)) (Fin (C.n t)) R)
      (hn : ∀ t, (combine C' (elementaryComplex R i)).n t = C.n t),
      (∀ j, C'.n j = if j = i then C.n i - 1 else if j = i - 1 then C.n (i - 1) - 1 else C.n j) ∧
      (∀ t, IsUnit (Pmat t).det) ∧
      (∀ t, (Pmat t) * (C.d t)
          = ((combine C' (elementaryComplex R i)).d t).submatrix
              (Fin.cast (hn t).symm) (Fin.cast (hn (t + 1)).symm) * (Pmat (t + 1))) := by
  set C'n : ℤ → ℕ := fun j =>
    if j = i then C.n i - 1 else if j = i - 1 then C.n (i - 1) - 1 else C.n j with hC'n
  have hi' : 1 ≤ C.n i := by simpa using hi
  have hn : ∀ t, (C'n t + elemRank i t) = C.n t := by
    intro t
    simp only [hC'n, elemRank]
    by_cases hti : t = i
    · subst hti
      have h1 : ¬ (t = t - 1) := by omega
      rw [ite_eq_left rfl, ite_eq_left (Or.inl rfl)]
      omega
    · by_cases htm : t = i - 1
      · subst htm
        have h2 : ¬ (i - 1 = i) := by omega
        rw [ite_eq_right h2, ite_eq_left rfl, ite_eq_left (Or.inr rfl)]
        omega
      · rw [ite_eq_right hti, ite_eq_right htm, ite_eq_right (by tauto : ¬ (t = i ∨ t = i - 1))]
        omega
  have hPinv : Invertible P := Matrix.invertibleOfIsUnitDet P hPdet
  have hQinv : Invertible Q := Matrix.invertibleOfIsUnitDet Q hQdet
  classical
  have hni : C.n (i - 1 + 1) = C.n i := by ring_nf
  set Brow : Fin (C.n (i-1) - 1) ⊕ Fin 1 ≃ Fin (C.n (i-1)) :=
    finSumFinEquiv.trans (finCongr (by omega)) with hBrowdef
  set Bcol : Fin (C.n (i-1+1) - 1) ⊕ Fin 1 ≃ Fin (C.n (i-1+1)) :=
    finSumFinEquiv.trans (finCongr (by omega)) with hBcoldef
  set Arow : Fin 1 ⊕ Fin (C.n (i-1) - 1) ≃ Fin (C.n (i-1)) :=
    finSumFinEquiv.trans (finCongr (by omega)) with hArowdef
  set Acol : Fin 1 ⊕ Fin (C.n (i-1+1) - 1) ≃ Fin (C.n (i-1+1)) :=
    finSumFinEquiv.trans (finCongr (by omega)) with hAcoldef
  set σr : Equiv.Perm (Fin (C.n (i-1))) :=
    (Brow.symm).trans ((Equiv.sumComm (Fin (C.n (i-1) - 1)) (Fin 1)).trans Arow) with hσrdef
  set σc : Equiv.Perm (Fin (C.n (i-1+1))) :=
    (Bcol.symm).trans ((Equiv.sumComm (Fin (C.n (i-1+1) - 1)) (Fin 1)).trans Acol) with hσcdef
  set Pmat : (t : ℤ) → Matrix (Fin (C.n t)) (Fin (C.n t)) R := fun t =>
    if ht1 : t = i - 1 then
      (σr.permMatrix R * P).submatrix (finCongr (congrArg C.n ht1)) (finCongr (congrArg C.n ht1))
    else if hti : t = i then
      (σc.permMatrix R * ⅟ Q).submatrix
        (finCongr (by rw [hti]; exact hni.symm)) (finCongr (by rw [hti]; exact hni.symm))
    else 1 with hPmatdef
  have hPmatdet : ∀ t, IsUnit (Pmat t).det := by
    intro t
    rw [hPmatdef]
    by_cases ht1 : t = i - 1
    · simp only [ht1, dite_eq_left]
      rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul]
      exact (perm_isUnit_det σr).mul hPdet
    · simp only [ht1, dite_eq_right, not_false_iff]
      by_cases hti : t = i
      · simp only [hti, dite_eq_left]
        rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul]
        exact (perm_isUnit_det σc).mul
          (Matrix.isUnit_iff_isUnit_det _ |>.mp (isUnit_of_invertible (⅟ Q)))
      · simp only [hti, dite_eq_right, not_false_iff, Matrix.det_one]
        exact isUnit_one
  set g : (t : ℤ) → (Fin (C.n t) ≃ Fin (C'n t) ⊕ Fin (elemRank i t)) := fun t =>
    (finCongr (hn t).symm).trans finSumFinEquiv.symm with hg
  set W : (t : ℤ) → Matrix (Fin (C'n t) ⊕ Fin (elemRank i t)) (Fin (C'n (t+1)) ⊕ Fin (elemRank i
      (t+1))) R :=
    fun t => (Pmat t * C.d t * (Pmat (t+1))⁻¹).submatrix (g t).symm (g (t+1)).symm with hW
  have hPmatMulInv : ∀ t, (Pmat t)⁻¹ * Pmat t = 1 := by
    intro t
    rw [Matrix.nonsing_inv_mul _ (hPmatdet t)]
  have hPmat_im1 : Pmat (i - 1) = σr.permMatrix R * P := by
    simp only [hPmatdef, dite_eq_left]
    rw [show (finCongr (congrArg C.n (rfl : i - 1 = i - 1))) = (Equiv.refl _) from rfl]
    simp [Matrix.submatrix_id_id]
  have hWzero : ∀ t, W t * W (t+1) = 0 := by
    intro t
    rw [hW]
    rw [Matrix.submatrix_mul_equiv (Pmat t * C.d t * (Pmat (t+1))⁻¹)
          (Pmat (t+1) * C.d (t+1) * (Pmat (t+1+1))⁻¹) (g t).symm (g (t+1)).symm (g (t+1+1)).symm]
    have : (Pmat t * C.d t * (Pmat (t+1))⁻¹) * (Pmat (t+1) * C.d (t+1) * (Pmat (t+1+1))⁻¹)
        = Pmat t * (C.d t * C.d (t+1)) * (Pmat (t+1+1))⁻¹ := by
      calc (Pmat t * C.d t * (Pmat (t+1))⁻¹) * (Pmat (t+1) * C.d (t+1) * (Pmat (t+1+1))⁻¹)
          = Pmat t * C.d t * ((Pmat (t+1))⁻¹ * Pmat (t+1)) * C.d (t+1) * (Pmat (t+1+1))⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = Pmat t * (C.d t * C.d (t+1)) * (Pmat (t+1+1))⁻¹ := by
            rw [hPmatMulInv (t+1)]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [this, C.dd t, Matrix.mul_zero, Matrix.zero_mul, Matrix.submatrix_zero]
    rfl
  have hii0 : i - 1 + 1 = i := by ring
  have hcr0 : C'n (i - 1) = C.n (i - 1) - 1 := by
    simp only [hC'n]; rw [ite_eq_right (show ¬ ((i:ℤ) - 1 = i) by omega)]; simp
  have her0 : elemRank i (i - 1) = 1 := by
    simp only [elemRank]; simp
  have hcc0 : C'n (i - 1 + 1) = C.n (i - 1 + 1) - 1 := by
    simp only [hC'n]; rw [ite_eq_left hii0, hni]
  have hec0 : elemRank i (i - 1 + 1) = 1 := by
    simp only [elemRank]; rw [ite_eq_left (Or.inl hii0)]
  set cr : Fin (C'n (i-1)) ⊕ Fin (elemRank i (i-1)) ≃ Fin (C.n (i-1) - 1) ⊕ Fin 1 :=
    Equiv.sumCongr (finCongr hcr0) (finCongr her0) with hcrdef0
  set cc : Fin (C'n (i-1+1)) ⊕ Fin (elemRank i (i-1+1)) ≃ Fin (C.n (i-1+1) - 1) ⊕ Fin 1 :=
    Equiv.sumCongr (finCongr hcc0) (finCongr hec0) with hccdef0
  have hWim1 : W (i - 1)
      = (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin 1) (Fin 1) R)).submatrix cr cc := by
    have hii : i - 1 + 1 = i := hii0
    have hPsucc : Pmat (i - 1 + 1) = σc.permMatrix R * ⅟ Q := by
      have : Pmat (i - 1 + 1)
          = (σc.permMatrix R * ⅟ Q).submatrix
              (finCongr (show C.n (i-1+1) = C.n (i-1+1) from rfl))
              (finCongr (show C.n (i-1+1) = C.n (i-1+1) from rfl)) := by
        simp only [hPmatdef]
        rw [dite_eq_right (by omega : ¬ (i - 1 + 1 = i - 1)), dite_eq_left hii]
      rw [this]
      simp [finCongr_refl, Matrix.submatrix_id_id]
    have hPsuccInv : (Pmat (i - 1 + 1))⁻¹ = Q * Equiv.Perm.permMatrix R σc⁻¹ := by
      rw [hPsucc, Matrix.mul_inv_rev, permMatrix_inv, Matrix.invOf_eq_nonsing_inv,
        Matrix.nonsing_inv_nonsing_inv Q hQdet]
    have hgrow : ⇑(g (i-1)).symm = ⇑Brow ∘ ⇑cr := by
      rw [hg, hBrowdef, hcrdef0]
      funext x
      apply Fin.ext
      rcases x with x|x <;>
        simp only [Equiv.symm_trans_apply, Equiv.trans_apply, finCongr_symm, finCongr_apply,
          Fin.cast, Equiv.symm_symm, Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl,
          Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd,
          Fin.val_natAdd]; omega
    have hgcol : ⇑(g (i-1+1)).symm = ⇑Bcol ∘ ⇑cc := by
      rw [hg, hBcoldef, hccdef0]
      funext x
      apply Fin.ext
      rcases x with x|x <;>
        simp only [Equiv.symm_trans_apply, Equiv.trans_apply, finCongr_symm, finCongr_apply,
          Fin.cast, Equiv.symm_symm, Function.comp_apply, Equiv.sumCongr_apply, Sum.map_inl,
          Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd,
          Fin.val_natAdd]; omega
    have hAr : (fun x => Fin.cast (show 1 + (C.n (i-1)-1) = C.n (i-1) by omega) (finSumFinEquiv x))
        = ⇑Arow := by funext x; rfl
    have hAc :
        (fun y => Fin.cast (show 1 + (C.n (i-1+1)-1) = C.n (i-1+1) by omega) (finSumFinEquiv y))
        = ⇑Acol := by funext y; rfl
    have hblock' := hblock
    rw [hAr, hAc] at hblock'
    have key : ((σr.permMatrix R * P) * C.d (i-1) * (Q * Equiv.Perm.permMatrix R σc⁻¹)).submatrix
        Brow Bcol
        = Matrix.fromBlocks M 0 0 1 := by
      have hmul : (σr.permMatrix R * P) * C.d (i-1) * (Q * Equiv.Perm.permMatrix R σc⁻¹)
          = (σr.permMatrix R) * (P * C.d (i-1) * Q) * (Equiv.Perm.permMatrix R σc⁻¹) := by
        simp only [Matrix.mul_assoc]
      rw [hmul, PEquiv.toMatrix_toPEquiv_mul σr (P * C.d (i-1) * Q),
        PEquiv.mul_toMatrix_toPEquiv ((P * C.d (i-1) * Q).submatrix σr id) σc⁻¹,
        Matrix.submatrix_submatrix, Matrix.submatrix_submatrix]
      have hPQ : P * C.d (i-1) * Q
          = (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) R) 0 0 M).submatrix
              Arow.symm Acol.symm := by
        rw [← hblock', Matrix.submatrix_submatrix]; simp
      rw [hPQ, Matrix.submatrix_submatrix, ← split_data_swap M]
      congr 1
      · funext x
        simp only [hσrdef, Function.comp, id, Equiv.trans_apply, Equiv.symm_apply_apply,
          ]
      · funext y
        simp only [hσcdef, Function.comp, id, Equiv.Perm.inv_def, Equiv.symm_symm,
          Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hW]
    simp only []
    rw [hPmat_im1, hPsuccInv, hgrow, hgcol, ← Matrix.submatrix_submatrix, key, hcrdef0, hccdef0]
  have hWim1nat : W (i - 1)
      = Matrix.fromBlocks ((W (i-1)).toBlocks₁₁) 0 0 ((elementaryComplex R i).d (i-1)) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (W (i-1))]
    congr 1
    · rw [hWim1]
      rw [Matrix.toBlocks₁₂]; ext a b
      simp [hcrdef0, hccdef0, Matrix.submatrix_apply, Equiv.sumCongr, Matrix.fromBlocks]
    · rw [hWim1]
      rw [Matrix.toBlocks₂₁]; ext a b
      simp [hcrdef0, hccdef0, Matrix.submatrix_apply, Equiv.sumCongr, Matrix.fromBlocks]
    · rw [hWim1]
      rw [Matrix.toBlocks₂₂]
      ext a b
      have hEd : (elementaryComplex R i).d (i-1) a b = 1 := by
        change (if i - 1 = i - 1 then
          (Matrix.of fun (_ : Fin (elemRank i (i-1))) (_ : Fin (elemRank i (i-1+1))) => (1:R))
          else 0) a b = 1
        rw [ite_eq_left rfl]; rfl
      have hab : (Fin.cast her0 a) = (Fin.cast hec0 b) := Subsingleton.elim _ _
      rw [hEd]
      simp [hcrdef0, hccdef0, Matrix.submatrix_apply, Equiv.sumCongr, Matrix.fromBlocks,
        Matrix.one_apply, hab]
  have hz0 : ∀ {m n : ℕ} (A B : Matrix (Fin m) (Fin n) R), m = 0 ∨ n = 0 → A = B := by
    rintro m n A B (rfl | rfl) <;> ext a b
    · exact a.elim0
    · exact b.elim0
  have hmaster : ∀ t, W t
      = Matrix.fromBlocks ((W t).toBlocks₁₁) 0 0 ((elementaryComplex R i).d t) := by
    intro t
    by_cases ht1 : t = i - 1
    · subst ht1
      exact hWim1nat
    suffices h : (W t).toBlocks₁₂ = 0 ∧ (W t).toBlocks₂₁ = 0
        ∧ (W t).toBlocks₂₂ = (elementaryComplex R i).d t by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks (W t)]
      rw [h.left, h.right.left, h.right.right]
    have hE0 : ∀ s : ℤ, s ≠ i → s ≠ i - 1 → elemRank i s = 0 := by
      intro s h1 h2; simp only [elemRank]; rw [ite_eq_right]; tauto
    by_cases hti : t = i
    · subst hti
      have er1 : elemRank t (t + 1) = 0 := hE0 (t+1) (by omega) (by omega)
      refine ⟨hz0 _ _ (Or.inr er1), ?_, hz0 _ _ (Or.inr er1)⟩
      have h0 : W (t - 1) * W (t - 1 + 1) = 0 := hWzero (t - 1)
      rw [hWim1] at h0
      have hsplit : W (t - 1 + 1)
          = ((W (t - 1 + 1)).submatrix cc.symm (Equiv.refl _)).submatrix cc (Equiv.refl _) := by
        rw [Matrix.submatrix_submatrix]
        simp [Equiv.symm_comp_self]
      rw [hsplit, Matrix.submatrix_mul_equiv] at h0
      have hprod : (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin 1) (Fin 1) R))
          * (W (t - 1 + 1)).submatrix cc.symm (Equiv.refl _) = 0 := by
        have := congrArg (fun X => Matrix.submatrix X cr.symm (Equiv.refl _)) h0
        simpa [Matrix.submatrix_submatrix, Equiv.symm_comp_self] using this
      obtain ⟨h21, _⟩ := split_data_clearRow' M _ hprod
      have key21 : (W (t - 1 + 1)).toBlocks₂₁ = 0 := by
        apply Matrix.ext
        intro a b
        have := congrArg (fun Z => Z (finCongr hec0 a) b) h21
        simpa [Matrix.toBlocks₂₁, Matrix.submatrix_apply, hccdef0, Equiv.sumCongr] using this
      have hcast : (W (t - 1 + 1)).toBlocks₂₁ = 0 → (W t).toBlocks₂₁ = 0 := by
        rw [show (t - 1 + 1 : ℤ) = t from hii0]; exact id
      exact hcast key21
    · by_cases ht2 : t = i - 2
      · subst ht2
        have hr0 : elemRank i (i - 2) = 0 := hE0 (i - 2) (by omega) (by omega)
        have hjj : i - 2 + 1 = i - 1 := by ring
        refine ⟨?_, ?_, ?_⟩
        · have her2 : elemRank i (i - 2 + 1) = 1 := by
            simp only [elemRank]; rw [ite_eq_left (Or.inr (by ring : i - 2 + 1 = i - 1))]
          have hec2 : elemRank i (i - 2 + 1 + 1) = 1 := by
            simp only [elemRank]; rw [ite_eq_left (Or.inl (by ring : i - 2 + 1 + 1 = i))]
          have hW2 : W (i - 2 + 1)
              = Matrix.fromBlocks ((W (i-2+1)).toBlocks₁₁) 0 0 ((elementaryComplex R i).d
                  (i-2+1)) :=
            hjj.symm ▸ hWim1nat
          set A := (W (i - 2 + 1)).toBlocks₁₁ with hAdef
          set E := (elementaryComplex R i).d (i - 2 + 1) with hEdef
          set erEq : Fin (C'n (i - 2 + 1)) ⊕ Fin (elemRank i (i - 2 + 1))
              ≃ Fin (C'n (i - 2 + 1)) ⊕ Fin 1 :=
            Equiv.sumCongr (Equiv.refl _) (finCongr her2) with herEqdef
          set ecEq : Fin (C'n (i - 2 + 1 + 1)) ⊕ Fin (elemRank i (i - 2 + 1 + 1))
              ≃ Fin (C'n (i - 2 + 1 + 1)) ⊕ Fin 1 :=
            Equiv.sumCongr (Equiv.refl _) (finCongr hec2) with hecEqdef
          have h0 : W (i - 2) * W (i - 2 + 1) = 0 := hWzero (i - 2)
          rw [hW2] at h0
          have hEconv : Matrix.fromBlocks A 0 0 E
              = (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) R)).submatrix erEq ecEq := by
            apply Matrix.ext
            intro x y
            have hE1 : ∀ (p : Fin (elemRank i (i-2+1))) (q : Fin (elemRank i (i-2+1+1))),
                E p q = 1 := by
              intro p q
              rw [hEdef]
              change (if i - 2 + 1 = i - 1 then
                (Matrix.of fun (_ : Fin (elemRank i (i-2+1)))
                  (_ : Fin (elemRank i (i-2+1+1))) => (1:R))
                else 0) p q = 1
              rw [ite_eq_left (by ring : i - 2 + 1 = i - 1)]; rfl
            rcases x with x | x <;> rcases y with y | y
            · simp [herEqdef, hecEqdef, Matrix.submatrix_apply, Equiv.sumCongr, Matrix.fromBlocks,
                ]
            · simp [herEqdef, hecEqdef, Matrix.submatrix_apply, Equiv.sumCongr, Matrix.fromBlocks,
                ]
            · simp [herEqdef, hecEqdef, Matrix.submatrix_apply, Equiv.sumCongr, Matrix.fromBlocks,
                ]
            · simp [herEqdef, hecEqdef, Matrix.submatrix_apply, Equiv.sumCongr, Matrix.fromBlocks,
                 hE1, Subsingleton.elim (Fin.cast her2 x) (Fin.cast hec2 y)]
          rw [hEconv] at h0
          have hsplit : W (i - 2)
              = ((W (i - 2)).submatrix (Equiv.refl _) erEq.symm).submatrix
                  (Equiv.refl _) erEq := by
            rw [Matrix.submatrix_submatrix]
            simp [ Equiv.symm_comp_self]
          rw [hsplit, Matrix.submatrix_mul_equiv] at h0
          have hprod : (W (i - 2)).submatrix (Equiv.refl _) erEq.symm
              * (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) R)) = 0 := by
            have := congrArg (fun X => Matrix.submatrix X (Equiv.refl _) ecEq.symm) h0
            simpa [Matrix.submatrix_submatrix, Equiv.self_comp_symm] using this
          obtain ⟨h12, _⟩ := split_data_clearCol' A _ hprod
          apply Matrix.ext
          intro a b
          have := congrArg (fun Z => Z a (finCongr her2 b)) h12
          simpa [Matrix.toBlocks₁₂, Matrix.submatrix_apply, herEqdef, Equiv.sumCongr] using this
        · exact hz0 _ _ (Or.inl hr0)
        · exact hz0 _ _ (Or.inl hr0)
      · have hr0 : elemRank i t = 0 := hE0 t hti ht1
        have hr0' : elemRank i (t + 1) = 0 := hE0 (t+1) (by omega) (by omega)
        exact ⟨hz0 _ _ (Or.inr hr0'), hz0 _ _ (Or.inl hr0), hz0 _ _ (Or.inl hr0)⟩
  set C' : FreeComplex R :=
    { n := C'n
      d := fun t => (W t).toBlocks₁₁
      dd := by
        intro t
        have hzero := hWzero t
        rw [hmaster t, hmaster (t+1), Matrix.fromBlocks_multiply] at hzero
        have := congrArg Matrix.toBlocks₁₁ hzero
        simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul, Matrix.mul_zero,
          add_zero] at this
        refine this.trans ?_
        ext i j
        simp [Matrix.toBlocks₁₁] } with hC'
  have hnD : ∀ t, (combine C' (elementaryComplex R i)).n t = C.n t := hn
  refine ⟨C', Pmat, hnD, fun j => rfl, hPmatdet, ?_⟩
  intro t
  have hDd : (combine C' (elementaryComplex R i)).d t
      = (Matrix.fromBlocks (C'.d t) 0 0 ((elementaryComplex R i).d t)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [hC']
    rfl
  rw [hDd, Matrix.submatrix_submatrix]
  have hcompose : ∀ s, (⇑finSumFinEquiv.symm ∘ (Fin.cast (hnD s).symm : Fin (C.n s) → _))
      = ⇑(g s) := by
    intro s; funext x; rfl
  rw [hcompose t, hcompose (t+1)]
  have hfb : Matrix.fromBlocks (C'.d t) 0 0 ((elementaryComplex R i).d t) = W t :=
    (hmaster t).symm
  rw [hfb, hW, Matrix.submatrix_submatrix]
  have he1 : ⇑(g t).symm ∘ ⇑(g t) = id := (g t).symm_comp_self
  have he2 : ⇑(g (t+1)).symm ∘ ⇑(g (t+1)) = id := (g (t+1)).symm_comp_self
  rw [he1, he2, Matrix.submatrix_id_id, Matrix.mul_assoc, hPmatMulInv (t+1), Matrix.mul_one]

/-- If the differential `φ_i = C.d (i-1)` of `C` has a unit matrix coefficient, then `C` splits
off the elementary identity complex `T^{(i)}`: there is `C'` with the ranks of `C` decremented at
`i` and `i - 1` and an isomorphism `C.toComplex ≅ (combine C' (elementaryComplex R i)).toComplex`.
-/
lemma freeComplex_split_unit {R : Type*} [CommRing R] (C : FreeComplex R) (i : ℤ)
    (h : HasInvertibleCoeff C i) :
    ∃ C' : FreeComplex R,
      (∀ j, C'.n j = if j = i then C.n i - 1 else if j = i - 1 then C.n (i - 1) - 1 else C.n j) ∧
      Nonempty (C.toComplex ≅ (combine C' (elementaryComplex R i)).toComplex) := by
  obtain ⟨k, j, hu⟩ := h
  have hi : 1 ≤ C.n (i - 1 + 1) := by have := j.isLt; omega
  have him1 : 1 ≤ C.n (i - 1) := by have := k.isLt; omega
  obtain ⟨hp, hq, P, Q, M, hPdet, hQdet, hblock⟩ := exists_pivot_block_split (C.d (i - 1)) k j hu
  obtain ⟨C', Pmat, hn, hrank, hPmatdet, hconj⟩ :=
    freeComplex_split_data C i hi him1 P Q M hPdet hQdet hblock
  refine ⟨C', hrank, ?_⟩
  have hP : ∀ t, Invertible (Pmat t) := fun t => Matrix.invertibleOfIsUnitDet (Pmat t) (hPmatdet t)
  exact freeComplex_changeOfBasis C (combine C' (elementaryComplex R i)) hn Pmat hP hconj

open FreeComplex in
/-- Let `R` be a ring and `C` a complex of finite free `R`-modules `C_j = R^{n_j}`. If the
differential `φ_i` has an invertible matrix coefficient, then `n_i ≥ 1`, `n_{i-1} ≥ 1`, and there
is a complex of finite free `R`-modules `C'` with the ranks decremented at degrees `i` and `i-1`
(and unchanged elsewhere) together with an isomorphism of complexes
`C ≅ C' ⊕ T^{(i)}`, where `T^{(i)}` is the elementary identity complex of `elementaryComplex`. -/
@[stacks 00MT]
theorem exists_splitOff_elementaryComplex_of_hasInvertibleCoeff {R : Type*} [CommRing R]
    (C : FreeComplex R) (i : ℤ) (h : HasInvertibleCoeff C i) :
    1 ≤ C.n i ∧ 1 ≤ C.n (i - 1) ∧
    ∃ C' : FreeComplex R,
      (∀ j, C'.n j = if j = i then C.n i - 1 else if j = i - 1 then C.n (i - 1) - 1 else C.n j) ∧
      Nonempty (C.toComplex ≅ C'.toComplex ⊞ (elementaryComplex R i).toComplex) := by
  obtain ⟨k, j, hu⟩ := h
  have hni1 : 1 ≤ C.n i := by
    have h0 : (0 : ℕ) < C.n (i - 1 + 1) := by
      have := j.isLt
      omega
    have hidx : i - 1 + 1 = i := by ring
    rw [hidx] at h0
    omega
  have hnim1 : 1 ≤ C.n (i - 1) := by
    have := k.isLt
    omega
  refine ⟨hni1, hnim1, ?_⟩
  obtain ⟨C', hrank, ⟨isoSplit⟩⟩ := freeComplex_split_unit C i ⟨k, j, hu⟩
  obtain ⟨isoBridge⟩ := combine_toComplex_iso_biprod C' (elementaryComplex R i)
  exact ⟨C', hrank, ⟨isoSplit.trans isoBridge⟩⟩

end
