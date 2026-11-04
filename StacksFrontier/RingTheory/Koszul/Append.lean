module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.LinearAlgebra.ExteriorAlgebra.Prod
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory

/-!
# The Koszul complex of a concatenated sequence

Let `R` be a commutative ring. For sequences `f_1, ..., f_r` and `g_1, ..., g_s` of elements of
`R`, the Koszul complex on the concatenation `Fin.append f g` is isomorphic, as a chain complex of
`R`-modules, to the total complex of the tensor product of the Koszul complexes on `f` and on `g`.

The total complex `Tot(A ⊗_R B)` of two chain complexes of `R`-modules has degree-`n` term
`⨁_{p+q=n} A_p ⊗_R B_q` and differential `d(x ⊗ y) = d(x) ⊗ y + (-1)^p x ⊗ d(y)` for `x ∈ A_p`;
it is the monoidal tensor product `HomologicalComplex.tensorObj` on
`ChainComplex (ModuleCat R) ℕ`.

## Main definitions

* `Koszul.totTensor`: the total complex of the tensor product of two chain complexes.
* `Koszul.seqComplexAppendIsoTotTensor`: the isomorphism
  `K_•(R, f, g) ≅ Tot(K_•(R, f) ⊗_R K_•(R, g))`.

## Main results

* `Koszul.seqComplex_append_iso_totTensor`: the Koszul complex on a concatenated sequence is
  isomorphic to the total complex of the tensor product of the two Koszul complexes.
-/

namespace Koszul

variable {R : Type*} [CommRing R]

/-! ## Main definitions

The Koszul differential `d φ n : ⋀^(n+1) M →ₗ[R] ⋀ⁿ M` (the contraction
`CliffordAlgebra.contractLeft φ` restricted to the exterior powers), the Koszul complex
`complex φ` of a functional, the functional `seqDual f` of a sequence
(`e_i ↦ f_i`) and the Koszul complex `seqComplex f` of a sequence are those of
`StacksFrontier.RingTheory.Koszul.Defs`; they are Definition 1 above. -/

/-- The total complex (Definition 2) of the tensor product of two chain complexes
`A_\bullet`, `B_\bullet` of `R`-modules: the monoidal tensor product
`HomologicalComplex.tensorObj` (written `A \otimes B`), whose degree-`n` term is
`\bigoplus_{p+q=n} A_p \otimes_R B_q` and whose differential implements the
homological graded Leibniz rule `d(x \otimes y) = d(x) \otimes y + (-1)^p x \otimes d(y)`. -/
@[sga "4 XVII 1.1.10" "Clause (i), special case",
  sga "4 XVII 4.1.6" "special case",
  sga "7 VII 3.6" "special case",
  sga "7 VII 3.8.8" "special case"]
noncomputable def totTensor (A B : ChainComplex (ModuleCat R) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  A ⊗ B

/-- `totTensor` is, by definition, the monoidal tensor product
`HomologicalComplex.tensorObj` (the total complex of the tensor product). -/
theorem totTensor_def (A B : ChainComplex (ModuleCat R) ℕ) :
    totTensor A B = HomologicalComplex.tensorObj A B := rfl

/-- The index type of the degree-`n` term of a total complex over `ComplexShape.down ℕ`:
the pairs `(p, q)` of naturals with `p + q = n`. -/
abbrev totTensorIndex (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- The `(p, q)`-summand `⋀^p (Fin r → R) ⊗[R] ⋀^q (Fin s → R)` of the degree-`n` term of the
total complex of the tensor product of the Koszul complexes on a sequence of length `r` and a
sequence of length `s`. -/
abbrev totTensorSummand (R : Type*) [CommRing R] (r s n : ℕ) (pq : totTensorIndex n) : Type _ :=
  TensorProduct R (⋀[R]^pq.1.1 (Fin r → R)) (⋀[R]^pq.1.2 (Fin s → R))

/-! ### The isomorphism -/

/-- The functional of a concatenated sequence evaluates on a concatenated vector as the sum
of the functionals of the two pieces:
`seqDual (Fin.append f g) (Fin.append u v) = seqDual f u + seqDual g v`. -/
@[simp]
theorem seqDual_append {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
    (u : Fin r → R) (v : Fin s → R) :
    seqDual (Fin.append f g) (Fin.append u v)
      = seqDual f u + seqDual g v := by
  simp only [seqDual_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- The tensor product of the two exterior powers indexed by `pq` is an additive group. -/
noncomputable instance instAddCommGroupTensorExteriorPower {r s n : ℕ}
    (pq : totTensorIndex n) :
    AddCommGroup (totTensorSummand R r s n pq) :=
  inferInstance

/-- The degree-`n` term of the total complex of the tensor product of the two Koszul
complexes, as the algebraic direct sum `⊕_{p+q=n} ⋀^p (Fin r → R) ⊗_R ⋀^q (Fin s → R)`. -/
noncomputable def totTensorXIsoDirectSum {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ) :
    (totTensor (seqComplex f) (seqComplex g)).X n
      ≅ ModuleCat.of R (DirectSum (totTensorIndex n) (totTensorSummand R r s n)) :=
  let p := ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  let K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    (((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)
  let XY : GradedObject (ℕ × ℕ) (ModuleCat R) := K.toGradedObject
  haveI : XY.HasMap p := (inferInstance : K.HasTotal (ComplexShape.down ℕ))
  (CategoryTheory.GradedObject.isColimitCofanMapObj XY p n).coconePointUniqueUpToIso
      (CategoryTheory.Limits.coproductIsCoproduct (XY.mapObjFun p n))
    ≪≫ ModuleCat.coprodIsoDirectSum (XY.mapObjFun p n)

/-- The degree-`n` term of the Koszul complex on the concatenated sequence is isomorphic
to the degree-`n` term of the total complex of the tensor product of the two Koszul
complexes: `⋀^n (Fin (r+s) → R) ≅ ⊕_{p+q=n} ⋀^p (Fin r → R) ⊗_R ⋀^q (Fin s → R)`. -/
noncomputable def seqComplexAppendXIso {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ) :
    (seqComplex (Fin.append f g)).X n
      ≅ (totTensor (seqComplex f) (seqComplex g)).X n :=
  (LinearEquiv.toModuleIso
      (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) n))
    ≪≫ (totTensorXIsoDirectSum f g n).symm

/-- Per-summand component of `totDiffDirectSum`: on the `⟨(p,q),h⟩` summand (with `p+q=n+1`)
it is the `(d (seqDual f)) ⊗ 1` contribution into block `(p-1,q)` (when `p>0`)
plus the `(-1)^p • 1 ⊗ (d (seqDual g))` contribution into block `(p,q-1)`
(when `q>0`); missing branches are `0`. -/
noncomputable def totDiffDirectSumSummand {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ) :
    (pq : totTensorIndex (n + 1)) →
      (totTensorSummand R r s (n + 1) pq →ₗ[R]
        DirectSum (totTensorIndex n) (totTensorSummand R r s n)) :=
  fun ⟨⟨p, q⟩, h⟩ ↦
    (match p, h with
      | 0, _ => 0
      | p' + 1, h =>
        (DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n) ⟨(p', q), by omega⟩)
          ∘ₗ TensorProduct.map (d (seqDual f) p') LinearMap.id)
    +
    (match q, h with
      | 0, _ => 0
      | q' + 1, h =>
        ((-1 : R) ^ p •
          ((DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n) ⟨(p, q'), by omega⟩)
            ∘ₗ TensorProduct.map LinearMap.id (d (seqDual g) q'))))

/-- The algebraic total differential `d_A ⊗ 1 + (-1)^p · 1 ⊗ d_B` on
`⊕_{p+q=n+1} ⋀^p (Fin r → R) ⊗_R ⋀^q (Fin s → R)`, reindexed on the
`{p+q=n+1} → {p+q=n}` blocks. -/
noncomputable def totDiffDirectSum {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ) :
    DirectSum (totTensorIndex (n + 1)) (totTensorSummand R r s (n + 1))
      →ₗ[R] DirectSum (totTensorIndex n) (totTensorSummand R r s n) :=
  DirectSum.toModule R _ _ (totDiffDirectSumSummand f g n)

/-- The functional `seqDual (append f g)` precomposed with the V-embedding
`(finAppendProdEquiv).symm ∘ jVAppend` is `seqDual f`. -/
theorem seqDual_append_comp_jVAppend {r s : ℕ} (f : Fin r → R) (g : Fin s → R) :
    (seqDual (Fin.append f g)).comp
        ((finAppendProdEquiv r s).symm.toLinearMap.comp (jVAppend r s))
      = seqDual f := by
  ext v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, jVAppend, LinearMap.inl_apply]
  rw [finAppendProdEquiv_symm_apply, seqDual_append]
  simp [seqDual]

/-- The functional `seqDual (append f g)` precomposed with the W-embedding
`(finAppendProdEquiv).symm ∘ jWAppend` is `seqDual g`. -/
theorem seqDual_append_comp_jWAppend {r s : ℕ} (f : Fin r → R) (g : Fin s → R) :
    (seqDual (Fin.append f g)).comp
        ((finAppendProdEquiv r s).symm.toLinearMap.comp (jWAppend r s))
      = seqDual g := by
  ext w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, jWAppend, LinearMap.inr_apply]
  rw [finAppendProdEquiv_symm_apply, seqDual_append]
  simp [seqDual]

/-- In the exterior algebra, the Koszul differential of the concatenated sequence applied to the
preimage of a block generator `a ⊗ b` under the direct-sum decomposition is
`(δ_f a) b + (-1)^p a (δ_g b)`, where `δ_f` and `δ_g` are the contractions by `seqDual f` and
`seqDual g`. -/
theorem d_append_symm_lof_coe {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
    (n p q : ℕ) (h : p + q = n + 1)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    ((d (seqDual (Fin.append f g)) n
        ((exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) (n + 1)).symm
          (DirectSum.lof R (totTensorIndex (n + 1)) (totTensorSummand R r s (n + 1))
            ⟨(p, q), h⟩ (a ⊗ₜ[R] b))) : ExteriorAlgebra R (Fin (r + s) → R)))
      = ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jVAppend r s))
            (CliffordAlgebra.contractLeft (seqDual f) (a : ExteriorAlgebra R (Fin r → R)))
          * ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jWAppend r s))
            (b : ExteriorAlgebra R (Fin s → R))
        + ((-1 : R) ^ p) •
          (ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jVAppend r s))
            (a : ExteriorAlgebra R (Fin r → R))
          * ExteriorAlgebra.map ((finAppendProdEquiv r s).symm.toLinearMap.comp (jWAppend r s))
            (CliffordAlgebra.contractLeft (seqDual g) (b : ExteriorAlgebra R (Fin s → R)))) := by
  set e := finAppendProdEquiv (R := R) r s
  set ιV := (e.symm.toLinearMap.comp (jVAppend r s)) with hιV
  set ιW := (e.symm.toLinearMap.comp (jWAppend r s)) with hιW
  set δ := seqDual (Fin.append f g) with hδ
  rw [d_apply_coe, exteriorPower_append_equiv_directSum_symm_lof_coe r s (n+1) p q h a b]
  have ha : ExteriorAlgebra.map ιV (a : ExteriorAlgebra R (Fin r → R))
      ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ p := map_mem_extPow_aux _ _ _ a.2
  rw [contractLeft_graded_leibniz δ p
    (ExteriorAlgebra.map ιV (a : ExteriorAlgebra R (Fin r → R))) ha]
  congr 1
  · congr 1
    rw [← map_contractLeft_pow ιV δ p (a : ExteriorAlgebra R (Fin r → R)) a.2]
    congr 2
    rw [hδ, hιV, seqDual_append_comp_jVAppend]
  · congr 2
    rw [← map_contractLeft_pow ιW δ q (b : ExteriorAlgebra R (Fin s → R)) b.2]
    congr 2
    rw [hδ, hιW, seqDual_append_comp_jWAppend]

/-- On a block generator `lof ⟨(p,q),h⟩ (a⊗ₜb)` (with
`p+q=n+1`), the natural iso `E(n)` applied to the appended Koszul differential of the
preimage equals the per-summand total differential `totDiffDirectSumSummand`. -/
theorem d_append_directSum_comm_lof_tmul {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
    (n p q : ℕ) (h : p + q = n + 1)
    (a : (⋀[R]^p (Fin r → R))) (b : (⋀[R]^q (Fin s → R))) :
    (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) n)
        (d (seqDual (Fin.append f g)) n
          ((exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) (n + 1)).symm
            (DirectSum.lof R (totTensorIndex (n + 1)) (totTensorSummand R r s (n + 1))
              ⟨(p, q), h⟩ (a ⊗ₜ[R] b))))
      = totDiffDirectSumSummand f g n ⟨(p, q), h⟩ (a ⊗ₜ[R] b) := by
  set e := finAppendProdEquiv (R := R) r s
  set ιV := (e.symm.toLinearMap.comp (jVAppend r s))
  set ιW := (e.symm.toLinearMap.comp (jWAppend r s))
  set δ := seqDual (Fin.append f g)
  set Y := (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) (n + 1)).symm
      (DirectSum.lof R (totTensorIndex (n + 1)) (totTensorSummand R r s (n + 1))
        ⟨(p, q), h⟩ (a ⊗ₜ[R] b)) with hY
  have hEapply : ∀ (z : ⋀[R]^n ((Fin (r + s) → R))),
      (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) n) z
        = extPow_fwd r s n (exteriorPowerCongr n e z) := by
    intro z
    rw [exteriorPower_append_equiv_directSum, LinearEquiv.trans_apply]
    rfl
  rw [hEapply]
  have hZ : ((d δ n Y : ⋀[R]^n (Fin (r + s) → R)) : ExteriorAlgebra R (Fin (r + s) → R))
      = ExteriorAlgebra.map ιV (CliffordAlgebra.contractLeft (seqDual f) (a : ExteriorAlgebra R (Fin
          r → R)))
          * ExteriorAlgebra.map ιW (b : ExteriorAlgebra R (Fin s → R))
        + ((-1 : R) ^ p) •
          (ExteriorAlgebra.map ιV (a : ExteriorAlgebra R (Fin r → R))
            * ExteriorAlgebra.map ιW (CliffordAlgebra.contractLeft (seqDual g)
              (b : ExteriorAlgebra R (Fin s → R)))) := by
    rw [hY]; exact d_append_symm_lof_coe f g n p q h a b
  have hembed : ∀ (p₁ q₁ : ℕ) (hpq : p₁ + q₁ = n) (A : ⋀[R]^p₁ (Fin r → R)) (B : ⋀[R]^q₁ (Fin s →
      R))
      (W : ⋀[R]^n ((Fin r → R) × (Fin s → R))),
      ((W : ExteriorAlgebra R ((Fin r → R) × (Fin s → R)))
        = ExteriorAlgebra.map (jVAppend r s) (A : ExteriorAlgebra R (Fin r → R))
          * ExteriorAlgebra.map (jWAppend r s) (B : ExteriorAlgebra R (Fin s → R))) →
      extPow_fwd r s n W
        = DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n)
          ⟨(p₁, q₁), hpq⟩ (A ⊗ₜ[R] B) := by
    intro p₁ q₁ hpq A B W hW
    have mem : ExteriorAlgebra.map (jVAppend r s) (A : ExteriorAlgebra R (Fin r → R))
        * ExteriorAlgebra.map (jWAppend r s) (B : ExteriorAlgebra R (Fin s → R))
        ∈ (⋀[R]^n ((Fin r → R) × (Fin s → R))) := hW ▸ W.2
    have : W = ⟨ExteriorAlgebra.map (jVAppend r s) (A : ExteriorAlgebra R (Fin r → R))
        * ExteriorAlgebra.map (jWAppend r s) (B : ExteriorAlgebra R (Fin s → R)), mem⟩ :=
      Subtype.ext hW
    rw [this, extPow_fwd_embed r s n p₁ q₁ hpq A B mem]
  have hF₁ : ∀ (p₁ q₁ : ℕ) (hpq : p₁ + q₁ = n) (A : ⋀[R]^(p₁ + 1) (Fin r → R))
      (B : ⋀[R]^q₁ (Fin s → R)) (W : ⋀[R]^n ((Fin r → R) × (Fin s → R))),
      (W : ExteriorAlgebra R ((Fin r → R) × (Fin s → R)))
        = ExteriorAlgebra.map (jVAppend r s)
              (CliffordAlgebra.contractLeft (seqDual f) (A : ExteriorAlgebra R (Fin r → R)))
          * ExteriorAlgebra.map (jWAppend r s) (B : ExteriorAlgebra R (Fin s → R)) →
      extPow_fwd r s n W
        = DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n)
          ⟨(p₁, q₁), hpq⟩ (d (seqDual f) p₁ A ⊗ₜ[R] B) :=
    fun p₁ q₁ hpq A B W hW ↦ hembed p₁ q₁ hpq _ B W (by rw [hW, d_apply_coe])
  have hF₂ : ∀ (p₁ q₁ : ℕ) (hpq : p₁ + q₁ = n) (A : ⋀[R]^p₁ (Fin r → R))
      (B : ⋀[R]^(q₁ + 1) (Fin s → R)) (W : ⋀[R]^n ((Fin r → R) × (Fin s → R))),
      (W : ExteriorAlgebra R ((Fin r → R) × (Fin s → R)))
        = ExteriorAlgebra.map (jVAppend r s) (A : ExteriorAlgebra R (Fin r → R))
          * ExteriorAlgebra.map (jWAppend r s)
              (CliffordAlgebra.contractLeft (seqDual g) (B : ExteriorAlgebra R (Fin s → R))) →
      extPow_fwd r s n W
        = DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n)
          ⟨(p₁, q₁), hpq⟩ (A ⊗ₜ[R] d (seqDual g) q₁ B) :=
    fun p₁ q₁ hpq A B W hW ↦ hembed p₁ q₁ hpq A _ W (by rw [hW, d_apply_coe])
  have hmem : ∀ (p₁ q₁ : ℕ), p₁ + q₁ = n → ∀ (x : ExteriorAlgebra R (Fin r → R))
      (y : ExteriorAlgebra R (Fin s → R)), x ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ p₁ →
      y ∈ (LinearMap.range (ExteriorAlgebra.ι R)) ^ q₁ →
      ExteriorAlgebra.map (jVAppend r s) x * ExteriorAlgebra.map (jWAppend r s) y
        ∈ (⋀[R]^n ((Fin r → R) × (Fin s → R))) := by
    intro p₁ q₁ hpq x y hx hy
    have := Submodule.mul_mem_mul (map_mem_extPow_aux (jVAppend r s) p₁ x hx)
      (map_mem_extPow_aux (jWAppend r s) q₁ y hy)
    rwa [← pow_add, hpq] at this
  rcases p with _ | p' <;> rcases q with _ | q'
  · exact absurd h (by omega)
  · refine (hF₂ 0 q' (by omega) a b _ ?_).trans ?_
    · rw [exteriorPowerCongr_coe, hZ, contractLeft_extPow_zero (seqDual f) a, map_zero, zero_mul,
        zero_add, pow_zero, one_smul, map_e_embed]
    · simp only [totDiffDirectSumSummand, zero_add,
        LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe,
        id_eq, pow_zero, one_smul, DirectSum.lof_eq_of]
  · refine (hF₁ p' 0 (by omega) a b _ ?_).trans ?_
    · rw [exteriorPowerCongr_coe, hZ, contractLeft_extPow_zero (seqDual g) b, map_zero, mul_zero,
        smul_zero, add_zero, map_e_embed]
    · simp only [totDiffDirectSumSummand, add_zero,
        LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  · set W₁ : ⋀[R]^n ((Fin r → R) × (Fin s → R)) :=
      ⟨_, hmem p' (q' + 1) (by omega) _ _ (contraction_mem (seqDual f) p' a.2) b.2⟩
    set W₂ : ⋀[R]^n ((Fin r → R) × (Fin s → R)) :=
      ⟨_, hmem (p' + 1) q' (by omega) _ _ a.2 (contraction_mem (seqDual g) q' b.2)⟩
    have hsplit : exteriorPowerCongr n e (d δ n Y) = W₁ + ((-1 : R) ^ (p' + 1)) • W₂ := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, exteriorPowerCongr_coe, hZ, map_add, map_smul,
        map_e_embed, map_e_embed]
    rw [hsplit, map_add, map_smul, hF₁ p' (q' + 1) (by omega) a b W₁ rfl,
      hF₂ (p' + 1) q' (by omega) a b W₂ rfl]
    simp only [totDiffDirectSumSummand, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

/-- The natural direct-sum decomposition of the exterior powers intertwines the Koszul
differential of the concatenated sequence with the algebraic total differential
`totDiffDirectSum`. -/
theorem d_append_directSum_comm {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ) :
    (totDiffDirectSum f g n).comp
        (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) (n + 1)).toLinearMap
      = (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) n).toLinearMap.comp
          (d (seqDual (Fin.append f g)) n) := by
  have hmain : totDiffDirectSum f g n
      = (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s) n).toLinearMap.comp
          ((d (seqDual (Fin.append f g)) n).comp
            (exteriorPower_append_equiv_directSum (R := R) (r := r) (s := s)
              (n + 1)).symm.toLinearMap) := by
    rw [totDiffDirectSum]
    apply DirectSum.linearMap_ext
    intro pq
    obtain ⟨⟨p, q⟩, h⟩ := pq
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
        simp only [map_add, hx, hy]
    | tmul a b =>
        rw [LinearMap.comp_apply, DirectSum.toModule_lof, LinearMap.comp_apply,
          LinearMap.comp_apply, LinearEquiv.coe_coe]
        exact (d_append_directSum_comm_lof_tmul f g n p q h a b).symm
  rw [hmain]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- The unit `(-1 : ℤˣ) ^ p` acts on an `R`-module as the scalar `(-1 : R) ^ p`. -/
private theorem neg_one_units_pow_smul {M : Type*} [AddCommGroup M] [Module R M]
    (p : ℕ) (x : M) :
    ((-1 : ℤˣ) ^ p) • x = ((-1 : R) ^ p) • x := by
  rw [Units.smul_def, show ((-1:R)^p) = ((((-1:ℤ)^p : ℤ)) : R) by push_cast; ring,
    Int.cast_smul_eq_zsmul R]
  congr 1

/-- The categorical cofan inclusion `ιMapObj` followed by the
`coconePointUniqueUpToIso ≪≫ coprodIsoDirectSum` direct-sum iso is the algebraic block
inclusion `lof`. -/
private theorem ιMapObj_isoDirectSum {I J : Type*} (X : GradedObject I (ModuleCat R))
    (p : I → J) [X.HasMap p] (m : J) [DecidableEq ↥(p ⁻¹' {m})]
    [Limits.HasCoproduct (X.mapObjFun p m)] (i : I) (hi : p i = m) :
    X.ιMapObj p i m hi
      ≫ ((GradedObject.isColimitCofanMapObj X p m).coconePointUniqueUpToIso
            (Limits.coproductIsCoproduct (X.mapObjFun p m))).hom
      ≫ (ModuleCat.coprodIsoDirectSum (X.mapObjFun p m)).hom
      = ModuleCat.ofHom (DirectSum.lof R _ (fun k => (X.mapObjFun p m k : Type _)) ⟨i, hi⟩) := by
  rw [← Category.assoc,
    show X.ιMapObj p i m hi = (X.cofanMapObj p m).ι.app ⟨⟨i, hi⟩⟩ from rfl,
    (GradedObject.isColimitCofanMapObj X p m).comp_coconePointUniqueUpToIso_hom
      (Limits.coproductIsCoproduct (X.mapObjFun p m)) ⟨⟨i, hi⟩⟩,
    show (Limits.Cofan.mk (∐ X.mapObjFun p m) (Limits.Sigma.ι (X.mapObjFun p m))).ι.app ⟨⟨i, hi⟩⟩
        = Limits.Sigma.ι (X.mapObjFun p m) ⟨i, hi⟩ from rfl,
    ModuleCat.ι_coprodIsoDirectSum_hom]

/-- The cofan inclusion of the `(p, q)` block into the degree-`n` term of the total complex,
followed by `totTensorXIsoDirectSum`, is the algebraic block inclusion `lof`. -/
theorem totTensor_ιMapObj_hom {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ)
    (pq : totTensorIndex n) :
    (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj
        (seqComplex g)).toGradedObject).ιMapObj
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
        pq.1 n pq.2
      ≫ (totTensorXIsoDirectSum f g n).hom
      = ModuleCat.ofHom (DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n) pq) := by
  obtain ⟨pq, h⟩ := pq
  rw [totTensorXIsoDirectSum, Iso.trans_hom]
  exact ιMapObj_isoDirectSum _ _ n pq h

/-- The inclusion `ιTotal` of the `(p, q)` block into the degree-`n` term of the total complex,
followed by `totTensorXIsoDirectSum`, is the algebraic block inclusion `lof`. -/
private theorem totTensor_ιTotal_hom {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (p q n : ℕ)
    (h : p + q = n) :
    (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj
        (seqComplex g)).ιTotal (ComplexShape.down ℕ) p q n h)
      ≫ (totTensorXIsoDirectSum f g n).hom
      = ModuleCat.ofHom (DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n)
          ⟨(p, q), h⟩) :=
  totTensor_ιMapObj_hom f g n ⟨(p, q), h⟩

/-- The `d₁` (=`d_A ⊗ 1`) part of the total differential, through the direct-sum iso,
lands in block `(p', q)` via the whiskered Koszul differential. -/
theorem totTensor_d₁ {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (p' q n : ℕ)
    (h : (p' + 1) + q = n + 1) :
    (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).d₁
        (ComplexShape.down ℕ) (p'+1) q n) ≫ (totTensorXIsoDirectSum f g n).hom
      = ModuleCat.ofHom ((DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n)
            ⟨(p', q), by omega⟩) ∘ₗ TensorProduct.map (d (seqDual f) p') LinearMap.id) := by
  have hrel : (ComplexShape.down ℕ).Rel (p'+1) p' := by rw [ComplexShape.down_Rel]
  have h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p', q) = n := by
    change p' + q = n; omega
  rw [HomologicalComplex₂.d₁_eq _ (ComplexShape.down ℕ) hrel q n h']
  rw [show (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p'+1, q) = 1 by
    simp [ComplexShape.ε₁]]
  rw [one_smul, Category.assoc, totTensor_ιTotal_hom f g p' q n h']
  rw [show ((((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat
      R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).d
        (p'+1) p').f q)
      = ModuleCat.ofHom (TensorProduct.map (d (seqDual f) p') LinearMap.id) from by
    change (seqComplex f).d (p'+1) p' ▷ (seqComplex g).X q = _
    rw [seqComplex_d]; rfl]
  rw [← ModuleCat.ofHom_comp]

/-- The `d₁` part of the total differential out of a block with `p = 0` vanishes. -/
theorem totTensor_d₁_eq_zero {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (q n : ℕ) :
    (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).d₁
        (ComplexShape.down ℕ) 0 q n) = 0 := by
  apply HomologicalComplex₂.d₁_eq_zero
  rw [ComplexShape.down_Rel]; omega

/-- The `d₂` (=`(-1)^p · 1 ⊗ d_B`) part of the total differential, through the direct-sum
iso, lands in block `(p, q')` with the Koszul sign `(-1)^p`. -/
theorem totTensor_d₂ {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (p q' n : ℕ)
    (h : p + (q' + 1) = n + 1) :
    (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).d₂
        (ComplexShape.down ℕ) p (q'+1) n) ≫ (totTensorXIsoDirectSum f g n).hom
      = (-1 : R)^p • ModuleCat.ofHom ((DirectSum.lof R (totTensorIndex n) (totTensorSummand R r s n)
            ⟨(p, q'), by omega⟩) ∘ₗ TensorProduct.map LinearMap.id (d (seqDual g) q')) := by
  have hrel : (ComplexShape.down ℕ).Rel (q'+1) q' := by rw [ComplexShape.down_Rel]
  have h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p, q') = n := by
    change p + q' = n; omega
  rw [HomologicalComplex₂.d₂_eq _ (ComplexShape.down ℕ) p hrel n h']
  rw [show (ComplexShape.down ℕ).ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q'+1)
        = ((-1:ℤˣ)^p) by
    simp [ComplexShape.ε₂, ComplexShape.ε_down_ℕ]]
  rw [show (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat
      R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).X p).d
            (q'+1) q'
      = ModuleCat.ofHom (TensorProduct.map LinearMap.id (d (seqDual g) q')) from by
    change (seqComplex f).X p ◁ (seqComplex g).d (q'+1) q' = _
    rw [seqComplex_d]
    rfl]
  rw [Linear.units_smul_comp, Category.assoc, totTensor_ιTotal_hom f g p q' n h']
  rw [← ModuleCat.ofHom_comp]
  exact neg_one_units_pow_smul p _

/-- The `d₂` part of the total differential out of a block with `q = 0` vanishes. -/
theorem totTensor_d₂_eq_zero {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (p n : ℕ) :
    (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).d₂
        (ComplexShape.down ℕ) p 0 n) = 0 := by
  apply HomologicalComplex₂.d₂_eq_zero
  rw [ComplexShape.down_Rel]; omega

/-- `totDiffDirectSum` realizes the categorical total differential: through
the categorical↔DirectSum identification `totTensorXIsoDirectSum`, the total-complex
differential `(totTensor (seqComplex f) (seqComplex g)).d (n+1) n` is `totDiffDirectSum f g n`. -/
theorem totTensor_d_eq_totDiffDirectSum {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ) :
    (totTensorXIsoDirectSum f g (n + 1)).inv
        ≫ (totTensor (seqComplex f) (seqComplex g)).d (n + 1) n
        ≫ (totTensorXIsoDirectSum f g n).hom
      = ModuleCat.ofHom (totDiffDirectSum f g n) := by
  rw [Iso.inv_comp_eq]
  apply GradedObject.mapObj_ext
  intro i hij
  obtain ⟨p, q⟩ := i
  rw [← Category.assoc]
  rw [show (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat
      R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj
        (seqComplex g)).toGradedObject).ιMapObj
          (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (p, q)
              (n+1) hij
      ≫ (totTensor (seqComplex f) (seqComplex g)).d (n+1) n
      = (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat
          R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).d₁
        (ComplexShape.down ℕ) p q n)
        + (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat
            R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).d₂
        (ComplexShape.down ℕ) p q n) from by
    change (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat
        R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g))).ιTotal
          (ComplexShape.down ℕ) p q (n+1) hij
        ≫ (((((CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat
            R)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (seqComplex f)).obj (seqComplex g)).total
          (ComplexShape.down ℕ)).d (n+1) n = _
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.ι_D₂]]
  rw [Preadditive.add_comp]
  rw [← Category.assoc, totTensor_ιMapObj_hom f g (n+1) ⟨(p, q), hij⟩]
  rcases p with _ | p' <;> rcases q with _ | q'
  · simp at hij
  · rw [totTensor_d₁_eq_zero f g (q'+1) n, Limits.zero_comp, zero_add,
      totTensor_d₂ f g 0 q' n hij]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro t
    simp only [totDiffDirectSum, ModuleCat.hom_smul, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.smul_apply, LinearMap.comp_apply]
    rw [DirectSum.toModule_lof]
    simp only [totDiffDirectSumSummand, zero_add,
      LinearMap.comp_apply, pow_zero, one_smul]
  · rw [totTensor_d₂_eq_zero f g (p'+1) n, Limits.zero_comp, add_zero,
      totTensor_d₁ f g p' 0 n hij]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro t
    simp only [totDiffDirectSum, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [DirectSum.toModule_lof]
    simp only [totDiffDirectSumSummand, add_zero,
      LinearMap.comp_apply]
  · rw [totTensor_d₁ f g p' (q'+1) n hij, totTensor_d₂ f g (p'+1) q' n hij]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro t
    simp only [totDiffDirectSum, ModuleCat.hom_add, ModuleCat.hom_smul, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    erw [DirectSum.toModule_lof]
    simp only [totDiffDirectSumSummand, LinearMap.add_apply,
      LinearMap.comp_apply, LinearMap.smul_apply]
    rfl

/-- The degreewise isomorphisms `seqComplexAppendXIso` commute with the differentials: the
Koszul differential of the concatenated sequence corresponds to the total-complex
differential. -/
theorem seqComplex_append_comm {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (seqComplexAppendXIso f g i).hom
        ≫ (totTensor (seqComplex f) (seqComplex g)).d i j
      = (seqComplex (Fin.append f g)).d i j
        ≫ (seqComplexAppendXIso f g j).hom := by
  obtain rfl : i = j + 1 := by
    have : j + 1 = i := hij; omega
  have key : (totTensorXIsoDirectSum f g (j + 1)).inv
        ≫ (totTensor (seqComplex f) (seqComplex g)).d (j + 1) j
      = ModuleCat.ofHom (totDiffDirectSum f g j)
        ≫ (totTensorXIsoDirectSum f g j).inv := by
    rw [← totTensor_d_eq_totDiffDirectSum f g j, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [seqComplex_d, seqComplexAppendXIso, seqComplexAppendXIso]
  simp only [Iso.trans_hom, Iso.symm_hom, LinearEquiv.toModuleIso_hom]
  rw [Category.assoc, key]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
  congr 1
  exact d_append_directSum_comm f g j

/- ASSEMBLY.  Package the degreewise isomorphisms `seqComplexAppendXIso` (M1) and
the commuting-square hypothesis `seqComplex_append_comm` (M2) via
`HomologicalComplex.Hom.isoOfComponents`, then wrap in `⟨·⟩`. -/
/-- **Stacks Tag 0664.** The canonical isomorphism of chain complexes of `R`-modules
  `K_\bullet(R, f, g) \cong Tot(K_\bullet(R, f) \otimes_R K_\bullet(R, g))`
between the Koszul complex on the concatenation of `f_1, ..., f_r` and `g_1, ..., g_s`
(a sequence of length `r + s`) and the total complex of the tensor product of the Koszul
complexes on `f` and on `g`.  An isomorphism in `ChainComplex (ModuleCat R) \mathbb{N}`
(a `HomologicalComplex` isomorphism) is by definition compatible with the differentials,
so this is the desired differential-compatible canonical isomorphism. -/
@[ega "III 1.1.1" "(f)"]
noncomputable def seqComplexAppendIsoTotTensor {r s : ℕ} (f : Fin r → R) (g : Fin s → R) :
    seqComplex (Fin.append f g) ≅ totTensor (seqComplex f) (seqComplex g) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ seqComplexAppendXIso f g n)
    (fun i j hij ↦ seqComplex_append_comm f g i j hij)

/-- In degree `n`, the isomorphism `seqComplexAppendIsoTotTensor` is the degreewise isomorphism
`seqComplexAppendXIso`. -/
@[simp]
theorem seqComplexAppendIsoTotTensor_hom_f {r s : ℕ} (f : Fin r → R) (g : Fin s → R) (n : ℕ) :
    (seqComplexAppendIsoTotTensor f g).hom.f n = (seqComplexAppendXIso f g n).hom := rfl

/-- **Stacks Tag 0664.** The Koszul complex on the concatenation of two sequences
`f_1, ..., f_r` and `g_1, ..., g_s` (length `r + s`) is isomorphic, as a chain
complex of `R`-modules, to the total complex of the tensor product of the Koszul
complexes on `f` and on `g`; see `seqComplexAppendIsoTotTensor` for the isomorphism
itself. -/
@[stacks 0664, ega "III 1.1.1" "(f)"]
theorem seqComplex_append_iso_totTensor {r s : ℕ} (f : Fin r → R) (g : Fin s → R) :
    Nonempty
      (seqComplex (Fin.append f g) ≅ totTensor (seqComplex f) (seqComplex g)) :=
  ⟨seqComplexAppendIsoTotTensor f g⟩

end Koszul
