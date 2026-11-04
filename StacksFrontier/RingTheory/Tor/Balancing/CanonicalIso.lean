module

public import StacksFrontier.RingTheory.Tor.Balancing.RowComparison

/-!
# The canonical isomorphism `H_i(R(A)_•) ≃ H_i(U(A)_•)`

The column comparison `cmpU`, obtained from `cmpR` for the transpose double complex,
the functoriality of the total homology and of both comparisons, and the main statements
`statement1` and `statement2` (Stacks, Tag 00M1).

This is part of the split of `StacksFrontier.RingTheory.Tor.Balancing`.
-/

@[expose] public section

open LinearMap Submodule

namespace Stacks.Tor.DoubleComplex

universe u
variable {R : Type u} [CommRing R]

/-! ## `cmpU` via the transpose double complex.

The `U`-side comparison is obtained from `cmpR` for the *transpose* double
complex `Aᵀ` (`Aᵀ_{i,j} = A_{j,i}`, with `d` and `δ` swapped), together with the
signed reversal isomorphism of total complexes `k ↦ i - k`. -/

/-- The transpose double complex: swap the two indices and the two differentials. -/
def DoubleCx.transpose (A : DoubleCx R) : DoubleCx R where
  A i j := A.A j i
  d i j := A.δ j i
  δ i j := A.d j i
  dd i j := A.δδ j i
  δδ i j := A.dd j i
  comm i j := (A.comm j i).symm

/-- The `(i, j)` entry of the transpose is the `(j, i)` entry of `A`. -/
@[simp] theorem DoubleCx.transpose_A (A : DoubleCx R) (i j : ℕ) :
    A.transpose.A i j = A.A j i := rfl

/-- The horizontal cokernels of the transpose are the vertical cokernels of `A`. -/
theorem DoubleCx.transpose_RObj (A : DoubleCx R) (i : ℕ) :
    A.transpose.RObj i = A.UObj i := rfl

/-- The induced differential on `R(Aᵀ)_•` is the induced differential on
`U(A)_•`. -/
theorem DoubleCx.transpose_RDiff (A : DoubleCx R) (i : ℕ) :
    A.transpose.RDiff i = A.UDiff i := rfl

/-- The `R`-edge homology of the transpose is the `U`-edge homology of `A`. -/
theorem DoubleCx.transpose_RHom (A : DoubleCx R) (i : ℕ) :
    A.transpose.RHom i = A.UHom i := rfl

/-- If the columns of `A` are exact in positive degree then the rows of the
transpose are. -/
theorem DoubleCx.transpose_RowResolution (A : DoubleCx R) (h : A.ColResolution) :
    A.transpose.RowResolution := fun i j => h j i

/-- If the rows of `A` are exact in positive degree then the columns of the
transpose are. -/
theorem DoubleCx.transpose_ColResolution (A : DoubleCx R) (h : A.RowResolution) :
    A.transpose.ColResolution := fun i j => h j i

/-- The signed index-reversal `k ↦ n - k` as a linear map between the total
chain groups of `A` and its transpose `Aᵀ`. -/
def revMap (A : DoubleCx R) (n : ℕ) :
    TotChain A n →ₗ[R] TotChain A.transpose n :=
  LinearMap.pi (fun k : Fin (n + 1) =>
    ((-1 : R) ^ ((k : ℕ) * (n + 1))) •
      ((transp A (n - (k : ℕ)) (n - (k : ℕ)) (n - (n - (k : ℕ))) (k : ℕ)
          rfl (by have := k.isLt; omega)).toLinearMap.comp
        (LinearMap.proj (⟨n - (k : ℕ), by omega⟩ : Fin (n + 1)))))

/-- The `k`-th component of the signed reversal: `(-1)^(k(n+1))` times the
component of `x` at the mirror index `n - k`. -/
theorem revMap_apply (A : DoubleCx R) (n : ℕ) (x : TotChain A n) (k : Fin (n + 1)) :
    revMap A n x k =
      ((-1 : R) ^ ((k : ℕ) * (n + 1))) •
        (transp A (n - (k : ℕ)) (n - (k : ℕ)) (n - (n - (k : ℕ))) (k : ℕ)
          rfl (by have := k.isLt; omega) (x ⟨n - (k : ℕ), by omega⟩)) := rfl

/-- Transport in the transpose complex is transport in `A` with the two index
equalities exchanged. -/
theorem transpose_transp (A : DoubleCx R) (a a' b b' : ℕ) (ha : a = a') (hb : b = b')
    (y : A.transpose.A a b) :
    transp A.transpose a a' b b' ha hb y
      = transp A b b' a a' hb ha y := by
  subst ha; subst hb; rfl

/-- The horizontal differential of the transpose is the vertical differential of
`A` at the exchanged indices. -/
theorem transpose_d (A : DoubleCx R) (i j : ℕ) :
    A.transpose.d i j = A.δ j i := rfl

/-- The vertical differential of the transpose is the horizontal differential of
`A` at the exchanged indices. -/
theorem transpose_δ (A : DoubleCx R) (i j : ℕ) :
    A.transpose.δ i j = A.d j i := rfl

/-- Two transports of `x` at value-equal antidiagonal indices agree. -/
theorem transp_apply_eq_of_eq (A : DoubleCx R) (NN p M2 v w : ℕ)
    (x : ∀ k : Fin NN, A.A k (NN - 1 - k))
    (hv : v < NN) (hw : w < NN) (hvp : v = p) (hwp : w = p)
    (h2v : NN - 1 - v = M2) (h2w : NN - 1 - w = M2) :
    transp A v p (NN - 1 - v) M2 hvp h2v (x ⟨v, hv⟩)
      = transp A w p (NN - 1 - w) M2 hwp h2w (x ⟨w, hw⟩) := by
  subst hvp; subst hwp
  rfl

/-- A power of `-1` depends only on the parity of its exponent. -/
theorem neg_one_pow_eq_of_mod_two_eq {R : Type u} [CommRing R] (a b : ℕ) (h : a % 2 = b % 2) :
    (-1 : R) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-- Variant of `transp_apply_eq_of_eq` with the antidiagonal length `N + 1`. -/
theorem transp_apply_eq_of_eq' (A : DoubleCx R) (N p M2 v w : ℕ)
    (x : ∀ k : Fin (N + 1), A.A k (N - k))
    (hv : v < N + 1) (hw : w < N + 1) (hvp : v = p) (hwp : w = p)
    (h2v : N - v = M2) (h2w : N - w = M2) :
    transp A v p (N - v) M2 hvp h2v (x ⟨v, hv⟩)
      = transp A w p (N - w) M2 hwp h2w (x ⟨w, hw⟩) := by
  subst hvp; subst hwp
  rfl

/-- Transporting `δ` of a transported element agrees with `δ` of any value-equal transport. -/
theorem transp_δ_eq_δ_transp (A : DoubleCx R) (p c M2 s f gg : ℕ)
    (hc : c = M2) (hf : f = p) (hgg : gg = M2 + 1) (hs : s = c + 1)
    (y : A.A p s) (z : A.A f gg)
    (hyz : transp A f p gg (M2 + 1) hf hgg z = transp A p p s (M2 + 1) rfl (by omega) y) :
    transp A p p c M2 rfl hc (A.δ p c (transp A p p s (c + 1) rfl (by omega) y))
      = A.δ p M2 (transp A f p gg (M2 + 1) hf hgg z) := by
  subst hc; subst hf; subst hgg; subst hs
  rw [hyz]
  simp only [transp_rfl]

/-- Transporting `d` of an element agrees with `d` of any value-equal transport. -/
theorem transp_d_eq_d_transp (A : DoubleCx R) (p c M2 f gg : ℕ)
    (hc : c = M2) (hf : f = p + 1) (hgg : gg = M2)
    (y : A.A (p + 1) c) (z : A.A f gg)
    (hyz : transp A f (p + 1) gg M2 hf hgg z = transp A (p + 1) (p + 1) c M2 rfl hc y) :
    transp A p p c M2 rfl hc (A.d p c y)
      = A.d p M2 (transp A f (p + 1) gg M2 hf hgg z) := by
  subst hc; subst hf; subst hgg
  rw [hyz]
  simp only [transp_rfl]

-- Without this option, `rw` reports a motive that is not type correct in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- The signed reversal `revMap` is a chain map from the total complex of `A` to
that of its transpose. -/
theorem revMap_comm (A : DoubleCx R) (n : ℕ) :
    (revMap A n).comp (Dtot A n) = (Dtot A.transpose n).comp (revMap A (n + 1)) := by
  refine LinearMap.ext fun x => ?_
  refine funext fun m => ?_
  obtain ⟨M, hMlt⟩ := m
  show revMap A n (Dtot A n x) ⟨M, hMlt⟩ = Dtot A.transpose n (revMap A (n + 1) x) ⟨M, hMlt⟩
  rw [revMap_apply, Dtot_apply, Dtot_apply, revMap_apply, revMap_apply]
  simp only [transpose_d, transpose_δ, transpose_transp, map_smul, map_add,
    d_transp, transp_trans, Fin.val_succ, Fin.val_castSucc]
  have hM : M ≤ n := by omega
  simp only [Fin.succ_mk, Fin.castSucc_mk, smul_add, smul_smul]
  obtain ⟨d, rfl⟩ : ∃ d, n = M + d := ⟨n - M, by omega⟩
  refine Eq.trans (add_comm _ _) ?_
  congr 1
  · congr 1
    · have hd : M + d - M = d := by omega
      rw [hd, ← pow_add]
      apply neg_one_pow_eq_of_mod_two_eq
      rw [show (M + 1) * (M + d + 1 + 1) = M * (M + d + 1) + d + 2 * (M + 1) by ring]
      omega
    · exact transp_δ_eq_δ_transp A (M + d - M) (M + d - (M + d - M)) M (M + d + 1 - (M + d - M))
        (M + d + 1 - (M + 1)) (M + d + 1 - (M + d + 1 - (M + 1)))
        (by omega) (by omega) (by omega) (by omega)
        (x ⟨M + d - M, by omega⟩) (x ⟨M + d + 1 - (M + 1), by omega⟩)
        (transp_apply_eq_of_eq A (M + d + 2) (M + d - M) (M + 1) (M + d + 1 - (M + 1)) (M + d - M)
          x (by omega) (by omega) (by omega) rfl (by omega) (by omega))
  · congr 1
    · rw [← pow_add,
        show M + M * (M + d + 1 + 1) = M * (M + d + 1) + 2 * M by ring,
        pow_add, pow_mul]
      simp
    · exact transp_d_eq_d_transp A (M + d - M) (M + d + 1 - (M + d - M + 1)) M
        (M + d + 1 - M) (M + d + 1 - (M + d + 1 - M))
        (by omega) (by omega) (by omega)
        (x ⟨M + d - M + 1, by omega⟩) (x ⟨M + d + 1 - M, by omega⟩)
        (transp_apply_eq_of_eq A (M + d + 2) (M + d - M + 1) M (M + d + 1 - M) (M + d - M + 1)
          x (by omega) (by omega) (by omega) rfl (by omega) (by omega))

/-- The signed reversal as a chain map `Tot A → Tot Aᵀ`. -/
def revChainHom (A : DoubleCx R) :
    ChainHom (fun n => ModuleCat.of R (TotChain A n))
      (fun n => ModuleCat.of R (TotChain A.transpose n))
      (fun n => Dtot A n) (fun n => Dtot A.transpose n) where
  f := fun n => revMap A n
  comm := fun n => revMap_comm A n

/-- Transposition of double complexes is involutive. -/
@[simp] theorem transpose_transpose (A : DoubleCx R) : A.transpose.transpose = A := rfl

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- The reversal is involutive: applying it for `A` then for `Aᵀ` is the identity. -/
theorem revMap_revMap (A : DoubleCx R) (n : ℕ) (x : TotChain A n) :
    revMap A.transpose n (revMap A n x) = x := by
  funext k
  have hk : (k : ℕ) ≤ n := by have := k.isLt; omega
  rw [revMap_apply, revMap_apply, transpose_transp, map_smul, transp_trans, smul_smul,
    ← pow_add]
  rw [transp_apply_eq_of_eq' A n (k : ℕ) (n - (k : ℕ)) (n - (n - (k : ℕ))) (k : ℕ)
        x (by have := k.isLt; omega) (by have := k.isLt; omega) (by omega) rfl (by omega) (by
            omega),
    transp_rfl]
  rw [show (-1 : R) ^ ((k : ℕ) * (n + 1)
      + (↑(⟨n - (k : ℕ), by omega⟩ : Fin (n + 1)) : ℕ) * (n + 1)) = 1 from ?_]
  · rw [one_smul]
  · rw [show (↑(⟨n - (k : ℕ), by omega⟩ : Fin (n + 1)) : ℕ) = n - (k : ℕ) from rfl]
    apply Even.neg_one_pow
    rw [show (k : ℕ) * (n + 1) + (n - (k : ℕ)) * (n + 1) = n * (n + 1) by
      rw [← add_mul]; congr 1; omega]
    exact Nat.even_mul_succ_self n

/-- Forward reversal on `Hthird`. -/
noncomputable def revHthirdfwd (A : DoubleCx R) (i : ℕ) :
    Hthird A i →ₗ[R] Hthird A.transpose i :=
  homologyMap (revChainHom A) i

/-- Round trip: reversing twice is the identity on `Hthird`. -/
theorem revHthird_roundtrip (A : DoubleCx R) (i : ℕ) :
    (revHthirdfwd A.transpose i).comp (revHthirdfwd A i) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  cases i with
  | zero =>
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact congrArg _ (revMap_revMap A 0 z)
  | succ j =>
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact congrArg _ (Subtype.ext (revMap_revMap A (j + 1) z))

/-- The reversal `Hthird A ≃ Hthird Aᵀ`, from the involutive chain map `revMap`. -/
noncomputable def revHthird (A : DoubleCx R) (i : ℕ) :
    Hthird A i ≃ₗ[R] Hthird A.transpose i :=
  LinearEquiv.ofLinearMap (revHthirdfwd A i) (revHthirdfwd A.transpose i)
    (revHthird_roundtrip A.transpose i) (revHthird_roundtrip A i)

/-- The edge comparison isomorphism `cmpU : H_i(A) ≃ H_i(U(A)_•)`, sending the class of
`(a_{0,i}, …, a_{i,0})` to the class of `a_{i,0}` in `U(A)_i = Coker(δ : A_{i,1} → A_{i,0})`, for a
double complex whose columns are exact in positive degree. It is the composite of the signed
reversal `revHthird : Hthird A ≃ Hthird Aᵀ` with `cmpR` for the transpose `Aᵀ`. -/
noncomputable def cmpU (A : DoubleCx R) (hcol : A.ColResolution) (i : ℕ) :
    Hthird A i ≃ₗ[R] A.UHom i :=
  (revHthird A i).trans
    (cmpR A.transpose (A.transpose_RowResolution hcol) i)

/-- The canonical isomorphism `H_i(R(A)_•) ≃ H_i(U(A)_•)`, defined as `cmpU ∘ cmpR⁻¹`. -/
noncomputable def canonIso (A : DoubleCx R) (hrow : A.RowResolution) (hcol : A.ColResolution)
    (i : ℕ) : A.RHom i ≃ₗ[R] A.UHom i :=
  (cmpR A hrow i).symm.trans (cmpU A hcol i)

/-! ### Functoriality of the third object

A morphism `Ψ : A → B` of double complexes induces `Hthird A i → Hthird B i` by
applying `Ψ.Φ` componentwise to zig-zag tuples; this is a chain map for the total
differentials, since `Ψ` commutes with `d` and `δ`, hence descends to homology. -/

/-- `Ψ.Φ` commutes with the index transports `transp`. -/
lemma Φ_transp {A B : DoubleCx R} (Ψ : DCxHom A B) (a a' b b' : ℕ)
    (ha : a = a') (hb : b = b') (x : A.A a b) :
    Ψ.Φ a' b' (transp A a a' b b' ha hb x) = transp B a a' b b' ha hb (Ψ.Φ a b x) := by
  subst ha; subst hb; rfl

/-- The chain map on total complexes induced by a morphism `Ψ : A → B` of double
complexes: apply `Ψ.Φ` componentwise to zig-zag tuples. -/
def totChainHom {A B : DoubleCx R} (Ψ : DCxHom A B) :
    ChainHom (fun n => ModuleCat.of R (TotChain A n))
      (fun n => ModuleCat.of R (TotChain B n))
      (fun n => Dtot A n) (fun n => Dtot B n) where
  f := fun n => LinearMap.pi (fun k : Fin (n + 1) =>
        (Ψ.Φ (k : ℕ) (n - (k : ℕ))).comp (LinearMap.proj k))
  comm n := by
    ext a m k
    simp only [Dtot, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply,
      LinearMap.add_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_add, map_smul]
    have hd : ∀ y, Ψ.Φ (k : ℕ) (n - (k : ℕ)) (A.d (k : ℕ) (n - (k : ℕ)) y)
        = B.d (k : ℕ) (n - (k : ℕ)) (Ψ.Φ ((k : ℕ) + 1) (n - (k : ℕ)) y) := by
      intro y
      have := congrArg (fun (g : _ →ₗ[R] _) => g y) (Ψ.commd (k : ℕ) (n - (k : ℕ)))
      simpa only [LinearMap.comp_apply] using this
    have hδ : ∀ y, Ψ.Φ (k : ℕ) (n - (k : ℕ)) (A.δ (k : ℕ) (n - (k : ℕ)) y)
        = B.δ (k : ℕ) (n - (k : ℕ)) (Ψ.Φ (k : ℕ) (n - (k : ℕ) + 1) y) := by
      intro y
      have := congrArg (fun (g : _ →ₗ[R] _) => g y) (Ψ.commδ (k : ℕ) (n - (k : ℕ)))
      simpa only [LinearMap.comp_apply] using this
    rw [hd, hδ, Φ_transp Ψ, Φ_transp Ψ]

/-- The map `H_i(Tot A) → H_i(Tot B)` induced by a morphism `Ψ : A → B` of double
complexes. -/
noncomputable def HthirdMap {A B : DoubleCx R} (Ψ : DCxHom A B) (i : ℕ) :
    Hthird A i →ₗ[R] Hthird B i :=
  homologyMap (totChainHom Ψ) i

-- Without this option, `rw` does not find its pattern in this proof.
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the `R`-edge comparison: for `Ψ : A → B`, the square relating `cmpR A`,
`cmpR B`, `HthirdMap Ψ` and `Ψ.RHomMap` commutes. -/
theorem cmpR_natural {A B : DoubleCx R}
    (hrowA : A.RowResolution) (hrowB : B.RowResolution)
    (Ψ : DCxHom A B) (i : ℕ) :
    (Ψ.RHomMap i).comp (cmpR A hrowA i : Hthird A i →ₗ[R] A.RHom i) =
      ((cmpR B hrowB i : Hthird B i →ₗ[R] B.RHom i)).comp (HthirdMap Ψ i) := by
  show (Ψ.RHomMap i).comp (cmpRfwd A i) =
      (cmpRfwd B i).comp (HthirdMap Ψ i)
  cases i with
  | zero =>
      refine Submodule.linearMap_qext _ ?_
      refine LinearMap.ext fun b => ?_
      change (Ψ.RHomMap 0) (cmpRfwd A 0 (Submodule.Quotient.mk b)) =
          (cmpRfwd B 0) (HthirdMap Ψ 0 (Submodule.Quotient.mk b))
      rfl
  | succ j =>
      refine Submodule.linearMap_qext _ ?_
      refine LinearMap.ext fun bc => ?_
      change (Ψ.RHomMap (j + 1)) (cmpRfwd A (j + 1) (Submodule.Quotient.mk bc)) =
          (cmpRfwd B (j + 1)) (HthirdMap Ψ (j + 1) (Submodule.Quotient.mk bc))
      rfl

/-- The transpose of a morphism of double complexes. -/
def DCxHom.transpose {A B : DoubleCx R} (Ψ : DCxHom A B) :
    DCxHom A.transpose B.transpose where
  Φ i j := Ψ.Φ j i
  commd i j := Ψ.commδ j i
  commδ i j := Ψ.commd j i

/-- Chain-level naturality of the signed reversal: `revMap` commutes with the
componentwise map `totChainHom` induced by `Ψ`. -/
theorem revMap_natural {A B : DoubleCx R} (Ψ : DCxHom A B) (n : ℕ) :
    ((totChainHom Ψ.transpose).f n).comp (revMap A n)
      = (revMap B n).comp ((totChainHom Ψ).f n) := by
  refine LinearMap.ext fun x => ?_
  refine funext fun k => ?_
  show (totChainHom Ψ.transpose).f n (revMap A n x) k
      = revMap B n ((totChainHom Ψ).f n x) k
  show Ψ.transpose.Φ (k : ℕ) (n - (k : ℕ)) (revMap A n x k)
      = revMap B n ((totChainHom Ψ).f n x) k
  rw [revMap_apply, revMap_apply]
  show Ψ.Φ (n - (k : ℕ)) (k : ℕ)
      (((-1 : R) ^ ((k : ℕ) * (n + 1))) •
        transp A (n - (k : ℕ)) (n - (k : ℕ)) (n - (n - (k : ℕ))) (k : ℕ)
          rfl _ (x ⟨n - (k : ℕ), _⟩))
    = ((-1 : R) ^ ((k : ℕ) * (n + 1))) •
        transp B (n - (k : ℕ)) (n - (k : ℕ)) (n - (n - (k : ℕ))) (k : ℕ)
          rfl _ (((totChainHom Ψ).f n x) ⟨n - (k : ℕ), _⟩)
  rw [map_smul, Φ_transp Ψ]
  rfl

/-- Naturality of `revHthirdfwd` against the induced maps on `Hthird`. -/
theorem revHthird_natural {A B : DoubleCx R} (Ψ : DCxHom A B) (i : ℕ) :
    (HthirdMap Ψ.transpose i).comp (revHthirdfwd A i)
      = (revHthirdfwd B i).comp (HthirdMap Ψ i) := by
  apply LinearMap.ext
  intro z
  simp only [HthirdMap, revHthirdfwd]
  cases i with
  | zero =>
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact congrArg _ (LinearMap.congr_fun (revMap_natural Ψ 0) z)
  | succ j =>
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact congrArg _ (Subtype.ext (LinearMap.congr_fun (revMap_natural Ψ (j + 1)) z))

/-- Naturality of the `U`-edge comparison: for `Ψ : A → B`, the square relating `cmpU A`,
`cmpU B`, `HthirdMap Ψ` and `Ψ.UHomMap` commutes. -/
theorem cmpU_natural {A B : DoubleCx R}
    (hcolA : A.ColResolution) (hcolB : B.ColResolution)
    (Ψ : DCxHom A B) (i : ℕ) :
    (Ψ.UHomMap i).comp (cmpU A hcolA i : Hthird A i →ₗ[R] A.UHom i) =
      ((cmpU B hcolB i : Hthird B i →ₗ[R] B.UHom i)).comp (HthirdMap Ψ i) := by
  apply LinearMap.ext
  intro x
  show (Ψ.UHomMap i) (cmpU A hcolA i x)
      = (cmpU B hcolB i) (HthirdMap Ψ i x)
  show (Ψ.UHomMap i)
        (cmpR A.transpose (A.transpose_RowResolution hcolA) i
          (revHthirdfwd A i x))
      = cmpR B.transpose (B.transpose_RowResolution hcolB) i
          (revHthirdfwd B i (HthirdMap Ψ i x))
  have hUR : Ψ.UHomMap i = Ψ.transpose.RHomMap i := rfl
  rw [hUR]
  have hR := DFunLike.congr_fun
    (cmpR_natural (A.transpose_RowResolution hcolA)
      (B.transpose_RowResolution hcolB) Ψ.transpose i)
    (revHthirdfwd A i x)
  simp only [LinearMap.comp_apply] at hR
  erw [hR]
  have hrev := DFunLike.congr_fun (revHthird_natural Ψ i) x
  simp only [LinearMap.comp_apply] at hrev
  rw [hrev]
  rfl

/-! ## Main statements -/

/-- For a double complex `A` whose rows are resolutions of the horizontal cokernels and whose
columns are resolutions of the vertical cokernels, there is an isomorphism of `R`-modules
`H_i(R(A)_•) ≅ H_i(U(A)_•)` for every `i ≥ 0`. -/
@[stacks 00M1 "(1)"]
theorem statement1 (A : DoubleCx R) (hrow : A.RowResolution) (hcol : A.ColResolution)
    (i : ℕ) : Nonempty (A.RHom i ≃ₗ[R] A.UHom i) :=
  ⟨canonIso A hrow hcol i⟩

/-- The isomorphisms `H_i(R(A)_•) ≅ H_i(U(A)_•)` can be chosen naturally in `A`: there is an
assignment, to every double complex `A` satisfying the resolution hypotheses and every `i`, of an
isomorphism `e A : H_i(R(A)_•) ≅ H_i(U(A)_•)`, such that `H_i(U(Ψ)) ∘ e A = e B ∘ H_i(R(Ψ))` for
every morphism `Ψ : A → B` of such double complexes. -/
@[stacks 00M1 "(2)"]
theorem statement2 :
    ∃ e : ∀ (A : DoubleCx R), A.RowResolution → A.ColResolution → ∀ i,
        (A.RHom i ≃ₗ[R] A.UHom i),
      ∀ (A B : DoubleCx R) (hrowA : A.RowResolution) (hcolA : A.ColResolution)
        (hrowB : B.RowResolution) (hcolB : B.ColResolution)
        (Ψ : DCxHom A B) (i : ℕ),
        (Ψ.UHomMap i).comp (e A hrowA hcolA i : A.RHom i →ₗ[R] A.UHom i) =
          ((e B hrowB hcolB i : B.RHom i →ₗ[R] B.UHom i)).comp (Ψ.RHomMap i) := by
  refine ⟨fun A hrow hcol i => canonIso A hrow hcol i, ?_⟩
  intro A B hrowA hcolA hrowB hcolB Ψ i
  ext x
  have hR := DFunLike.congr_fun (cmpR_natural hrowA hrowB Ψ i)
    ((cmpR A hrowA i).symm x)
  have hU := DFunLike.congr_fun (cmpU_natural hcolA hcolB Ψ i)
    ((cmpR A hrowA i).symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at hR hU ⊢
  show (Ψ.UHomMap i) ((cmpR A hrowA i).symm.trans (cmpU A hcolA i) x) =
      (cmpR B hrowB i).symm.trans (cmpU B hcolB i) ((Ψ.RHomMap i) x)
  simp only [LinearEquiv.trans_apply]
  rw [hU]
  congr 1
  rw [hR, LinearEquiv.symm_apply_apply]

end Stacks.Tor.DoubleComplex
