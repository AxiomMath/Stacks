module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.Defs
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.FiniteSupportMatrix
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsFinite

/-!
# Upper triangular elements of `GL_n(A)` with bounded diagonal

Let `K` be a global function field over the finite field `k`. We show that the upper triangular
elements `t ∈ GL_n(A)` whose diagonal entries `λ_i` satisfy `B⁻¹ ≤ N(div λ_i) ≤ B` lie in
finitely many double cosets `GL_n(O) · s · GL_n(K)`.

By the finiteness of the divisor classes of bounded norm, `div λ_i = D_i - div κ_i` with `D_i` in
a finite set and `κ_i ∈ Kˣ`; a diagonal element of `GL_n(O)` on the left and one of `GL_n(K)` on
the right replace `λ_i` by the idele `idelOfDiv D_i`. The entries above the diagonal are then
reduced, band after band, by unipotent elements of `GL_n(O)` on the left and of `GL_n(K)` on the
right: the entry `(p, q)` divided by the diagonal entry `δ_p` is reduced modulo
`K + A(div δ_p - div δ_q)`, whose quotient of `A` is finite, to a fixed transversal.

## Main definitions

* `Stacks.Adeles.GeneralLinear.adeleTransversal` — a transversal of `A / (K + A(E))`.
* `Stacks.Adeles.GeneralLinear.normalForms` — the finite set of normalized upper triangular
  elements.

## Main results

* `Stacks.Adeles.GeneralLinear.exists_finset_upperTriangular`.
-/

@[expose] public noncomputable section

open Matrix

universe u

namespace Stacks.Adeles.GeneralLinear

open Stacks.Adeles.GlobalFunctionField hiding mapO mapK scalarGL coe_scalarGL

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] {n : ℕ}

variable (K) in
/-- A transversal of `A / (K + A(E))`: the chosen representatives of its classes. -/
public def adeleTransversal (E : Place K →₀ ℤ) : Set (AdeleRing K) :=
  Set.range (Quotient.out : AdeleRing K ⧸ (principal k K ⊔ adeleLattice K E) → AdeleRing K)

/-- The transversal of `A / (K + A(E))` is finite. -/
public theorem finite_adeleTransversal (E : Place K →₀ ℤ) : (adeleTransversal k K E).Finite := by
  have := finite_quotient_principal_sup_adeleLattice k (K := K) E
  exact Set.finite_range _

/-- For ideles `α, β` and an adele `x` there are `o ∈ O` and `c ∈ K` such that
`α⁻¹ (x + o β + α c)` lies in the transversal of `A / (K + A(div α - div β))`. -/
public theorem exists_reduce (α β : (AdeleRing K)ˣ) (x : AdeleRing K) :
    ∃ o ∈ integralAdeles K, ∃ c ∈ principalAdeles K,
      ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * (x + o * β + α * c) ∈
        adeleTransversal k K (idelDiv k K α - idelDiv k K β) := by
  set E := idelDiv k K α - idelDiv k K β with hE
  set αi := ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)
  set βi := ((β⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)
  set r := Quotient.out (QuotientAddGroup.mk (αi * x) :
    AdeleRing K ⧸ (principal k K ⊔ adeleLattice K E))
  have hr : -r + αi * x ∈ principal k K ⊔ adeleLattice K E := by
    rw [← QuotientAddGroup.eq]
    exact Quotient.out_eq _
  obtain ⟨κa, hκ, y, hy, hsum⟩ := AddSubgroup.mem_sup.1 hr
  have hκ' : κa ∈ principalAdeles K := by rw [← range_diag k]; exact hκ
  have hy' : βi * α * y ∈ integralAdeles K := by
    rw [← mem_adeleLattice_zero_iff]
    have h := (idele_mul_mem_adeleLattice_iff k (β⁻¹ * α) (E := E)).2 hy
    have hE0 : E - idelDiv k K (β⁻¹ * α) = 0 := by
      rw [hE, idelDiv_mul, idelDiv_inv]; abel
    rw [hE0] at h
    simpa [βi] using h
  refine ⟨-(βi * α * y), (integralAdeles K).neg_mem hy', -κa, (principalAdeles K).neg_mem hκ',
    (QuotientAddGroup.mk (αi * x) : AdeleRing K ⧸ _), ?_⟩
  change r = _
  have hα : αi * α = 1 := Units.inv_mul α
  have hβ : βi * β = 1 := Units.inv_mul β
  linear_combination hsum + κa * hα + y * βi * β * hα + y * hβ

/-- `t` is upper triangular with diagonal `δ`, and its entries `(p, q)` with `p < q < p + d`,
divided by `δ p`, lie in the transversals of `A / (K + A(div δ_p - div δ_q))`. -/
public def IsReducedUpTo (δ : Fin n → (AdeleRing K)ˣ) (d : ℕ) (t : GL (Fin n) (AdeleRing K)) :
    Prop :=
  IsUpperTriangularWith t δ ∧ ∀ p q : Fin n, p < q → (q : ℕ) < p + d →
    ((δ p)⁻¹ : (AdeleRing K)ˣ) * (t : Matrix (Fin n) (Fin n) (AdeleRing K)) p q ∈
      adeleTransversal k K (idelDiv k K (δ p) - idelDiv k K (δ q))

/-- One reduction step: the band `q = p + d` is reduced by a unipotent element of `GL_n(O)` on the
left and one of `GL_n(K)` on the right, without changing the entries closer to the diagonal. -/
public theorem exists_isReducedUpTo_succ {δ : Fin n → (AdeleRing K)ˣ} {d : ℕ} (hd : 1 ≤ d)
    {t : GL (Fin n) (AdeleRing K)} (ht : IsReducedUpTo k δ d t) :
    ∃ (υ : GL (Fin n) (integralAdeles K)) (ν : GL (Fin n) (principalAdeles K)),
      IsReducedUpTo k δ (d + 1) (mapO K n υ * t * mapK K n ν) := by
  classical
  choose o ho c hc hred using fun p q : Fin n =>
    exists_reduce k (δ p) (δ q) ((t : Matrix (Fin n) (Fin n) (AdeleRing K)) p q)
  let NO : Matrix (Fin n) (Fin n) (integralAdeles K) := fun p q =>
    if (q : ℕ) = p + d then ⟨o p q, ho p q⟩ else 0
  let NK : Matrix (Fin n) (Fin n) (principalAdeles K) := fun p q =>
    if (q : ℕ) = p + d then ⟨c p q, hc p q⟩ else 0
  have hNO : IsUpperBand d NO := fun p q hpq => by
    simp [NO, show ¬((q : ℕ) = p + d) by omega]
  have hNK : IsUpperBand d NK := fun p q hpq => by
    simp [NK, show ¬((q : ℕ) = p + d) by omega]
  have hNOv : ∀ p q, NO.map (integralAdeles K).subtype p q =
      if (q : ℕ) = p + d then o p q else 0 := by
    intro p q
    change (integralAdeles K).subtype (NO p q) = _
    simp only [NO]
    split_ifs <;> rfl
  have hNKv : ∀ p q, NK.map (principalAdeles K).subtype p q =
      if (q : ℕ) = p + d then c p q else 0 := by
    intro p q
    change (principalAdeles K).subtype (NK p q) = _
    simp only [NK]
    split_ifs <;> rfl
  refine ⟨unipotentOfBand NO (hNO.mono hd), unipotentOfBand NK (hNK.mono hd), ?_⟩
  set T := (t : Matrix (Fin n) (Fin n) (AdeleRing K))
  have hlow : ∀ i j, j < i → T i j = 0 := ht.1.1
  have hdiag : ∀ i, T i i = δ i := ht.1.2
  have hold : ∀ p q : Fin n, p < q → (q : ℕ) < p + d →
      ((δ p)⁻¹ : (AdeleRing K)ˣ) * T p q ∈
        adeleTransversal k K (idelDiv k K (δ p) - idelDiv k K (δ q)) := ht.2
  have hred' : ∀ p q : Fin n, ((δ p)⁻¹ : (AdeleRing K)ˣ) * (T p q + o p q * δ q + δ p * c p q) ∈
      adeleTransversal k K (idelDiv k K (δ p) - idelDiv k K (δ q)) := hred
  have ht0 : IsUpperBand 0 T := isUpperBand_zero_iff.2 hlow
  have hmat : ((mapO K n (unipotentOfBand NO (hNO.mono hd)) * t *
      mapK K n (unipotentOfBand NK (hNK.mono hd)) : GL (Fin n) (AdeleRing K)) :
        Matrix (Fin n) (Fin n) (AdeleRing K)) =
      (1 + NO.map (integralAdeles K).subtype) * T * (1 + NK.map (principalAdeles K).subtype) := by
    rw [Units.val_mul, Units.val_mul, coe_map_unipotentOfBand, coe_map_unipotentOfBand]
  have hentry : ∀ p q : Fin n, (q : ℕ) < p + d + 1 →
      ((mapO K n (unipotentOfBand NO (hNO.mono hd)) * t *
        mapK K n (unipotentOfBand NK (hNK.mono hd)) : GL (Fin n) (AdeleRing K)) :
          Matrix (Fin n) (Fin n) (AdeleRing K)) p q =
        T p q + (if (q : ℕ) = p + d then o p q else 0) * T q q +
          T p p * (if (q : ℕ) = p + d then c p q else 0) := by
    intro p q hpq
    rw [hmat, one_add_mul_mul_one_add_apply hd ht0 (hNO.map _) (hNK.map _) hpq, hNOv, hNKv]
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun p q hpq hq => ?_⟩
  · have hij' := Fin.lt_def.1 hij
    have hne : ¬((j : ℕ) = i + d) := by omega
    rw [hentry i j (by omega)]
    simp [hne, hlow i j hij]
  · have hne : ¬((i : ℕ) = i + d) := by omega
    rw [hentry i i (by omega)]
    simp [hdiag i, show d ≠ 0 by omega]
  · have hpq' := Fin.lt_def.1 hpq
    rw [hentry p q hq]
    rcases Nat.lt_or_ge (q : ℕ) (p + d) with h | h
    · have hne : ¬((q : ℕ) = p + d) := by omega
      simpa [hne] using hold p q hpq h
    · have heq : (q : ℕ) = p + d := by omega
      simp only [heq, ↓reduceIte]
      rw [hdiag q, hdiag p]
      exact hred' p q

/-- Iterating the reduction step: every upper triangular `t` with diagonal `δ` becomes, after
multiplication by `GL_n(O)` on the left and `GL_n(K)` on the right, reduced up to any width. -/
public theorem exists_isReducedUpTo (δ : Fin n → (AdeleRing K)ˣ) {t : GL (Fin n) (AdeleRing K)}
    (ht : IsUpperTriangularWith t δ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (υ : GL (Fin n) (integralAdeles K)) (ν : GL (Fin n) (principalAdeles K)),
      IsReducedUpTo k δ d (mapO K n υ * t * mapK K n ν) := by
  induction d, hd using Nat.le_induction with
  | base =>
    refine ⟨1, 1, by simpa using ht, fun p q hpq hq => ?_⟩
    have := Fin.lt_def.1 hpq
    omega
  | succ d hd ih =>
    obtain ⟨υ, ν, h⟩ := ih
    obtain ⟨υ', ν', h'⟩ := exists_isReducedUpTo_succ k hd h
    exact ⟨υ' * υ, ν * ν', by simpa [mul_assoc] using h'⟩

variable (K) in
/-- The upper triangular matrix with diagonal entries `idelOfDiv (D p)` and entries
`idelOfDiv (D p) * r p q` above the diagonal. -/
public def normalForm (D : Fin n → Place K →₀ ℤ) (r : Fin n → Fin n → AdeleRing K) :
    Matrix (Fin n) (Fin n) (AdeleRing K) := fun p q =>
  if p = q then (idelOfDiv k K (D p) : AdeleRing K)
  else if p < q then (idelOfDiv k K (D p) : AdeleRing K) * r p q else 0

variable (K) in
/-- The entries allowed above the diagonal of a normal form: `0` and the transversals of
`A / (K + A(D - D'))` for `D, D' ∈ F`. -/
public def entrySet (F : Finset (Place K →₀ ℤ)) : Set (AdeleRing K) :=
  insert 0 (⋃ D₁ ∈ F, ⋃ D₂ ∈ F, adeleTransversal k K (D₁ - D₂))

/-- The set of allowed entries is finite. -/
public theorem finite_entrySet (F : Finset (Place K →₀ ℤ)) : (entrySet k K F).Finite := by
  refine Set.Finite.insert (0 : AdeleRing K) ?_
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun D₁ _ =>
    Set.Finite.biUnion (Finset.finite_toSet _) fun D₂ _ => finite_adeleTransversal k _

variable (K n) in
open Classical in
/-- The normal forms: the elements of `GL_n(A)` whose matrix is `normalForm D r` with all `D p`
in `F` and all `r p q` in `entrySet F`. -/
public def normalForms (F : Finset (Place K →₀ ℤ)) : Finset (GL (Fin n) (AdeleRing K)) :=
  ((Finset.univ : Finset ((Fin n → F) × (Fin n → Fin n → (finite_entrySet k F).toFinset))).image
    fun pr => normalForm k K (fun p => (pr.1 p : Place K →₀ ℤ))
      fun p q => (pr.2 p q : AdeleRing K)).preimage
    Units.val fun _ _ _ _ h => Units.ext h

/-- The image in `A` of the unit `κ ∈ Kˣ` of `principalAdeles K` is `diag κ`. -/
public theorem coe_map_diagP_mk0 {κ : K} (hκ : κ ≠ 0) :
    (((Units.map (diagP k K).toMonoidHom (Units.mk0 κ hκ) : (principalAdeles K)ˣ) :
      principalAdeles K) : AdeleRing K) = diag k K κ := rfl

/-- The divisor of `λ diag(κ) / idelOfDiv D` vanishes when `div λ = D - div κ`. -/
public theorem idelDiv_mul_diagUnit_mul_inv {lam : (AdeleRing K)ˣ} {D : Place K →₀ ℤ} {κ : K}
    (hκ : κ ≠ 0) (hD : idelDiv k K lam = D - principalDivisor k K κ) :
    idelDiv k K (lam * diagUnit k hκ * (idelOfDiv k K D)⁻¹) = 0 := by
  rw [idelDiv_mul, idelDiv_mul, idelDiv_inv, idelDiv_diagUnit, hD, idelDiv_idelOfDiv]
  abel

/-- If `o` is an integral unit with `o = λ diag(κ) δ⁻¹`, then `o⁻¹ λ diag(κ) = δ`. -/
public theorem integralUnit_inv_mul_mul_diag_eq {lam δ : (AdeleRing K)ˣ} {κ : K} (hκ : κ ≠ 0)
    {u : (integralAdeles K)ˣ}
    (hu : ((u : integralAdeles K) : AdeleRing K) = ((lam * diagUnit k hκ * δ⁻¹ :
      (AdeleRing K)ˣ) : AdeleRing K)) :
    ((((u⁻¹ : (integralAdeles K)ˣ) : integralAdeles K) : AdeleRing K) * lam) * diag k K κ =
      δ := by
  have h1 : ((((u⁻¹ : (integralAdeles K)ˣ) : integralAdeles K)) : AdeleRing K) *
      (((u : integralAdeles K)) : AdeleRing K) = 1 := by
    exact_mod_cast congrArg Subtype.val (Units.inv_mul u)
  rw [hu, Units.val_mul, Units.val_mul, coe_diagUnit] at h1
  have h2 : ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * (δ : AdeleRing K) = 1 := Units.inv_mul _
  linear_combination (δ : AdeleRing K) * h1 -
    ((((u⁻¹ : (integralAdeles K)ˣ) : integralAdeles K) : AdeleRing K) * (lam : AdeleRing K) *
      diag k K κ * h2)

/-- **Normalizing the diagonal**: if `div λ_i = D_i - div κ_i`, a diagonal element of `GL_n(O)`
on the left and one of `GL_n(K)` on the right turn an upper triangular `t` with diagonal `λ` into
an upper triangular element with diagonal `idelOfDiv D_i`. -/
public theorem exists_isUpperTriangularWith_idelOfDiv {t : GL (Fin n) (AdeleRing K)}
    {lam : Fin n → (AdeleRing K)ˣ} (ht : IsUpperTriangularWith t lam) (D : Fin n → Place K →₀ ℤ)
    {κ : Fin n → K} (hκ : ∀ i, κ i ≠ 0)
    (hD : ∀ i, idelDiv k K (lam i) = D i - principalDivisor k K (κ i)) :
    ∃ (X : GL (Fin n) (integralAdeles K)) (Y : GL (Fin n) (principalAdeles K)),
      IsUpperTriangularWith (mapO K n X * t * mapK K n Y) fun i => idelOfDiv k K (D i) := by
  choose u hu using fun i =>
    exists_integralUnit_of_idelDiv_eq_zero k (idelDiv_mul_diagUnit_mul_inv k (hκ i) (hD i))
  let κ' : Fin n → (principalAdeles K)ˣ := fun i =>
    Units.map (diagP k K).toMonoidHom (Units.mk0 (κ i) (hκ i))
  refine ⟨diagonalGL fun i => (u i)⁻¹, diagonalGL κ', ?_⟩
  have hmat : ∀ p q, ((mapO K n (diagonalGL fun i => (u i)⁻¹) * t * mapK K n (diagonalGL κ') :
      GL (Fin n) (AdeleRing K)) : Matrix (Fin n) (Fin n) (AdeleRing K)) p q =
      ((((u p)⁻¹ : (integralAdeles K)ˣ) : integralAdeles K) : AdeleRing K) *
        (t : Matrix (Fin n) (Fin n) (AdeleRing K)) p q * diag k K (κ q) := by
    intro p q
    rw [Units.val_mul, Units.val_mul, coe_map_diagonalGL, coe_map_diagonalGL,
      mul_diagonal, diagonal_mul]
    exact congrArg (_ * _ * ·) (coe_map_diagP_mk0 k (hκ q))
  refine ⟨fun i j hij => by rw [hmat, ht.1 i j hij, mul_zero, zero_mul], fun i => ?_⟩
  rw [hmat, ht.2 i]
  exact integralUnit_inv_mul_mul_diag_eq k (hκ i) (hu i)

open Classical in
/-- An element reduced up to width `n + 1` with diagonal `idelOfDiv D_i`, `D_i ∈ F`, is a normal
form. -/
public theorem mem_normalForms {F : Finset (Place K →₀ ℤ)} {D : Fin n → Place K →₀ ℤ}
    (hDF : ∀ i, D i ∈ F) {t : GL (Fin n) (AdeleRing K)}
    (hred : IsReducedUpTo k (fun i => idelOfDiv k K (D i)) (n + 1) t) :
    t ∈ normalForms k K n F := by
  have hmem : ∀ p q : Fin n, p < q →
      ((idelOfDiv k K (D p))⁻¹ : (AdeleRing K)ˣ) * (t : Matrix (Fin n) (Fin n) (AdeleRing K)) p q ∈
        (finite_entrySet k F).toFinset := by
    intro p q hpq
    rw [Set.Finite.mem_toFinset]
    refine Set.mem_insert_of_mem _ (Set.mem_iUnion₂.2 ⟨D p, hDF p,
      Set.mem_iUnion₂.2 ⟨D q, hDF q, ?_⟩⟩)
    have h := hred.2 p q hpq (by omega)
    rwa [idelDiv_idelOfDiv, idelDiv_idelOfDiv] at h
  have h0 : (0 : AdeleRing K) ∈ (finite_entrySet k F).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_insert _ _
  let r : Fin n → Fin n → (finite_entrySet k F).toFinset := fun p q =>
    if h : p < q then ⟨_, hmem p q h⟩ else ⟨0, h0⟩
  unfold normalForms
  refine Finset.mem_preimage.2
    (Finset.mem_image.2 ⟨(fun p => ⟨D p, hDF p⟩, r), Finset.mem_univ _, ?_⟩)
  refine Matrix.ext fun p q => ?_
  simp only [normalForm]
  split_ifs with h1 h2
  · subst h1
    exact (hred.1.2 p).symm
  · simp only [r, h2, ↓reduceDIte]
    exact Units.mul_inv_cancel_left _ _
  · exact (hred.1.1 p q (lt_of_le_of_ne (not_lt.1 h2) fun h => h1 h.symm)).symm

/-- **Finiteness for bounded diagonals**: for every `B` there is a finite set `S ⊆ GL_n(A)` such
that every upper triangular `t` whose diagonal entries `λ_i` satisfy `B⁻¹ ≤ N(div λ_i) ≤ B` lies
in `GL_n(O) · s · GL_n(K)` for some `s ∈ S`. -/
public theorem exists_finset_upperTriangular (B : ℚ) :
    ∃ S : Finset (GL (Fin n) (AdeleRing K)), ∀ (t : GL (Fin n) (AdeleRing K))
      (lam : Fin n → (AdeleRing K)ˣ), IsUpperTriangularWith t lam →
      (∀ i, B⁻¹ ≤ divNorm K (idelDiv k K (lam i)) ∧ divNorm K (idelDiv k K (lam i)) ≤ B) →
      ∃ s ∈ S, ∃ (υ : GL (Fin n) (integralAdeles K)) (ν : GL (Fin n) (principalAdeles K)),
        t = mapO K n υ * s * mapK K n ν := by
  obtain ⟨F, hF⟩ := exists_finset_divisor_classes k (K := K) B
  refine ⟨normalForms k K n F, fun t lam ht hB => ?_⟩
  choose D hDF κ hκ hD using fun i => hF _ (hB i).1 (hB i).2
  obtain ⟨X, Y, h₁⟩ := exists_isUpperTriangularWith_idelOfDiv k ht D hκ hD
  obtain ⟨υ, ν, hred⟩ := exists_isReducedUpTo k _ h₁ (n + 1) (by omega)
  refine ⟨_, mem_normalForms k hDF hred, X⁻¹ * υ⁻¹, ν⁻¹ * Y⁻¹, ?_⟩
  simp only [map_mul, map_inv]
  group

end Stacks.Adeles.GeneralLinear

end
