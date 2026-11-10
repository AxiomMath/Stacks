module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.WhittakerModel

/-!
# The function `x ↦ ∑_{ξ ∈ Kˣ} W(x diag(ξ, 1))` attached to Whittaker coefficients

The converse direction of Stacks Tag 03VU builds an eigenform `f` out of its prospective
Whittaker coefficients `c`. With the Whittaker function `W = whittakerModel ψ ω c` of
`ConverseTheorem/WhittakerModel.lean`, the candidate is the Fourier–Whittaker sum
`f(x) = ∑_{ξ ∈ Kˣ} W(x diag(ξ, 1))` (for an eigenform this is
`IsUnramifiedCuspForm.whittaker_expansion`). This file proves the properties of `f` which hold for
every family of coefficients:

* the sum has finite support (`c(D) = 0` unless `ψ(A(D)) = 1`, and the `ξ` with
  `ψ(ξ⁻¹ A(D₀)) = 1` form the finite group `charKernel ψ D₀`);
* `f` is left `GL₂(O)`-invariant and `f(a x) = ω(a) f(x)` for scalar ideles `a`;
* `f` is right invariant under `diag(η, 1)` and `n(κ)` for `η ∈ Kˣ`, `κ ∈ K`, i.e. under the
  mirabolic subgroup `P(K)`;
* `f(x n(z)) = ∑_ξ ψ(ξ⁻¹ z) W(x diag(ξ, 1))`, and consequently the constant term of `f` along
  `n(z)` vanishes, in the form of part (3) of Tag 03VS: the sum over a transversal of
  `A / (K + U)` is `0` (each character `ψ(ξ⁻¹ ·)` which occurs is trivial on `U` by Dedekind's
  independence of characters, and nontrivial on the finite group `A / (K + U)`).

* if the coefficients satisfy the Hecke recursion `t_v c(D) = q_v c(D - v) + u_v c(D + v)`
  wherever `ψ(A(D)) = 1` and `ω(ϖ_v⁻¹) = u_v`, then `T_v f = t_v f` and `U_v f = u_v f`: the
  computation of `IsEigenform.whittakerDiv_recursion` run backwards, plus the vanishing of a Gauss
  sum over `κ_v` at the divisors where `ψ(A(D)) ≠ 1 = ψ(A(D - v))`;
* `f ≠ 0` as soon as some `c(D₀) ≠ 0`, by Dedekind's independence of characters.

Hence `f` is an eigenform with eigenvalues `(t, u)` once it is right `GL₂(K)`-invariant
(`isEigenform_whittakerSum`). That invariance, equivalently the invariance under
`w = (0, 1; -1, 0)`, is the content of the converse theorem and is not proved here.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.whittakerSum ψ ω c` — the function `f`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.finite_support_whittakerModel_mul_diagK`
* `Stacks.Adeles.GlobalFunctionField.whittakerSum_mapO_mul`,
  `Stacks.Adeles.GlobalFunctionField.whittakerSum_scalarGL_mul`,
  `Stacks.Adeles.GlobalFunctionField.whittakerSum_mul_diagK`,
  `Stacks.Adeles.GlobalFunctionField.whittakerSum_mul_upperRightHom_diag`
* `Stacks.Adeles.GlobalFunctionField.whittakerSum_mul_upperRightHom` — the Fourier expansion
  along `n(z)`.
* `Stacks.Adeles.GlobalFunctionField.sum_whittakerSum_mul_upperRightHom_eq_zero` — the vanishing
  constant term.
* `Stacks.Adeles.GlobalFunctionField.heckeOperator_whittakerModel`,
  `Stacks.Adeles.GlobalFunctionField.isHeckeEigenvalueAt_whittakerSum`,
  `Stacks.Adeles.GlobalFunctionField.isCentralEigenvalueAt_whittakerSum` — the eigen-equations.
* `Stacks.Adeles.GlobalFunctionField.exists_whittakerSum_ne_zero` — nonvanishing.
* `Stacks.Adeles.GlobalFunctionField.isEigenform_whittakerSum` — `f` is an eigenform once it is
  right `GL₂(K)`-invariant.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, §11.
* A. Weil, *Dirichlet series and automorphic forms*, LNM 189.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section Characters

variable {G : Type*} [AddCommGroup G] {Λ : Type*} [Field Λ]

/-- **Dedekind's independence of characters, translation form.** If a finite combination
`∑ᵢ aᵢ χᵢ` of distinct characters is invariant under translation by `y`, every character
occurring with a nonzero coefficient is trivial at `y`. -/
public theorem apply_eq_one_of_sum_comp_add {ι : Type*} {S : Finset ι} {χ : ι → AddChar G Λ}
    (hχ : Function.Injective χ) {a : ι → Λ} {y : G}
    (h : ∀ z, ∑ i ∈ S, a i * χ i (z + y) = ∑ i ∈ S, a i * χ i z) {i : ι} (hi : i ∈ S)
    (hai : a i ≠ 0) : χ i y = 1 := by
  classical
  have hinj : Function.Injective fun j => (χ j).toMonoidHom := fun j j' hjj' =>
    hχ (AddChar.toMonoidHomEquiv.injective hjj')
  have hli := (linearIndependent_monoidHom (Multiplicative G) Λ).comp _ hinj
  have hsum : ∑ j ∈ S, (a j * (χ j y - 1)) •
      (fun z : Multiplicative G => (χ j).toMonoidHom z) = 0 := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      AddChar.toMonoidHom_apply]
    have hz := h (Multiplicative.toAdd z)
    simp only [AddChar.map_add_eq_mul] at hz
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hz
    rw [← hz]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := (linearIndependent_iff'.1 hli) S (fun j => a j * (χ j y - 1)) hsum i hi
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hai)

/-- The sum of a nontrivial character trivial on `H` over a transversal of `G ⧸ H` vanishes. -/
public theorem sum_transversal_eq_zero {H : AddSubgroup G} {s : Finset G}
    (hs : ∀ a : G, ∃! z ∈ s, a - z ∈ H) {θ : AddChar G Λ} (hθ : ∀ a ∈ H, θ a = 1)
    (hne : θ ≠ 1) : ∑ z ∈ s, θ z = 0 := by
  classical
  have hsurj : ∀ g : G ⧸ H, ∃ z ∈ s, ((z : G) : G ⧸ H) = g := by
    intro g
    induction g using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨z, ⟨hz, haz⟩, -⟩ := hs a
      exact ⟨z, hz, QuotientAddGroup.eq.2 (by simpa [sub_eq_add_neg, add_comm] using haz)⟩
  have hinj : Set.InjOn (fun z : G => ((z : G) : G ⧸ H)) s := by
    intro z hz z' hz' hzz'
    have hmem : z - z' ∈ H := by
      have := QuotientAddGroup.eq.1 hzz'
      rw [← H.neg_mem_iff] at this
      simpa [sub_eq_add_neg, add_comm] using this
    obtain ⟨w, -, huniq⟩ := hs z
    exact (huniq z ⟨hz, by simp⟩).trans (huniq z' ⟨hz', hmem⟩).symm
  have : Finite (G ⧸ H) := by
    refine Finite.of_surjective (fun z : s => ((z : G) : G ⧸ H)) fun g => ?_
    obtain ⟨z, hz, rfl⟩ := hsurj g
    exact ⟨⟨z, hz⟩, rfl⟩
  let := Fintype.ofFinite (G ⧸ H)
  have himage : s.image (fun z : G => ((z : G) : G ⧸ H)) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun g => ?_
    obtain ⟨z, hz, rfl⟩ := hsurj g
    exact Finset.mem_image_of_mem _ hz
  have hlift : liftChar H θ hθ ≠ 1 := by
    intro h1
    apply hne
    ext a
    have := congrArg (fun χ : AddChar (G ⧸ H) Λ => χ (a : G ⧸ H)) h1
    simpa using this
  calc ∑ z ∈ s, θ z = ∑ z ∈ s, liftChar H θ hθ ((z : G) : G ⧸ H) := rfl
    _ = ∑ g ∈ s.image (fun z : G => ((z : G) : G ⧸ H)), liftChar H θ hθ g :=
        (Finset.sum_image hinj).symm
    _ = 0 := by rw [himage]; exact AddChar.sum_eq_zero_of_ne_one hlift

end Characters

section Residues

variable {R : Type*} [CommRing R] {Λ : Type*} [Field Λ] {π : R} {q : ℕ} {lam : Fin q → R}

/-- **The sum of a nontrivial character of `R / (π)` over a residue system vanishes.** -/
public theorem sum_residueSystem_eq_zero (hlam : ∀ a : R, ∃! i : Fin q, a - lam i ∈ Ideal.span {π})
    {θ : R → Λ} (hθ : ∀ a b, θ (a + b) = θ a * θ b) (hθπ : ∀ a ∈ Ideal.span {π}, θ a = 1)
    {a : R} (ha : θ a ≠ 1) : ∑ i, θ (lam i) = 0 := by
  have hcong : ∀ x y, x - y ∈ Ideal.span {π} → θ x = θ y := by
    intro x y h
    rw [show x = y + (x - y) by ring, hθ, hθπ _ h, mul_one]
  choose σ hσ using fun i => (hlam (lam i + a)).exists
  have hinj : Function.Injective σ := by
    intro i i' h
    have h1 := hσ i
    have h2 := hσ i'
    rw [h] at h1
    have hmem : lam i - lam i' ∈ Ideal.span {π} := by
      have := sub_mem h1 h2
      convert this using 1
      ring
    obtain ⟨j, -, hj⟩ := hlam (lam i)
    exact (hj i (by simp)).trans (hj i' hmem).symm
  set e := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)
  have hsum : ∑ i, θ (lam i) = θ a * ∑ i, θ (lam i) := by
    calc ∑ i, θ (lam i) = ∑ i, θ (lam (e i)) := (Equiv.sum_comp e _).symm
      _ = ∑ i, θ (lam i + a) := Finset.sum_congr rfl fun i _ => (hcong _ _ (hσ i)).symm
      _ = θ a * ∑ i, θ (lam i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hθ, mul_comm]
  have : (θ a - 1) * ∑ i, θ (lam i) = 0 := by rw [sub_mul, ← hsum, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)

/-- **The Gauss sum of the Hecke computation.** If `λ_{i₀} ∈ (π)` and `μ_i λ_i = -1` for the other
indices, then `∑_{i ≠ i₀} θ(μ_i) = -1` for a nontrivial character `θ` of `R / (π)`: the `μ_i`
run over the nonzero residues. -/
public theorem sum_erase_residueSystem_eq_neg_one
    (hlam : ∀ a : R, ∃! i : Fin q, a - lam i ∈ Ideal.span {π}) (h1 : (1 : R) ∉ Ideal.span {π})
    {θ : R → Λ} (hθ : ∀ a b, θ (a + b) = θ a * θ b) (hθπ : ∀ a ∈ Ideal.span {π}, θ a = 1)
    {a : R} (ha : θ a ≠ 1) {i₀ : Fin q} (hi₀ : lam i₀ ∈ Ideal.span {π}) {μ : Fin q → R}
    (hμ : ∀ i, i ≠ i₀ → μ i * lam i = -1) :
    ∑ i ∈ Finset.univ.erase i₀, θ (μ i) = -1 := by
  classical
  have hcong : ∀ x y, x - y ∈ Ideal.span {π} → θ x = θ y := by
    intro x y h
    rw [show x = y + (x - y) by ring, hθ, hθπ _ h, mul_one]
  choose τ hτ using fun i => (hlam (μ i)).exists
  have hmaps : Set.MapsTo τ (Finset.univ.erase i₀ : Set (Fin q)) (Finset.univ.erase i₀) := by
    intro i hi
    have hi' : i ≠ i₀ := Finset.ne_of_mem_erase hi
    refine Finset.mem_erase.2 ⟨fun h => h1 ?_, Finset.mem_univ _⟩
    have hμmem : μ i ∈ Ideal.span {π} := by
      have := add_mem (hτ i) (h ▸ hi₀)
      simpa using this
    have := Ideal.mul_mem_right (lam i) _ hμmem
    rw [hμ i hi'] at this
    simpa using neg_mem this
  have hinj : Set.InjOn τ (Finset.univ.erase i₀ : Set (Fin q)) := by
    intro i hi i' hi' h
    have hne := Finset.ne_of_mem_erase hi
    have hne' := Finset.ne_of_mem_erase hi'
    have hdiff : μ i - μ i' ∈ Ideal.span {π} := by
      have := sub_mem (hτ i) (hτ i')
      rw [h] at this
      convert this using 1
      ring
    have hmem : lam i - lam i' ∈ Ideal.span {π} := by
      have hm := Ideal.mul_mem_right (lam i * lam i') _ hdiff
      convert hm using 1
      linear_combination (-lam i') * hμ i hne + lam i * hμ i' hne'
    obtain ⟨j, -, hj⟩ := hlam (lam i)
    exact (hj i (by simp)).trans (hj i' hmem).symm
  have hsurj := Finset.surjOn_of_injOn_of_card_le τ hmaps hinj le_rfl
  rw [Finset.sum_nbij (g := fun j => θ (lam j)) τ hmaps hinj hsurj (fun i _ => hcong _ _ (hτ i))]
  have hA := sum_residueSystem_eq_zero hlam hθ hθπ ha
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hθπ _ hi₀] at hA
  linear_combination hA

end Residues

section Sum

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [Field Λ]

variable {ψ : AddChar (AdeleRing K) Λ} {ω : (AdeleRing K)ˣ →* Λˣ} {c : (Place K →₀ ℤ) → Λ}

/-- The idele `diag(ξ)` of `ξ ∈ Kˣ`. -/
public theorem upperGL_mul_diagK (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) (ξ : Kˣ) :
    upperGL α δ β * diagK k K ξ = upperGL (α * Units.map (diag k K).toMonoidHom ξ) δ β := by
  rw [diagK_eq_upperGL, upperGL_mul]
  congr 1 <;> simp

/-- `W(κ (α, β; 0, δ) diag(ξ, 1)) = ψ((α ξ)⁻¹ β) ω(δ) c(div (α ξ δ⁻¹))`. -/
public theorem whittakerModel_mapO_mul_upperGL_mul_diagK
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (κ : GL (Fin 2) (integralAdeles K))
    (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) (ξ : Kˣ) :
    whittakerModel k K ψ ω c (mapO κ * upperGL α δ β * diagK k K ξ) =
      whittakerValue k K ψ ω c (α * Units.map (diag k K).toMonoidHom ξ) δ β := by
  rw [mul_assoc, upperGL_mul_diagK, whittakerModel_mapO_mul_upperGL k hω hc]

/-- The `ξ ∈ Kˣ` with `W(x diag(ξ, 1)) ≠ 0` form a finite set. -/
public theorem finite_support_whittakerModel_mul_diagK (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1)
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (x : GL (Fin 2) (AdeleRing K)) :
    (Function.support fun ξ : Kˣ => whittakerModel k K ψ ω c (x * diagK k K ξ)).Finite := by
  obtain ⟨κ, α, δ, β, rfl⟩ := exists_iwasawa x
  set D₀ := idelDiv k K (α * δ⁻¹)
  have := finite_charKernel k hψ hψ1 D₀
  have hfin : (charKernel k K ψ D₀ : Set K).Finite := Set.toFinite _
  refine (hfin.preimage fun ξ _ ξ' _ h => inv_injective (Units.ext h) :
    ((fun ξ : Kˣ => ((ξ⁻¹ : Kˣ) : K)) ⁻¹' (charKernel k K ψ D₀ : Set K)).Finite).subset ?_
  intro ξ hξ
  change whittakerModel k K ψ ω c (mapO κ * upperGL α δ β * diagK k K ξ) ≠ 0 at hξ
  rw [whittakerModel_mapO_mul_upperGL_mul_diagK k hω hc, whittakerValue] at hξ
  have hc0 := right_ne_zero_of_mul (right_ne_zero_of_mul hξ)
  have htriv := hc _ hc0
  set ξ' := Units.map (diag k K).toMonoidHom ξ
  have hdiv : idelDiv k K (α * ξ' * δ⁻¹) = D₀ - idelDiv k K ξ'⁻¹ := by
    simp only [D₀, idelDiv_mul, idelDiv_inv]
    abel
  intro a ha
  have hmem := (idele_mul_mem_adeleLattice_iff k ξ'⁻¹ (E := D₀)).2 ha
  rw [← hdiv] at hmem
  have := htriv _ hmem
  simpa [ξ'] using this

variable (K) in
/-- **The Fourier–Whittaker sum** `f(x) = ∑_{ξ ∈ Kˣ} W(x diag(ξ, 1))` of the Whittaker function
`W = whittakerModel ψ ω c`. -/
public def whittakerSum (ψ : AddChar (AdeleRing K) Λ) (ω : (AdeleRing K)ˣ →* Λˣ)
    (c : (Place K →₀ ℤ) → Λ) (x : GL (Fin 2) (AdeleRing K)) : Λ :=
  ∑ᶠ ξ : Kˣ, whittakerModel k K ψ ω c (x * diagK k K ξ)

/-- `f` is left `GL₂(O)`-invariant. -/
public theorem whittakerSum_mapO_mul
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (κ : GL (Fin 2) (integralAdeles K))
    (x : GL (Fin 2) (AdeleRing K)) :
    whittakerSum k K ψ ω c (mapO κ * x) = whittakerSum k K ψ ω c x := by
  simp only [whittakerSum, mul_assoc, whittakerModel_mapO_mul k hω hc]

/-- Scalar ideles act on `f` by `ω`. -/
public theorem whittakerSum_scalarGL_mul
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (a : (AdeleRing K)ˣ)
    (x : GL (Fin 2) (AdeleRing K)) :
    whittakerSum k K ψ ω c (scalarGL a * x) = ω a * whittakerSum k K ψ ω c x := by
  simp only [whittakerSum, mul_assoc, whittakerModel_scalarGL_mul k hω hc]
  exact (mul_finsum _ _).symm

/-- `diag(η, 1) diag(ξ, 1) = diag(η ξ, 1)`. -/
public theorem diagK_mul (η ξ : Kˣ) : diagK k K η * diagK k K ξ = diagK k K (η * ξ) := by
  simp only [diagK, ← map_mul, diagGL_mul]

/-- `f` is right invariant under `diag(η, 1)`, `η ∈ Kˣ`. -/
public theorem whittakerSum_mul_diagK (x : GL (Fin 2) (AdeleRing K)) (η : Kˣ) :
    whittakerSum k K ψ ω c (x * diagK k K η) = whittakerSum k K ψ ω c x := by
  simp only [whittakerSum, mul_assoc, diagK_mul]
  exact finsum_comp_equiv (Equiv.mulLeft η)
    (f := fun ξ => whittakerModel k K ψ ω c (x * diagK k K ξ))

/-- `n(z) diag(ξ, 1) = diag(ξ, 1) n(ξ⁻¹ z)`. -/
public theorem upperRightHom_mul_diagK (z : AdeleRing K) (ξ : Kˣ) :
    GeneralLinearGroup.upperRightHom z * diagK k K ξ =
      diagK k K ξ * GeneralLinearGroup.upperRightHom (diag k K ((ξ⁻¹ : Kˣ) : K) * z) := by
  rw [diagK_mul_upperRightHom, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val,
    mul_inv_cancel₀ ξ.ne_zero, map_one, one_mul]

/-- **The Fourier expansion of `f` along `n(z)`**:
`f(x n(z)) = ∑_{ξ ∈ Kˣ} ψ(ξ⁻¹ z) W(x diag(ξ, 1))`. -/
public theorem whittakerSum_mul_upperRightHom
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (x : GL (Fin 2) (AdeleRing K))
    (z : AdeleRing K) :
    whittakerSum k K ψ ω c (x * GeneralLinearGroup.upperRightHom z) =
      ∑ᶠ ξ : Kˣ, ψ (diag k K ((ξ⁻¹ : Kˣ) : K) * z) *
        whittakerModel k K ψ ω c (x * diagK k K ξ) := by
  rw [whittakerSum]
  congr 1
  funext ξ
  rw [mul_assoc, upperRightHom_mul_diagK, ← mul_assoc, whittakerModel_mul_upperRightHom k hω hc]

/-- `f` is right invariant under `n(κ)`, `κ ∈ K`. -/
public theorem whittakerSum_mul_upperRightHom_diag (hψ : IsAdelicChar k K ψ)
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (x : GL (Fin 2) (AdeleRing K))
    (κ : K) :
    whittakerSum k K ψ ω c (x * GeneralLinearGroup.upperRightHom (diag k K κ)) =
      whittakerSum k K ψ ω c x := by
  rw [whittakerSum_mul_upperRightHom k hω hc, whittakerSum]
  congr 1
  funext ξ
  rw [← map_mul, hψ.1, one_mul]

/-- `ξ ↦ ψ(ξ⁻¹ ·)` is injective on `Kˣ` for a nontrivial character `ψ`. -/
private theorem injective_mulShift_inv_diag (hψ1 : ψ ≠ 1) :
    Function.Injective fun ξ : Kˣ => ψ.mulShift (diag k K ((ξ⁻¹ : Kˣ) : K)) := by
    intro ξ ξ' h
    by_contra hne
    apply hψ1
    have hd : ((ξ⁻¹ : Kˣ) : K) - ((ξ'⁻¹ : Kˣ) : K) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h' => hne (inv_injective (Units.ext h'))
    ext a
    set d := ((ξ⁻¹ : Kˣ) : K) - ((ξ'⁻¹ : Kˣ) : K)
    have hne : ∀ b, ψ b ≠ 0 := fun b h0 => by
      have := AddChar.map_add_eq_mul ψ b (-b)
      rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
      exact one_ne_zero this
    have := congrArg (fun θ : AddChar (AdeleRing K) Λ => θ (diag k K d⁻¹ * a)) h
    simp only [AddChar.mulShift_apply, ← mul_assoc, ← map_mul] at this
    have key : ψ a = ψ (diag k K (((ξ⁻¹ : Kˣ) : K) * d⁻¹) * a) /
        ψ (diag k K (((ξ'⁻¹ : Kˣ) : K) * d⁻¹) * a) := by
      rw [← AddChar.map_sub_eq_div, ← sub_mul, ← map_sub, ← sub_mul, mul_inv_cancel₀ hd, map_one,
        one_mul]
    rw [key, this, div_self (hne _), AddChar.one_apply]

/-- Expansion of `f(x n(z))` as a finite sum over any `S` containing the support. -/
private theorem whittakerSum_mul_upperRightHom_eq_sum
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (x : GL (Fin 2) (AdeleRing K))
    (S : Finset Kˣ)
    (hS : (Function.support fun ξ : Kˣ => whittakerModel k K ψ ω c (x * diagK k K ξ)) ⊆ S)
    (z : AdeleRing K) :
    whittakerSum k K ψ ω c (x * GeneralLinearGroup.upperRightHom z) =
      ∑ ξ ∈ S, whittakerModel k K ψ ω c (x * diagK k K ξ) *
        ψ.mulShift (diag k K ((ξ⁻¹ : Kˣ) : K)) z := by
  rw [whittakerSum_mul_upperRightHom k hω hc, finsum_eq_sum_of_support_subset _ (s := S) ?_]
  · exact Finset.sum_congr rfl fun ξ _ => mul_comm _ _
  · exact fun ξ hξ => hS (right_ne_zero_of_mul hξ)

/-- **The constant term of `f` vanishes**, in the form of part (3) of Tag 03VS. -/
public theorem sum_whittakerSum_mul_upperRightHom_eq_zero (hψ : IsAdelicChar k K ψ)
    (hψ1 : ψ ≠ 1)
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (x : GL (Fin 2) (AdeleRing K))
    (U : AddSubgroup (AdeleRing K))
    (hinv : ∀ z : AdeleRing K, ∀ y ∈ U,
      whittakerSum k K ψ ω c (x * GeneralLinearGroup.upperRightHom (z + y)) =
        whittakerSum k K ψ ω c (x * GeneralLinearGroup.upperRightHom z))
    (s : Finset (AdeleRing K))
    (hs : ∀ a : AdeleRing K, ∃! z ∈ s, a - z ∈ (principalAdeles K).toAddSubgroup ⊔ U) :
    ∑ z ∈ s, whittakerSum k K ψ ω c (x * GeneralLinearGroup.upperRightHom z) = 0 := by
  classical
  set A : Kˣ → Λ := fun ξ => whittakerModel k K ψ ω c (x * diagK k K ξ)
  have hfin := finite_support_whittakerModel_mul_diagK k hψ hψ1 hω hc x
  set S := hfin.toFinset
  set χ : Kˣ → AddChar (AdeleRing K) Λ := fun ξ => ψ.mulShift (diag k K ((ξ⁻¹ : Kˣ) : K))
  have hχ : Function.Injective χ := injective_mulShift_inv_diag k hψ1
  have hexp : ∀ z, whittakerSum k K ψ ω c (x * GeneralLinearGroup.upperRightHom z) =
      ∑ ξ ∈ S, A ξ * χ ξ z :=
    whittakerSum_mul_upperRightHom_eq_sum k hω hc x S fun ξ hξ => hfin.mem_toFinset.2 hξ
  have hprin : (principalAdeles K).toAddSubgroup = principal k K := by
    rw [principal, range_diag]
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ξ hξ => ?_
  by_cases hA : A ξ = 0
  · simp [hA]
  rw [← Finset.mul_sum]
  refine mul_eq_zero_of_right _ (sum_transversal_eq_zero hs ?_ ?_)
  · intro a ha
    obtain ⟨b, hb, y, hy, rfl⟩ := AddSubgroup.mem_sup.1 ha
    rw [AddChar.map_add_eq_mul]
    have hbK : χ ξ b = 1 := by
      rw [hprin] at hb
      obtain ⟨κ, rfl⟩ := (mem_principal k).1 hb
      simp only [χ, AddChar.mulShift_apply, ← map_mul]
      exact hψ.1 _
    have hyU : χ ξ y = 1 := by
      refine apply_eq_one_of_sum_comp_add hχ (S := S) (a := A) (fun z => ?_) hξ hA
      rw [← hexp, ← hexp]
      exact hinv z y hy
    rw [hbK, hyU, one_mul]
  · intro h1
    apply hψ1
    ext a
    have := congrArg (fun θ : AddChar (AdeleRing K) Λ => θ (diag k K (ξ : K) * a)) h1
    simpa [χ, ← mul_assoc, ← map_mul] using this

section Hecke

variable {v : Place K} {t u : Place K → Λ}

open scoped Classical in
/-- `singleAdele` is additive. -/
public theorem singleAdele_add (v : Place K) (a b : v.completion) :
    singleAdele v (a + b) = singleAdele v a + singleAdele v b := by
  ext w
  rcases eq_or_ne w v with rfl | hw
  · change singleAdele w (a + b) w = singleAdele w a w + singleAdele w b w
    rw [singleAdele_apply_self, singleAdele_apply_self, singleAdele_apply_self]
  · change singleAdele v (a + b) w = singleAdele v a w + singleAdele v b w
    rw [singleAdele_apply_ne hw, singleAdele_apply_ne hw, singleAdele_apply_ne hw, add_zero]

/-- `-(λ y_v)⁻¹` at `v`, for a unit `λ`, lies in `A(div y)`. -/
public theorem singleAdele_mem_adeleLattice {v : Place K} {l : v.integers} (hl : IsUnit l)
    (y : (AdeleRing K)ˣ) :
    singleAdele v (-((l : v.completion) * (y : AdeleRing K) v)⁻¹) ∈
      adeleLattice K (idelDiv k K y) := by
  classical
  have hv := isDiscrete k v
  intro w
  rcases eq_or_ne w v with rfl | hw
  · rw [singleAdele_apply_self, Place.mem_ball, Valuation.map_neg, map_inv₀, map_mul,
      valued_eq_one_of_isUnit hl, one_mul,
      Place.valued_eq_unifVal_zpow_ordC hv (idele_apply_ne_zero y w), ← idelDiv_apply k y w,
      zpow_neg]
  · rw [singleAdele_apply_ne hw]
    exact (w.ball _).zero_mem

/-- **The Gauss sum in `T_v`.** If `ψ` is trivial on `A(D - v)` but not on `A(D)`, `D = div y`,
then `∑_{i ≠ i₀} ψ(-(λᵢ y_v)⁻¹ at v) = -1`: `x ↦ ψ(x y_v⁻¹ at v)` is a nontrivial character of
`O_v / (π)` and the `-λᵢ⁻¹` run over the nonzero residues. -/
public theorem sum_erase_singleAdele_eq_neg_one {v : Place K} {q : ℕ} {π : v.integers}
    {lam : Fin q → v.integers} (hπ : Place.IsUniformizer v π)
    (hlam : Place.IsResidueSystem v π lam) {i₀ : Fin q} (hmem₀ : lam i₀ ∈ Ideal.span {π})
    (hunit : ∀ i, i ≠ i₀ → IsUnit (lam i)) (y : (AdeleRing K)ˣ)
    (hD : ¬∀ a ∈ adeleLattice K (idelDiv k K y), ψ a = 1)
    (hD1 : ∀ a ∈ adeleLattice K (idelDiv k K y - Finsupp.single v 1), ψ a = 1) :
    ∑ i ∈ Finset.univ.erase i₀,
      ψ (singleAdele v (-((lam i : v.completion) * (y : AdeleRing K) v)⁻¹)) = -1 := by
  classical
  have hv := isDiscrete k v
  set D := idelDiv k K y with hDdef
  have hyv : Valued.v ((y : AdeleRing K) v) = v.unifVal ^ (D v) := by
    rw [Place.valued_eq_unifVal_zpow_ordC hv (idele_apply_ne_zero y v)]
    rfl
  have hl0 : ∀ i, i ≠ i₀ → (lam i : v.completion) ≠ 0 := by
    intro i hi h
    have hval := valued_eq_one_of_isUnit (hunit i hi)
    rw [h, map_zero] at hval
    exact zero_ne_one hval
  set θ : v.integers → Λ := fun x =>
    ψ (singleAdele v ((x : v.completion) * ((y : AdeleRing K) v)⁻¹)) with hθdef
  have hθ : ∀ a b, θ (a + b) = θ a * θ b := by
    intro a b
    simp only [θ]
    push_cast
    rw [add_mul, singleAdele_add, AddChar.map_add_eq_mul]
  have hθπ : ∀ x ∈ Ideal.span {π}, θ x = 1 := by
    intro x hx
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine hD1 _ fun w => ?_
    rcases eq_or_ne w v with rfl | hw
    · rw [singleAdele_apply_self, Place.mem_ball]
      push_cast
      rw [map_mul, map_mul, map_inv₀, hyv, valued_eq_unifVal_of_isUniformizer hv hπ]
      rw [Pi.sub_apply, Finsupp.single_eq_same]
      have he : w.unifVal ^ (-(D w - 1)) = w.unifVal * (w.unifVal ^ D w)⁻¹ := by
        rw [neg_sub, zpow_sub₀ (Place.unifVal_ne_zero hv), zpow_one, div_eq_mul_inv]
      rw [he]
      have hs1 : Valued.v (s : w.completion) ≤ 1 := s.2
      have := mul_le_of_le_one_left' (a := w.unifVal) hs1
      gcongr
    · rw [singleAdele_apply_ne hw]
      exact (w.ball _).zero_mem
  obtain ⟨b, hb, hψb⟩ : ∃ b ∈ adeleLattice K D, ψ b ≠ 1 := by
    by_contra h
    push Not at h
    exact hD h
  have hsplit : b - singleAdele v (b v) ∈ adeleLattice K (D - Finsupp.single v 1) := by
    intro w
    rcases eq_or_ne w v with rfl | hw
    · change b w - singleAdele w (b w) w ∈ _
      rw [singleAdele_apply_self, sub_self]
      exact (w.ball _).zero_mem
    · change b w - singleAdele v (b v) w ∈ _
      rw [singleAdele_apply_ne hw, sub_zero, Finsupp.coe_sub, Pi.sub_apply,
        Finsupp.single_eq_of_ne hw, sub_zero]
      exact hb w
  have hbv : b v * (y : AdeleRing K) v ∈ v.integers := by
    change Valued.v (b v * (y : AdeleRing K) v) ≤ 1
    rw [map_mul, hyv]
    have := Place.mem_ball.1 (hb v)
    have e1 : v.unifVal ^ (-D v) * v.unifVal ^ D v = 1 := by
      rw [← zpow_add₀ (Place.unifVal_ne_zero hv), neg_add_cancel, zpow_zero]
    rw [← e1]
    gcongr
  have ha : θ ⟨_, hbv⟩ ≠ 1 := by
    simp only [θ]
    rw [mul_assoc, mul_inv_cancel₀ (idele_apply_ne_zero y v), mul_one]
    intro h
    apply hψb
    have e := AddChar.map_add_eq_mul ψ (b - singleAdele v (b v)) (singleAdele v (b v))
    rw [sub_add_cancel, hD1 _ hsplit, h, one_mul] at e
    exact e
  set μ : Fin q → v.integers := fun i =>
    if h : IsUnit (lam i) then -((h.unit⁻¹ : v.integersˣ) : v.integers) else 0
  have hμ : ∀ i, i ≠ i₀ → μ i * lam i = -1 := by
    intro i hi
    simp only [μ, dite_eq_left (hunit i hi), neg_mul, IsUnit.val_inv_mul]
  have hμc : ∀ i, i ≠ i₀ → ((μ i : v.integers) : v.completion) = -(lam i : v.completion)⁻¹ := by
    intro i hi
    have h := congrArg (fun z : v.integers => (z : v.completion)) (hμ i hi)
    push_cast at h
    have hl := hl0 i hi
    field_simp
    linear_combination h
  have h1 : (1 : v.integers) ∉ Ideal.span {π} := by
    rw [hπ]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal v.integers).ne_top
      ((Ideal.eq_top_iff_one _).2 h)
  rw [← sum_erase_residueSystem_eq_neg_one hlam h1 hθ hθπ ha hmem₀ hμ]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [θ]
  rw [hμc i (Finset.ne_of_mem_erase hi), mul_inv, neg_mul]

/-- **`T_v` on the Whittaker model at `diag(y, 1)`.** If the coefficients satisfy the Hecke
recursion `t_v c(D) = q_v c(D - v) + u_v c(D + v)` wherever `ψ(A(D)) = 1`, and `ω(ϖ_v⁻¹) = u_v`,
then `W(g₀ diag(y, 1)) + ∑ᵢ W(gᵢ diag(y, 1)) = t_v W(diag(y, 1))`. Where `ψ(A(D)) ≠ 1` but
`ψ(A(D - v)) = 1` this is the vanishing of a Gauss sum over the residue field. -/
public theorem heckeOperator_whittakerModel_diagGL
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1)
    (hrec : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) → t v * c D =
      (v.residueCard : Λ) * c (D - Finsupp.single v 1) + u v * c (D + Finsupp.single v 1))
    (hωu : ∀ {π : v.integers} (hπ : Place.IsUniformizer v π),
      (ω (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) : Λ) = u v)
    {q : ℕ} {π : v.integers} {lam : Fin q → v.integers} {g₀ : GL (Fin 2) (AdeleRing K)}
    {g : Fin q → GL (Fin 2) (AdeleRing K)} (hd : IsHeckeDataAt v π lam g₀ g)
    (y : (AdeleRing K)ˣ) :
    heckeOperator g₀ g (whittakerModel k K ψ ω c) (diagGL y) =
      t v * whittakerModel k K ψ ω c (diagGL y) := by
  classical
  have hv := isDiscrete k v
  have hπ := hd.isUniformizer
  have hπ0 := coe_ne_zero_of_isUniformizer k hπ
  set D := idelDiv k K y with hDdef
  have hW : ∀ y' : (AdeleRing K)ˣ, whittakerModel k K ψ ω c (diagGL y') = c (idelDiv k K y') :=
    whittakerModel_diagGL k hω hc
  have hyv : Valued.v ((y : AdeleRing K) v) = v.unifVal ^ (D v) := by
    rw [Place.valued_eq_unifVal_zpow_ordC hv (idele_apply_ne_zero y v)]
    rfl
  have h0 : whittakerModel k K ψ ω c (g₀ * diagGL y) = c (D - Finsupp.single v 1) := by
    rw [mul_diagGL_of_isLocalMatrixAt_diagonal hπ0 hd.diagonal, hW, idelDiv_mul,
      idelDiv_localIdele k, ordC_inv_of_isUniformizer hv hπ hπ0, Finsupp.single_neg,
      neg_add_eq_sub]
  obtain ⟨i₀, hi₀, -⟩ := hd.isResidueSystem 0
  have hmem₀ : lam i₀ ∈ Ideal.span {π} := by simpa using hi₀
  have hunit : ∀ i, i ≠ i₀ → IsUnit (lam i) := by
    intro i hi
    by_contra hnu
    apply hi
    obtain ⟨j, -, hj⟩ := hd.isResidueSystem 0
    have : lam i ∈ IsLocalRing.maximalIdeal v.integers := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [← hπ] at this
    exact (hj i (by simpa using this)).trans (hj i₀ hi₀).symm
  have hc' : (π : v.completion)⁻¹ * (lam i₀ : v.completion) ∈ v.integers := by
    rw [mul_comm]
    exact div_mem_integers_of_mem_span hmem₀ hπ0
  obtain ⟨κ₁, hκ₁⟩ := exists_mapO_eq_localGL
    (lowerGL (-((π : v.completion)⁻¹ * (lam i₀ : v.completion))))
    (isIntMat_lowerGL (neg_mem hc')) (isIntMat_lowerGL_inv (neg_mem hc'))
  have hi₀W : whittakerModel k K ψ ω c (g i₀ * diagGL y) = u v * c (D + Finsupp.single v 1) := by
    rw [mul_diagGL_of_isLocalMatrixAt_coset hπ0 (hd.coset i₀) y, ← hκ₁,
      whittakerModel_mapO_mul k hω hc, whittakerModel_scalarGL_mul k hω hc, hωu hπ, hW,
      idelDiv_mul, idelDiv_localIdele k, ordC_of_isUniformizer k hπ, add_comm]
  -- the cosets with `λ` a unit
  have hl0 : ∀ i, i ≠ i₀ → (lam i : v.completion) ≠ 0 := by
    intro i hi h
    have hval := valued_eq_one_of_isUnit (hunit i hi)
    rw [h, map_zero] at hval
    exact zero_ne_one hval
  have hiW : ∀ i ∈ Finset.univ.erase i₀, whittakerModel k K ψ ω c (g i * diagGL y) =
      ψ (singleAdele v (-((lam i : v.completion) * (y : AdeleRing K) v)⁻¹)) *
        c (D - Finsupp.single v 1) := by
    intro i hi
    have hi' := Finset.ne_of_mem_erase hi
    have hu := hunit i hi'
    have hval := valued_eq_one_of_isUnit hu
    have hlinv : (lam i : v.completion)⁻¹ ∈ v.integers := by
      change Valued.v ((lam i : v.completion)⁻¹) ≤ 1
      rw [map_inv₀, hval, inv_one]
    obtain ⟨κ, hκ⟩ := exists_mapO_eq_localGL (swapGL (π : v.completion) (hl0 i hi'))
      (isIntMat_swapGL (hl0 i hi') π.2 hlinv) (isIntMat_swapGL_inv (hl0 i hi') π.2 (lam i).2)
    rw [mul_diagGL_of_isLocalMatrixAt_coset_of_ne_zero hπ0 (hl0 i hi') (hd.coset i) y, ← hκ,
      whittakerModel_mapO_mul k hω hc, whittakerModel_mul_upperRightHom k hω hc, hW,
      idelDiv_mul, idelDiv_localIdele k, ordC_neg_inv_mul_mul k hπ hu, Finsupp.single_neg,
      neg_add_eq_sub]
  have hq : (q : Λ) = v.residueCard := by
    rw [Place.residueCard_eq_of_isResidueSystem hπ hd.isResidueSystem]
  rw [heckeOperator, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hi₀W,
    Finset.sum_congr rfl hiW, h0, hW]
  by_cases hD : ∀ a ∈ adeleLattice K D, ψ a = 1
  · have hz : ∀ i ∈ Finset.univ.erase i₀,
        ψ (singleAdele v (-((lam i : v.completion) * (y : AdeleRing K) v)⁻¹)) = 1 := fun i hi =>
      hD _ (singleAdele_mem_adeleLattice k (hunit i (Finset.ne_of_mem_erase hi)) y)
    rw [Finset.sum_congr rfl fun i hi => by rw [hz i hi, one_mul], Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hrec D hD]
    have hq1 : 1 ≤ q := Fin.pos i₀
    rw [Nat.cast_sub hq1, Nat.cast_one, hq]
    ring
  have hcD : c D = 0 := by
    by_contra h
    exact hD (hc D h)
  have hcD1 : c (D + Finsupp.single v 1) = 0 := by
    by_contra h
    apply hD
    intro a ha
    refine hc _ h a (adeleLattice_mono k ?_ ha)
    exact le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one)
  rw [hcD, hcD1, mul_zero, mul_zero, zero_add]
  by_cases hc1 : c (D - Finsupp.single v 1) = 0
  · simp [hc1]
  have hD1 := hc _ hc1
  have hG := sum_erase_singleAdele_eq_neg_one k hπ hd.isResidueSystem hmem₀ hunit y hD hD1
  rw [← Finset.sum_mul, hG]
  ring

/-- **`T_v` on the Whittaker model.** Under the hypotheses of
`heckeOperator_whittakerModel_diagGL`, `T_v W = t_v W` everywhere: by the Iwasawa decomposition
`x = κ δ diag(α δ⁻¹, 1) n(b)`, and `T_v` commutes with `GL₂(O)` on the left and with the
centre and `n(b)` on the right. -/
public theorem heckeOperator_whittakerModel
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1)
    (hrec : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) → t v * c D =
      (v.residueCard : Λ) * c (D - Finsupp.single v 1) + u v * c (D + Finsupp.single v 1))
    (hωu : ∀ {π : v.integers} (hπ : Place.IsUniformizer v π),
      (ω (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) : Λ) = u v)
    {q : ℕ} {π : v.integers} {lam : Fin q → v.integers} {g₀ : GL (Fin 2) (AdeleRing K)}
    {g : Fin q → GL (Fin 2) (AdeleRing K)} (hd : IsHeckeDataAt v π lam g₀ g)
    (x : GL (Fin 2) (AdeleRing K)) :
    heckeOperator g₀ g (whittakerModel k K ψ ω c) x = t v * whittakerModel k K ψ ω c x := by
  have hπ0 := coe_ne_zero_of_isUniformizer k hd.isUniformizer
  obtain ⟨κ, α, δ, β, rfl⟩ := exists_iwasawa x
  change heckeOperator g₀ g _ (mapO κ * upperGL α δ β) =
    t v * whittakerModel k K ψ ω c (mapO κ * upperGL α δ β)
  rw [heckeOperator_left_invariant hd hπ0 (whittakerModel_mapO_mul k hω hc),
    whittakerModel_mapO_mul k hω hc, upperGL_eq_scalarGL_mul]
  set b := ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β
  have key : ∀ h : GL (Fin 2) (AdeleRing K), whittakerModel k K ψ ω c
      (h * (scalarGL δ * diagGL (α * δ⁻¹) * GeneralLinearGroup.upperRightHom b)) =
        ω δ * (ψ b * whittakerModel k K ψ ω c (h * diagGL (α * δ⁻¹))) := by
    intro h
    have e : h * (scalarGL δ * diagGL (α * δ⁻¹) * GeneralLinearGroup.upperRightHom b) =
        scalarGL δ * (h * diagGL (α * δ⁻¹) * GeneralLinearGroup.upperRightHom b) := by
      simp only [mul_assoc]
      rw [← mul_assoc h (scalarGL δ), ← scalarGL_mul_comm, mul_assoc]
    rw [e, whittakerModel_scalarGL_mul k hω hc, whittakerModel_mul_upperRightHom k hω hc]
  have hD := heckeOperator_whittakerModel_diagGL k hω hc hrec hωu hd (α * δ⁻¹)
  have h1 := key 1
  simp only [one_mul] at h1
  rw [heckeOperator] at hD ⊢
  rw [key, Finset.sum_congr rfl fun i _ => key (g i), ← Finset.mul_sum, ← Finset.mul_sum, h1,
    ← mul_add, ← mul_add, hD]
  ring

/-- **`f` is a `T_v`-eigenfunction with eigenvalue `t_v`.** -/
public theorem isHeckeEigenvalueAt_whittakerSum (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1)
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1)
    (hrec : ∀ D, (∀ a ∈ adeleLattice K D, ψ a = 1) → t v * c D =
      (v.residueCard : Λ) * c (D - Finsupp.single v 1) + u v * c (D + Finsupp.single v 1))
    (hωu : ∀ {π : v.integers} (hπ : Place.IsUniformizer v π),
      (ω (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) : Λ) = u v) :
    IsHeckeEigenvalueAt v (whittakerSum k K ψ ω c) (t v) := by
  classical
  intro q π lam g₀ g hd x
  rw [heckeOperator_eq_sum]
  have hfin : ∀ j, (Function.support fun ξ : Kˣ =>
      whittakerModel k K ψ ω c (heckeFamily g₀ g j * x * diagK k K ξ)).Finite := fun j =>
    finite_support_whittakerModel_mul_diagK k hψ hψ1 hω hc _
  have hfx := finite_support_whittakerModel_mul_diagK k hψ hψ1 hω hc x
  set S : Finset Kˣ := (Finset.univ.biUnion fun j => (hfin j).toFinset) ∪ hfx.toFinset
  have hsub : ∀ j, (Function.support fun ξ : Kˣ =>
      whittakerModel k K ψ ω c (heckeFamily g₀ g j * x * diagK k K ξ)) ⊆ S := by
    intro j ξ hξ
    exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
      (hfin j).mem_toFinset.2 hξ⟩)
  have hsubx : (Function.support fun ξ : Kˣ =>
      whittakerModel k K ψ ω c (x * diagK k K ξ)) ⊆ S := fun ξ hξ =>
    Finset.mem_union_right _ (hfx.mem_toFinset.2 hξ)
  simp only [whittakerSum]
  rw [Finset.sum_congr rfl fun j _ => finsum_eq_sum_of_support_subset _ (hsub j),
    finsum_eq_sum_of_support_subset _ hsubx, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  have := heckeOperator_whittakerModel k hω hc hrec hωu hd (x * diagK k K ξ)
  rw [heckeOperator_eq_sum] at this
  simpa only [mul_assoc] using this

include k in
/-- The data of `U_v` is the scalar idele `π⁻¹` at `v`. -/
public theorem eq_scalarGL_of_isCentralDataAt {a : GL (Fin 2) (AdeleRing K)}
    (ha : IsCentralDataAt v a) : ∃ (π : v.integers) (hπ : Place.IsUniformizer v π),
      a = scalarGL (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) := by
  classical
  obtain ⟨π, hπ, h⟩ := ha
  refine ⟨π, hπ, localMat_ext fun w => ?_⟩
  rw [localMat_scalarGL]
  rcases eq_or_ne w v with rfl | hw
  · rw [localMat_of_isLocalMatrixAt_self h, localIdele_apply_self]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [localMat_of_isLocalMatrixAt_ne h hw, localIdele_apply_ne hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- **`f` is a `U_v`-eigenfunction with eigenvalue `u_v`.** -/
public theorem isCentralEigenvalueAt_whittakerSum
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1)
    (hωu : ∀ {π : v.integers} (hπ : Place.IsUniformizer v π),
      (ω (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) : Λ) = u v) :
    IsCentralEigenvalueAt v (whittakerSum k K ψ ω c) (u v) := by
  intro a ha x
  obtain ⟨π, hπ, rfl⟩ := eq_scalarGL_of_isCentralDataAt k ha
  rw [centralOperator, whittakerSum_scalarGL_mul k hω hc, hωu hπ]

end Hecke

section Nonvanishing

/-- **Dedekind's independence of characters.** -/
public theorem eq_zero_of_sum_mul_eq_zero {G : Type*} [AddCommGroup G] {ι : Type*}
    {S : Finset ι} {χ : ι → AddChar G Λ} (hχ : Function.Injective χ) {a : ι → Λ}
    (h : ∀ z, ∑ i ∈ S, a i * χ i z = 0) {i : ι} (hi : i ∈ S) : a i = 0 := by
  classical
  have hinj : Function.Injective fun j => (χ j).toMonoidHom := fun j j' hjj' =>
    hχ (AddChar.toMonoidHomEquiv.injective hjj')
  have hli := (linearIndependent_monoidHom (Multiplicative G) Λ).comp _ hinj
  have hsum : ∑ j ∈ S, a j • (fun z : Multiplicative G => (χ j).toMonoidHom z) = 0 := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      AddChar.toMonoidHom_apply]
    exact h (Multiplicative.toAdd z)
  exact (linearIndependent_iff'.1 hli) S a hsum i hi

/-- `diag(1, 1) = 1`. -/
public theorem diagK_one : diagK k K 1 = 1 := by
  have h := diagK_mul k (K := K) 1 1
  rw [mul_one] at h
  exact mul_eq_left.1 h

/-- **`f ≠ 0` when some coefficient is nonzero**: the coefficient `W(x)` of `ψ(z)` in the Fourier
expansion of `z ↦ f(x n(z))` is determined by `f`. -/
public theorem exists_whittakerSum_ne_zero (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1)
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) {D₀ : Place K →₀ ℤ} (hD₀ : c D₀ ≠ 0) :
    ∃ x, whittakerSum k K ψ ω c x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  set x := diagGL (idelOfDiv k K D₀)
  set A : Kˣ → Λ := fun ξ => whittakerModel k K ψ ω c (x * diagK k K ξ)
  have hfin := finite_support_whittakerModel_mul_diagK k hψ hψ1 hω hc x
  set S := hfin.toFinset ∪ {1}
  set χ : Kˣ → AddChar (AdeleRing K) Λ := fun ξ => ψ.mulShift (diag k K ((ξ⁻¹ : Kˣ) : K))
  have hχ : Function.Injective χ := injective_mulShift_inv_diag k hψ1
  have hexp : ∀ z, ∑ ξ ∈ S, A ξ * χ ξ z = 0 := fun z => by
    rw [← h (x * GeneralLinearGroup.upperRightHom z),
      whittakerSum_mul_upperRightHom_eq_sum k hω hc x S fun ξ hξ =>
        Finset.mem_union_left _ (hfin.mem_toFinset.2 hξ)]
  have h1 := eq_zero_of_sum_mul_eq_zero hχ hexp
    (Finset.mem_union_right _ (Finset.mem_singleton_self 1))
  apply hD₀
  rw [← h1]
  simp only [A, x, diagK_one, mul_one, whittakerModel_diagGL k hω hc, idelDiv_idelOfDiv]

end Nonvanishing

section Eigenform

variable {t u : Place K → Λ}

/-- **Step A of the converse direction.** If the coefficients `c` satisfy the Hecke recursion at
every place, `ω(ϖ_v⁻¹) = u_v`, and some `c(D₀) ≠ 0`, then `f = whittakerSum ψ ω c` is an eigenform
with eigenvalues `(t, u)` as soon as it is right `GL₂(K)`-invariant. That invariance (the converse
theorem) is the remaining input. -/
public theorem isEigenform_whittakerSum (hψ : IsAdelicChar k K ψ) (hψ1 : ψ ≠ 1)
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1)
    (hrec : ∀ (v : Place K) D, (∀ a ∈ adeleLattice K D, ψ a = 1) → t v * c D =
      (v.residueCard : Λ) * c (D - Finsupp.single v 1) + u v * c (D + Finsupp.single v 1))
    (hωu : ∀ (v : Place K) {π : v.integers} (hπ : Place.IsUniformizer v π),
      (ω (localIdele v (inv_ne_zero (coe_ne_zero_of_isUniformizer k hπ))) : Λ) = u v)
    {D₀ : Place K →₀ ℤ} (hD₀ : c D₀ ≠ 0)
    (hK : ∀ (x : GL (Fin 2) (AdeleRing K)) (γ : GL (Fin 2) (principalAdeles K)),
      whittakerSum k K ψ ω c (x * GeneralLinearGroup.map (principalAdeles K).subtype γ) =
        whittakerSum k K ψ ω c x) :
    IsEigenform (whittakerSum k K ψ ω c) t u where
  isUnramifiedCuspForm :=
    { right_invariant := hK
      left_invariant := fun x κ => whittakerSum_mapO_mul k hω hc κ x
      vanishing_constant_term := fun x U _ hinv s hs =>
        sum_whittakerSum_mul_upperRightHom_eq_zero k hψ hψ1 hω hc x U hinv s hs }
  exists_isUnit := by
    obtain ⟨x, hx⟩ := exists_whittakerSum_ne_zero k hψ hψ1 hω hc hD₀
    exact ⟨x, isUnit_iff_ne_zero.2 hx⟩
  hecke v := isHeckeEigenvalueAt_whittakerSum k hψ hψ1 hω hc (hrec v) (hωu v)
  central v := isCentralEigenvalueAt_whittakerSum k hω hc (hωu v)

end Eigenform

end Sum

end Stacks.Adeles.GlobalFunctionField

end
