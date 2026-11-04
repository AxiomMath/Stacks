module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields

/-!
# The \(C_r\) property for systems of forms

A field `K` has the \(C_r\) property for systems of forms when every family of `s` forms of a
common degree `d > 0` in `n` variables has a common nontrivial zero as soon as `s * d ^ r < n`.
Taking `s = 1` recovers the \(C_r\) property of Stacks 03R9.

The point of the stronger property is that it passes to finite extensions with no loss in the
numerology, which the \(C_r\) property for a single form does not visibly do once `r ≥ 2`. If
`L/K` has a `K`-basis `e_1, ..., e_N`, a form of degree `d` in `n` variables over `L` becomes,
after writing every variable as `∑ j, y_{ij} e_j` and expanding every coefficient in the basis,
`N` forms of degree `d` in `n * N` variables over `K`, whose common zeros are the zeros of the
original form. So `s` forms over `L` become `s * N` forms over `K` in `n * N` variables, and
`s * N * d ^ r < n * N` is exactly `s * d ^ r < n`. This is the Weil-restriction argument, and
it is what reduces Tsen's theorem (Stacks 03RD) for an arbitrary function field to the case of
a rational function field.

## Main definitions

* `IsCFieldForSystems`: the \(C_r\) property for systems of forms of a common degree.

## Main results

* `IsCFieldForSystems.exists_nonzero_common_zero`: the defining property for families and
  variables indexed by arbitrary finite types.
* `IsCFieldForSystems.isCField`: the property for systems implies the \(C_r\) property.
* `IsCFieldForSystems.of_ringEquiv`: the property is invariant under isomorphism of fields.
* `IsCFieldForSystems.of_module_finite`: the property passes to finite extensions.

## References

* [Stacks Project, Tag 03R9](https://stacks.math.columbia.edu/tag/03R9)
* [Stacks Project, Tag 03RD](https://stacks.math.columbia.edu/tag/03RD)
-/

@[expose] public noncomputable section

/-- A field `K` has the \(C_r\) property for systems of forms if every family of `s`
homogeneous polynomials of a common degree `d > 0` in `n` variables has a common nonzero zero
whenever `s * d ^ r < n`. -/
def IsCFieldForSystems (K : Type*) [Field K] (r : ℕ) : Prop :=
  ∀ (s d n : ℕ), 0 < d → s * d ^ r < n → ∀ f : Fin s → MvPolynomial (Fin n) K,
    (∀ i, (f i).IsHomogeneous d) → ∃ α : Fin n → K, α ≠ 0 ∧ ∀ i, MvPolynomial.eval α (f i) = 0

namespace IsCFieldForSystems

variable {K : Type*} [Field K] {r : ℕ}

/-- The defining property of `IsCFieldForSystems`, for a family of forms and a set of variables
indexed by arbitrary finite types. -/
theorem exists_nonzero_common_zero (hK : IsCFieldForSystems K r) {S ι : Type*} [Fintype S]
    [Fintype ι] {d : ℕ} (hd : 0 < d) (hc : Fintype.card S * d ^ r < Fintype.card ι)
    (f : S → MvPolynomial ι K) (hf : ∀ i, (f i).IsHomogeneous d) :
    ∃ α : ι → K, α ≠ 0 ∧ ∀ i, MvPolynomial.eval α (f i) = 0 := by
  classical
  obtain ⟨τ⟩ := Fintype.truncEquivFin S
  obtain ⟨σ⟩ := Fintype.truncEquivFin ι
  obtain ⟨α, hα0, hα⟩ := hK _ d _ hd hc (fun j => MvPolynomial.rename σ (f (τ.symm j)))
    (fun j => (hf _).rename_isHomogeneous)
  refine ⟨α ∘ σ, ?_, fun i => ?_⟩
  · intro hcon
    exact hα0 (funext fun j => by simpa using congrFun hcon (σ.symm j))
  · simpa [MvPolynomial.eval_rename] using hα (τ i)

/-- Evaluating `eval₂ h a f` along a retraction `g` of `h` is the evaluation of `f` at `g ∘ a`. -/
private theorem apply_eval₂_eq_eval {R S : Type*} [CommRing R] [CommRing S] {σ : Type*}
    (g : S →+* R) (h : R →+* S) (hgh : ∀ a, g (h a) = a) (a : σ → S)
    (f : MvPolynomial σ R) : g (MvPolynomial.eval₂ h a f) = MvPolynomial.eval (g ∘ a) f := by
  have hcl := MvPolynomial.eval₂_comp_left g h a f
  rwa [show g.comp h = RingHom.id R from RingHom.ext hgh, MvPolynomial.eval₂_id] at hcl

/-- The \(C_r\) property for systems of forms implies the \(C_r\) property: a single form is a
system of one form. -/
theorem isCField (hK : IsCFieldForSystems K r) : IsCField K r := by
  rintro d n ⟨hd, hdn⟩ f hf
  obtain ⟨α, hα0, hα⟩ := hK 1 d n hd (by simpa using hdn) (fun _ => f) (fun _ => hf)
  exact ⟨α, hα0, hα 0⟩

/-- The \(C_r\) property for systems of forms is invariant under isomorphism of fields. -/
theorem of_ringEquiv (hK : IsCFieldForSystems K r) {L : Type*} [Field L] (φ : K ≃+* L) :
    IsCFieldForSystems L r := by
  intro s d n hd hsn f hf
  obtain ⟨α, hα0, hα⟩ := hK s d n hd hsn (fun i => MvPolynomial.map (φ.symm : L →+* K) (f i))
    (fun i => (hf i).map (φ.symm : L →+* K))
  refine ⟨fun j => φ (α j), ?_, fun i => ?_⟩
  · intro hcon
    exact hα0 (funext fun j => φ.injective (by simpa using congrFun hcon j))
  · have hcl := apply_eval₂_eq_eval (φ : K →+* L) (φ.symm : L →+* K) (by simp) α (f i)
    have hi := hα i
    rw [MvPolynomial.eval_map] at hi
    rw [hi, map_zero] at hcl
    simpa [Function.comp_def] using hcl.symm

/-- **The \(C_r\) property for systems passes to finite extensions.**

Let `e_1, ..., e_N` be a `K`-basis of `L`. Substituting `∑ j, y_{ij} e_j` for the `i`-th
variable of a form of degree `d` over `L` and expanding each coefficient of the result in the
basis writes it as `∑ j, e_j G_j` with `G_j` forms of degree `d` in the `n * N` variables
`y_{ij}` over `K`. A common zero of all the `G_j` is a zero of the form, and it is nontrivial
over `L` because the `e_j` are linearly independent. A system of `s` forms over `L` thus
becomes a system of `s * N` forms over `K` in `n * N` variables, and `s * N * d ^ r < n * N`
follows from `s * d ^ r < n`. -/
theorem of_module_finite (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (hK : IsCFieldForSystems K r) : IsCFieldForSystems L r := by
  classical
  intro s d n hd hsn f hf
  set N := Module.finrank K L with hN
  set e : Module.Basis (Fin N) K L := Module.finBasis K L with he
  have hNpos : 0 < N := Fin.pos_iff_nonempty.mpr e.index_nonempty
  set sub : Fin n → MvPolynomial (Fin n × Fin N) L := fun i =>
    ∑ j, MvPolynomial.C (e j) * MvPolynomial.X (i, j) with hsub
  have hsubhom : ∀ i, (sub i).IsHomogeneous 1 := fun i =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _
  set F : Fin s → MvPolynomial (Fin n × Fin N) L := fun i =>
    MvPolynomial.eval₂ MvPolynomial.C sub (f i) with hF
  have hFhom : ∀ i, (F i).IsHomogeneous d := fun i => by
    have h := (hf i).eval₂ (MvPolynomial.C (σ := Fin n × Fin N) (R := L)) sub
      (fun r => MvPolynomial.isHomogeneous_C _ r) hsubhom
    simpa using h
  -- the components of `F i` in the basis `e`
  set G : Fin s × Fin N → MvPolynomial (Fin n × Fin N) K := fun p =>
    ∑ ν ∈ (F p.1).support, MvPolynomial.monomial ν (e.repr ((F p.1).coeff ν) p.2) with hG
  have hGhom : ∀ p, (G p).IsHomogeneous d := fun p =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun ν hν =>
      MvPolynomial.isHomogeneous_monomial _
        (by rw [Finsupp.degree_apply]; exact ((hFhom p.1).degree_eq_sum_deg_support hν).symm)
  have hGcoeff : ∀ p μ, (G p).coeff μ = e.repr ((F p.1).coeff μ) p.2 := by
    intro p μ
    rw [hG, MvPolynomial.coeff_sum]
    by_cases hμ : μ ∈ (F p.1).support
    · rw [Finset.sum_eq_single_of_mem μ hμ fun c _ hc => by
        simp [MvPolynomial.coeff_monomial, hc]]
      simp
    · rw [Finset.sum_eq_zero fun c hc => by
        have hcμ : c ≠ μ := fun hcm => hμ (hcm ▸ hc)
        simp [MvPolynomial.coeff_monomial, hcμ]]
      rw [MvPolynomial.notMem_support_iff.mp hμ, map_zero, Finsupp.zero_apply]
  have hdecomp : ∀ i, F i = ∑ j, MvPolynomial.C (e j) *
      MvPolynomial.map (algebraMap K L) (G (i, j)) := by
    intro i
    refine MvPolynomial.ext _ _ fun μ => ?_
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      hGcoeff]
    conv_lhs => rw [← e.sum_repr ((F i).coeff μ)]
    exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
  have hcount : Fintype.card (Fin s × Fin N) * d ^ r < Fintype.card (Fin n × Fin N) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    calc s * N * d ^ r = s * d ^ r * N := by ring
      _ < n * N := Nat.mul_lt_mul_of_pos_right hsn hNpos
  obtain ⟨y, hy0, hy⟩ := hK.exists_nonzero_common_zero hd hcount G hGhom
  refine ⟨fun i => ∑ j, y (i, j) • e j, ?_, fun i => ?_⟩
  · intro hcon
    refine hy0 (funext fun x => ?_)
    exact Fintype.linearIndependent_iff.mp e.linearIndependent
      (fun j => y (x.1, j)) (congrFun hcon x.1) x.2
  · have hcl := apply_eval₂_eq_eval (MvPolynomial.eval fun x => algebraMap K L (y x))
      (MvPolynomial.C : L →+* MvPolynomial (Fin n × Fin N) L) (by simp) sub (f i)
    have hsubeval : (fun i => MvPolynomial.eval (fun x => algebraMap K L (y x)) (sub i))
        = fun i => ∑ j, y (i, j) • e j := by
      funext i
      rw [hsub]
      simp [Algebra.smul_def, mul_comm]
    have hFzero : MvPolynomial.eval (fun x => algebraMap K L (y x)) (F i) = 0 := by
      rw [hdecomp i, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hyj := MvPolynomial.eval₂_comp (algebraMap K L) y (G (i, j))
      rw [hy (i, j), map_zero] at hyj
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_map]
      exact mul_eq_zero_of_right _ hyj.symm
    rw [hF, hcl] at hFzero
    simpa only [Function.comp_def, hsubeval] using hFzero

end IsCFieldForSystems

end
