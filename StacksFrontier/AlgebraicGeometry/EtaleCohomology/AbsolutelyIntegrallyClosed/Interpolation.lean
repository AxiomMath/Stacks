module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.MonogenicExtension
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed

/-!
# Interpolating two points of a deformed multiplicative group

Let `π` be an element of an absolutely integrally closed ring for which `1 + π` has finite
multiplicative order. Given two comaximal ideals, there is an element `s` which is zero modulo
the first and one modulo the second, while `1 + π s` is a unit.

## Main results

* `exists_isUnit_one_add_mul_of_comaximal`: for comaximal ideals `I` and `J` there is `s ∈ I`
  with `s - 1 ∈ J` and `1 + π s` a unit.

## Implementation notes

The source fixes a cyclotomic ring `A`, with `π = ζ - 1`, and writes the answer as a point of
the group scheme `G = Spec(A[s, 1/(1 + πs)])`. Such a point over `R` is exactly an element
`s : R` for which `1 + πs` is a unit. The fixed cyclotomic base is replaced by the property of
`π` used in the proof: `1 + π` has finite multiplicative order. Congruence to the distinguished
points `σ₀` and `σ₁` is expressed by membership of `s` and `s - 1` in the respective ideals.

## References

* [Stacks Project, Tag 0GY6](https://stacks.math.columbia.edu/tag/0GY6)
-/

@[expose] public section


private lemma one_add_mul_pow_identity {R : Type*} [CommRing R] (π x : R)
    (h : π * x * (x - 1) = 0) :
    ∀ n : ℕ, (1 + π * x) ^ n = 1 + x * ((1 + π) ^ n - 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      (1 + x * ((1 + π) ^ n - 1)) * (1 + π * x) =
          1 + x * ((1 + π) ^ n * (1 + π) - 1) +
            (π * x * (x - 1)) * ((1 + π) ^ n - 1) := by ring
      _ = 1 + x * ((1 + π) ^ n * (1 + π) - 1) := by rw [h, zero_mul, add_zero]

/-- Let `R` be absolutely integrally closed and `π ∈ R` with `1 + π` of finite order. For
comaximal ideals `I` and `J` of `R` there is `s ∈ I` with `s - 1 ∈ J` and `1 + π s` a unit. -/
@[stacks 0GY6]
public theorem exists_isUnit_one_add_mul_of_comaximal
    {R : Type*} [CommRing R]
    (hR : IsAbsolutelyIntegrallyClosed R) (π : R) (hπ : IsOfFinOrder (1 + π))
    (I J : Ideal R) (hIJ : I + J = ⊤) :
    ∃ s : R, IsUnit (1 + π * s) ∧ s ∈ I ∧ s - 1 ∈ J := by
  rcases subsingleton_or_nontrivial R with hsub | hnontrivial
  · let := hsub
    refine ⟨0, by simp, Ideal.zero_mem _, ?_⟩
    simp [show (1 : R) = 0 from Subsingleton.elim _ _]
  let := hnontrivial
  obtain ⟨n, hn, hπpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hπ
  obtain ⟨u, hu⟩ := hπ.isUnit
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Submodule.mem_sup.mp (show (1 : R) ∈ I ⊔ J by rw [← Ideal.add_eq_sup, hIJ]; trivial)
  have hxsub : x - 1 ∈ J := by convert J.neg_mem hy using 1 ; rw [← hxy] ; ring
  let v : R := (u⁻¹ : Rˣ)
  let a : R := 1 + π * x
  let b : R := π * x * (x - 1)
  have hcop1 : IsCoprime a (π * x) := by refine ⟨1, -1, ?_⟩; dsimp [a]; ring
  have hcop2 : IsCoprime a (x - 1) := by
    refine ⟨v, -(v * π), ?_⟩
    calc
      v * a + -(v * π) * (x - 1) = v * (a - π * (x - 1)) := by ring
      _ = v * (1 + π) := by dsimp [a]; ring
      _ = 1 := by rw [← hu]; dsimp [v]; simp
  have hcop : IsCoprime a b := by simpa [b] using hcop1.mul_right hcop2
  let K : Ideal R := Ideal.span {b}
  let q : R →+* R ⧸ K := Ideal.Quotient.mk K
  have hqb : q b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hrel : q π * q x * (q x - 1) = 0 := by
    simpa [q, b, map_mul, map_sub] using hqb
  have hπpowQ : (1 + q π) ^ n = 1 := by
    simpa [q] using congrArg q hπpow
  have hfinite : IsOfFinOrder (q a) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    have haq : q a = 1 + q π * q x := by simp [q, a]
    rw [haq, one_add_mul_pow_identity (q π) (q x) hrel n, hπpowQ]
    ring
  obtain ⟨P, hPmonic, hPinj, hunit⟩ :=
    exists_monic_adjoinRoot_isUnit_sub_mul_root a b hcop hfinite
  have hPne : P ≠ 1 := by
    intro hP
    have hzero : (0 : AdjoinRoot P) = 1 := by
      rw [hP]
      simpa using (AdjoinRoot.eval₂_root (1 : Polynomial R)).symm
    exact zero_ne_one (hPinj (by simpa using hzero))
  obtain ⟨r, hr⟩ := hR.exists_root P hPmonic (hPmonic.natDegree_pos.mpr hPne)
  let φ : AdjoinRoot P →+* R := AdjoinRoot.lift (RingHom.id R) r (by simpa using hr)
  have hunit' : IsUnit (1 + π * (x * (1 - (x - 1) * r))) := by
    convert hunit.map φ using 1 ;
      simp [φ, a, b, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_root,
        AdjoinRoot.lift_of] ; ring
  refine ⟨x * (1 - (x - 1) * r), hunit', ?_, ?_⟩
  · exact Ideal.mul_mem_right _ I hx
  · rw [show x * (1 - (x - 1) * r) - 1 = (x - 1) * (1 - x * r) by ring]
    exact Ideal.mul_mem_right _ J hxsub

