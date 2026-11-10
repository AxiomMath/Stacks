module

public import StacksFrontier.FieldTheory.PerfectCore
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separability against the perfect core, and against a base change

If every element of `perfectCore E p` is separable over `F`, then the minimal polynomial over `F`
of an element of `perfectCore E p` has its coefficients in `perfectCore F p`, and is the image of a
monic separable polynomial over `perfectCore F p`. This is `minpoly_coeff_mem_perfectCore` with
its hypothesis `Algebra.IsSeparable F E` weakened to separability of the elements of the perfect
core, which is `Stacks.EppTheorem.EppCondition` read at the residue fields.

A field generated over `L` by a `K`-embedded copy of a separable extension `E / K` is separable
over `L`. This applies to a field factor of `(L ⊗[K] K₂) ⧸ nilradical` when `K₂ / K` is
separable.

## Main results

* `minpoly_coeff_mem_perfectCore_of_forall_isSeparable`: if every element of `perfectCore E p` is
  separable over `F`, the coefficients of the minimal polynomial over `F` of an element of
  `perfectCore E p` lie in `perfectCore F p`.
* `exists_monic_separable_map_eq_minpoly_of_forall_isSeparable`: under the same hypothesis, that
  minimal polynomial is the image of a monic separable polynomial over `perfectCore F p`.
* `isSeparable_of_adjoin_range_of_isSeparable`: a field generated over `L` by a `K`-embedded copy
  of a separable `E / K` is separable over `L`.

## References

* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open Polynomial

/-! ### The perfect core of the base -/

section PerfectCore

variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [ExpChar F p]
variable {E : Type*} [Field E] [Algebra F E] [ExpChar E p]

/-- If every element of `perfectCore E p` is separable over `F`, then for `x ∈ perfectCore E p`
every coefficient of `minpoly F x` lies in `perfectCore F p`. -/
theorem minpoly_coeff_mem_perfectCore_of_forall_isSeparable
    (hsep : ∀ y ∈ perfectCore E p, IsSeparable F y)
    {x : E} (hx : x ∈ perfectCore E p) (i : ℕ) :
    (minpoly F x).coeff i ∈ perfectCore F p := by
  rw [mem_perfectCore_iff]
  intro n
  have hfrob : ∀ (k : ℕ) (a b : E), a ^ p ^ k = b ^ p ^ k → a = b := fun k a b h => by
    have hne : p ^ k ≠ 0 := (Nat.pow_pos (Fact.out : p.Prime).pos).ne'
    have h0 : (a - b) ^ p ^ k = 0 := by rw [sub_pow_expChar_pow, h, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff hne).mp h0)
  obtain ⟨y, hy⟩ := mem_perfectCore_iff.mp hx n
  have hyc : y ∈ perfectCore E p := by
    rw [mem_perfectCore_iff]
    intro m
    obtain ⟨z, hz⟩ := mem_perfectCore_iff.mp hx (n + m)
    refine ⟨z, (hfrob n y (z ^ p ^ m) ?_).symm⟩
    rw [hy, ← pow_mul, ← pow_add, add_comm m n, hz]
  refine ⟨(minpoly F y).coeff i, ?_⟩
  have h := minpoly.iterateFrobenius_of_isSeparable (F := F) (E := E) p n (hsep y hyc)
  rw [iterateFrobenius_def, hy] at h
  rw [h, Polynomial.coeff_map, iterateFrobenius_def]

/-- If every element of `perfectCore E p` is separable over `F`, then for `x ∈ perfectCore E p`
the minimal polynomial of `x` over `F` is the image of a monic separable polynomial over
`perfectCore F p`. -/
theorem exists_monic_separable_map_eq_minpoly_of_forall_isSeparable
    (hsep : ∀ y ∈ perfectCore E p, IsSeparable F y)
    {x : E} (hx : x ∈ perfectCore E p) :
    ∃ q : (perfectCore F p)[X], q.Monic ∧ q.Separable ∧
      q.map (algebraMap (perfectCore F p) F) = minpoly F x := by
  classical
  have hlifts : minpoly F x ∈ Polynomial.lifts (algebraMap (perfectCore F p) F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, minpoly_coeff_mem_perfectCore_of_forall_isSeparable hsep hx n⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts
      (minpoly.monic (IsSeparable.isIntegral (hsep x hx)))
  refine ⟨q, hqmonic, ?_, hqmap⟩
  refine (Polynomial.separable_map (algebraMap (perfectCore F p) F)).mp ?_
  rw [hqmap]; exact hsep x hx

end PerfectCore

/-! ### A field factor of a base change -/

/-- Let `E / K` be separable and let `F` be a field containing `L` and a `K`-embedded copy of `E`,
generated over `L` by that copy. Then `F / L` is separable. -/
@[ega "0 20.6.19" "(ii), case F/K algebraic"]
theorem isSeparable_of_adjoin_range_of_isSeparable
    {K L E F : Type*} [Field K] [Field L] [Field E] [Field F]
    [Algebra K L] [Algebra K E] [Algebra L F] [Algebra E F] [Algebra K F]
    [IsScalarTower K L F] [IsScalarTower K E F]
    [Algebra.IsSeparable K E]
    (hgen : Algebra.adjoin L (Set.range (algebraMap E F)) = ⊤) :
    Algebra.IsSeparable L F := by
  have hsepL : ∀ x ∈ Set.range (algebraMap E F), IsSeparable L x := by
    rintro _ ⟨e, rfl⟩
    have hK : IsSeparable K (algebraMap E F e) := by
      change (minpoly K (algebraMap E F e)).Separable
      rw [show algebraMap E F e = (IsScalarTower.toAlgHom K E F) e from rfl,
        minpoly.algHom_eq _ (algebraMap E F).injective e]
      exact Algebra.IsSeparable.isSeparable K e
    exact IsSeparable.tower_top (F := K) (L := L) hK
  have htop : IntermediateField.adjoin L (Set.range (algebraMap E F)) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := L) (E := F)
      (S := Set.range (algebraMap E F))
      (fun x hx => ((hsepL x hx).isIntegral).isAlgebraic), hgen]
    rfl
  have hsep := (IntermediateField.isSeparable_adjoin_iff_isSeparable (F := L) (E := F)
    (S := Set.range (algebraMap E F))).mpr hsepL
  rw [htop] at hsep
  exact Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl L)
    (IntermediateField.topEquiv (F := L) (E := F)).toRingEquiv (by ext x; rfl)

end
