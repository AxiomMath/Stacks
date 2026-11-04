module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.RingTheory.NoetherNormalization.Basic

/-!
# Cohomological dimension of a punctured henselian local domain

Let `K` be a field and `O` a henselian local domain over `K` with separably closed residue field,
of transcendence degree at most `a + 1 + m` over `K`, containing a field `F ⊇ K` of
transcendence degree `a`. For a nonzero `f` in the maximal ideal of `O`, the localization `O_f`
has cohomological dimension at most `m + 1`, provided Stacks 0F0V is known in dimension at most
`m`. This is the commutative algebra of Interlude I in the proof of Stacks 0F0V, where `O` is a
strict henselization of a smooth variety of dimension `d = a + 1 + m` at a point whose residue
field has transcendence degree `a`, and `f` is a local equation of a divisor.

The argument is the source's. A separable closure `L₀` of `F` maps into `O`, `O` being henselian
with separably closed residue field (the universal property of a strict henselization, Stacks
04GU). The rational function field `E = L₀(f)` maps into `O_f`: a nonzero polynomial `p` in `f`
is `f^k` times a polynomial with nonzero constant term, whose value is a unit of the local ring
`O`. Then `cd(E) ≤ 1` (Stacks 0F0T for transcendence degree one, `L₀` being separably closed),
`O_f` is the directed union of its finitely generated `E`-subalgebras, each of dimension at most
`trdeg_E(O_f) ≤ m`, and Stacks 0F0R bounds `cd(O_f)` by the supremum of their cohomological
dimensions.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_away_le_of_isSepClosed`: the bound
  when `F = L₀` is separably closed.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_away_le`: the bound above.

## Implementation notes

The induction hypothesis `hIH` is Stacks 0F0V in dimension at most `m`, in the form of
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_add_of_topologicalKrullDim_le`.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 0F0T](https://stacks.math.columbia.edu/tag/0F0T)
* [Stacks Project, Tag 0F0R](https://stacks.math.columbia.edu/tag/0F0R)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial

universe u

namespace AlgebraicGeometry

namespace Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- A nonzero polynomial over a field `L₀ ⊆ O`, evaluated at an element `f` of the maximal ideal
of the local ring `O`, is a power of `f` times a unit. -/
private theorem exists_eval₂_eq_pow_mul_unit {L₀ O : Type u} [Field L₀] [CommRing O]
    [IsLocalRing O] (ε : L₀ →+* O) (f : O) (hf : f ∈ maximalIdeal O) (p : L₀[X])
    (hp : p ≠ 0) : ∃ (k : ℕ) (v : O), IsUnit v ∧ p.eval₂ ε f = f ^ k * v := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  rw [map_zero, sub_zero, X_dvd_iff] at hq
  refine ⟨p.rootMultiplicity 0, q.eval₂ ε f, ?_, ?_⟩
  · by_contra hu
    have hres : IsLocalRing.residue O (q.eval₂ ε f) = IsLocalRing.residue O (ε (q.coeff 0)) := by
      rw [Polynomial.hom_eval₂, ((residue_eq_zero_iff f).2 hf), eval₂_at_zero]
      rfl
    have hc : IsLocalRing.residue O (ε (q.coeff 0)) = 0 := by
      rw [← hres]
      exact (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)
    exact (residue_ne_zero_iff_isUnit _).2 ((Units.mk0 _ hq).isUnit.map ε) hc
  · conv_lhs => rw [hpq]
    rw [map_zero, sub_zero, eval₂_mul, eval₂_X_pow]

/-- A nonzero polynomial over `L₀ ⊆ O`, evaluated at the image of an element `f` of the maximal
ideal of the local ring `O`, is a unit of `O_f`. -/
private theorem isUnit_eval₂_away {L₀ O : Type u} [Field L₀] [CommRing O] [IsLocalRing O]
    [Algebra L₀ O] {f : O} (hf : f ∈ maximalIdeal O) {p : L₀[X]} (hp : p ≠ 0) :
    IsUnit (p.eval₂ (algebraMap L₀ (Localization.Away f))
      (algebraMap O (Localization.Away f) f)) := by
  obtain ⟨k, v, hv, hpv⟩ := exists_eval₂_eq_pow_mul_unit (algebraMap L₀ O) f hf p hp
  have h : p.eval₂ (algebraMap L₀ (Localization.Away f)) (algebraMap O (Localization.Away f) f) =
      algebraMap O (Localization.Away f) (p.eval₂ (algebraMap L₀ O) f) := by
    rw [Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq]
  rw [h, hpv, map_mul, map_pow]
  exact ((IsLocalization.Away.algebraMap_isUnit f).pow k).mul (hv.map _)

/-- An algebra over a field, which is a nontrivial ring, is a faithful module. -/
private theorem faithfulSMul_of_field (K A : Type u) [Field K] [Semiring A] [Nontrivial A]
    [Algebra K A] : FaithfulSMul K A :=
  (faithfulSMul_iff_algebraMap_injective K A).2 (algebraMap K A).injective

/-- The field of rational functions in one variable has transcendence degree one. -/
private theorem trdeg_ratFunc_eq_one (L₀ : Type u) [Field L₀] :
    Algebra.trdeg L₀ (RatFunc L₀) = 1 := by
  have : Algebra.IsAlgebraic L₀[X] (RatFunc L₀) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors L₀[X])
  rw [← trdeg_add_eq L₀ L₀[X] (A := RatFunc L₀), Polynomial.trdeg_of_isDomain,
    trdeg_eq_zero, add_zero]

/-- The field of rational functions in one variable over a separably closed field has étale
cohomological dimension at most one. -/
public theorem etaleCohomologicalDimension_spec_ratFunc_le_one (L₀ : Type u) [Field L₀]
    [IsSepClosed L₀] : etaleCohomologicalDimension (Spec (.of (RatFunc L₀))) ≤ 1 := by
  refine (etaleCohomologicalDimension_spec_le_one_add_of_trdeg_le_one
    (trdeg_ratFunc_eq_one L₀).le).trans ?_
  have h0 := etaleCohomologicalDimension_spec_le_zero_of_isSepClosed L₀
  calc 1 + etaleCohomologicalDimension (Spec (.of L₀)) ≤ 1 + 0 := by gcongr
    _ = 1 := add_zero 1

/-- The spectrum of a nontrivial algebra of finite type over a field `E` has dimension at most
its transcendence degree over `E`. -/
public theorem topologicalKrullDim_spec_le_of_trdeg_le {E A : Type u} [Field E] [CommRing A]
    [Nontrivial A] [Algebra E A] [Algebra.FiniteType E A] {m : ℕ}
    (hA : Algebra.trdeg E A ≤ m) : topologicalKrullDim (Spec (.of A)) ≤ m := by
  rw [show topologicalKrullDim (Spec (.of A)) = ringKrullDim A from
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A]
  obtain ⟨k, φ, hk, hφ, -⟩ := noether_normalization_global (k := E) (T := A)
  have h := lift_trdeg_le_of_injective φ hφ
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast,
    Cardinal.lift_id] at h
  rw [← hk]
  exact_mod_cast (Nat.cast_le.mp (h.trans hA) : k ≤ m)

/-- **Cohomological dimension of a punctured local domain over a separably closed field.** Let
`L₀` be a separably closed field and `O` a local domain over `L₀` with `trdeg_{L₀}(O) ≤ 1 + m`. For
a nonzero `f` in the maximal ideal of `O`, `cd(Spec O_f) ≤ m + 1`, given Stacks 0F0V for affine
schemes of finite type and dimension at most `m` over fields (`hIH`). The field `E = L₀(f)` maps
into `O_f`, has `cd(E) ≤ 1` (Stacks 0F0T for transcendence degree one) and `trdeg_E(O_f) ≤ m`;
`O_f` is the directed union of its finitely generated `E`-subalgebras, each of dimension at most
`m`, and Stacks 0F0R bounds `cd(O_f)` by the supremum of their cohomological dimensions. -/
public theorem etaleCohomologicalDimension_spec_away_le_of_isSepClosed
    {L₀ O : Type u} [Field L₀] [IsSepClosed L₀] [CommRing O] [IsDomain O] [IsLocalRing O]
    [Algebra L₀ O] (m : ℕ) (hO : Algebra.trdeg L₀ O ≤ 1 + m)
    (f : O) (hf : f ∈ maximalIdeal O) (hf0 : f ≠ 0)
    (hIH : ∀ ⦃E : Type u⦄ [Field E] ⦃Y : Scheme.{u}⦄ [IsAffine Y] (g : Y ⟶ Spec (.of E))
      [LocallyOfFiniteType g], topologicalKrullDim Y ≤ m →
        etaleCohomologicalDimension Y ≤ m + etaleCohomologicalDimension (Spec (.of E))) :
    etaleCohomologicalDimension (Spec (.of (Localization.Away f))) ≤ m + 1 := by
  classical
  let Of := Localization.Away f
  let E := RatFunc L₀
  have hmem : (Submonoid.powers f) ≤ nonZeroDivisors O :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  have : IsDomain Of :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (S := Of) (M := Submonoid.powers f) hmem
  let θ : L₀[X] →+* Of := Polynomial.eval₂RingHom (algebraMap L₀ Of) (algebraMap O Of f)
  have hθ : ∀ p : nonZeroDivisors L₀[X], IsUnit (θ p) := fun p =>
    isUnit_eval₂_away hf (nonZeroDivisors.ne_zero p.2)
  let ι : E →+* Of := IsLocalization.lift (M := nonZeroDivisors L₀[X]) (S := E) hθ
  let : Algebra E Of := ι.toAlgebra
  have hιC : ∀ c : L₀, ι (algebraMap L₀ E c) = algebraMap L₀ Of c := by
    intro c
    change IsLocalization.lift hθ (algebraMap L₀[X] E (Polynomial.C c)) = _
    rw [IsLocalization.lift_eq]
    exact Polynomial.eval₂_C _ _
  have : IsScalarTower L₀ E Of := .of_algebraMap_eq fun c => (hιC c).symm
  have : FaithfulSMul O Of := (faithfulSMul_iff_algebraMap_injective O Of).2
    (IsLocalization.injective Of hmem)
  have : FaithfulSMul L₀ O := faithfulSMul_of_field L₀ O
  have : FaithfulSMul E Of := faithfulSMul_of_field E Of
  have : FaithfulSMul L₀ E := faithfulSMul_of_field L₀ E
  have htrOf : Algebra.trdeg L₀ Of = Algebra.trdeg L₀ O := by
    have h0 : Algebra.trdeg O Of = 0 := by
      have := IsLocalization.isAlgebraic (R := O) (S := Of) (Submonoid.powers f)
      exact trdeg_eq_zero
    rw [← trdeg_add_eq (A := Of) L₀ O, h0, add_zero]
  have hEOf : Algebra.trdeg E Of ≤ m := by
    have h := trdeg_add_le (R := L₀) (S := E) (A := Of)
    rw [htrOf, trdeg_ratFunc_eq_one] at h
    have h' : Algebra.trdeg E Of + 1 ≤ (m : Cardinal) + 1 := by
      rw [add_comm, add_comm (m : Cardinal)]
      exact h.trans hO
    exact Cardinal.add_one_le_add_one_iff.1 h'
  refine (etaleCohomologicalDimension_spec_le_iSup_adjoin E Of).trans (iSup_le fun s => ?_)
  let A := Algebra.adjoin E ((s.unop : Finset Of) : Set Of)
  have : Algebra.FiniteType E A :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s.unop)
  have hg : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap E A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact (hIH (Spec.map (CommRingCat.ofHom (algebraMap E A)))
    (topologicalKrullDim_spec_le_of_trdeg_le
      ((trdeg_le_of_injective A.val Subtype.val_injective).trans hEOf))).trans
    (add_le_add le_rfl (etaleCohomologicalDimension_spec_ratFunc_le_one L₀))

/-- **Cohomological dimension of a punctured henselian local domain** (Interlude I of the proof
of Stacks 0F0V). Let `K` be a field, `O` a henselian local domain over `K` with separably closed
residue field, `F ⊇ K` a field with `trdeg_K(F) ≥ a` mapping into `O` over `K`, and suppose
`trdeg_K(O) ≤ a + 1 + m`. For a nonzero `f` in the maximal ideal of `O`,
`cd(Spec O_f) ≤ m + 1`, given Stacks 0F0V for affine schemes of finite type and dimension at most
`m` over fields (`hIH`).

A separable closure `L₀` of `F` maps into `O`
(`AlgebraicGeometry.exists_algHom_separableClosure_of_henselianLocalRing`), and
`trdeg_{L₀}(O) = trdeg_F(O) ≤ 1 + m`, so this is
`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_away_le_of_isSepClosed`. -/
public theorem etaleCohomologicalDimension_spec_away_le
    {K O F : Type u} [Field K] [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianLocalRing O]
    [IsSepClosed (ResidueField O)] [Algebra K O] [Field F] [Algebra K F] (ψ : F →ₐ[K] O)
    (a m : ℕ) (ha : (a : Cardinal) ≤ Algebra.trdeg K F) (hO : Algebra.trdeg K O ≤ a + 1 + m)
    (f : O) (hf : f ∈ maximalIdeal O) (hf0 : f ≠ 0)
    (hIH : ∀ ⦃E : Type u⦄ [Field E] ⦃Y : Scheme.{u}⦄ [IsAffine Y] (g : Y ⟶ Spec (.of E))
      [LocallyOfFiniteType g], topologicalKrullDim Y ≤ m →
        etaleCohomologicalDimension Y ≤ m + etaleCohomologicalDimension (Spec (.of E))) :
    etaleCohomologicalDimension (Spec (.of (Localization.Away f))) ≤ m + 1 := by
  let : Algebra F O := ψ.toRingHom.toAlgebra
  have : IsScalarTower K F O := .of_algebraMap_eq fun k => (ψ.commutes k).symm
  have : FaithfulSMul K F := faithfulSMul_of_field K F
  have : FaithfulSMul F O := faithfulSMul_of_field F O
  have hFO : Algebra.trdeg F O ≤ 1 + m := by
    refine (Cardinal.add_nat_le_add_nat_iff a).1 ?_
    rw [add_comm, add_comm _ (a : Cardinal), ← add_assoc]
    exact ((add_le_add ha le_rfl).trans (trdeg_add_le (R := K) (S := F) (A := O))).trans hO
  obtain ⟨ε⟩ := exists_algHom_separableClosure_of_henselianLocalRing F O
  let L₀ := SeparableClosure F
  let : Algebra L₀ O := ε.toRingHom.toAlgebra
  have : IsScalarTower F L₀ O := .of_algebraMap_eq fun c => (ε.commutes c).symm
  have : FaithfulSMul F L₀ := faithfulSMul_of_field F L₀
  have : FaithfulSMul L₀ O := faithfulSMul_of_field L₀ O
  have hL₀O : Algebra.trdeg L₀ O ≤ 1 + m := by
    have h := trdeg_add_eq (A := O) F L₀
    rw [trdeg_eq_zero, zero_add] at h
    rwa [h]
  exact etaleCohomologicalDimension_spec_away_le_of_isSepClosed m hL₀O f hf hf0 hIH

end Scheme

end AlgebraicGeometry

end
