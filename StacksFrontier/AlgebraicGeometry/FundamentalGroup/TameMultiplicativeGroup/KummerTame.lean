module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.ChartTameness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.KummerCover
public import StacksFrontier.RingTheory.DiscreteValuationRing.KummerConstantTame

/-!
# Kummer covers of `𝐆_m` are tame

The Kummer cover `Spec F[X]_X ⟶ 𝐆_{m,k}`, `x ↦ X^n`, with `F / k` finite separable and `n ≥ 1`
invertible in `k`, is tamely ramified at `0` and at `∞`: every field factor `L` over the local
ring `O` of `Spec k[x]` at `(x)` (respectively of `Spec k[y]` at `(y)`, `y = x⁻¹`) is generated
by an `n`-th root `X` (respectively `X⁻¹`) of the uniformizer and by the constant field extension
`F`, so `IsDiscreteValuationRing.isTamelyRamifiedWithRespectTo_of_pow_eq_of_sup` applies.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.isTameCover_kummerCover`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial IntermediateField

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

/-- The generators of an intermediate field, viewed inside it, generate it. -/
theorem adjoin_preimage_val_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) :
    adjoin K (Subtype.val ⁻¹' S : Set (adjoin K S)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hmap : (adjoin K (Subtype.val ⁻¹' S : Set (adjoin K S))).map (adjoin K S).val =
      adjoin K S := by
    rw [adjoin_map]
    congr 1
    rw [IntermediateField.coe_val, Set.image_preimage_eq_of_subset]
    intro s hs
    exact ⟨⟨s, subset_adjoin K S hs⟩, rfl⟩
  have hx : (x : L) ∈ (adjoin K (Subtype.val ⁻¹' S : Set (adjoin K S))).map (adjoin K S).val := by
    rw [hmap]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← Subtype.ext hyx]

section DVR

variable {O K L : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [Algebra O L] [IsScalarTower O K L]

/-- The field generated over `K` by the image of a finite separable extension `F / k`, with
`k → O`, is unramified with respect to `O`. -/
theorem isUnramifiedWithRespectTo_adjoin_range {k F : Type*} [Field k] [Field F] [Algebra k F]
    [FiniteDimensional k F] [Algebra.IsSeparable k F] (ι : k →+* O) (ψ : F →+* L)
    (hψ : ∀ a : k, ψ (algebraMap k F a) = algebraMap O L (ι a)) :
    IsDiscreteValuationRing.IsUnramifiedWithRespectTo O K (adjoin K (Set.range ψ)) := by
  set E := adjoin K (Set.range ψ)
  let : Algebra k O := ι.toAlgebra
  let : Algebra k E := ((algebraMap O E).comp ι).toAlgebra
  have : IsScalarTower k O E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ψE : F →ₐ[k] E :=
    { toFun := fun a ↦ ⟨ψ a, subset_adjoin K _ ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun a b ↦ Subtype.ext (map_mul ψ a b)
      map_zero' := Subtype.ext (map_zero ψ)
      map_add' := fun a b ↦ Subtype.ext (map_add ψ a b)
      commutes' := fun a ↦ Subtype.ext (hψ a) }
  refine IsDiscreteValuationRing.isUnramifiedWithRespectTo_of_adjoin_range_eq_top ψE ?_
  rw [← adjoin_preimage_val_eq_top (K := K) (Set.range ψ)]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

end DVR

variable {k : Type u} [Field k]

/-- A ring map out of `k[x]_x` which sends `k[x]` into the image of a field `K` lands in that
image. -/
theorem mem_bot_of_comp_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (g : Ring k →+* L)
    (hg : ∀ p : k[X], g (algebraMap k[X] (Ring k) p) ∈ (⊥ : IntermediateField K L))
    (z : Ring k) : g z ∈ (⊥ : IntermediateField K L) := by
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (X : k[X])) z
  have h1 : g (IsLocalization.mk' (Ring k) p s) * g (algebraMap k[X] (Ring k) s) =
      g (algebraMap k[X] (Ring k) p) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  have hs : g (algebraMap k[X] (Ring k) s) ≠ 0 :=
    ((IsLocalization.map_units (Ring k) s).map g).ne_zero
  rw [(eq_div_iff hs).mpr h1]
  exact div_mem (hg p) (hg s)

section Kummer

variable (k) (F : Type u) [Field F] [Algebra k F] [FiniteDimensional k F]
  [Algebra.IsSeparable k F] (n : ℕ)

variable {k F n} in
/-- **The field factors of a Kummer cover are tame.** A field `L` over the local ring at `(x)`,
generated over `K` by the image of `ψ : F[X]_X → L`, where `θ = ψ(X)^{±1}` is an `n`-th root of the
uniformizer and `ψ` maps the Kummer structure into `K`, is tamely ramified. -/
theorem isTamelyRamifiedWithRespectTo_of_kummer (hn : IsUnit (n : k)) (hn0 : 0 < n)
    (q : Spec (CommRingCat.of k[X])) (hq : (X : k[X]) ∈ q.asIdeal)
    [IsDomain (stalkAt k q)] [IsDiscreteValuationRing (stalkAt k q)]
    (K L : Type u) [Field K] [Field L] [Algebra (stalkAt k q) K]
    [IsFractionRing (stalkAt k q) K] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Algebra (stalkAt k q) L] [IsScalarTower (stalkAt k q) K L]
    (ψ : Ring F →+* L) (θ : L)
    (hθn : θ ^ n = algebraMap (stalkAt k q) L (algebraMap k[X] (stalkAt k q) X))
    (hθ : θ = ψ (coord F) ∨ θ * ψ (coord F) = 1)
    (hφ : ∀ z : Ring k, ψ (kummerMap k F n z) ∈ (⊥ : IntermediateField K L))
    (hconst : ∀ a : k, ψ (algebraMap F (Ring F) (algebraMap k F a)) =
      algebraMap (stalkAt k q) L (algebraMap k[X] (stalkAt k q) (C a)))
    (hgen : Algebra.adjoin K (Set.range ψ) = ⊤) :
    IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo (stalkAt k q) K L := by
  set π : (stalkAt k q) := algebraMap k[X] (stalkAt k q) X
  -- `q = (x)` and `π` is a uniformizer
  have hqX : q.asIdeal = Ideal.span {(X : k[X])} := by
    have hmax : (Ideal.span {(X : k[X])}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
    exact (hmax.eq_of_le q.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hq)).symm
  have hπ0 : π ≠ 0 := by
    intro h0
    exact X_ne_zero (IsLocalization.injective (stalkAt k q)
      (Ideal.primeCompl_le_nonZeroDivisors q.asIdeal) (h0.trans (map_zero _).symm))
  have hmaxO : IsLocalRing.maximalIdeal (stalkAt k q) = Ideal.span {π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (stalkAt k q), hqX, Ideal.map_span,
      Set.image_singleton]
  have hπ : Irreducible π := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π hπ0 hmaxO
  have hunit : IsUnit (n : IsLocalRing.ResidueField (stalkAt k q)) := by
    simpa only [map_natCast] using
      ((hn.map (algebraMap k k[X])).map (algebraMap k[X] (stalkAt k q))).map
        (IsLocalRing.residue (stalkAt k q))
  let ψF : F →+* L := ψ.comp (algebraMap F (Ring F))
  set E := IntermediateField.adjoin K (Set.range ψF)
  have hE := isUnramifiedWithRespectTo_adjoin_range (K := K)
    ((algebraMap k[X] (stalkAt k q)).comp C) ψF hconst
  have hgen' : K⟮θ⟯ ⊔ E = ⊤ := by
    set M := K⟮θ⟯ ⊔ E
    have hθM : θ ∈ M := (le_sup_left : K⟮θ⟯ ≤ M) (mem_adjoin_simple_self K θ)
    let := (kummerMap k F n).toAlgebra
    let S : Subalgebra (Ring k) (Ring F) :=
      { M.toSubring.comap ψ with
        algebraMap_mem' := fun r ↦ (bot_le : (⊥ : IntermediateField K L) ≤ M) (hφ r) }
    have hS : Algebra.adjoin (Ring k) ({coord F} ∪ Set.range
        (fun i ↦ algebraMap F (Ring F) (Module.finBasis k F i))) ≤ S := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | ⟨i, rfl⟩)
      · rw [Set.mem_singleton_iff.mp hz]
        change ψ (coord F) ∈ M
        rcases hθ with h | h
        · rw [← h]
          exact hθM
        · rw [eq_inv_of_mul_eq_one_right h]
          exact inv_mem hθM
      · change ψ (algebraMap F (Ring F) _) ∈ M
        exact (le_sup_right : E ≤ M) (subset_adjoin K _ ⟨_, rfl⟩)
    rw [adjoin_coord_basis_eq_top k F n hn0] at hS
    have hrange : Algebra.adjoin K (Set.range ψ) ≤ M.toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact hS (Algebra.mem_top : z ∈ (⊤ : Subalgebra (Ring k) (Ring F)))
    rw [hgen, top_le_iff] at hrange
    exact IntermediateField.toSubalgebra_injective
      (hrange.trans IntermediateField.top_toSubalgebra.symm)
  exact IsDiscreteValuationRing.isTamelyRamifiedWithRespectTo_of_pow_eq_of_sup hπ hn0 hunit hθn E
    hE hgen'

omit [FiniteDimensional k F] [Algebra.IsSeparable k F] in
/-- The Kummer map sends the constant `a ∈ k` of `k[x]_x` to the constant `a ∈ F` of `F[X]_X`. -/
theorem kummerMap_const (a : k) :
    algebraMap F (Ring F) (algebraMap k F a) =
      kummerMap k F n (algebraMap k[X] (Ring k) (C a)) := by
  rw [kummerMap_C, IsScalarTower.algebraMap_apply F F[X] (Ring F), ← C_eq_algebraMap]

omit [FiniteDimensional k F] [Algebra.IsSeparable k F] in
/-- The Kummer map sends `x⁻¹ ∈ k[x]_x` to `X⁻ⁿ ∈ F[X]_X`. -/
theorem kummerMap_invSelf :
    kummerMap k F n (IsLocalization.Away.invSelf (X : k[X])) =
      ((isUnit_coord F).unit⁻¹ : (Ring F)ˣ).1 ^ n := by
  have h1 : kummerMap k F n (IsLocalization.Away.invSelf (X : k[X])) * coord F ^ n = 1 := by
    rw [← kummerMap_coord k F n, ← map_mul, mul_comm, coord, IsLocalization.Away.mul_invSelf,
      map_one]
  have h2 : ((isUnit_coord F).unit⁻¹ : (Ring F)ˣ).1 ^ n * coord F ^ n = 1 := by
    rw [← mul_pow, (isUnit_coord F).val_inv_mul, one_pow]
  exact ((isUnit_coord F).pow n).mul_left_inj.mp (h1.trans h2.symm)

variable {k F n} in
/-- If a ring homomorphism `g : k[x]_x → L` agrees on `k[x]` with the composite of the
localization `k[x] → stalkAt k q` and the structure map `stalkAt k q → L`, where `L / K` is an
extension over `stalkAt k q`, then every value of `g` lies in `⊥ : IntermediateField K L`. -/
theorem mem_bot_of_hψ {K L : Type u} [Field K] [Field L] [Algebra K L]
    (q : Spec (CommRingCat.of k[X])) [Algebra (stalkAt k q) K] [Algebra (stalkAt k q) L]
    [IsScalarTower (stalkAt k q) K L] (g : Ring k →+* L)
    (hg : ∀ r : k[X], g (algebraMap k[X] (Ring k) r) =
      algebraMap (stalkAt k q) L (algebraMap k[X] (stalkAt k q) r)) (z : Ring k) :
    g z ∈ (⊥ : IntermediateField K L) := by
  refine mem_bot_of_comp_algebraMap g (fun p ↦ ?_) z
  rw [hg, IsScalarTower.algebraMap_apply (stalkAt k q) K L]
  exact IntermediateField.algebraMap_mem _ _

/-- **Kummer covers are tame** at `0` and at `∞`. -/
theorem isTameCover_kummerCover (hn : IsUnit (n : k)) (hn0 : 0 < n) :
    IsTameCover (kummerCover k F n hn hn0) := by
  constructor
  · refine isTamelyRamifiedInCodimensionOne_chartZero_of (Ring F) (kummerMap k F n) ?_
    intro q hq _ _ K L _ _ _ _ _ _ _ _ _ ψ hψ hgen
    refine isTamelyRamifiedWithRespectTo_of_kummer hn hn0 q hq K L ψ (ψ (coord F)) ?_ (Or.inl rfl)
      (mem_bot_of_hψ q (ψ.comp (kummerMap k F n)) hψ)
      (fun a ↦ (congrArg ψ (kummerMap_const k F n a)).trans (hψ _)) hgen
    rw [← map_pow, ← kummerMap_coord k F n]
    exact hψ X
  · change Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartInfty k)
      (Spec.map (CommRingCat.ofHom (kummerMap k F n)))
    rw [isTamelyRamifiedInCodimensionOne_chartInfty_iff]
    refine isTamelyRamifiedInCodimensionOne_chartZero_of (Ring F)
      ((kummerMap k F n).comp (inversionHom k)) ?_
    intro q hq _ _ K L _ _ _ _ _ _ _ _ _ ψ hψ hgen
    have hinvX : inversionHom k (algebraMap k[X] (Ring k) X) =
        IsLocalization.Away.invSelf (X : k[X]) := by
      rw [inversionHom_algebraMap, inverseCoordinate, coe_eval₂RingHom, eval₂_X]
    refine isTamelyRamifiedWithRespectTo_of_kummer hn hn0 q hq K L ψ
      (ψ ((isUnit_coord F).unit⁻¹ : (Ring F)ˣ).1) ?_ (Or.inr ?_) (fun z ↦ ?_) (fun a ↦ ?_) hgen
    · rw [← map_pow, ← kummerMap_invSelf k F n, ← hinvX]
      exact hψ X
    · rw [← map_mul, (isUnit_coord F).val_inv_mul, map_one]
    · simpa only [RingHom.comp_apply, inversionHom_inversionHom] using
        mem_bot_of_hψ (K := K) q (ψ.comp ((kummerMap k F n).comp (inversionHom k))) hψ
          (inversionHom k z)
    · rw [kummerMap_const k F n]
      have := hψ (C a)
      rwa [RingHom.comp_apply, algebraMap_C k a, inversionHom_algebraMap_k, ← algebraMap_C k a]
        at this

end Kummer

end AlgebraicGeometry.TameMultiplicativeGroup

end
