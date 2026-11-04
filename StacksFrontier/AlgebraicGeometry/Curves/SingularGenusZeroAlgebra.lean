module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# A finite extension of a local ring by a field of degree `n` has cokernel of dimension `≥ n / 2`

Let `k` be a field, `A` a local `k`-algebra with residue field `κ` finite over `k`, and `B` a
finite `A`-algebra containing a field `k'` which is a finite extension of `k`, of degree `n`.
Write `B / A` for the cokernel of `A → B`, and suppose it finite-dimensional over `k` and
nonzero. This file proves the two dimension counts that the proof of [Stacks, Tag 0DJB] runs at
the singular points of a genus-zero curve, where `A = 𝒪_{X, x}`, `B = (ν_* 𝒪_{X'})_x` and
`k' = H⁰(X', 𝒪_{X'})`:

1. `n ≤ 2 dim_k (B / A)`;
2. if `dim_k (B / A) = n - 1`, then `κ = k`, the ideal `𝔪_A B` is maximal with `k' ≅ B / 𝔪_A B`,
   and `𝔪_A B` lies in the image of `A`.

## The argument

Write `e = dim_k κ` and `D = dim_k (B / 𝔪_A B)`. Three facts give everything.

* A nonzero `A`-module of finite dimension over `k` has dimension at least `e`: it contains a
  cyclic submodule `A / I` with `I` proper, hence `I ⊆ 𝔪_A`, which surjects onto `κ`
  (`Stacks.Curves.finrank_residueField_le`).
* `B / 𝔪_A B` is nonzero by Nakayama and is a `k'`-vector space, so `n` divides `D` and `n ≤ D`.
* The image `W` of `A` in `B / 𝔪_A B` is `A / 𝔪_A = κ`, and `B / A` surjects onto
  `(B / 𝔪_A B) / W` with kernel the image `K` of `𝔪_A B`, an `A`-submodule of `B / A`. Hence
  `dim_k (B / A) = dim_k K + D - e`.

For (1): `n ≤ D = dim_k (B / A) + e - dim_k K ≤ dim_k (B / A) + e ≤ 2 dim_k (B / A)`, the last
step by the first fact applied to `B / A`. For (2): then `D ≤ 2n - 2 < 2n`, so `D = n` and
`B / 𝔪_A B ≅ k'`; and `dim_k K = e - 1 < e` forces `K = 0` by the first fact, whence `e = 1`.

## Implementation notes

The source's proof of [Stacks, Tag 0DJB] bounds the dimension of the image of `𝒪_X(U)` in
`End_k(V)`, `V = H⁰(X, 𝒬)` of dimension `n - 1`, by `n - 1` as "a property of commutative
subalgebras of matrix algebras". That property is false in general (Schur's bound for a
commutative subalgebra of `M_m(k)` is `⌊m² / 4⌋ + 1`), and the conductor is not used here at all:
the argument above replaces it, using only that `B / A` is a module over the local ring `A` and
that `B / 𝔪_A B` is a vector space over `k'`.

## Main results

* `Stacks.Curves.finrank_residueField_le`: a nonzero module over a local `k`-algebra, of finite
  dimension over `k`, has dimension at least that of the residue field.
* `Stacks.Curves.finrank_le_two_mul_finrank_quotient_range`: assertion (1).
* `Stacks.Curves.finrank_residueField_eq_one_of_finrank_quotient_range_add_one_eq`:
  assertion (2).

## References

* [Stacks Project, Tag 0DJB](https://stacks.math.columbia.edu/tag/0DJB)
-/

@[expose] public noncomputable section

universe u

open IsLocalRing

namespace Stacks.Curves

/-- **A nonzero module over a local `k`-algebra has `k`-dimension at least that of the residue
field.** A nonzero element `m` spans a cyclic submodule `A / I` with `I` proper, hence contained
in the maximal ideal, so that `A / I` surjects onto the residue field. -/
theorem finrank_residueField_le (k : Type u) {A M : Type u} [Field k] [CommRing A]
    [IsLocalRing A] [Algebra k A] [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] [Nontrivial M] :
    Module.finrank k (ResidueField A) ≤ Module.finrank k M := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let φ : A →ₗ[A] M := LinearMap.toSpanSingleton A M m
  have hker : LinearMap.ker φ ≤ maximalIdeal A := by
    refine le_maximalIdeal fun h => hm ?_
    simpa [φ] using (Ideal.eq_top_iff_one _).mp h
  let e : (A ⧸ LinearMap.ker φ) ≃ₗ[k] LinearMap.range φ :=
    φ.quotKerEquivRange.restrictScalars k
  have : FiniteDimensional k (LinearMap.range φ) :=
    FiniteDimensional.finiteDimensional_submodule ((LinearMap.range φ).restrictScalars k)
  have : FiniteDimensional k (A ⧸ LinearMap.ker φ) := e.symm.finiteDimensional
  let g : (A ⧸ LinearMap.ker φ) →ₐ[k] ResidueField A :=
    Ideal.Quotient.factorₐ k (I := (LinearMap.ker φ : Ideal A)) hker
  calc Module.finrank k (ResidueField A)
      ≤ Module.finrank k (A ⧸ LinearMap.ker φ) :=
        LinearMap.finrank_le_finrank_of_surjective (f := g.toLinearMap)
          (Ideal.Quotient.factor_surjective hker)
    _ = Module.finrank k (LinearMap.range φ) := e.finrank_eq
    _ ≤ Module.finrank k M := Submodule.finrank_le ((LinearMap.range φ).restrictScalars k)

/-- The residue field of `A` has `k`-dimension at most that of a nonzero cokernel `B / A`. -/
private theorem finrank_residueField_le_finrank_quotient_range {k A B : Type u} [Field k]
    [CommRing A] [IsLocalRing A] [Algebra k A] [CommRing B] [Algebra A B] [Algebra k B]
    [IsScalarTower k A B]
    (hR : LinearMap.range (Algebra.linearMap A B) ≠ ⊤)
    [FiniteDimensional k (B ⧸ LinearMap.range (Algebra.linearMap A B))] :
    Module.finrank k (ResidueField A) ≤
      Module.finrank k (B ⧸ LinearMap.range (Algebra.linearMap A B)) := by
  have : Nontrivial (B ⧸ LinearMap.range (Algebra.linearMap A B)) :=
    Submodule.Quotient.nontrivial_iff.mpr hR
  exact finrank_residueField_le k (A := A) (M := B ⧸ LinearMap.range (Algebra.linearMap A B))

section Cokernel

variable {k k' A B : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [CommRing A] [IsLocalRing A] [Algebra k A] [FiniteDimensional k (ResidueField A)]
  [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B] [Algebra k' B]
  [IsScalarTower k k' B] [Module.Finite A B]

/-- The extension of the maximal ideal of `A` to `B` is a proper ideal when `B` is a nonzero finite
`A`-module: this is Nakayama's lemma. -/
private theorem map_maximalIdeal_ne_top [Nontrivial B] :
    Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊤ := by
  intro h
  have hle : (⊤ : Submodule A B) ≤ maximalIdeal A • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map, h]
    exact le_rfl
  exact top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top hle
    (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)

/-- The quotient of `B` by the extension of the maximal ideal of `A` is finite-dimensional over
`k`. -/
private theorem finiteDimensional_quotient_map_maximalIdeal :
    FiniteDimensional k (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := by
  set mB := Ideal.map (algebraMap A B) (maximalIdeal A)
  have : Module.Finite A (B ⧸ mB) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A mB).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ mB) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ maximalIdeal A) (B ⧸ mB)
  have : FiniteDimensional k (A ⧸ maximalIdeal A) :=
    inferInstanceAs (FiniteDimensional k (ResidueField A))
  have : IsScalarTower k (A ⧸ maximalIdeal A) (B ⧸ mB) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k (B ⧸ mB) c = Ideal.Quotient.mk mB (algebraMap A B (algebraMap k A c))
      rw [← IsScalarTower.algebraMap_apply]
      rfl
  exact Module.Finite.trans (A ⧸ maximalIdeal A) (B ⧸ mB)

/-- The kernel of `A → B / 𝔪_A B` is the maximal ideal of `A`. -/
private theorem ker_linearMap_quotient_map_maximalIdeal [Nontrivial B] :
    LinearMap.ker (Algebra.linearMap A (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) =
      maximalIdeal A := by
  set mB := Ideal.map (algebraMap A B) (maximalIdeal A)
  have : Nontrivial (B ⧸ mB) := Ideal.Quotient.nontrivial_iff.mpr map_maximalIdeal_ne_top
  have hle : maximalIdeal A ≤ LinearMap.ker (Algebra.linearMap A (B ⧸ mB)) := fun a ha => by
    change algebraMap A (B ⧸ mB) a = 0
    rw [IsScalarTower.algebraMap_apply A B (B ⧸ mB)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  have hne : (LinearMap.ker (Algebra.linearMap A (B ⧸ mB)) : Ideal A) ≠ ⊤ := fun h =>
    one_ne_zero (by simpa using (Ideal.eq_top_iff_one _).mp h : (1 : B ⧸ mB) = 0)
  exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hne hle).symm

/-- The data of the dimension count at once: writing `e = dim_k κ`, `D = dim_k (B / 𝔪_A B)`,
`d = dim_k (B / A)` and `K` for the image of `𝔪_A B` in `B / A`, one has `n ∣ D`, `n ≤ D` and
`d + e = dim_k K + D`, where `K` is an `A`-submodule of `B / A` all of whose elements come from
`𝔪_A B`, and conversely. -/
private theorem dimension_count
    (hR : LinearMap.range (Algebra.linearMap A B) ≠ ⊤)
    [FiniteDimensional k (B ⧸ LinearMap.range (Algebra.linearMap A B))] :
    ∃ (D : ℕ) (K : Submodule A (B ⧸ LinearMap.range (Algebra.linearMap A B))),
      Module.finrank k k' ∣ D ∧ Module.finrank k k' ≤ D ∧
      Module.finrank k (B ⧸ LinearMap.range (Algebra.linearMap A B)) +
          Module.finrank k (ResidueField A) = Module.finrank k (K.restrictScalars k) + D ∧
      (D = Module.finrank k k' →
        Function.Bijective (algebraMap k' (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)))) ∧
      (K = ⊥ → ∀ b ∈ Ideal.map (algebraMap A B) (maximalIdeal A),
        b ∈ LinearMap.range (Algebra.linearMap A B)) := by
  set R := LinearMap.range (Algebra.linearMap A B)
  set mB := Ideal.map (algebraMap A B) (maximalIdeal A)
  have : Nontrivial B := not_subsingleton_iff_nontrivial.mp fun _ => hR (Subsingleton.elim _ _)
  have : Nontrivial (B ⧸ mB) := Ideal.Quotient.nontrivial_iff.mpr map_maximalIdeal_ne_top
  have : FiniteDimensional k (B ⧸ mB) := finiteDimensional_quotient_map_maximalIdeal
  have : FiniteDimensional k' (B ⧸ mB) := Module.Finite.of_restrictScalars_finite k k' (B ⧸ mB)
  refine ⟨Module.finrank k (B ⧸ mB), ?_⟩
  -- `n ∣ D` and `n ≤ D`
  have hmul : Module.finrank k k' * Module.finrank k' (B ⧸ mB) = Module.finrank k (B ⧸ mB) :=
    Module.finrank_mul_finrank k k' (B ⧸ mB)
  -- the image `W` of `A` in `B / 𝔪_A B`
  let ψ : A →ₗ[A] B ⧸ mB := Algebra.linearMap A (B ⧸ mB)
  have hkerψ : LinearMap.ker ψ = maximalIdeal A := ker_linearMap_quotient_map_maximalIdeal
  set W := LinearMap.range ψ
  have hWdim : Module.finrank k (W.restrictScalars k) = Module.finrank k (ResidueField A) :=
    ((((Submodule.quotEquivOfEq _ _ hkerψ.symm).trans
      ψ.quotKerEquivRange).restrictScalars k).finrank_eq).symm
  -- the map `σ : B / A → (B / 𝔪_A B) / W`
  let g : B →ₗ[A] B ⧸ mB := (Ideal.Quotient.mkₐ A mB).toLinearMap
  have hg : R ≤ W.comap g := by
    rintro b ⟨a, rfl⟩
    exact ⟨a, by simp [ψ, g, Algebra.algebraMap_eq_smul_one]⟩
  let σ : (B ⧸ R) →ₗ[A] (B ⧸ mB) ⧸ W := R.mapQ W g hg
  have hσ : Function.Surjective σ := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective W y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Submodule.mkQ R b, rfl⟩
  refine ⟨LinearMap.ker σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨_, hmul.symm⟩
  · rw [← hmul]
    exact Nat.le_mul_of_pos_right _ Module.finrank_pos
  · -- rank-nullity for `σ` and for the quotient by `W`
    have h1 := LinearMap.finrank_range_add_finrank_ker (σ.restrictScalars k)
    rw [(LinearMap.range_eq_top (f := σ.restrictScalars k)).mpr hσ, finrank_top] at h1
    have h2 := Submodule.finrank_quotient_add_finrank (W.restrictScalars k)
    rw [((Submodule.Quotient.restrictScalarsEquiv k W)).finrank_eq, hWdim] at h2
    have hker : LinearMap.ker (σ.restrictScalars k) = (LinearMap.ker σ).restrictScalars k := rfl
    rw [hker] at h1
    omega
  · intro hD
    rw [hD] at hmul
    have h1 : Module.finrank k' (B ⧸ mB) = 1 := (Nat.mul_eq_left Module.finrank_pos.ne').mp hmul
    refine ⟨(algebraMap k' (B ⧸ mB)).injective, ?_⟩
    have hinj : Function.Injective (Algebra.linearMap k' (B ⧸ mB)) :=
      (algebraMap k' (B ⧸ mB)).injective
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_self, h1])).mp hinj
  · intro hK b hb
    have : Submodule.mkQ R b ∈ LinearMap.ker σ := by
      change Submodule.mkQ W (Ideal.Quotient.mk mB b) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
    rwa [hK, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

/-- **[Stacks, Tag 0DJB], the dimension bound at a singular point.** Let `A` be a local
`k`-algebra with residue field finite over `k`, and `B` a finite `A`-algebra containing a finite
field extension `k'` of `k` of degree `n`. If the cokernel `B / A` of `A → B` is nonzero and
finite-dimensional over `k`, then `n ≤ 2 dim_k (B / A)`. -/
theorem finrank_le_two_mul_finrank_quotient_range
    (hR : LinearMap.range (Algebra.linearMap A B) ≠ ⊤)
    [FiniteDimensional k (B ⧸ LinearMap.range (Algebra.linearMap A B))] :
    Module.finrank k k' ≤ 2 * Module.finrank k (B ⧸ LinearMap.range (Algebra.linearMap A B)) := by
  obtain ⟨D, K, -, hnD, hcount, -, -⟩ := dimension_count (k := k) (k' := k') hR
  have he := finrank_residueField_le_finrank_quotient_range (k := k) (B := B) hR
  omega

/-- **[Stacks, Tag 0DJB], the equality case at a singular point.** In the situation of
`Stacks.Curves.finrank_le_two_mul_finrank_quotient_range`, if `dim_k (B / A) + 1 = n`, then the
residue field of `A` is `k`, the extension `𝔪_A B` of the maximal ideal is a maximal ideal of `B`
with `k' → B / 𝔪_A B` bijective, and `𝔪_A B` lies in the image of `A`. -/
theorem finrank_residueField_eq_one_of_finrank_quotient_range_add_one_eq
    (hR : LinearMap.range (Algebra.linearMap A B) ≠ ⊤)
    [FiniteDimensional k (B ⧸ LinearMap.range (Algebra.linearMap A B))]
    (hd : Module.finrank k (B ⧸ LinearMap.range (Algebra.linearMap A B)) + 1 =
      Module.finrank k k') :
    Module.finrank k (ResidueField A) = 1 ∧
      (Ideal.map (algebraMap A B) (maximalIdeal A)).IsMaximal ∧
      Function.Bijective (algebraMap k' (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))) ∧
      ∀ b ∈ Ideal.map (algebraMap A B) (maximalIdeal A),
        b ∈ LinearMap.range (Algebra.linearMap A B) := by
  obtain ⟨D, K, hdvd, hnD, hcount, hbij, hsub⟩ := dimension_count (k := k) (k' := k') hR
  have he := finrank_residueField_le_finrank_quotient_range (k := k) (B := B) hR
  have hepos : 0 < Module.finrank k (ResidueField A) := Module.finrank_pos
  -- `D = n`
  have hDn : D = Module.finrank k k' := by
    obtain ⟨c, hc⟩ := hdvd
    have hlt : D < 2 * Module.finrank k k' := by omega
    have hn : 0 < Module.finrank k k' := by omega
    rcases c with _ | _ | c
    · omega
    · simpa using hc
    · nlinarith
  -- `K = 0`
  have hK : K = ⊥ := by
    by_contra hne
    have : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hne
    have : FiniteDimensional k K :=
      FiniteDimensional.finiteDimensional_submodule (K.restrictScalars k)
    have := finrank_residueField_le k (A := A) (M := K)
    change _ ≤ Module.finrank k (K.restrictScalars k) at this
    omega
  have hKdim : Module.finrank k (K.restrictScalars k) = 0 := by
    rw [hK]
    exact finrank_bot k _
  have hbij' := hbij hDn
  exact ⟨by omega, Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (Field.toIsField k')
    (RingEquiv.ofBijective (algebraMap k' _) hbij').symm.toMulEquiv), hbij', hsub hK⟩

end Cokernel

end Stacks.Curves
