module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGaloisCochains
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.KummerCochains
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.OpenSubgroupFixedField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionCochainVanishing

/-!
# The base of the dévissage for an absolute Galois group

Let `Ω/K` be a Galois extension with `Ω` separably closed, so that `Gal(Ω/K)` is the absolute
Galois group of `K`, and suppose the Brauer group of every finite subextension of `Ω/K` vanishes.
This file proves that `Gal(Ω/K)` satisfies `Stacks.GroupCohomology.HasPrimeBase`: for every prime
`p` there is an open normal subgroup of index prime to `p` over whose open subgroups the
degree-two cochain statement with values in `ℤ/p` with the trivial action holds.

## Main definitions

* `Stacks.GaloisCohomology.addEquivTrivialModArtinSchreierKer`: the kernel of the Artin-Schreier
  map of a field of characteristic `p`, as the coefficient module
  `Stacks.GroupCohomology.TrivialMod p`.

## Main results

* `Stacks.GaloisCohomology.vanishesTwo_of_continuousMulEquiv`: the degree-two cochain statement
  transports along a topological group isomorphism acting compatibly on the coefficients.
* `Stacks.GaloisCohomology.exists_nsmul_eq_one_of_artinSchreier_eq_zero`: every root of
  `X ^ p - X` in a field of characteristic `p` is a natural multiple of `1`.
* `Stacks.GaloisCohomology.vanishesTwo_trivialMod_of_charP`: the degree-two cochain statement for
  `ℤ/p` with the trivial action holds for `Gal(Ω/K)` when `Ω` has characteristic `p`.
* `Stacks.GaloisCohomology.exists_isPrimitiveRoot_units`,
  `Stacks.GaloisCohomology.normal_stabilizer_of_isPrimitiveRoot`,
  `Stacks.GaloisCohomology.not_dvd_index_stabilizer_of_isPrimitiveRoot`: away from the
  characteristic, `Ω` has a primitive `p`-th root of unity, and its stabilizer is a normal subgroup
  of index prime to `p`.
* `Stacks.GaloisCohomology.vanishesTwo_trivialMod_of_le_stabilizer`: the degree-two cochain
  statement for `ℤ/p` holds over every open subgroup fixing a primitive `p`-th root of unity.
* `Stacks.GaloisCohomology.hasPrimeBase_of_forall_brauer`: the base of the dévissage for the
  absolute Galois group of a field all of whose finite extensions have trivial Brauer group.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8)
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence.
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the vanishing of the
  Galois cohomology of the additive group.
-/

@[expose] public noncomputable section

open groupCohomology IntermediateField Stacks.GroupCohomology

universe u

namespace Stacks.GaloisCohomology

/-! ### Transport along a topological group isomorphism -/

/-- **The degree-two cochain statement transports along a topological group isomorphism** acting
compatibly on the coefficients. -/
theorem vanishesTwo_of_continuousMulEquiv {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction H M] (e : H ≃ₜ* G) (hcompat : ∀ (h : H) (m : M), (e h) • m = h • m)
    (hG : VanishesTwo G M) : VanishesTwo H M := by
  intro f hflc hfcoc
  have hsymm : Continuous (e.symm : G → H) := e.symm.continuous_toFun
  have hc : ∀ (g : G) (m : M), (e.symm g) • m = g • m := fun g m ↦ by
    rw [← hcompat (e.symm g) m, e.apply_symm_apply]
  obtain ⟨x, hxlc, hx⟩ := hG (fun q ↦ f (e.symm q.1, e.symm q.2))
    (hflc.comp_continuous ((hsymm.comp continuous_fst).prodMk (hsymm.comp continuous_snd)))
    (fun g h j ↦ by simpa only [map_mul, hc] using hfcoc (e.symm g) (e.symm h) (e.symm j))
  refine ⟨fun h ↦ x (e h), hxlc.comp_continuous e.continuous_toFun,
    funext fun ⟨h₁, h₂⟩ ↦ ?_⟩
  simpa only [dOne_apply, map_mul, ← hcompat h₁, e.symm_apply_apply] using
    congrFun hx (e h₁, e h₂)

/-! ### The kernel of the Artin-Schreier map is the prime field -/

section ArtinSchreierKernel

variable {Ω : Type*} [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p]

/-- **Every root of `X ^ p - X` in a field of characteristic `p` is a natural multiple of `1`**:
the kernel of the Artin-Schreier map is the prime field. -/
theorem exists_nsmul_eq_one_of_artinSchreier_eq_zero (x : Ω) (hx : x ^ p - x = 0) :
    ∃ k : ℕ, x = k • (1 : Ω) := by
  have hpow : x ^ p = x := by linear_combination hx
  have hmem : x ∈ (ZMod.castHom (dvd_refl p) Ω).fieldRange := by
    rw [ZMod.fieldRange_castHom_eq_bot p]
    exact (Subfield.mem_bot_iff_pow_eq_self Ω p).2 hpow
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a.val, by rw [nsmul_eq_mul, mul_one, ← ha, ZMod.castHom_apply, ← ZMod.natCast_val]⟩

variable (Ω)

/-- `1` lies in the kernel of the Artin-Schreier map. -/
theorem one_mem_ker_artinSchreier : (1 : Ω) ∈ (artinSchreier Ω p).ker := by
  simp [AddMonoidHom.mem_ker]

/-- **The kernel of the Artin-Schreier map of a field of characteristic `p` is the coefficient
module `TrivialMod p`.** -/
def addEquivTrivialModArtinSchreierKer : ↥(artinSchreier Ω p).ker ≃+ TrivialMod p :=
  addEquiv_trivialMod_of_prime (Fact.out (p := p.Prime))
    (⟨1, one_mem_ker_artinSchreier Ω p⟩ : ↥(artinSchreier Ω p).ker)
    (fun h ↦ by simpa using congrArg Subtype.val h)
    (Subtype.ext (by simp))
    (fun a ↦ by
      obtain ⟨k, hk⟩ :=
        exists_nsmul_eq_one_of_artinSchreier_eq_zero p (a : Ω) (AddMonoidHom.mem_ker.1 a.2)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩)

end ArtinSchreierKernel

/-! ### The characteristic case, by Artin-Schreier -/

/-- **The degree-two cochain statement with values in `ℤ/p` with the trivial action, in
characteristic `p`.** -/
theorem vanishesTwo_trivialMod_of_charP {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] [IsSepClosed Ω] :
    VanishesTwo Gal(Ω/K) (TrivialMod p) := by
  have : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  obtain ⟨ι, hιinj, hιsmul, hιpow, hιsurj⟩ : ∃ ι : TrivialMod p →+ Ω, Function.Injective ι ∧
      (∀ (g : Gal(Ω/K)) (a : TrivialMod p), ι (g • a) = g • ι a) ∧
      (∀ a : TrivialMod p, (ι a) ^ p - ι a = 0) ∧
      (∀ x : Ω, x ^ p - x = 0 → ∃ a : TrivialMod p, ι a = x) := by
    refine ⟨(ZMod.castHom (dvd_refl p) Ω).toAddMonoidHom.comp
      (TrivialMod.addEquivZMod p).toAddMonoidHom, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact (TrivialMod.addEquivZMod p).injective
        ((ZMod.castHom (dvd_refl p) Ω).injective hab)
    · intro g a
      have hnat : (ZMod.castHom (dvd_refl p) Ω) (TrivialMod.addEquivZMod p a) =
          (((TrivialMod.addEquivZMod p a).val : ℕ) : Ω) := by
        rw [ZMod.castHom_apply, ← ZMod.natCast_val]
      show (ZMod.castHom (dvd_refl p) Ω) (TrivialMod.addEquivZMod p (g • a)) =
        g • (ZMod.castHom (dvd_refl p) Ω) (TrivialMod.addEquivZMod p a)
      rw [TrivialMod.smul_eq, hnat]
      show (((TrivialMod.addEquivZMod p a).val : ℕ) : Ω) =
        g (((TrivialMod.addEquivZMod p a).val : ℕ) : Ω)
      rw [map_natCast]
    · intro a
      show ((ZMod.castHom (dvd_refl p) Ω) (TrivialMod.addEquivZMod p a)) ^ p -
        (ZMod.castHom (dvd_refl p) Ω) (TrivialMod.addEquivZMod p a) = 0
      rw [← map_pow, ZMod.pow_card, sub_self]
    · intro x hx
      obtain ⟨k, hk⟩ := exists_nsmul_eq_one_of_artinSchreier_eq_zero p x hx
      refine ⟨(TrivialMod.addEquivZMod p).symm (k : ZMod p), ?_⟩
      show (ZMod.castHom (dvd_refl p) Ω) (TrivialMod.addEquivZMod p
        ((TrivialMod.addEquivZMod p).symm (k : ZMod p))) = x
      rw [AddEquiv.apply_symm_apply, map_natCast, hk, nsmul_eq_mul, mul_one]
  intro F hFlc hFcoc
  obtain ⟨x, hxlc, hxker, hx⟩ := exists_dOne_eq_artinSchreier (K := K) p (fun q ↦ ι (F q))
    (hFlc.comp ι) (isCocycle₂_comp ι hιsmul hFcoc) (fun q ↦ hιpow (F q))
  choose y hy using fun g : Gal(Ω/K) ↦ hιsurj (x g) (hxker g)
  have hyx : (fun g : Gal(Ω/K) ↦ ι (y g)) = x := funext hy
  refine ⟨y, isLocallyConstant_of_comp_injective hιinj (by rwa [hyx]),
    funext fun q ↦ hιinj ?_⟩
  have h1 := congrFun (dOne_map ι hιsmul y) q
  rw [hyx] at h1
  rw [show ι (dOne y q) = (⇑ι ∘ dOne y) q from rfl, h1, congrFun hx q]

/-! ### Primitive roots of unity and their stabilizers -/

section PrimitiveRoot

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- **A separably closed field contains a primitive `p`-th root of unity** for every prime `p`
not equal to its characteristic, and it may be taken to be a unit. -/
theorem exists_isPrimitiveRoot_units [IsSepClosed Ω] (p : ℕ) (hp : p.Prime) [NeZero (p : Ω)] :
    ∃ ζ : Ωˣ, IsPrimitiveRoot ζ p := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  exact ⟨(hζ.isUnit hp.ne_zero).unit, hζ.isUnit_unit hp.ne_zero⟩

variable {p : ℕ} [NeZero p] {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
include hζ

omit [IsGalois K Ω] in
/-- The Galois group permutes the `p`-th roots of unity, which are the powers of a primitive
`p`-th root `ζ`. -/
theorem smul_mem_zpowers_of_isPrimitiveRoot (g : Gal(Ω/K)) : g • ζ ∈ Subgroup.zpowers ζ := by
  rw [hζ.zpowers_eq]
  have h1 : (g • ζ) ^ p = 1 := by rw [← smul_pow', hζ.pow_eq_one, smul_one]
  simpa only [mem_rootsOfUnity] using h1

omit [IsGalois K Ω] in
/-- **The stabilizer of a primitive `p`-th root of unity is normal.** -/
theorem normal_stabilizer_of_isPrimitiveRoot :
    (MulAction.stabilizer Gal(Ω/K) ζ).Normal := by
  refine ⟨fun n hn g ↦ MulAction.mem_stabilizer_iff.2 ?_⟩
  have hfix : n • (g⁻¹ • ζ) = g⁻¹ • ζ :=
    smul_eq_of_mem_zpowers n hn (smul_mem_zpowers_of_isPrimitiveRoot hζ g⁻¹)
  rw [mul_smul, mul_smul, hfix, ← mul_smul, mul_inv_cancel, one_smul]

omit [IsGalois K Ω] in
/-- **The index of the stabilizer of a primitive `p`-th root of unity is prime to `p`** when `p`
is prime. -/
theorem not_dvd_index_stabilizer_of_isPrimitiveRoot (hp : p.Prime) :
    ¬ p ∣ (MulAction.stabilizer Gal(Ω/K) ζ).index := by
  have hequiv : ZMod p ≃ ↥(Subgroup.zpowers ζ) :=
    hζ.zmodEquivZPowers.toEquiv.trans Additive.toMul
  have : Finite ↥(Subgroup.zpowers ζ) := Finite.of_equiv _ hequiv
  have hzp : ((Subgroup.zpowers ζ : Subgroup Ωˣ) : Set Ωˣ).ncard = p := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr hequiv).symm.trans (Nat.card_zmod p)
  have hfin : ((Subgroup.zpowers ζ : Subgroup Ωˣ) : Set Ωˣ).Finite := Set.toFinite _
  have hsub : MulAction.orbit Gal(Ω/K) ζ ⊆ ((Subgroup.zpowers ζ : Subgroup Ωˣ) : Set Ωˣ) := by
    rintro _ ⟨g, rfl⟩
    exact smul_mem_zpowers_of_isPrimitiveRoot hζ g
  have hone : (1 : Ωˣ) ∉ MulAction.orbit Gal(Ω/K) ζ := by
    rintro ⟨g, hg⟩
    have hg' : g • ζ = 1 := hg
    rw [← inv_smul_smul g ζ, hg', smul_one] at hζ
    exact hp.ne_one (Nat.dvd_one.1 (hζ.dvd_of_pow_eq_one 1 (one_pow 1)))
  have hlt : (MulAction.orbit Gal(Ω/K) ζ).ncard < p := by
    rw [← hzp]
    exact Set.ncard_lt_ncard (lt_of_le_of_ne hsub fun hc ↦ hone (hc ▸ Subgroup.one_mem _)) hfin
  have hidx : (MulAction.stabilizer Gal(Ω/K) ζ).index =
      (MulAction.orbit Gal(Ω/K) ζ).ncard := by
    rw [Subgroup.index_eq_card, ← Nat.card_coe_set_eq,
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Gal(Ω/K) ζ)]
  have hpos : 0 < (MulAction.orbit Gal(Ω/K) ζ).ncard :=
    (Set.ncard_pos (hfin.subset hsub)).2 ⟨ζ, MulAction.mem_orbit_self ζ⟩
  rw [hidx]
  exact Nat.not_dvd_of_pos_of_lt hpos hlt

end PrimitiveRoot

/-! ### The non-characteristic case, by Kummer theory -/

section Kummer

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The degree-two cochain statement over an open subgroup follows from that over the Galois group
of its fixed field. -/
private theorem vanishesTwo_of_fixedField {p : ℕ} (U : OpenSubgroup Gal(Ω/K))
    (h : VanishesTwo Gal(Ω/↥(fixedField (U : Subgroup Gal(Ω/K)))) (TrivialMod p)) :
    VanishesTwo ↥U (TrivialMod p) :=
  vanishesTwo_of_continuousMulEquiv
    (fixedFieldContinuousMulEquiv (U : Subgroup Gal(Ω/K)) U.isOpen').symm (fun _ _ ↦ rfl) h

/-- **The degree-two cochain statement with values in `ℤ/p` with the trivial action, over an open
subgroup fixing a primitive `p`-th root of unity.** -/
theorem vanishesTwo_trivialMod_of_le_stabilizer [IsSepClosed Ω] (p : ℕ) (hp : p.Prime)
    [NeZero (p : Ω)]
    (hBr : ∀ L : IntermediateField K Ω, FiniteDimensional K ↥L → ∀ y : BrauerGroup ↥L, y = 1)
    {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p) (U : OpenSubgroup Gal(Ω/K))
    (hU : (U : Subgroup Gal(Ω/K)) ≤ MulAction.stabilizer Gal(Ω/K) ζ) :
    VanishesTwo ↥U (TrivialMod p) := by
  have hfd : FiniteDimensional K ↥(fixedField (U : Subgroup Gal(Ω/K))) :=
    finiteDimensional_fixedField_of_isOpen (U : Subgroup Gal(Ω/K)) U.isOpen'
  have : IsGalois ↥(fixedField (U : Subgroup Gal(Ω/K))) Ω := inferInstance
  have hfix : ∀ g : Gal(Ω/↥(fixedField (U : Subgroup Gal(Ω/K)))), g • ζ = ζ := by
    intro g
    have hmem : AlgEquiv.restrictScalarsHom K g ∈ (U : Subgroup Gal(Ω/K)) :=
      (range_restrictScalarsHom_fixedField (U : Subgroup Gal(Ω/K)) U.isOpen').le ⟨g, rfl⟩
    have h2 := congrArg (fun u : Ωˣ ↦ (u : Ω)) (hU hmem : _ • ζ = ζ)
    exact Units.val_inj.mp (by simpa using h2)
  have hvan : VanishesTwo Gal(Ω/↥(fixedField (U : Subgroup Gal(Ω/K)))) (TrivialMod p) := by
    intro F hFlc hFcoc
    obtain ⟨x, hxlc, hx⟩ := exists_dOne_eq_kummer p hp
      (hBr (fixedField (U : Subgroup Gal(Ω/K))) hfd) ζ hζ hfix
      (fun q ↦ TrivialMod.addEquivZMod p (F q))
      (hFlc.comp fun a ↦ TrivialMod.addEquivZMod p a)
      (fun g₁ g₂ g₃ ↦ by
        simpa only [map_add, TrivialMod.smul_eq] using
          congrArg (TrivialMod.addEquivZMod p) (hFcoc g₁ g₂ g₃))
    refine ⟨fun g ↦ (TrivialMod.addEquivZMod p).symm (x g),
      hxlc.comp fun a ↦ (TrivialMod.addEquivZMod p).symm a, funext fun q ↦ ?_⟩
    obtain ⟨g₁, g₂⟩ := q
    simp only [dOne_apply, TrivialMod.smul_eq]
    rw [← map_sub, ← map_add, hx g₁ g₂, AddEquiv.symm_apply_apply]
  exact vanishesTwo_of_fixedField U hvan

/-! ### The base of the dévissage -/

/-- **The base of the dévissage for an absolute Galois group.** Let `Ω/K` be Galois with `Ω`
separably closed and suppose the Brauer group of every finite subextension of `Ω/K` vanishes.
Then for every prime `p` there is an open normal subgroup of `Gal(Ω/K)` of index prime to `p`
over whose open subgroups every locally constant `2`-cocycle with values in `ℤ/p` with the
trivial action is a coboundary. -/
theorem hasPrimeBase_of_forall_brauer [IsSepClosed Ω]
    (hBr : ∀ L : IntermediateField K Ω, FiniteDimensional K ↥L → ∀ y : BrauerGroup ↥L, y = 1) :
    HasPrimeBase Gal(Ω/K) := by
  intro p hp
  have := Fact.mk hp
  by_cases hchar : (p : Ω) = 0
  · have : CharP Ω p := by
      rw [← CharP.ringChar_of_prime_eq_zero hp hchar]
      exact ringChar.charP Ω
    refine ⟨⊤, inferInstance, by rw [Subgroup.coe_top]; exact isOpen_univ, ?_, fun U _ ↦ ?_⟩
    · rw [Subgroup.index_top]
      exact hp.not_dvd_one
    · have : FiniteDimensional K ↥(fixedField (U : Subgroup Gal(Ω/K))) :=
        finiteDimensional_fixedField_of_isOpen (U : Subgroup Gal(Ω/K)) U.isOpen'
      exact vanishesTwo_of_fixedField U (vanishesTwo_trivialMod_of_charP p)
  · have : NeZero (p : Ω) := ⟨hchar⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_units (Ω := Ω) p hp
    exact ⟨MulAction.stabilizer Gal(Ω/K) ζ, normal_stabilizer_of_isPrimitiveRoot hζ,
      isOpen_stabilizer_units ζ, not_dvd_index_stabilizer_of_isPrimitiveRoot hζ hp,
      fun U hUle ↦ vanishesTwo_trivialMod_of_le_stabilizer p hp hBr hζ U hUle⟩

end Kummer

end Stacks.GaloisCohomology

end
