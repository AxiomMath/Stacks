module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.ConeDepth
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal

/-!
# Dimension on the punctured affine cone over a projective spectrum

Let `A` be a graded ring of finite type over a field `k` sitting in degree zero, `g = cb` with
`c ∈ A_{m+1}` and `b ∈ A_m`, `𝔭` a prime of `A` not containing `g`, and `𝔮 ⊂ A₍g₎` the prime under
`𝔭` (`Stacks.DegreeOneUnitAway.conePrime`). The residue field of `A₍g₎` at `𝔮` embeds into the
residue field of `A` at `𝔭`, so comparing transcendence degrees gives

`dim A₍g₎/𝔮 ≤ dim A/𝔭`.

On the punctured cone `U → P = Proj A` this says that the closure of a point of `U` has at least
the dimension of the closure of its image in `P`.

## Main results

* `Stacks.DegreeOneUnitAway.ringKrullDim_quotient_conePrime_le`: `dim A₍g₎/𝔮 ≤ dim A/𝔭`.
* `Stacks.DegreeOneUnitAway.ringKrullDim_quotient_conePrime_add_one_le`:
  `dim A₍g₎/𝔮 + 1 ≤ dim A/𝔭*`, where `𝔭*` is the homogeneous core of `𝔭`.
-/

@[expose] public noncomputable section

namespace Stacks.DegreeOneUnitAway

open HomogeneousLocalization IsLocalRing

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {g : A}

/-! ### Dehomogenization along the unit of degree one -/

section Dehomogenize

variable {c b : A} {m : ℕ}

/-- **Dehomogenization** `A → A[1/g]`, `a ↦ a u⁻ᵈ` on `A_d`, `u = c²/g` the unit of degree one. -/
def dehomogenize (hcb : c * b = g) : A →+* Localization.Away g :=
  (DirectSum.toSemiring (fun d => ((AddMonoidHom.mulRight
      (((chartUnit hcb)⁻¹ ^ d : (Localization.Away g)ˣ) : Localization.Away g)).comp
        ((algebraMap A (Localization.Away g)).toAddMonoidHom.comp
          (AddSubmonoidClass.subtype (𝒜 d)))))
    (by simp)
    (fun {i j} ai aj => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddSubmonoidClass.coe_subtype,
        SetLike.coe_gMul, map_mul, pow_add, Units.val_mul]
      ring)).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- On a homogeneous element `a ∈ A_d` the dehomogenization is `a ↦ a u⁻ᵈ`. -/
theorem dehomogenize_of_mem (hcb : c * b = g) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    dehomogenize (𝒜 := 𝒜) hcb a = algebraMap A (Localization.Away g) a *
      (((chartUnit hcb)⁻¹ ^ d : (Localization.Away g)ˣ) : Localization.Away g) := by
  rw [dehomogenize, RingHom.comp_apply]
  have h : (DirectSum.decomposeRingEquiv 𝒜).toRingHom a = DirectSum.of (fun i => 𝒜 i) d ⟨a, ha⟩ :=
    DirectSum.decompose_of_mem 𝒜 ha
  rw [h, DirectSum.toSemiring_of]
  rfl

/-- `c² = g u` in `A[1/g]`. -/
theorem algebraMap_sq_eq_mul_chartUnit (hcb : c * b = g) :
    algebraMap A (Localization.Away g) (c ^ 2) =
      algebraMap A (Localization.Away g) g * ((chartUnit hcb : (Localization.Away g)ˣ) :
        Localization.Away g) := by
  subst hcb
  rw [coe_chartUnit, ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [gen]⟩

/-- **A non-homogeneous prime over every homogeneous prime missing `g`**: the pullback along the
dehomogenization of the prime of `A[1/g]` under `𝔭`. It has the same homogeneous core as `𝔭`,
strictly contains it, and misses `g`. -/
theorem exists_isPrime_homogeneousCore_eq (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    ∃ p' : Ideal A, p'.IsPrime ∧ g ∉ p' ∧ (p.homogeneousCore 𝒜).toIdeal < p' ∧
      p'.homogeneousCore 𝒜 = p.homogeneousCore 𝒜 := by
  have hg := mul_mem hc hb hcb
  set P := (maximalIdeal (Localization.AtPrime p)).comap (awayToAtPrime p hgp) with hP
  set p' := P.comap (dehomogenize (𝒜 := 𝒜) hcb) with hp'
  have hmem : ∀ {d : ℕ} {a : A}, a ∈ 𝒜 d → (a ∈ p' ↔ a ∈ p) := by
    intro d a ha
    rw [hp', Ideal.mem_comap, dehomogenize_of_mem hcb ha,
      Ideal.mul_unit_mem_iff_mem _ (Units.isUnit _), hP, Ideal.mem_comap, awayToAtPrime_algebraMap,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p]
  have hcore : p'.homogeneousCore 𝒜 = p.homogeneousCore 𝒜 := by
    apply HomogeneousIdeal.ext
    show Ideal.span _ = Ideal.span _
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
    constructor <;> rintro ⟨y, hy, rfl⟩ <;> obtain ⟨d, hd⟩ := y.2
    exacts [⟨y, (hmem hd).1 hy, rfl⟩, ⟨y, (hmem hd).2 hy, rfl⟩]
  have hgp' : g ∉ p' := fun h => hgp ((hmem hg).1 h)
  have hdiff : c ^ 2 - g ∈ p' := by
    rw [hp', Ideal.mem_comap, map_sub,
      dehomogenize_of_mem hcb (SetLike.pow_mem_graded 2 hc), dehomogenize_of_mem hcb hg,
      algebraMap_sq_eq_mul_chartUnit hcb,
      show 2 • (m + 1) = (2 * m + 1) + 1 by simp only [smul_eq_mul]; ring, pow_succ,
      Units.val_mul]
    have hu : ((chartUnit hcb : (Localization.Away g)ˣ) : Localization.Away g) *
        (((chartUnit hcb)⁻¹ : (Localization.Away g)ˣ) : Localization.Away g) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [show algebraMap A (Localization.Away g) g *
        ((chartUnit hcb : (Localization.Away g)ˣ) : Localization.Away g) *
        ((((chartUnit hcb)⁻¹ ^ (2 * m + 1) : (Localization.Away g)ˣ) : Localization.Away g) *
          (((chartUnit hcb)⁻¹ : (Localization.Away g)ˣ) : Localization.Away g)) =
        algebraMap A (Localization.Away g) g *
          (((chartUnit hcb)⁻¹ ^ (2 * m + 1) : (Localization.Away g)ˣ) : Localization.Away g) *
            (((chartUnit hcb : (Localization.Away g)ˣ) : Localization.Away g) *
              (((chartUnit hcb)⁻¹ : (Localization.Away g)ˣ) : Localization.Away g)) by ring,
      hu, mul_one, sub_self]
    exact Ideal.zero_mem _
  refine ⟨p', Ideal.comap_isPrime _ _, hgp', lt_of_le_of_ne ?_ ?_, hcore⟩
  · rw [← hcore]
    exact Ideal.toIdeal_homogeneousCore_le 𝒜 p'
  · intro heq
    have hdec := (p.homogeneousCore 𝒜).isHomogeneous (2 * m + 1) (heq ▸ hdiff)
    rw [DirectSum.decompose_sub, DirectSum.sub_apply, AddSubgroupClass.coe_sub,
      DirectSum.decompose_of_mem_ne 𝒜 (SetLike.pow_mem_graded 2 hc)
        (by simp only [smul_eq_mul]; omega),
      DirectSum.decompose_of_mem_same 𝒜 hg, zero_sub, neg_mem_iff] at hdec
    exact hgp (Ideal.toIdeal_homogeneousCore_le 𝒜 p hdec)

end Dehomogenize

section Field

variable (k : Type u) [Field k] [Algebra k A] (hk : ∀ r : k, algebraMap k A r ∈ 𝒜 0)

/-- The structure map `k → A₀`. -/
def fieldToZero : k →+* 𝒜 0 where
  toFun r := ⟨algebraMap k A r, hk r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- The structure map `k → A₍g₎`. -/
def fieldToAway : k →+* Away 𝒜 g :=
  (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers g)).comp (fieldToZero k hk)

/-- The image of `r ∈ k` under `fieldToAway` maps to the image of `r` in `A[1/g]`. -/
theorem algebraMap_fieldToAway (r : k) :
    algebraMap (Away 𝒜 g) (Localization.Away g) (fieldToAway k hk r) =
      algebraMap A (Localization.Away g) (algebraMap k A r) :=
  rfl

include hk in
/-- **The closure of a point of the cone has at least the dimension of the closure of its image**:
`dim A₍g₎/𝔮 ≤ dim A/𝔭` for `A` of finite type over a field in degree zero. -/
theorem ringKrullDim_quotient_conePrime_le [Algebra.FiniteType k A] {d : ℕ} (_hd : 0 < d)
    (hgd : g ∈ 𝒜 d) (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    ringKrullDim (Away 𝒜 g ⧸ conePrime 𝒜 p hgp) ≤ ringKrullDim (A ⧸ p) := by
  let : Algebra k (Away 𝒜 g) := (fieldToAway k hk).toAlgebra
  let : Algebra k (𝒜 0) := (fieldToZero k hk).toAlgebra
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : Algebra.FiniteType (𝒜 0) A :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒜
  have : Algebra.FiniteType (𝒜 0) (Away 𝒜 g) := HomogeneousLocalization.Away.finiteType g d hgd
  have : Algebra.FiniteType k (𝒜 0) := by
    let φ : A →ₐ[k] 𝒜 0 :=
      { GradedRing.projZeroRingHom' 𝒜 with
        commutes' := fun r => Subtype.ext (by
          show GradedRing.projZeroRingHom 𝒜 (algebraMap k A r) = algebraMap k A r
          rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_same 𝒜 (hk r)]) }
    refine Algebra.FiniteType.of_surjective φ fun a => ⟨a, Subtype.ext ?_⟩
    show GradedRing.projZeroRingHom 𝒜 a = a
    rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_same 𝒜 a.2]
  have : IsScalarTower k (𝒜 0) (Away 𝒜 g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType k (Away 𝒜 g) :=
    Algebra.FiniteType.trans (S := 𝒜 0) inferInstance inferInstance
  have := conePrime_isPrime (𝒜 := 𝒜) p hgp
  let : Algebra k p.ResidueField :=
    ((algebraMap A p.ResidueField).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k (A ⧸ p) p.ResidueField := IsScalarTower.of_algebraMap_eq fun r => by
    rw [show algebraMap k (A ⧸ p) r = algebraMap A (A ⧸ p) (algebraMap k A r) from rfl,
      ← IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField]
    rfl
  have h1 := (Stacks.KrullDimension.TranscendenceDegree.solution.{u, u, u, u} k
    (Away 𝒜 g ⧸ conePrime 𝒜 p hgp) (FractionRing (Away 𝒜 g ⧸ conePrime 𝒜 p hgp))).1
  have h2 := (Stacks.KrullDimension.TranscendenceDegree.solution.{u, u, u, u} k (A ⧸ p)
    p.ResidueField).1
  rw [h1, h2]
  let ψ : Away 𝒜 g →+* p.ResidueField :=
    (algebraMap (Localization.AtPrime p) p.ResidueField).comp (degreeZeroToAtPrime 𝒜 p hgp)
  have hker : ∀ z, ψ z = 0 ↔ z ∈ conePrime 𝒜 p hgp := fun z => by
    show IsLocalRing.residue _ _ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff]
    rfl
  let ψbar : Away 𝒜 g ⧸ conePrime 𝒜 p hgp →+* p.ResidueField :=
    Ideal.Quotient.lift _ ψ fun z hz => (hker z).2 hz
  have hψinj : Function.Injective ψbar := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.lift_mk] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hker z).1 hz)
  let f : FractionRing (Away 𝒜 g ⧸ conePrime 𝒜 p hgp) →ₐ[k] p.ResidueField :=
    { IsFractionRing.lift hψinj with
      commutes' := fun r => by
        show IsFractionRing.lift hψinj (algebraMap (Away 𝒜 g ⧸ conePrime 𝒜 p hgp) _
          (algebraMap k _ r)) = _
        rw [IsFractionRing.lift_algebraMap]
        show ψ (fieldToAway k hk r) = algebraMap A p.ResidueField (algebraMap k A r)
        show algebraMap (Localization.AtPrime p) p.ResidueField
          (awayToAtPrime p hgp (algebraMap A (Localization.Away g) (algebraMap k A r))) = _
        rw [awayToAtPrime_algebraMap, ← IsScalarTower.algebraMap_apply] }
  exact_mod_cast Cardinal.toENat.monotone' (trdeg_le_of_injective f f.injective)

include hk in
/-- **The closure of the generic point of a fibre of the cone is one dimension bigger**:
`dim A₍g₎/𝔮 + 1 ≤ dim A/𝔭*`, `𝔭*` the homogeneous core of `𝔭`. -/
theorem ringKrullDim_quotient_conePrime_add_one_le [Algebra.FiniteType k A] {c b : A} {m : ℕ}
    (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) (p : Ideal A) [p.IsPrime]
    (hgp : g ∉ p) :
    ringKrullDim (Away 𝒜 g ⧸ conePrime 𝒜 p hgp) + 1 ≤
      ringKrullDim (A ⧸ (p.homogeneousCore 𝒜).toIdeal) := by
  obtain ⟨p', hp'prime, hgp', hlt, hcore⟩ := exists_isPrime_homogeneousCore_eq hc hb hcb p hgp
  have := hp'prime
  have hcone : conePrime 𝒜 p' hgp' = conePrime 𝒜 p hgp := by
    have : Fact (g ∉ p) := ⟨hgp⟩
    have : Fact (g ∉ p') := ⟨hgp'⟩
    rw [conePrime_eq_comap p' hc hb hcb, conePrime_eq_comap p hc hb hcb, hcore]
  have h1 := ringKrullDim_quotient_conePrime_le k hk (Nat.succ_pos _) (mul_mem hc hb hcb) p' hgp'
  rw [hcone] at h1
  have hPprime : ((p.homogeneousCore 𝒜).toIdeal).IsPrime :=
    (inferInstance : p.IsPrime).homogeneousCore
  have h2 : Order.coheight (⟨p', hp'prime⟩ : PrimeSpectrum A) + 1 ≤
      Order.coheight (⟨(p.homogeneousCore 𝒜).toIdeal, hPprime⟩ : PrimeSpectrum A) :=
    Order.coheight_add_one_le hlt
  have h2' : ringKrullDim (A ⧸ p') + 1 ≤ ringKrullDim (A ⧸ (p.homogeneousCore 𝒜).toIdeal) := by
    rw [← coheight_eq_ringKrullDim_quotient ⟨p', hp'prime⟩,
      ← coheight_eq_ringKrullDim_quotient ⟨_, hPprime⟩]
    exact_mod_cast h2
  exact (add_le_add_left h1 1).trans h2'

end Field

end Stacks.DegreeOneUnitAway

end
