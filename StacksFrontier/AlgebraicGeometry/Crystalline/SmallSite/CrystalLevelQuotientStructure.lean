module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalLevelQuotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemLevelRings

/-!
# The crystal level-quotient property for the coefficient sheaf `𝒪_{X/S}`

The sections of `𝒪_{X/S}` over the level `(n, e)` of `wholeSpaceSystem S hp` are the ring
`D(n)/(p)^{N + e}`, with `N + e = wholeSpaceLevelExponent hp e`, and the restriction along a level
drop is the reduction `D(n)/(p)^{N + e + 1} ⟶ D(n)/(p)^{N + e}`. We show that the kernel of this
restriction consists of the `p^{N + e}`-multiples, and deduce that `𝒪_{X/S}` satisfies
`IsCrystalLevelQuotient`, the distinguishing hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG],
under hypotheses (1) and (2) of [Stacks, Proposition 60.20.1, Tag 07JN].

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite` except the
first, which is a statement about quotient rings.

* `DividedPowers.pAdicIdeal_pow_succ_map_eq_zero_iff_exists_nsmul`: the kernel of a reduction
  `R/(m)^{k+1} ⟶ R/(m)^k` is the subgroup of `m^k`-multiples.
* `levelRestrict_structureSheaf_eq_zero_iff`: a section of `𝒪_{X/S}` over `T(n)_{e+1}` restricts
  to zero over `T(n)_e` exactly when it is `p^{N+e}` times a section over `T(n)_{e+1}`.
* `levelMap_abelianSheaf_unit_eq_zero_iff`: the same statement for the underlying abelian sheaf of
  `𝒪_{X/S}` at the coefficient universe `u + 1`, which is the kernel clause of
  `IsCrystalLevelQuotient`.
* `isCrystalLevelQuotient_wholeSpaceSystem_unit`: `𝒪_{X/S}` satisfies `IsCrystalLevelQuotient`,
  given hypotheses (1) and (2) of [Stacks, Tag 07JN].

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace DividedPowers

/-- The kernel of the reduction `R/(m)^{k+1} ⟶ R/(m)^k` is the subgroup of `m^k`-multiples: for a
ring homomorphism `f` sending the class of every `d : R` modulo `pAdicIdeal m ^ (k + 1)` to its
class modulo `pAdicIdeal m ^ k`, `f X = 0` exactly when `X = m ^ k • Y` for some `Y`. -/
theorem pAdicIdeal_pow_succ_map_eq_zero_iff_exists_nsmul {R : Type*} [CommRing R] (m k : ℕ)
    (f : (R ⧸ pAdicIdeal (A := R) m ^ (k + 1)) →+* (R ⧸ pAdicIdeal (A := R) m ^ k))
    (hf : ∀ d : R, f (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ d)
    (X : R ⧸ pAdicIdeal (A := R) m ^ (k + 1)) :
    f X = 0 ↔ ∃ Y, X = m ^ k • Y := by
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective X
  rw [hf, Ideal.Quotient.eq_zero_iff_mem, pAdicIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [nsmul_eq_mul, Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul]
  · rintro ⟨Y, hY⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective Y
    rw [nsmul_eq_mul, Nat.cast_pow, ← map_natCast (Ideal.Quotient.mk _), ← map_pow, ← map_mul,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hY
    have hmem : d - (m : R) ^ k * r ∈ pAdicIdeal (A := R) m ^ k :=
      Ideal.pow_le_pow_right (Nat.le_succ k) hY
    rw [pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact Dvd.intro (r + c) (by linear_combination -hc)

end DividedPowers

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- A section of `𝒪_{X/S}` over the level `(n, e + 1)` of `wholeSpaceSystem S hp` restricts to
zero over the level `(n, e)` exactly when it is `p ^ wholeSpaceLevelExponent hp e` times a section
over `(n, e + 1)`. -/
theorem levelRestrict_structureSheaf_eq_zero_iff (n e : ℕ)
    (z : ((structureSheaf S).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1))) : Type u)) :
    ((structureSheaf S).obj.map
        (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op).hom z = 0 ↔
      ∃ w, z = S.p ^ wholeSpaceLevelExponent hp e • w := by
  rw [← RingEquiv.map_eq_zero_iff (wholeSpaceSystemLevelRingEquiv hp n e),
    wholeSpaceSystemLevelRingEquiv_restrict hp n (homOfLE (Nat.le_succ e)) z]
  refine Iff.trans (DividedPowers.pAdicIdeal_pow_succ_map_eq_zero_iff_exists_nsmul S.p
    (wholeSpaceLevelExponent hp e)
    (wholeSpaceSystemLevelMap hp n (Nat.le_succ e)).hom.hom.toRingHom
    (wholeSpaceSystemLevelMap_mk hp n (Nat.le_succ e)) _) ?_
  constructor
  · rintro ⟨Y, hY⟩
    obtain ⟨w, rfl⟩ := (wholeSpaceSystemLevelRingEquiv hp n (e + 1)).surjective Y
    exact ⟨w, (wholeSpaceSystemLevelRingEquiv hp n (e + 1)).injective
      (hY.trans (map_nsmul _ _ _).symm)⟩
  · rintro ⟨w, hw⟩
    exact ⟨wholeSpaceSystemLevelRingEquiv hp n (e + 1) w,
      (congrArg (wholeSpaceSystemLevelRingEquiv hp n (e + 1)) hw).trans (map_nsmul _ _ _)⟩

/-- The kernel clause of `IsCrystalLevelQuotient` for `𝒪_{X/S}`: a section `x` of the underlying
abelian sheaf of `SheafOfModules.unit (structureSheaf S)` over the level `(n, e + 1)` of
`wholeSpaceSystem S hp` has `levelMap` zero exactly when `x = p ^ wholeSpaceLevelExponent hp e • y`
for some `y`. -/
theorem levelMap_abelianSheaf_unit_eq_zero_iff (n e : ℕ)
    (x : (abelianSheaf (SheafOfModules.unit (structureSheaf S))).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))) :
    levelMap (wholeSpaceSystem S hp)
        (abelianSheaf (SheafOfModules.unit (structureSheaf S))).obj n e x = 0 ↔
      ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (levelRestrict_structureSheaf_eq_zero_iff hp n e x.down).1
      (congrArg ULift.down h)
    exact ⟨ULift.up w, ULift.ext hw⟩
  · rintro ⟨y, hy⟩
    exact ULift.ext ((levelRestrict_structureSheaf_eq_zero_iff hp n e x.down).2
      ⟨y.down, congrArg ULift.down hy⟩)

/-- The coefficient sheaf `𝒪_{X/S}` satisfies `IsCrystalLevelQuotient` along
`wholeSpaceSystem S hp` with the exponents `wholeSpaceLevelExponent hp`, provided it is locally
quasi-coherent and its comparison maps are surjective (hypotheses (1) and (2) of
[Stacks, Tag 07JN]). -/
theorem isCrystalLevelQuotient_wholeSpaceSystem_unit
    (hF : IsLocallyQuasiCoherent (SheafOfModules.unit (structureSheaf S)))
    (hM : CohomologyRestriction.IsSurjectiveComparison
      (SheafOfModules.unit (structureSheaf S)).val) :
    IsCrystalLevelQuotient (wholeSpaceSystem S hp)
      (abelianSheaf (SheafOfModules.unit (structureSheaf S))).obj
      (wholeSpaceLevelExponent hp) :=
  isCrystalLevelQuotient_wholeSpaceSystem_of_ker hp _ hF hM
    (levelMap_abelianSheaf_unit_eq_zero_iff hp)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
