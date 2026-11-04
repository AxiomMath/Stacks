module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.AffineFieldFactors
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CodimensionOneIso
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.Basic

/-!
# Tameness of affine covers of `𝐆_m` at `0` and at `∞`, algebraically

Let `C` be a ring with a map `φ : k[x]_x → C`, giving a cover `Spec C ⟶ 𝐆_{m,k}`. Tameness of this
cover at `0` (`Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne` along the chart
`j₀ : 𝐆_m ⟶ Spec k[x]`) is a statement about the field factors of `C` over the local ring of
`Spec k[x]` at the point `(x)`: fields `L` over a fraction field `K` of that local ring together
with a map `ψ : C → L` compatible with `k[x] → L` and generating `L` over `K`. This file proves
both directions of this translation (through `AffineFieldFactors`), and reduces tameness at `∞`
to tameness at `0` through the inversion `x ↦ x⁻¹` of `k[x]_x`.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.inversion k`: `x ↦ x⁻¹` on `k[x]_x`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.isTamelyRamifiedInCodimensionOne_chartZero_of`:
  tameness at `0` from tameness of the field factors.
* `AlgebraicGeometry.TameMultiplicativeGroup.isTamelyRamifiedWithRespectTo_of_chartZero`:
  the field factors of a cover tame at `0` are tame.
* `AlgebraicGeometry.TameMultiplicativeGroup.isTamelyRamifiedInCodimensionOne_chartInfty_iff`:
  tameness at `∞` is tameness at `0` of the cover twisted by the inversion.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

/-- A point of coheight one is the generic point of a prime divisor in the sense of
`StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup`. -/
def weilPrimeDivisorOfCoheightOne {S : Scheme.{u}} (x : S) (hx : Order.coheight x = 1) :
    StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor S :=
  ⟨(PrimeDivisor.ofCoheightOne x hx).idealSheaf, (PrimeDivisor.ofCoheightOne x hx).integral,
    (PrimeDivisor.ofCoheightOne x hx).codimension_one⟩

/-- The generic point of `weilPrimeDivisorOfCoheightOne x hx` is `x`. -/
theorem genericPoint_weilPrimeDivisorOfCoheightOne {S : Scheme.{u}} (x : S)
    (hx : Order.coheight x = 1) : (weilPrimeDivisorOfCoheightOne x hx).genericPoint = x :=
  PrimeDivisor.genericPoint_ofCoheightOne x hx

variable (k : Type u) [Field k]

/-- The inverse `x⁻¹` of `x` in `k[x]_x` is a unit. -/
theorem isUnit_invSelf : IsUnit (IsLocalization.Away.invSelf (X : k[X]) : Ring k) :=
  IsUnit.of_mul_eq_one (algebraMap k[X] (Ring k) X) (by
    rw [mul_comm, IsLocalization.Away.mul_invSelf])

/-- **The inversion** `x ↦ x⁻¹` of `k[x]_x`. -/
def inversionHom : Ring k →+* Ring k :=
  IsLocalization.Away.lift (X : k[X]) (g := inverseCoordinate k) (by
    change IsUnit (eval₂ (algebraMap k (Ring k)) _ X)
    rw [eval₂_X]
    exact isUnit_invSelf k)

/-- The inversion sends the image of a polynomial `p` to `p(x⁻¹)`. -/
theorem inversionHom_algebraMap (p : k[X]) :
    inversionHom k (algebraMap k[X] (Ring k) p) = inverseCoordinate k p :=
  IsLocalization.Away.lift_eq _ _ p

/-- The inversion composed with `k[x] → k[x]_x` is the substitution `x ↦ x⁻¹`. -/
theorem inversionHom_comp_algebraMap :
    (inversionHom k).comp (algebraMap k[X] (Ring k)) = inverseCoordinate k :=
  RingHom.ext (inversionHom_algebraMap k)

/-- The image in `k[x]_x` of a constant polynomial `C a` is the image of `a`. -/
theorem algebraMap_C (a : k) : algebraMap k[X] (Ring k) (C a) = algebraMap k (Ring k) a := by
  rw [IsScalarTower.algebraMap_apply k k[X] (Ring k), C_eq_algebraMap]

/-- The inversion fixes the constants `k`. -/
theorem inversionHom_algebraMap_k (a : k) :
    inversionHom k (algebraMap k (Ring k) a) = algebraMap k (Ring k) a := by
  rw [← algebraMap_C, inversionHom_algebraMap, inverseCoordinate, coe_eval₂RingHom, eval₂_C,
    algebraMap_C]

/-- The inversion sends the image of `x` to `x⁻¹`. -/
private theorem inversionHom_algebraMap_X :
    inversionHom k (algebraMap k[X] (Ring k) X) = IsLocalization.Away.invSelf (X : k[X]) := by
  rw [inversionHom_algebraMap, inverseCoordinate, coe_eval₂RingHom, eval₂_X]

/-- The inversion sends `x⁻¹` to `x`. -/
theorem inversionHom_invSelf :
    inversionHom k (IsLocalization.Away.invSelf (X : k[X])) = algebraMap k[X] (Ring k) X := by
  have h1 : inversionHom k (IsLocalization.Away.invSelf (X : k[X])) *
      IsLocalization.Away.invSelf (X : k[X]) = 1 := by
    have := inversionHom_algebraMap_X k
    calc inversionHom k (IsLocalization.Away.invSelf (X : k[X])) *
          IsLocalization.Away.invSelf (X : k[X]) =
          inversionHom k (IsLocalization.Away.invSelf (X : k[X])) *
            inversionHom k (algebraMap k[X] (Ring k) X) := by rw [this]
      _ = inversionHom k (IsLocalization.Away.invSelf (X : k[X]) * algebraMap k[X] (Ring k) X) :=
          (map_mul _ _ _).symm
      _ = 1 := by rw [mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  exact (isUnit_invSelf k).mul_left_inj.mp (h1.trans (IsLocalization.Away.mul_invSelf _).symm)

/-- The inversion is an involution. -/
theorem inversionHom_inversionHom (z : Ring k) : inversionHom k (inversionHom k z) = z := by
  have : (inversionHom k).comp (inversionHom k) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X : k[X]))
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [algebraMap_C, inversionHom_algebraMap_k, inversionHom_algebraMap_k]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [inversionHom_algebraMap_X, inversionHom_invSelf]
  exact DFunLike.congr_fun this z

/-- The inversion as a ring automorphism. -/
def inversion : Ring k ≃+* Ring k :=
  RingEquiv.ofRingHom (inversionHom k) (inversionHom k)
    (RingHom.ext (inversionHom_inversionHom k)) (RingHom.ext (inversionHom_inversionHom k))

/-- The chart at `∞` is the chart at `0` precomposed with the inversion. -/
theorem chartInfty_eq :
    chartInfty k = Spec.map (CommRingCat.ofHom (inversionHom k)) ≫ chartZero k := by
  rw [chartInfty, chartZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    inversionHom_comp_algebraMap]

/-- The local ring of `Spec k[x]` at a point, with its `k[x]`-algebra structure. -/
abbrev stalkAt (q : Spec (CommRingCat.of k[X])) : CommRingCat :=
  (Spec (CommRingCat.of k[X])).presheaf.stalk q

/-- The `k[x]`-algebra structure on the local ring of `Spec k[x]` at `q`. -/
instance (q : Spec (CommRingCat.of k[X])) : Algebra k[X] (stalkAt k q) :=
  StructureSheaf.stalkAlgebra (CommRingCat.of k[X]) q

/-- The ideal of a point of `Spec k[x]` is prime. -/
instance (q : Spec (CommRingCat.of k[X])) : q.asIdeal.IsPrime := q.isPrime

/-- The local ring of `Spec k[x]` at `q` is the localization of `k[x]` at the prime `q`. -/
instance (q : Spec (CommRingCat.of k[X])) : IsLocalization.AtPrime (stalkAt k q) q.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (CommRingCat.of k[X]) q

variable {k}

variable (k) in
/-- The chart at `0` is the inclusion of the basic open `D(x)` of `Spec k[x]`, through the
isomorphism `D(x) ≅ Spec k[x]_x`. -/
theorem basicOpenIsoSpecAway_hom_chartZero :
    (basicOpenIsoSpecAway (R := CommRingCat.of k[X]) (X : k[X])).hom ≫ chartZero k =
      Scheme.Opens.ι (X := Spec (CommRingCat.of k[X])) (PrimeSpectrum.basicOpen (X : k[X])) :=
  basicOpenIsoSpecAway_hom_SpecMap _

/-- The morphism `Spec C ⟶ Spec k[x]_x` induced by `φ` is the cover map
`AffineFieldFactors.coverMap` to `D(x)` followed by the isomorphism `D(x) ≅ Spec k[x]_x`. -/
theorem coverMap_comp_basicOpenIsoSpecAway_hom {C : Type u} [CommRing C] (φ : Ring k →+* C) :
    letI : Algebra (Localization.Away (X : k[X])) C := φ.toAlgebra
    (Iso.refl (Spec (CommRingCat.of C))).hom ≫ Spec.map (CommRingCat.ofHom φ) =
      AffineFieldFactors.coverMap (R := CommRingCat.of k[X]) (X : k[X]) C ≫
        (basicOpenIsoSpecAway (R := CommRingCat.of k[X]) (X : k[X])).hom := by
  let : Algebra (Localization.Away (X : k[X])) C := φ.toAlgebra
  rw [Iso.refl_hom, Category.id_comp, AffineFieldFactors.coverMap, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The spectrum of the map to the stalk at `q` is `fromSpecStalk q`. -/
private theorem spec_map_algebraMap_stalk (q : Spec (CommRingCat.of k[X])) :
    Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of k[X])
      ((Spec (CommRingCat.of k[X])).presheaf.stalk q))) =
      (Spec (CommRingCat.of k[X])).fromSpecStalk q := by
  rw [Spec.fromSpecStalk_eq']
  rfl

/-- **Tameness at `0` from the field factors.** -/
theorem isTamelyRamifiedInCodimensionOne_chartZero_of (C : Type u) [CommRing C]
    (φ : Ring k →+* C)
    (H : ∀ (q : Spec (CommRingCat.of k[X])), (X : k[X]) ∈ q.asIdeal →
      ∀ [IsDomain (stalkAt k q)] [IsDiscreteValuationRing (stalkAt k q)]
        (K L : Type u) [Field K] [Field L] [Algebra (stalkAt k q) K]
        [IsFractionRing (stalkAt k q) K] [Algebra K L] [FiniteDimensional K L]
        [Algebra.IsSeparable K L] [Algebra (stalkAt k q) L] [IsScalarTower (stalkAt k q) K L]
        (ψ : C →+* L),
        (∀ r : k[X], ψ (φ (algebraMap k[X] (Ring k) r)) =
          algebraMap (stalkAt k q) L (algebraMap k[X] (stalkAt k q) r)) →
        Algebra.adjoin K (Set.range ψ) = ⊤ →
        IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo (stalkAt k q) K L) :
    Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartZero k)
      (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra (Localization.Away (X : k[X])) C := φ.toAlgebra
  have key : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec (CommRingCat.of k[X])) (PrimeSpectrum.basicOpen (X : k[X])))
      (AffineFieldFactors.coverMap (R := CommRingCat.of k[X]) (X : k[X]) C) := by
    intro Z hZ hD hV K L _ _ _ _ _ _ _ _ _ hFF
    obtain ⟨ψ, hψ, hgen⟩ := AffineFieldFactors.exists_ringHom_of_isFieldFactorAt Z.genericPoint
      (spec_map_algebraMap_stalk Z.genericPoint) hFF
    have hX : (X : k[X]) ∈ Z.genericPoint.asIdeal := by
      by_contra h
      exact hZ ⟨⟨Z.genericPoint, h⟩, rfl⟩
    have := hD
    have := hV
    exact H Z.genericPoint hX K L ψ hψ hgen
  exact Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne.of_iso _ _
    (basicOpenIsoSpecAway_hom_chartZero k) (coverMap_comp_basicOpenIsoSpecAway_hom φ) key

/-- **The field factors of a cover tame at `0` are tame.** For the point `q` of `Spec k[x]` on
the boundary (`x ∈ q`) with discrete valuation local ring, every field factor of the cover is
tamely ramified over that local ring. -/
theorem isTamelyRamifiedWithRespectTo_of_chartZero {C : Type u} [CommRing C] (φ : Ring k →+* C)
    (h : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartZero k)
      (Spec.map (CommRingCat.ofHom φ)))
    (q : Spec (CommRingCat.of k[X])) (hq : (X : k[X]) ∈ q.asIdeal)
    [IsDomain (stalkAt k q)] [IsDiscreteValuationRing (stalkAt k q)]
    (K L : Type u) [Field K] [Field L] [Algebra (stalkAt k q) K]
    [IsFractionRing (stalkAt k q) K] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Algebra (stalkAt k q) L] [IsScalarTower (stalkAt k q) K L]
    (ψ : C →+* L)
    (hψ : ∀ r : k[X], ψ (φ (algebraMap k[X] (Ring k) r)) =
      algebraMap (stalkAt k q) L (algebraMap k[X] (stalkAt k q) r))
    (hgen : Algebra.adjoin K (Set.range ψ) = ⊤) :
    IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo (stalkAt k q) K L := by
  let : Algebra (Localization.Away (X : k[X])) C := φ.toAlgebra
  have hj : (basicOpenIsoSpecAway (R := CommRingCat.of k[X]) (X : k[X])).symm.hom ≫
      Scheme.Opens.ι (X := Spec (CommRingCat.of k[X])) (PrimeSpectrum.basicOpen (X : k[X])) =
        chartZero k := by
    rw [Iso.symm_hom, ← basicOpenIsoSpecAway_hom_chartZero k, Iso.inv_hom_id_assoc]
  have hf : (Iso.refl (Spec (CommRingCat.of C))).hom ≫
      AffineFieldFactors.coverMap (R := CommRingCat.of k[X]) (X : k[X]) C =
        Spec.map (CommRingCat.ofHom φ) ≫
          (basicOpenIsoSpecAway (R := CommRingCat.of k[X]) (X : k[X])).symm.hom := by
    rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    rfl
  have h' := Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne.of_iso _ _ hj hf h
  have hco : Order.coheight q = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight q
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  obtain ⟨Z, rfl⟩ : ∃ Z : StacksDraft.AlgebraicGeometry.Divisors.PrimeDivisorWeilGroup.PrimeDivisor
      (Spec (CommRingCat.of k[X])), Z.genericPoint = q :=
    ⟨weilPrimeDivisorOfCoheightOne q hco, genericPoint_weilPrimeDivisorOfCoheightOne q hco⟩
  have hZ : Z.genericPoint ∉ Set.range (Scheme.Opens.ι (X := Spec (CommRingCat.of k[X]))
      (PrimeSpectrum.basicOpen (X : k[X]))).base := by
    rintro ⟨u, hu⟩
    rw [← hu] at hq
    exact u.2 hq
  have hg : IsUnit (algebraMap (stalkAt k Z.genericPoint) K
      (algebraMap (CommRingCat.of k[X]) _ (X : k[X]))) := by
    rw [isUnit_iff_ne_zero, Ne, ← map_zero (algebraMap (stalkAt k Z.genericPoint) K),
      (IsFractionRing.injective _ K).eq_iff, ← map_zero (algebraMap (CommRingCat.of k[X])
        (stalkAt k Z.genericPoint))]
    intro h0
    exact X_ne_zero (IsLocalization.injective (stalkAt k Z.genericPoint)
      (Ideal.primeCompl_le_nonZeroDivisors Z.genericPoint.asIdeal) h0)
  exact h' Z hZ inferInstance inferInstance K L
    (AffineFieldFactors.isFieldFactorAt_of_ringHom Z.genericPoint
      (spec_map_algebraMap_stalk Z.genericPoint) hg ψ hψ hgen)

/-- The inversion is an isomorphism in `CommRingCat`. -/
theorem isIso_ofHom_inversionHom : IsIso (CommRingCat.ofHom (inversionHom k)) :=
  ⟨⟨CommRingCat.ofHom (inversionHom k), by ext; exact inversionHom_inversionHom k _,
    by ext; exact inversionHom_inversionHom k _⟩⟩

/-- **Tameness at `∞` is tameness at `0` after the inversion.** -/
theorem isTamelyRamifiedInCodimensionOne_chartInfty_iff {C : Type u} [CommRing C]
    (φ : Ring k →+* C) :
    Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartInfty k)
        (Spec.map (CommRingCat.ofHom φ)) ↔
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (chartZero k)
        (Spec.map (CommRingCat.ofHom (φ.comp (inversionHom k)))) := by
  have := isIso_ofHom_inversionHom (k := k)
  let eU : Gm k ≅ Gm k := asIso (Spec.map (CommRingCat.ofHom (inversionHom k)))
  have hcomp : Spec.map (CommRingCat.ofHom (φ.comp (inversionHom k))) =
      Spec.map (CommRingCat.ofHom φ) ≫ eU.hom := by
    rw [asIso_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne.of_iso eU
      (Iso.refl (Spec (CommRingCat.of C))) (by rw [asIso_hom, chartInfty_eq])
      (by rw [Iso.refl_hom, Category.id_comp, hcomp]) h
  · refine Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne.of_iso eU.symm
      (Iso.refl (Spec (CommRingCat.of C))) ?_ ?_ h
    · rw [Iso.symm_hom, chartInfty_eq]
      show eU.inv ≫ eU.hom ≫ chartZero k = chartZero k
      rw [Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.id_comp, hcomp, Category.assoc, Iso.symm_hom, Iso.hom_inv_id,
        Category.comp_id]

end AlgebraicGeometry.TameMultiplicativeGroup

end
