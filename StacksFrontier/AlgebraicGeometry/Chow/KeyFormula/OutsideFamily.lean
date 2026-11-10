module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.HeightOnePrimeDictionary
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationData

/-!
# The prime divisors outside the family contribute nothing

The local reciprocity law Stacks 0EAX,
`Stacks.Chow.finsum_fracTameSymbolOrderAt_stalk_eq_zero`, sums over *all* height-one primes of
the local ring `A = 𝒪_{X, x}` at a codimension-two point, while the two cycles of the key
formula Stacks 0AYC are indexed by the family `{Z_i}` of the situation Stacks 0AYB. The two
index sets are compared through the condition that `s` generates `L` and `t` generates `N` at
the generic point of every prime divisor outside the family,
`Stacks.Chow.KeyFormulaSituation.isCoordinateAt_one_of_notMem`: along such a prime divisor the
two rational functions `f` and `g` of the source are units of the local ring, so the tame symbol
`∂(f, g)` is trivial there and the omitted primes contribute zero.

The comparison factors into three steps. The geometric one is that a coordinate of `s` at a
codimension-one point outside the family is the image of a unit of the local ring there — a
coordinate is determined up to a unit by `Stacks.Divisors.exists_isUnit_smul_eq`, and the
constant `1` is one of them. The algebraic one is that the summand of Stacks 0EAX vanishes at a
height-one prime at which both arguments come from units of the localization, which is
`Stacks.Chow.RegularTameSymbol.eq_one_of_isUnit`. Joining them is the identification of the local
ring at the point cut out by a height-one prime `𝔮` with the localization `A_𝔮`
(`Stacks.Chow.isLocalization_stalk_of_specializes`), under which the two structure maps to the
fraction field of `A` agree, both being maps out of a localization of `A` extending
`A → Frac(A)`.

A single pair of rational functions serves all the primes above one point: a local
trivialization of `L` near `x` is a trivialization at every generization of `x`, so the
coordinate it produces is a coordinate at every point of `X` specializing to `x`.

## Main definitions

* `Stacks.Chow.functionFieldEquivFractionRing` — the function field as the fraction field of the
  local ring at a point.
* `Stacks.Chow.KeyFormulaSituation.componentHeightOnePrime` — the height-one prime of
  `𝒪_{X, x}` cut out by a member of the family through `x`.

## Main results

* `Stacks.Chow.exists_isCoordinateAt_of_specializes` — a coordinate read from a local
  trivialization at `x` is a coordinate at every generization of `x`.
* `Stacks.Chow.exists_isUnit_algebraMap_eq_of_isCoordinateAt_one` — a coordinate of a
  meromorphic section that generates the stalk at `x` is the image of a unit of `𝒪_{X, x}`.
* `Stacks.Chow.KeyFormulaSituation.exists_isUnit_algebraMap_eq_sectionL` and
  `Stacks.Chow.KeyFormulaSituation.exists_isUnit_algebraMap_eq_sectionN` — **the ratios are
  units along a prime divisor outside the family**.
* `Stacks.Chow.KeyFormulaSituation.ord_eq_zero_of_notMem_left` and
  `Stacks.Chow.KeyFormulaSituation.ord_eq_zero_of_notMem_right` — hence they have order of
  vanishing zero there.
* `Stacks.Chow.fracTameSymbolOrderAt_eq_zero_of_isUnit` — the summand of Stacks 0EAX vanishes at
  a height-one prime at which both arguments come from units of the localization.
* `Stacks.Chow.exists_isUnit_algebraMap_localization_eq` — a unit of the local ring at the point
  cut out by a height-one prime is a unit of the localization at that prime.
* `Stacks.Chow.KeyFormulaSituation.fracTameSymbolOrderAt_eq_zero_of_notMem` — **the contribution
  of a prime divisor outside the family vanishes**.
* `Stacks.Chow.KeyFormulaSituation.finsum_fracTameSymbolOrderAt_eq_finsum_component` — **the
  reciprocity sum of Stacks 0EAX at a codimension-two point is the sum over the members of the
  family through that point**.
* `Stacks.Chow.KeyFormulaSituation.finsum_fracTameSymbolOrderAt_component_eq_zero` and
  `Stacks.Chow.KeyFormulaSituation.exists_finsum_fracTameSymbolOrderAt_component_eq_zero` —
  hence that family sum is zero, which is the local identity Stacks 0AYC consumes.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Coordinates at the generizations of a point -/

section Coordinate

variable {X : Scheme.{u}} [IsIntegral X] {L : X.Modules}

/-- **A coordinate read from a local trivialization at `x` is a coordinate at every generization
of `x`.** The trivializing section is defined at every point of an open neighbourhood of `x`,
hence at every generization of `x`, and its generic value does not depend on the point. -/
theorem exists_isCoordinateAt_of_specializes {x : X} (hL : IsTrivializedNear L x)
    (s : L.presheaf.stalk (genericPoint X)) :
    ∃ a : X.functionField, ∀ z : X, z ⤳ x → IsCoordinateAt L z s a := by
  obtain ⟨W, hxW, t, ht⟩ := hL
  have hηW : genericPoint X ∈ W := genericPoint_mem_of_mem hxW
  obtain ⟨a, ha⟩ := (IsStalkBasis.toGenericStalk ⟨W, hxW, t, ht⟩ (ht x hxW)).surjective s
  refine ⟨a, fun z hz ↦ ?_⟩
  have hzW : z ∈ W := hz.mem_open W.isOpen hxW
  refine ⟨L.presheaf.germ W z hzW t, ht z hzW, ?_⟩
  rw [toGenericStalk_germ hzW hηW, ← toGenericStalk_germ hxW hηW]
  exact ha.symm

/-- **A coordinate of a section generating the stalk is the image of a unit.** If the
meromorphic section `s` of `L` has the coordinate `1` at `x`, that is, if it is the generic value
of a generator of `L_x`, then every coordinate of `s` at `x` is the image in `R(X)` of a unit of
`𝒪_{X, x}`: two generators of `L_x` differ by a unit. -/
theorem exists_isUnit_algebraMap_eq_of_isCoordinateAt_one {x : X}
    (hL : IsTrivializedNear L x) {s : L.presheaf.stalk (genericPoint X)}
    (h1 : IsCoordinateAt L x s 1) {a : X.functionField} (ha : IsCoordinateAt L x s a) :
    ∃ u : X.presheaf.stalk x, IsUnit u ∧
      algebraMap (X.presheaf.stalk x) X.functionField u = a := by
  obtain ⟨m, hm, hs1⟩ := h1
  obtain ⟨m', hm', hsa⟩ := ha
  obtain ⟨u, hu, hmu⟩ := exists_isUnit_smul_eq hm hm'
  have key : a * algebraMap (X.presheaf.stalk x) X.functionField u = 1 := by
    refine (hm.toGenericStalk hL).injective ?_
    change (a * algebraMap (X.presheaf.stalk x) X.functionField u) • toGenericStalk L x m =
      (1 : X.functionField) • toGenericStalk L x m
    rw [mul_smul, ← toGenericStalk_smul, ← hmu, ← hsa, ← hs1]
  obtain ⟨v, huv, hvu⟩ := isUnit_iff_exists.mp hu
  refine ⟨v, isUnit_iff_exists.mpr ⟨u, hvu, huv⟩, ?_⟩
  calc algebraMap (X.presheaf.stalk x) X.functionField v
      = a * algebraMap (X.presheaf.stalk x) X.functionField u *
          algebraMap (X.presheaf.stalk x) X.functionField v := by rw [key, one_mul]
    _ = a * algebraMap (X.presheaf.stalk x) X.functionField (u * v) := by
        rw [map_mul]; ring
    _ = a := by rw [huv, map_one, mul_one]

end Coordinate

/-! ### The ratios along a prime divisor outside the family -/

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

/-- A codimension-one point which is not the generic point of a member of the family cuts out a
prime divisor which is not a member of the family. -/
theorem component_ne_ofCoheightOne {z : X} (hz : coheight z = 1)
    (hnot : ∀ i, ℱ.componentPoint i ≠ z) (i : ℱ.Index) :
    ℱ.component i ≠ PrimeDivisor.ofCoheightOne z hz := by
  intro hi
  refine hnot i ?_
  change (ℱ.component i).genericPoint = z
  rw [hi, PrimeDivisor.genericPoint_ofCoheightOne]

/-- **The ratio `f` is a unit along a prime divisor outside the family.** At a codimension-one
point `z` which is not the generic point of a member of the family the section `s` generates
`L_z`, so every coordinate of `s` at `z` is the image of a unit of `𝒪_{X, z}`.

This is the hypothesis of Stacks 0AYB that makes the family large enough to carry the key
formula Stacks 0AYC. -/
theorem exists_isUnit_algebraMap_eq_sectionL {z : X} (hz : coheight z = 1)
    (hnot : ∀ i, ℱ.componentPoint i ≠ z) {a : X.functionField}
    (ha : IsCoordinateAt L z ℱ.sectionL a) :
    ∃ u : X.presheaf.stalk z, IsUnit u ∧
      algebraMap (X.presheaf.stalk z) X.functionField u = a := by
  have := isInvertible_presheaf L
  have h1 := (ℱ.isCoordinateAt_one_of_notMem (PrimeDivisor.ofCoheightOne z hz)
    (ℱ.component_ne_ofCoheightOne hz hnot)).1
  rw [PrimeDivisor.genericPoint_ofCoheightOne] at h1
  exact exists_isUnit_algebraMap_eq_of_isCoordinateAt_one
    (isTrivializedNear_of_isInvertible L z) h1 ha

/-- **The ratio `g` is a unit along a prime divisor outside the family**, as in
`Stacks.Chow.KeyFormulaSituation.exists_isUnit_algebraMap_eq_sectionL`. -/
theorem exists_isUnit_algebraMap_eq_sectionN {z : X} (hz : coheight z = 1)
    (hnot : ∀ i, ℱ.componentPoint i ≠ z) {b : X.functionField}
    (hb : IsCoordinateAt N z ℱ.sectionN b) :
    ∃ v : X.presheaf.stalk z, IsUnit v ∧
      algebraMap (X.presheaf.stalk z) X.functionField v = b := by
  have := isInvertible_presheaf N
  have h1 := (ℱ.isCoordinateAt_one_of_notMem (PrimeDivisor.ofCoheightOne z hz)
    (ℱ.component_ne_ofCoheightOne hz hnot)).2
  rw [PrimeDivisor.genericPoint_ofCoheightOne] at h1
  exact exists_isUnit_algebraMap_eq_of_isCoordinateAt_one
    (isTrivializedNear_of_isInvertible N z) h1 hb

/-- **A coordinate of `s` at a codimension-one point outside the family has order of vanishing
zero**, being the image of a unit of the local ring there. -/
theorem ord_eq_zero_of_notMem_left [IsLocallyNoetherian X] {z : X} (hz : coheight z = 1)
    (hnot : ∀ i, ℱ.componentPoint i ≠ z) {a : X.functionField}
    (ha : IsCoordinateAt L z ℱ.sectionL a) : X.ord a z = 0 := by
  obtain ⟨u, hu, rfl⟩ := ℱ.exists_isUnit_algebraMap_eq_sectionL hz hnot ha
  exact Scheme.ord_algebraMap_of_isUnit hz hu

/-- **A coordinate of `t` at a codimension-one point outside the family has order of vanishing
zero**, as in `Stacks.Chow.KeyFormulaSituation.ord_eq_zero_of_notMem_left`. -/
theorem ord_eq_zero_of_notMem_right [IsLocallyNoetherian X] {z : X} (hz : coheight z = 1)
    (hnot : ∀ i, ℱ.componentPoint i ≠ z) {b : X.functionField}
    (hb : IsCoordinateAt N z ℱ.sectionN b) : X.ord b z = 0 := by
  obtain ⟨v, hv, rfl⟩ := ℱ.exists_isUnit_algebraMap_eq_sectionN hz hnot hb
  exact Scheme.ord_algebraMap_of_isUnit hz hv

end KeyFormulaSituation

/-! ### The summand of the local reciprocity law at a prime avoiding both arguments -/

section Algebraic

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

attribute [local instance] krullDimLE_localization_heightOnePrime

/-- **The summand of Stacks 0EAX vanishes at a height-one prime where both arguments are units of
the localization.** The tame symbol of two units of `A_𝔮` is trivial, by Stacks 0EAN, so its
order of vanishing along `A / 𝔮` is zero.

In the key formula Stacks 0AYC this is the vanishing of the contribution of a prime divisor
outside the family: there both `f` and `g` are units of the local ring at its generic point. -/
theorem fracTameSymbolOrderAt_eq_zero_of_isUnit (hdim : ringKrullDim A = 2)
    (p : HeightOnePrime A) (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    {f g : (FractionRing A)ˣ} {u v : Localization.AtPrime p.1.asIdeal}
    (hu : IsUnit u) (hv : IsUnit v)
    (hf : (f : FractionRing A) =
      algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) u)
    (hg : (g : FractionRing A) =
      algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) v) :
    fracTameSymbolOrderAt hdim p symb f g = 0 := by
  have hreg : ∀ (c : (FractionRing A)ˣ) {w : Localization.AtPrime p.1.asIdeal} (hw : IsUnit w),
      (c : FractionRing A) = algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) w →
        c = regularFractionUnit (Q := FractionRing A) ⟨w, hw.mem_nonZeroDivisors⟩ :=
    fun c _ _ h ↦ Units.ext (by rw [h, regularFractionUnit_val])
  rw [fracTameSymbolOrderAt_eq_heightOneOrd, hreg f hu hf, hreg g hv hg,
    RegularTameSymbol.extend_regularFractionUnit, symb.eq_one_of_isUnit hu hv,
    heightOneOrd_one]

end Algebraic

/-! ### The local ring at a generization as a localization -/

section Bridge

variable {X : Scheme.{u}} [IsIntegral X]

/-- The function field of an integral scheme as the fraction field of the local ring at a point:
both are localizations of that local ring at its nonzerodivisors. -/
abbrev functionFieldEquivFractionRing (x : X) :
    X.functionField ≃ₐ[X.presheaf.stalk x] FractionRing (X.presheaf.stalk x) :=
  (FractionRing.algEquiv (X.presheaf.stalk x) X.functionField).symm

/-- The structure map of the local ring at a generization `z` of `x` into the function field
factors the structure map of the local ring at `x`, the specialization maps on stalks being
functorial. -/
theorem algebraMap_stalk_functionField_algebraMap {x z : X} (h : z ⤳ x)
    (r : X.presheaf.stalk x) :
    letI : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    algebraMap (X.presheaf.stalk z) X.functionField
        (algebraMap (X.presheaf.stalk x) (X.presheaf.stalk z) r) =
      algebraMap (X.presheaf.stalk x) X.functionField r := by
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk z) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  simp only [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply,
    X.presheaf.stalkSpecializes_comp]

/-- **A unit of the local ring at the point cut out by a height-one prime is a unit of the
localization at that prime.** The local ring at that point is `A_𝔮`, by
`Stacks.Chow.isLocalization_stalk_of_specializes`, and its structure map to the fraction field of
`A` is the structure map of `A_𝔮`: both extend `A → Frac(A)` over a localization of `A`. -/
theorem exists_isUnit_algebraMap_localization_eq {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x))
    {u : X.presheaf.stalk (pointOfHeightOnePrime 𝔮)} (hu : IsUnit u) :
    ∃ w : Localization.AtPrime 𝔮.1.asIdeal, IsUnit w ∧
      algebraMap (Localization.AtPrime 𝔮.1.asIdeal) (FractionRing (X.presheaf.stalk x)) w =
        functionFieldEquivFractionRing x
          (algebraMap (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) X.functionField u) := by
  have hspec : pointOfHeightOnePrime 𝔮 ⤳ x := pointOfHeightOnePrime_specializes 𝔮
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) :=
    (X.presheaf.stalkSpecializes hspec).hom.toAlgebra
  have hloc : IsLocalization 𝔮.1.asIdeal.primeCompl
      (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) :=
    isLocalization_stalk_of_specializes hspec 𝔮.1 rfl
  set e := Localization.algEquiv 𝔮.1.asIdeal.primeCompl
    (X.presheaf.stalk (pointOfHeightOnePrime 𝔮))
  refine ⟨e.symm u, hu.map e.symm, ?_⟩
  have hcomp : ∀ r : X.presheaf.stalk x,
      algebraMap (Localization.AtPrime 𝔮.1.asIdeal) (FractionRing (X.presheaf.stalk x))
          (e.symm (algebraMap (X.presheaf.stalk x)
            (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) r)) =
        functionFieldEquivFractionRing x
          (algebraMap (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) X.functionField
            (algebraMap (X.presheaf.stalk x)
              (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) r)) := by
    intro r
    rw [e.symm.commutes r, ← IsScalarTower.algebraMap_apply,
      algebraMap_stalk_functionField_algebraMap hspec r, AlgEquiv.commutes]
  have key : (algebraMap (Localization.AtPrime 𝔮.1.asIdeal)
          (FractionRing (X.presheaf.stalk x))).comp e.symm.toRingEquiv.toRingHom =
      ((functionFieldEquivFractionRing x).toRingEquiv.toRingHom).comp
        (algebraMap (X.presheaf.stalk (pointOfHeightOnePrime 𝔮)) X.functionField) :=
    IsLocalization.ringHom_ext 𝔮.1.asIdeal.primeCompl (RingHom.ext hcomp)
  exact RingHom.congr_fun key u

end Bridge

/-! ### The contribution of a prime divisor outside the family -/

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

/-- **The contribution of a prime divisor outside the family to the local reciprocity law
vanishes.** At a height-one prime `𝔮` of `A = 𝒪_{X, x}` whose point is not the generic point of a
member of the family, the two rational functions `f` and `g` are units of `A_𝔮`, so the summand
`ord_{A/𝔮}(∂_{A_𝔮}(f, g))` of Stacks 0EAX is zero. -/
theorem fracTameSymbolOrderAt_eq_zero_of_notMem [IsLocallyNoetherian X] {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (𝔮 : HeightOnePrime (X.presheaf.stalk x))
    (hnot : ∀ i, ℱ.componentPoint i ≠ pointOfHeightOnePrime 𝔮)
    {a b : X.functionField}
    (ha : IsCoordinateAt L (pointOfHeightOnePrime 𝔮) ℱ.sectionL a)
    (hb : IsCoordinateAt N (pointOfHeightOnePrime 𝔮) ℱ.sectionN b)
    {F G : (FractionRing (X.presheaf.stalk x))ˣ}
    (hF : (F : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x a)
    (hG : (G : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x b) :
    fracTameSymbolOrderAt hdim 𝔮 (canonicalHeightOneSymbol 𝔮) F G = 0 := by
  obtain ⟨u, hu, hua⟩ := ℱ.exists_isUnit_algebraMap_eq_sectionL
    (coheight_pointOfHeightOnePrime 𝔮) hnot ha
  obtain ⟨v, hv, hvb⟩ := ℱ.exists_isUnit_algebraMap_eq_sectionN
    (coheight_pointOfHeightOnePrime 𝔮) hnot hb
  obtain ⟨w, hw, hwu⟩ := exists_isUnit_algebraMap_localization_eq 𝔮 hu
  obtain ⟨w', hw', hw'v⟩ := exists_isUnit_algebraMap_localization_eq 𝔮 hv
  exact fracTameSymbolOrderAt_eq_zero_of_isUnit hdim 𝔮 _ hw hw'
    (by rw [hF, hwu, hua]) (by rw [hG, hw'v, hvb])

/-- The height-one prime of `𝒪_{X, x}` cut out by a member of the family through `x`. -/
def componentHeightOnePrime {x : X} (i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x}) :
    HeightOnePrime (X.presheaf.stalk x) :=
  (heightOnePrimeEquivCoheightOneGenerization x).symm
    ⟨ℱ.componentPoint i.1, i.2, ℱ.coheight_componentPoint i.1⟩

/-- The height-one prime cut out by a member `Z_i` of the family through `x` corresponds to the
generic point `ξ_i` of `Z_i`. -/
@[simp]
theorem pointOfHeightOnePrime_componentHeightOnePrime {x : X}
    (i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x}) :
    pointOfHeightOnePrime (ℱ.componentHeightOnePrime i) = ℱ.componentPoint i.1 := by
  rw [← heightOnePrimeEquivCoheightOneGenerization_apply, componentHeightOnePrime,
    Equiv.apply_symm_apply]

/-- Distinct members of the family through `x` cut out distinct height-one primes of
`𝒪_{X, x}`. -/
theorem componentHeightOnePrime_injective {x : X} :
    Function.Injective (ℱ.componentHeightOnePrime (x := x)) := by
  intro i j hij
  have h : ℱ.componentPoint i.1 = ℱ.componentPoint j.1 := by
    rw [← ℱ.pointOfHeightOnePrime_componentHeightOnePrime i,
      ← ℱ.pointOfHeightOnePrime_componentHeightOnePrime j, hij]
  exact Subtype.ext (ℱ.component_injective (PrimeDivisor.genericPoint_injective h))

/-- **The reciprocity sum of Stacks 0EAX at a codimension-two point is carried by the family.**
Only the height-one primes of `𝒪_{X, x}` cut out by the members `Z_i` of the family through `x`
contribute to the sum of Stacks 0EAX, the summand at any other prime vanishing because `s` and
`t` generate there.

This is the index comparison the key formula Stacks 0AYC needs: its two cycles are indexed by the
family, while the local reciprocity law
`Stacks.Chow.finsum_fracTameSymbolOrderAt_stalk_eq_zero` sums over all height-one primes. -/
theorem finsum_fracTameSymbolOrderAt_eq_finsum_component [IsLocallyNoetherian X] {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    {a b : X.functionField}
    (ha : ∀ z : X, z ⤳ x → IsCoordinateAt L z ℱ.sectionL a)
    (hb : ∀ z : X, z ⤳ x → IsCoordinateAt N z ℱ.sectionN b)
    {F G : (FractionRing (X.presheaf.stalk x))ˣ}
    (hF : (F : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x a)
    (hG : (G : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x b) :
    ∑ᶠ 𝔮 : HeightOnePrime (X.presheaf.stalk x),
        fracTameSymbolOrderAt hdim 𝔮 (canonicalHeightOneSymbol 𝔮) F G =
      ∑ᶠ i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x},
        fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i)
          (canonicalHeightOneSymbol (ℱ.componentHeightOnePrime i)) F G := by
  set h : HeightOnePrime (X.presheaf.stalk x) → ℤ := fun 𝔮 =>
    fracTameSymbolOrderAt hdim 𝔮 (canonicalHeightOneSymbol 𝔮) F G
  have hsupp : Function.support h ⊆ Set.range (ℱ.componentHeightOnePrime (x := x)) := by
    intro 𝔮 h𝔮
    by_contra hmem
    refine h𝔮 (ℱ.fracTameSymbolOrderAt_eq_zero_of_notMem hdim 𝔮 (fun i hi ↦ ?_)
      (ha _ (pointOfHeightOnePrime_specializes 𝔮))
      (hb _ (pointOfHeightOnePrime_specializes 𝔮)) hF hG)
    have hs : ℱ.componentPoint i ⤳ x := hi ▸ pointOfHeightOnePrime_specializes 𝔮
    refine hmem ⟨⟨i, hs⟩, pointOfHeightOnePrime_injective ?_⟩
    rw [ℱ.pointOfHeightOnePrime_componentHeightOnePrime, hi]
  calc ∑ᶠ 𝔮, h 𝔮
      = ∑ᶠ 𝔮 ∈ Set.range (ℱ.componentHeightOnePrime (x := x)), h 𝔮 := by
        rw [finsum_mem_inter_support_eq h (Set.range (ℱ.componentHeightOnePrime (x := x)))
          Set.univ (by rw [Set.univ_inter]; exact Set.inter_eq_right.mpr hsupp),
          finsum_mem_univ]
    _ = ∑ᶠ i, h (ℱ.componentHeightOnePrime i) :=
        finsum_mem_range ℱ.componentHeightOnePrime_injective

/-- **The members of the family through a codimension-two point satisfy the local reciprocity
law.** Combining the index comparison with Stacks 0EAX,
`Stacks.Chow.finsum_fracTameSymbolOrderAt_stalk_eq_zero`: the contributions of the members `Z_i`
of the family through `x` sum to zero. -/
theorem finsum_fracTameSymbolOrderAt_component_eq_zero [IsLocallyNoetherian X] {x : X}
    (hx : coheight x = 2)
    {a b : X.functionField}
    (ha : ∀ z : X, z ⤳ x → IsCoordinateAt L z ℱ.sectionL a)
    (hb : ∀ z : X, z ⤳ x → IsCoordinateAt N z ℱ.sectionN b)
    {F G : (FractionRing (X.presheaf.stalk x))ˣ}
    (hF : (F : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x a)
    (hG : (G : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x b) :
    ∑ᶠ i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x},
        fracTameSymbolOrderAt (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx)
          (ℱ.componentHeightOnePrime i)
          (canonicalHeightOneSymbol (ℱ.componentHeightOnePrime i)) F G = 0 :=
  (ℱ.finsum_fracTameSymbolOrderAt_eq_finsum_component
    (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx) ha hb hF hG).symm.trans
    (finsum_fracTameSymbolOrderAt_stalk_eq_zero hx F G)

/-- **The two rational functions of the source, at a point of `X`.** A coordinate of `s` and a
coordinate of `t` read from local trivializations at `x` serve every generization of `x` at once,
and both are nonzero, the sections being nonzero. -/
theorem exists_isCoordinateAt_forall_specializes (x : X) :
    ∃ a b : X.functionField, a ≠ 0 ∧ b ≠ 0 ∧
      (∀ z : X, z ⤳ x → IsCoordinateAt L z ℱ.sectionL a) ∧
      ∀ z : X, z ⤳ x → IsCoordinateAt N z ℱ.sectionN b := by
  have := isInvertible_presheaf L
  have := isInvertible_presheaf N
  obtain ⟨a, ha⟩ :=
    exists_isCoordinateAt_of_specializes (isTrivializedNear_of_isInvertible L x) ℱ.sectionL
  obtain ⟨b, hb⟩ :=
    exists_isCoordinateAt_of_specializes (isTrivializedNear_of_isInvertible N x) ℱ.sectionN
  exact ⟨a, b, (ha x (specializes_refl x)).ne_zero ℱ.sectionL_ne_zero,
    (hb x (specializes_refl x)).ne_zero ℱ.sectionN_ne_zero, ha, hb⟩

/-- **The local reciprocity law of the situation at a codimension-two point.** For the pair of
rational functions `f`, `g` expressing `s` and `t` in local trivializations at a point `x` of
codimension two, the summands `ord_{A/𝔮_i}(∂_{A_{𝔮_i}}(f, g))` of Stacks 0EAX at the height-one
primes `𝔮_i` of `A = 𝒪_{X, x}` cut out by the members `Z_i` of the family through `x` sum to
zero: the primes omitted by the family contribute nothing.

This is the local identity the key formula Stacks 0AYC consumes at a codimension-two point of the
family, with the index set of the family rather than that of the local ring. -/
theorem exists_finsum_fracTameSymbolOrderAt_component_eq_zero [IsLocallyNoetherian X] {x : X}
    (hx : coheight x = 2) :
    ∃ (a b : X.functionField) (F G : (FractionRing (X.presheaf.stalk x))ˣ),
      (∀ z : X, z ⤳ x → IsCoordinateAt L z ℱ.sectionL a) ∧
      (∀ z : X, z ⤳ x → IsCoordinateAt N z ℱ.sectionN b) ∧
      (F : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x a ∧
      (G : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x b ∧
      ∑ᶠ i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x},
          fracTameSymbolOrderAt (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx)
            (ℱ.componentHeightOnePrime i)
            (canonicalHeightOneSymbol (ℱ.componentHeightOnePrime i)) F G = 0 := by
  obtain ⟨a, b, ha0, hb0, ha, hb⟩ := ℱ.exists_isCoordinateAt_forall_specializes x
  exact ⟨a, b, Units.mk0 _ ((map_ne_zero _).2 ha0), Units.mk0 _ ((map_ne_zero _).2 hb0), ha, hb,
    rfl, rfl, ℱ.finsum_fracTameSymbolOrderAt_component_eq_zero hx ha hb rfl rfl⟩

end KeyFormulaSituation

end Stacks.Chow

end
