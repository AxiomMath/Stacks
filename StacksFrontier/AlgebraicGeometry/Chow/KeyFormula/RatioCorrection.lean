module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.OutsideFamily

/-!
# Changing the local generator: the ratio correction

The local reciprocity law at a codimension-two point `x` of `X` is read in
`Stacks.Chow.KeyFormulaSituation.exists_finsum_fracTameSymbolOrderAt_component_eq_zero` through a
single pair of rational functions `a`, `b` expressing `s` and `t` in trivializations of `L` and
`N` valid at every generization of `x`, while the situation of Stacks 0AYB carries the
per-component ratios `f_i = s / s_i` and `g_i = t / t_i` of its chosen generators. The two differ
by a unit, and this file is the bookkeeping of that difference.

Two coordinates `a`, `a'` of one meromorphic section of `L` at a point `z` satisfy `a = u a'` for
a unit `u` of `𝒪_{X, z}`: the two stalk bases they are taken against differ by a unit, which is
the mechanism behind the well-definedness of the order of vanishing, Stacks 02SF. Applied to
`f_i` and to any coordinate `a` of `s` at `ξ_i` this gives `f_i = u a`, and when `ξ_i` is the
point cut out by a height-one prime `𝔮` of `A = 𝒪_{X, x}` the local ring `𝒪_{X, ξ_i}` is the
localization `A_𝔮` (`Stacks.Chow.exists_isUnit_algebraMap_localization_eq`), so `u` is a unit of
`A_𝔮` as well.

The change this produces in the summand `ord_{A/𝔮}(∂_{A_𝔮}(·, ·))` of Stacks 0EAX is additive,
the summand being bi-additive, but it is **not zero**. By Stacks 0EAN the symbol of a unit `u` of
`A_𝔮` against a nonzerodivisor `c` is the residue of `u` raised to `length(A_𝔮 / c A_𝔮)`, so for
`g = c / d` the summand is

`ord_{A/𝔮}(∂_{A_𝔮}(u, g)) = (length(A_𝔮/c) - length(A_𝔮/d)) · ord_{A/𝔮}(ū)`,

and the second factor is the order of vanishing along `A / 𝔮` of a *nonzero element of the
residue field* `κ(𝔮)`, which is unconstrained: for `A = k[X₀, X₁]`, `𝔮 = (X₀)`, the unit `X₁` of
`A_𝔮` and the argument `X₀`, the summand is `1`. Only when *both* arguments come from units of
`A_𝔮` does the summand vanish, which is
`Stacks.Chow.fracTameSymbolOrderAt_eq_zero_of_isUnit`. So the generators cannot be substituted
for free in the local reciprocity law; the correction is recorded here instead.

## Main results

* `Stacks.Chow.exists_isUnit_mul_eq_of_isCoordinateAt` — **two coordinates of the same
  meromorphic section at a point differ by the image of a unit of the local ring there**.
* `Stacks.Chow.exists_isUnit_localization_mul_eq_of_isCoordinateAt` — the same, with the unit read
  in the localization of `𝒪_{X, x}` at a height-one prime.
* `Stacks.Chow.KeyFormulaSituation.exists_isUnit_mul_eq_ratioL` and
  `Stacks.Chow.KeyFormulaSituation.exists_isUnit_mul_eq_ratioN` — **`f_i = u a` and `g_i = v b`**
  for any coordinates `a` of `s` and `b` of `t` at `ξ_i`.
* `Stacks.Chow.KeyFormulaSituation.exists_isUnit_localization_mul_eq_ratioL` and
  `Stacks.Chow.KeyFormulaSituation.exists_isUnit_localization_mul_eq_ratioN` — the same with the
  unit read in `A_{𝔮_i}`, for a member of the family through a point `x`.
* `Stacks.Chow.fracTameSymbolOrderAt_isUnit_left` — **the summand of Stacks 0EAX on a unit of
  `A_𝔮` against a fraction**, as a product of two orders of vanishing.
* `Stacks.Chow.exists_isUnit_fracTameSymbolOrderAt_ne_zero` — **that summand is not always zero**,
  so substituting one coordinate for another changes the summand of Stacks 0EAX.
* `Stacks.Chow.KeyFormulaSituation.fracTameSymbolOrderAt_ratioL_eq_add` and
  `Stacks.Chow.KeyFormulaSituation.fracTameSymbolOrderAt_ratioN_eq_add` — **the summand at `f_i`
  is the summand at `a` plus the summand at the correcting unit**.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0EAN](https://stacks.math.columbia.edu/tag/0EAN)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Two coordinates of one section differ by a unit -/

section Coordinate

variable {X : Scheme.{u}} [IsIntegral X] {L : X.Modules}

/-- **Two coordinates of the same meromorphic section at a point differ by a unit.** If `a` and
`a'` both express the meromorphic section `s` of `L` in bases of the stalk `L_z`, then `a = u a'`
for a unit `u` of `𝒪_{X, z}`: the two bases differ by a unit. -/
theorem exists_isUnit_mul_eq_of_isCoordinateAt {z : X} (hL : IsTrivializedNear L z)
    {s : L.presheaf.stalk (genericPoint X)} {a a' : X.functionField}
    (ha : IsCoordinateAt L z s a) (ha' : IsCoordinateAt L z s a') :
    ∃ u : X.presheaf.stalk z, IsUnit u ∧
      a = algebraMap (X.presheaf.stalk z) X.functionField u * a' := by
  obtain ⟨m, hm, hsa⟩ := ha
  obtain ⟨m', hm', hsa'⟩ := ha'
  obtain ⟨u, hu, hmu⟩ := exists_isUnit_smul_eq hm hm'
  refine ⟨u, hu, (hm.toGenericStalk hL).injective ?_⟩
  show a • toGenericStalk L z m =
    (algebraMap (X.presheaf.stalk z) X.functionField u * a') • toGenericStalk L z m
  rw [mul_comm, mul_smul, ← toGenericStalk_smul, ← hmu, ← hsa', hsa]

/-- **Two coordinates at the point of a height-one prime `𝔮` of `𝒪_{X, x}` differ by a unit of
`A_𝔮`.** The local ring at that point is the localization `A_𝔮`, and the two structure maps to the
fraction field of `A = 𝒪_{X, x}` agree. -/
theorem exists_isUnit_localization_mul_eq_of_isCoordinateAt {x : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x))
    (hL : IsTrivializedNear L (pointOfHeightOnePrime 𝔮))
    {s : L.presheaf.stalk (genericPoint X)} {a a' : X.functionField}
    (ha : IsCoordinateAt L (pointOfHeightOnePrime 𝔮) s a)
    (ha' : IsCoordinateAt L (pointOfHeightOnePrime 𝔮) s a') :
    ∃ w : Localization.AtPrime 𝔮.1.asIdeal, IsUnit w ∧
      functionFieldEquivFractionRing x a =
        algebraMap (Localization.AtPrime 𝔮.1.asIdeal) (FractionRing (X.presheaf.stalk x)) w *
          functionFieldEquivFractionRing x a' := by
  obtain ⟨u, hu, hau⟩ := exists_isUnit_mul_eq_of_isCoordinateAt hL ha ha'
  obtain ⟨w, hw, hwu⟩ := exists_isUnit_algebraMap_localization_eq 𝔮 hu
  exact ⟨w, hw, by rw [hau, map_mul, hwu]⟩

end Coordinate

/-! ### The ratios of the situation against an arbitrary coordinate -/

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

/-- **`f_i = u a`.** The ratio `f_i = s / s_i` of the situation and any coordinate `a` of `s` at
`ξ_i` differ by a unit of `B_i = 𝒪_{X, ξ_i}`, both expressing `s` in a basis of `L_{ξ_i}`. -/
theorem exists_isUnit_mul_eq_ratioL (i : ℱ.Index) {a : X.functionField}
    (ha : IsCoordinateAt L (ℱ.componentPoint i) ℱ.sectionL a) :
    ∃ u : X.presheaf.stalk (ℱ.componentPoint i), IsUnit u ∧
      ℱ.ratioL i =
        algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField u * a :=
  have := isInvertible_presheaf L
  exists_isUnit_mul_eq_of_isCoordinateAt
    (isTrivializedNear_of_isInvertible L (ℱ.componentPoint i)) (ℱ.isCoordinateAt_ratioL i) ha

/-- **`g_i = v b`**, as in `Stacks.Chow.KeyFormulaSituation.exists_isUnit_mul_eq_ratioL`. -/
theorem exists_isUnit_mul_eq_ratioN (i : ℱ.Index) {b : X.functionField}
    (hb : IsCoordinateAt N (ℱ.componentPoint i) ℱ.sectionN b) :
    ∃ v : X.presheaf.stalk (ℱ.componentPoint i), IsUnit v ∧
      ℱ.ratioN i =
        algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField v * b :=
  have := isInvertible_presheaf N
  exists_isUnit_mul_eq_of_isCoordinateAt
    (isTrivializedNear_of_isInvertible N (ℱ.componentPoint i)) (ℱ.isCoordinateAt_ratioN i) hb

/-- Two coordinates at a point `z` equal to that of a height-one prime differ by a unit of `A_𝔮`. -/
private theorem exists_isUnit_localization_mul_eq_of_pointOfHeightOnePrime_eq {x z : X}
    (𝔮 : HeightOnePrime (X.presheaf.stalk x)) (hz : pointOfHeightOnePrime 𝔮 = z)
    {M : X.Modules} [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property M]
    {s : M.presheaf.stalk (genericPoint X)} {a a' : X.functionField}
    (ha : IsCoordinateAt M z s a) (ha' : IsCoordinateAt M z s a') :
    ∃ w : Localization.AtPrime 𝔮.1.asIdeal, IsUnit w ∧
      functionFieldEquivFractionRing x a =
        algebraMap (Localization.AtPrime 𝔮.1.asIdeal) (FractionRing (X.presheaf.stalk x)) w *
          functionFieldEquivFractionRing x a' := by
  subst hz
  have := isInvertible_presheaf M
  exact exists_isUnit_localization_mul_eq_of_isCoordinateAt 𝔮
    (isTrivializedNear_of_isInvertible M _) ha ha'

/-- **`f_i = u a` with `u` a unit of `A_{𝔮_i}`.** For a member `Z_i` of the family through `x`,
the correcting unit of `𝒪_{X, ξ_i}` is a unit of the localization of `A = 𝒪_{X, x}` at the
height-one prime `𝔮_i` that `Z_i` cuts out. -/
theorem exists_isUnit_localization_mul_eq_ratioL {x : X}
    (i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x}) {a : X.functionField}
    (ha : IsCoordinateAt L (ℱ.componentPoint i.1) ℱ.sectionL a) :
    ∃ w : Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal, IsUnit w ∧
      functionFieldEquivFractionRing x (ℱ.ratioL i.1) =
        algebraMap (Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal)
            (FractionRing (X.presheaf.stalk x)) w *
          functionFieldEquivFractionRing x a :=
  exists_isUnit_localization_mul_eq_of_pointOfHeightOnePrime_eq _
    (ℱ.pointOfHeightOnePrime_componentHeightOnePrime i) (ℱ.isCoordinateAt_ratioL i.1) ha

/-- **`g_i = v b` with `v` a unit of `A_{𝔮_i}`**, as in
`Stacks.Chow.KeyFormulaSituation.exists_isUnit_localization_mul_eq_ratioL`. -/
theorem exists_isUnit_localization_mul_eq_ratioN {x : X}
    (i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x}) {b : X.functionField}
    (hb : IsCoordinateAt N (ℱ.componentPoint i.1) ℱ.sectionN b) :
    ∃ w : Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal, IsUnit w ∧
      functionFieldEquivFractionRing x (ℱ.ratioN i.1) =
        algebraMap (Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal)
            (FractionRing (X.presheaf.stalk x)) w *
          functionFieldEquivFractionRing x b :=
  exists_isUnit_localization_mul_eq_of_pointOfHeightOnePrime_eq _
    (ℱ.pointOfHeightOnePrime_componentHeightOnePrime i) (ℱ.isCoordinateAt_ratioN i.1) hb

end KeyFormulaSituation

/-! ### The summand of Stacks 0EAX on a unit -/

section Algebraic

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

attribute [local instance] krullDimLE_localization_heightOnePrime

/-- **The summand of Stacks 0EAX on a unit of `A_𝔮` against a fraction `c / d`.** By Stacks 0EAN
the symbol of a unit `w` against a nonzerodivisor is the residue of `w` raised to the length of
the quotient, so the summand is

`ord_{A/𝔮}(∂_{A_𝔮}(w, c/d)) = (length(A_𝔮/c) - length(A_𝔮/d)) · ord_{A/𝔮}(w̄)`. -/
theorem fracTameSymbolOrderAt_isUnit_left (hdim : ringKrullDim A = 2) (p : HeightOnePrime A)
    (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
    {w : Localization.AtPrime p.1.asIdeal} (hw : IsUnit w)
    {W G : (FractionRing A)ˣ}
    (hW : (W : FractionRing A) =
      algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing A) w)
    (c d : nonZeroDivisors (Localization.AtPrime p.1.asIdeal))
    (hG : G = regularFractionUnit c * (regularFractionUnit (Q := FractionRing A) d)⁻¹) :
    fracTameSymbolOrderAt hdim p symb W G =
      ((Ring.ord (Localization.AtPrime p.1.asIdeal)
            (c : Localization.AtPrime p.1.asIdeal)).toNat -
          (Ring.ord (Localization.AtPrime p.1.asIdeal)
            (d : Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
        heightOneOrd hdim p
          (Units.map (IsLocalRing.residue (Localization.AtPrime p.1.asIdeal)).toMonoidHom
            hw.unit) := by
  have hwz : w ∈ nonZeroDivisors (Localization.AtPrime p.1.asIdeal) := hw.mem_nonZeroDivisors
  have hWp : W = regularFractionUnit (Q := FractionRing A) ⟨w, hwz⟩ *
      (regularFractionUnit (Q := FractionRing A)
        (1 : nonZeroDivisors (Localization.AtPrime p.1.asIdeal)))⁻¹ := by
    rw [map_one, inv_one, mul_one]
    exact Units.ext (by rw [hW, regularFractionUnit_val])
  rw [fracTameSymbolOrderAt_eq_heightOneOrd,
    symb.extend_eq (FractionRing A) ⟨w, hwz⟩ 1 c d hWp hG,
    symb.unit_left ⟨w, hwz⟩ c hw.unit hw.unit_spec.symm,
    symb.unit_left ⟨w, hwz⟩ d hw.unit hw.unit_spec.symm,
    symb.one_left, symb.one_left, inv_one, mul_one, mul_one,
    heightOneOrd_mul, heightOneOrd_inv, heightOneOrd_pow, heightOneOrd_pow]
  ring

end Algebraic

/-! ### The summand of Stacks 0EAX on a unit does not vanish -/

/-- **A unit argument does not make the summand of Stacks 0EAX vanish.** At the height-one prime
`(X₀)` of `k[X₀, X₁]` the variable `X₁` becomes a unit of the localization, and the summand of
Stacks 0EAX on the pair `X₁`, `X₀` is `1`.

So in `Stacks.Chow.KeyFormulaSituation.fracTameSymbolOrderAt_ratioL_eq_add` the correcting term is
genuinely present: the ratio `f_i` and a coordinate `a` of `s` at `ξ_i` can have different
tame-symbol orders. Vanishing needs *both* arguments to come from units of the localization,
which is `Stacks.Chow.fracTameSymbolOrderAt_eq_zero_of_isUnit`. -/
theorem exists_isUnit_fracTameSymbolOrderAt_ne_zero (k : Type u) [Field k] :
    ∃ (p : HeightOnePrime (MvPolynomial (Fin 2) k))
      (symb : RegularTameSymbol (Localization.AtPrime p.1.asIdeal))
      (w : Localization.AtPrime p.1.asIdeal) (W G : (FractionRing (MvPolynomial (Fin 2) k))ˣ),
      IsUnit w ∧
      (W : FractionRing (MvPolynomial (Fin 2) k)) =
        algebraMap (Localization.AtPrime p.1.asIdeal)
          (FractionRing (MvPolynomial (Fin 2) k)) w ∧
      fracTameSymbolOrderAt (MvPolynomial.ringKrullDim_fin_two k) p symb W G ≠ 0 := by
  refine ⟨mvPolynomialHeightOnePrimeX k 0, normalHeightOneSymbol _,
    toLocalizationNonZeroDivisor (mvPolynomialHeightOnePrimeX k 0).1.asIdeal
      (mvPolynomialX k 1),
    regularFractionUnit (mvPolynomialX k 1), regularFractionUnit (mvPolynomialX k 0),
    isUnit_toLocalizationNonZeroDivisor (mvPolynomialHeightOnePrimeX k 0).1.asIdeal
      (mvPolynomialX k 1) (notMem_span_mvPolynomialX k (by decide : (0 : Fin 2) ≠ 1)), ?_, ?_⟩
  · rw [← regularFractionUnit_toLocalizationNonZeroDivisor
      (mvPolynomialHeightOnePrimeX k 0) (mvPolynomialX k 1), regularFractionUnit_val]
  · rw [fracTameSymbolOrderAt_mvPolynomialX_eq_one k (by decide : (0 : Fin 2) ≠ 1)]
    exact one_ne_zero

/-! ### Substituting the ratios of the situation into the local reciprocity law -/

/-- A unit `Fr = (image of a unit `w`) * F` of an algebra is `W * F` for a unit `W` over `w`. -/
private theorem exists_unit_eq_mul_of_isUnit {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {w : R} (hw : IsUnit w) {F Fr : Sˣ} (h : (Fr : S) = algebraMap R S w * F) :
    ∃ W : Sˣ, (W : S) = algebraMap R S w ∧ Fr = W * F :=
  ⟨(hw.map (algebraMap R S)).unit, (hw.map _).unit_spec,
    Units.ext (by rw [Units.val_mul, (hw.map _).unit_spec, h])⟩

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

/-- **The summand of Stacks 0EAX at `f_i` is the summand at `a` plus the summand at the
correcting unit.** For a member `Z_i` of the family through a codimension-two point `x`, the ratio
`f_i` of the situation is `W a` for a unit `W` coming from a unit of `A_{𝔮_i}`, and the summand of
Stacks 0EAX is additive in its first argument.

The correcting summand is computed by `Stacks.Chow.fracTameSymbolOrderAt_isUnit_left`, and is not
zero in general (`Stacks.Chow.exists_isUnit_fracTameSymbolOrderAt_ne_zero`). -/
theorem fracTameSymbolOrderAt_ratioL_eq_add [IsLocallyNoetherian X] {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x})
    (symb : RegularTameSymbol (Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal))
    {a : X.functionField} (ha : IsCoordinateAt L (ℱ.componentPoint i.1) ℱ.sectionL a)
    {F Fr G : (FractionRing (X.presheaf.stalk x))ˣ}
    (hF : (F : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x a)
    (hFr : (Fr : FractionRing (X.presheaf.stalk x)) =
      functionFieldEquivFractionRing x (ℱ.ratioL i.1)) :
    ∃ (W : (FractionRing (X.presheaf.stalk x))ˣ)
      (w : Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal), IsUnit w ∧
      (W : FractionRing (X.presheaf.stalk x)) =
        algebraMap (Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal)
          (FractionRing (X.presheaf.stalk x)) w ∧
      Fr = W * F ∧
      fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i) symb Fr G =
        fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i) symb W G +
          fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i) symb F G := by
  obtain ⟨w, hw, hwr⟩ := ℱ.exists_isUnit_localization_mul_eq_ratioL i ha
  obtain ⟨W, hW, hfactor⟩ := exists_unit_eq_mul_of_isUnit (F := F) hw (by rw [hFr, hwr, ← hF])
  exact ⟨W, w, hw, hW, hfactor, by
    rw [hfactor]; exact fracTameSymbolOrderAt_mul_left hdim _ symb _ F G⟩

/-- **The summand of Stacks 0EAX at `g_i` is the summand at `b` plus the summand at the correcting
unit**, as in `Stacks.Chow.KeyFormulaSituation.fracTameSymbolOrderAt_ratioL_eq_add`, in the second
argument of the symbol. -/
theorem fracTameSymbolOrderAt_ratioN_eq_add [IsLocallyNoetherian X] {x : X}
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (i : {i : ℱ.Index // ℱ.componentPoint i ⤳ x})
    (symb : RegularTameSymbol (Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal))
    {b : X.functionField} (hb : IsCoordinateAt N (ℱ.componentPoint i.1) ℱ.sectionN b)
    {F G Gr : (FractionRing (X.presheaf.stalk x))ˣ}
    (hG : (G : FractionRing (X.presheaf.stalk x)) = functionFieldEquivFractionRing x b)
    (hGr : (Gr : FractionRing (X.presheaf.stalk x)) =
      functionFieldEquivFractionRing x (ℱ.ratioN i.1)) :
    ∃ (V : (FractionRing (X.presheaf.stalk x))ˣ)
      (v : Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal), IsUnit v ∧
      (V : FractionRing (X.presheaf.stalk x)) =
        algebraMap (Localization.AtPrime (ℱ.componentHeightOnePrime i).1.asIdeal)
          (FractionRing (X.presheaf.stalk x)) v ∧
      Gr = V * G ∧
      fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i) symb F Gr =
        fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i) symb F V +
          fracTameSymbolOrderAt hdim (ℱ.componentHeightOnePrime i) symb F G := by
  obtain ⟨v, hv, hvr⟩ := ℱ.exists_isUnit_localization_mul_eq_ratioN i hb
  obtain ⟨V, hV, hfactor⟩ := exists_unit_eq_mul_of_isUnit (F := G) hv (by rw [hGr, hvr, ← hG])
  exact ⟨V, v, hv, hV, hfactor, by
    rw [hfactor]; exact fracTameSymbolOrderAt_mul_right hdim _ symb F _ G⟩

end KeyFormulaSituation

end Stacks.Chow

end
