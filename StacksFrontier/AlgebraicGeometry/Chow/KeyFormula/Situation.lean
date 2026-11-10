module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.DivisorRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.OrderComparison

/-!
# The situation preceding the key formula

Let `X` be an integral, locally Noetherian scheme, let `L` and `N` be invertible `𝒪_X`-modules
and let `s` and `t` be nonzero meromorphic sections of `L` and `N`. Choose a locally finite
family `{Z_i}` of prime divisors of `X` containing every prime divisor along which `s` or `t`
fails to generate, and for each `i` a generator `s_i` of `L_{ξ_i}` and a generator `t_i` of
`N_{ξ_i}`, where `ξ_i` is the generic point of `Z_i` and `B_i = 𝒪_{X, ξ_i}`. Writing

`s = f_i s_i` and `t = g_i t_i`

with `f_i`, `g_i` nonzero rational functions, one has `ord_{Z_i, L}(s) = ord_{B_i}(f_i)` and
`ord_{Z_i, N}(t) = ord_{B_i}(g_i)`, the divisors `div_L(s)` and `div_N(t)` are supported on the
family, the image `t_i|_{Z_i}` of `t_i` in the fibre `N_{ξ_i} ⊗ κ(ξ_i)` is a nonzero meromorphic
section of `N|_{Z_i}`, and the tame symbol `∂_{B_i}(f_i, g_i)` is a nonzero element of `κ(ξ_i)`.

This is the data and the elementary consequences from which Stacks 0AYC, the key formula,
compares `c_1(N) ∩ div_L(s)` with `c_1(L) ∩ div_N(t)`.

## Conventions

A meromorphic section is given by its value in the generic stalk: on an integral scheme the
sheaf of meromorphic sections of a quasi-coherent module is constant with value that stalk, and
a meromorphic section is regular exactly when its generic value is nonzero. This is the model
`Stacks.Divisors.orderOfVanishing` and `Stacks.Divisors.weilDivisorOfMeromorphicSection` use.

The generic value of a generator of `L_{ξ_i}` is a basis of the generic stalk `L_η` over the
function field, so `f_i` is the coordinate of `s` in that basis. The delta-dimension of `X` over
the base does not appear: it grades the Chow groups in which Stacks 0AYC takes place, and the
data of the situation are independent of it.

## Main definitions

* `Stacks.Chow.genericCoordOf` — the rational function `v / m` expressing a meromorphic section
  in terms of a stalk basis.
* `Stacks.Chow.KeyFormulaSituation` — the situation of Stacks 0AYB.
* `Stacks.Chow.KeyFormulaSituation.ratioL` and `Stacks.Chow.KeyFormulaSituation.ratioN` — the
  rational functions `f_i` and `g_i`.
* `Stacks.Chow.KeyFormulaSituation.weilDivisorL`,
  `Stacks.Chow.KeyFormulaSituation.weilDivisorN` — the divisors `div_L(s)` and `div_N(t)`.
* `Stacks.Chow.KeyFormulaSituation.restrictedGeneratorL`,
  `Stacks.Chow.KeyFormulaSituation.restrictedGeneratorN` — the restrictions `s_i|_{Z_i}` and
  `t_i|_{Z_i}`.
* `Stacks.Chow.KeyFormulaSituation.restrictedWeilDivisorL`,
  `Stacks.Chow.KeyFormulaSituation.restrictedWeilDivisorN` — the divisors
  `div_{L|Z_i}(s_i|Z_i)` and `div_{N|Z_i}(t_i|Z_i)`.
* `Stacks.Chow.KeyFormulaSituation.tameSymbol` — the tame symbol `∂_{B_i}(f_i, g_i)`.

## Main results

* `Stacks.Chow.KeyFormulaSituation.ratioL_smul_localGeneratorL` and
  `Stacks.Chow.KeyFormulaSituation.ratioN_smul_localGeneratorN` — the equations `s = f_i s_i`
  and `t = g_i t_i`.
* `Stacks.Chow.KeyFormulaSituation.orderL_eq_ord_ratioL` and
  `Stacks.Chow.KeyFormulaSituation.orderN_eq_ord_ratioN` — the identities
  `ord_{Z_i, L}(s) = ord_{B_i}(f_i)` and `ord_{Z_i, N}(t) = ord_{B_i}(g_i)`.
* `Stacks.Chow.KeyFormulaSituation.orderL_eq_sub_ringOrd` — the same read as a length in the
  local ring `B_i`.
* `Stacks.Chow.KeyFormulaSituation.weilDivisorL_apply_eq_zero_of_notMem` — `div_L(s)` is
  supported on the family.
* `Stacks.Chow.KeyFormulaSituation.isStalkBasis_restrictedGeneratorN` and
  `Stacks.Chow.KeyFormulaSituation.restrictedGeneratorN_ne_zero` — `t_i|_{Z_i}` is a nonzero
  meromorphic section of `N|_{Z_i}`.
* `Stacks.Chow.genericCoordOf_mul_algebraMap` — rescaling the generator by a unit `u` rescales
  the ratio by `u⁻¹`.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SG](https://stacks.math.columbia.edu/tag/02SG)
* [Stacks Project, Tag 02SH](https://stacks.math.columbia.edu/tag/02SH)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

attribute [local instance] Stacks.Divisors.PrimeDivisor.integral

/-! ### The ratio of a meromorphic section to a local generator -/

section Ratio

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L : X.Modules} {x : X}

/-- **The ratio `v / m`.** The rational function expressing a meromorphic section `v` of `L`,
given by its generic value, in terms of a stalk basis `m` of `L_x`: the generic value of `m` is
a basis of `L_η` over the function field, and `v / m` is the coordinate of `v` in it.

This is the function the source of the key formula calls `f_i` when `v` is the section and `m`
the chosen generator at the generic point of a member of the family. -/
public def genericCoordOf (hL : IsTrivializedNear L x) {m : L.presheaf.stalk x}
    (hm : IsStalkBasis L x m) (v : L.presheaf.stalk (genericPoint X)) : X.functionField :=
  (Equiv.ofBijective _ (hm.toGenericStalk hL)).symm v

omit [IsLocallyNoetherian X] in
/-- The defining equation `v = (v / m) · m` of the ratio, read in the generic stalk. -/
public theorem smul_genericCoordOf (hL : IsTrivializedNear L x) {m : L.presheaf.stalk x}
    (hm : IsStalkBasis L x m) (v : L.presheaf.stalk (genericPoint X)) :
    genericCoordOf hL hm v • toGenericStalk L x m = v :=
  (Equiv.ofBijective _ (hm.toGenericStalk hL)).apply_symm_apply v

omit [IsLocallyNoetherian X] in
/-- The ratio of `v` to a stalk basis of `L_x` is a coordinate of `v` at `x`, so it computes the
order of vanishing of `v` at `x` by `Stacks.Divisors.orderOfVanishing_eq`. -/
public theorem isCoordinateAt_genericCoordOf (hL : IsTrivializedNear L x)
    {m : L.presheaf.stalk x} (hm : IsStalkBasis L x m)
    (v : L.presheaf.stalk (genericPoint X)) :
    IsCoordinateAt L x v (genericCoordOf hL hm v) :=
  ⟨m, hm, (smul_genericCoordOf hL hm v).symm⟩

omit [IsLocallyNoetherian X] in
/-- The ratio of a nonzero meromorphic section to a stalk basis is nonzero. -/
public theorem genericCoordOf_ne_zero (hL : IsTrivializedNear L x) {m : L.presheaf.stalk x}
    (hm : IsStalkBasis L x m) {v : L.presheaf.stalk (genericPoint X)} (hv : v ≠ 0) :
    genericCoordOf hL hm v ≠ 0 :=
  (isCoordinateAt_genericCoordOf hL hm v).ne_zero hv

omit [IsLocallyNoetherian X] in
/-- **Rescaling the generator by a unit `u` rescales the ratio by `u⁻¹`.** This is the
computation the proof of the key formula opens with: replacing the chosen generator `s_i` by
`u s_i` replaces `f_i` by `u^{-1} f_i`. -/
public theorem genericCoordOf_mul_algebraMap (hL : IsTrivializedNear L x)
    {m : L.presheaf.stalk x} (hm : IsStalkBasis L x m) {u : X.presheaf.stalk x} (hu : IsUnit u)
    (v : L.presheaf.stalk (genericPoint X)) :
    genericCoordOf hL (hm.smul_of_isUnit hu) v *
        algebraMap (X.presheaf.stalk x) X.functionField u =
      genericCoordOf hL hm v := by
  refine (hm.toGenericStalk hL).injective ?_
  change (genericCoordOf hL (hm.smul_of_isUnit hu) v *
    algebraMap (X.presheaf.stalk x) X.functionField u) • toGenericStalk L x m = _
  rw [mul_smul, ← toGenericStalk_smul, smul_genericCoordOf, smul_genericCoordOf]

end Ratio

/-! ### The situation -/

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **The situation preceding the key formula, Stacks 0AYB.** On an integral, locally Noetherian
scheme `X`, two invertible `𝒪_X`-modules `L` and `N` with nonzero meromorphic sections `s` and
`t`, together with a locally finite family `{Z_i}` of prime divisors of `X` large enough that
`s` generates `L` and `t` generates `N` at the generic point of every prime divisor outside the
family, and, for each `i`, chosen generators `s_i` of `L_{ξ_i}` and `t_i` of `N_{ξ_i}` at the
generic point `ξ_i` of `Z_i`.

The ratios `f_i = s / s_i` and `g_i = t / t_i`, the orders of vanishing, the restrictions
`s_i|_{Z_i}` and `t_i|_{Z_i}` and the tame symbols `∂_{B_i}(f_i, g_i)` are determined by these
data, and are constructed from them below.

A meromorphic section is given by its value in the generic stalk, and is nonzero exactly when
that value is; see the module documentation. -/
@[stacks 0AYB "the situation preceding the key formula: two invertible modules with nonzero \
meromorphic sections, and a family of prime divisors with chosen local generators"]
public structure KeyFormulaSituation (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] where
  /-- The meromorphic section `s` of `L`, given by its value in the generic stalk. -/
  sectionL : L.presheaf.stalk (genericPoint X)
  /-- The section `s` is nonzero, that is, regular. -/
  sectionL_ne_zero : sectionL ≠ 0
  /-- The meromorphic section `t` of `N`, given by its value in the generic stalk. -/
  sectionN : N.presheaf.stalk (genericPoint X)
  /-- The section `t` is nonzero, that is, regular. -/
  sectionN_ne_zero : sectionN ≠ 0
  /-- The index set `I` of the family. -/
  Index : Type u
  /-- The member `Z_i` of the family, a prime divisor of `X`. -/
  component : Index → PrimeDivisor X
  /-- Distinct indices give distinct members, so that the family is a set of prime divisors. -/
  component_injective : Function.Injective component
  /-- The family `{Z_i}` is locally finite. -/
  locallyFinite_component : LocallyFinite fun i ↦ (component i).support
  /-- Along a prime divisor outside the family, `s` generates `L` and `t` generates `N` at the
  generic point: each is the generic value of a generator of the stalk there. -/
  isCoordinateAt_one_of_notMem : ∀ Z : PrimeDivisor X, (∀ i, component i ≠ Z) →
    IsCoordinateAt L Z.genericPoint sectionL 1 ∧ IsCoordinateAt N Z.genericPoint sectionN 1
  /-- The chosen generator `s_i` of `L_{ξ_i}`. -/
  localGeneratorL : (i : Index) → L.presheaf.stalk (component i).genericPoint
  /-- The chosen generator `t_i` of `N_{ξ_i}`. -/
  localGeneratorN : (i : Index) → N.presheaf.stalk (component i).genericPoint
  /-- `s_i` generates `L_{ξ_i}` over `B_i`. -/
  isStalkBasis_localGeneratorL :
    ∀ i, IsStalkBasis L (component i).genericPoint (localGeneratorL i)
  /-- `t_i` generates `N_{ξ_i}` over `B_i`. -/
  isStalkBasis_localGeneratorN :
    ∀ i, IsStalkBasis N (component i).genericPoint (localGeneratorN i)

namespace KeyFormulaSituation

variable {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

/-- The generic point `ξ_i` of the member `Z_i` of the family. -/
public abbrev componentPoint (i : ℱ.Index) : X := (ℱ.component i).genericPoint

/-- The member `Z_i` of the family, as a scheme. -/
public abbrev componentScheme (i : ℱ.Index) : Scheme.{u} := (ℱ.component i).idealSheaf.subscheme

omit [IsLocallyNoetherian X] in
/-- Each `Z_i` has codimension one in `X`. -/
public theorem coheight_componentPoint (i : ℱ.Index) : coheight (ℱ.componentPoint i) = 1 :=
  PrimeDivisor.coheight_genericPoint _

/-! ### The ratios `f_i` and `g_i` -/

/-- **The rational function `f_i = s / s_i`.** The coordinate of the section `s` of `L` in the
chosen generator `s_i` of `L_{ξ_i}`. -/
public def ratioL (i : ℱ.Index) : X.functionField :=
  have := isInvertible_presheaf L
  genericCoordOf (isTrivializedNear_of_isInvertible L (ℱ.componentPoint i))
    (ℱ.isStalkBasis_localGeneratorL i) ℱ.sectionL

/-- **The rational function `g_i = t / t_i`.** The coordinate of the section `t` of `N` in the
chosen generator `t_i` of `N_{ξ_i}`. -/
public def ratioN (i : ℱ.Index) : X.functionField :=
  have := isInvertible_presheaf N
  genericCoordOf (isTrivializedNear_of_isInvertible N (ℱ.componentPoint i))
    (ℱ.isStalkBasis_localGeneratorN i) ℱ.sectionN

omit [IsLocallyNoetherian X] in
/-- The equation `s = f_i s_i`. -/
public theorem ratioL_smul_localGeneratorL (i : ℱ.Index) :
    ℱ.ratioL i • toGenericStalk L (ℱ.componentPoint i) (ℱ.localGeneratorL i) = ℱ.sectionL :=
  have := isInvertible_presheaf L
  smul_genericCoordOf (isTrivializedNear_of_isInvertible L (ℱ.componentPoint i))
    (ℱ.isStalkBasis_localGeneratorL i) ℱ.sectionL

omit [IsLocallyNoetherian X] in
/-- The equation `t = g_i t_i`. -/
public theorem ratioN_smul_localGeneratorN (i : ℱ.Index) :
    ℱ.ratioN i • toGenericStalk N (ℱ.componentPoint i) (ℱ.localGeneratorN i) = ℱ.sectionN :=
  have := isInvertible_presheaf N
  smul_genericCoordOf (isTrivializedNear_of_isInvertible N (ℱ.componentPoint i))
    (ℱ.isStalkBasis_localGeneratorN i) ℱ.sectionN

omit [IsLocallyNoetherian X] in
/-- `f_i` is a coordinate of `s` at `ξ_i`. -/
public theorem isCoordinateAt_ratioL (i : ℱ.Index) :
    IsCoordinateAt L (ℱ.componentPoint i) ℱ.sectionL (ℱ.ratioL i) :=
  ⟨ℱ.localGeneratorL i, ℱ.isStalkBasis_localGeneratorL i,
    (ℱ.ratioL_smul_localGeneratorL i).symm⟩

omit [IsLocallyNoetherian X] in
/-- `g_i` is a coordinate of `t` at `ξ_i`. -/
public theorem isCoordinateAt_ratioN (i : ℱ.Index) :
    IsCoordinateAt N (ℱ.componentPoint i) ℱ.sectionN (ℱ.ratioN i) :=
  ⟨ℱ.localGeneratorN i, ℱ.isStalkBasis_localGeneratorN i,
    (ℱ.ratioN_smul_localGeneratorN i).symm⟩

omit [IsLocallyNoetherian X] in
/-- `f_i` is nonzero, the section `s` being nonzero. -/
public theorem ratioL_ne_zero (i : ℱ.Index) : ℱ.ratioL i ≠ 0 :=
  (ℱ.isCoordinateAt_ratioL i).ne_zero ℱ.sectionL_ne_zero

omit [IsLocallyNoetherian X] in
/-- `g_i` is nonzero, the section `t` being nonzero. -/
public theorem ratioN_ne_zero (i : ℱ.Index) : ℱ.ratioN i ≠ 0 :=
  (ℱ.isCoordinateAt_ratioN i).ne_zero ℱ.sectionN_ne_zero

/-! ### The orders of vanishing and the divisors on `X` -/

/-- The order of vanishing `ord_{Z_i, L}(s)` of `s` along the member `Z_i`. -/
public abbrev orderL (i : ℱ.Index) : ℤ := orderOfVanishing L ℱ.sectionL (ℱ.component i)

/-- The order of vanishing `ord_{Z_i, N}(t)` of `t` along the member `Z_i`. -/
public abbrev orderN (i : ℱ.Index) : ℤ := orderOfVanishing N ℱ.sectionN (ℱ.component i)

/-- **`ord_{Z_i, L}(s) = ord_{B_i}(f_i)`.** -/
public theorem orderL_eq_ord_ratioL (i : ℱ.Index) :
    ℱ.orderL i = X.ord (ℱ.ratioL i) (ℱ.componentPoint i) :=
  have := isInvertible_presheaf L
  orderOfVanishing_eq (isTrivializedNear_of_isInvertible L (ℱ.componentPoint i))
    (ℱ.isCoordinateAt_ratioL i)

/-- **`ord_{Z_i, N}(t) = ord_{B_i}(g_i)`.** -/
public theorem orderN_eq_ord_ratioN (i : ℱ.Index) :
    ℱ.orderN i = X.ord (ℱ.ratioN i) (ℱ.componentPoint i) :=
  have := isInvertible_presheaf N
  orderOfVanishing_eq (isTrivializedNear_of_isInvertible N (ℱ.componentPoint i))
    (ℱ.isCoordinateAt_ratioN i)

/-- **`ord_{Z_i, L}(s)` as a length in the local ring `B_i`.** Writing `f_i = b / c` with `b`
and `c` nonzero elements of `B_i`, the order of vanishing of `s` along `Z_i` is
`ord_{B_i}(b) - ord_{B_i}(c)`, the difference of the lengths of `B_i / (b)` and `B_i / (c)`.

Such a presentation exists, `B_i` being a Noetherian local domain with fraction field the
function field of `X`; this is `Stacks.Chow.exists_ringOrd_presentation`. -/
public theorem orderL_eq_sub_ringOrd (i : ℱ.Index)
    {b c : X.presheaf.stalk (ℱ.componentPoint i)} (hb : b ≠ 0) (hc : c ≠ 0)
    (hf : algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField c * ℱ.ratioL i =
      algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField b)
    {m k : ℕ} (hm : Ring.ord (X.presheaf.stalk (ℱ.componentPoint i)) b = m)
    (hk : Ring.ord (X.presheaf.stalk (ℱ.componentPoint i)) c = k) :
    ℱ.orderL i = (m : ℤ) - k :=
  (ℱ.orderL_eq_ord_ratioL i).trans
    (ord_eq_sub_ringOrd (ℱ.coheight_componentPoint i) hb hc hf hm hk)

/-- **`ord_{Z_i, N}(t)` as a length in the local ring `B_i`**, as in
`Stacks.Chow.KeyFormulaSituation.orderL_eq_sub_ringOrd`. -/
public theorem orderN_eq_sub_ringOrd (i : ℱ.Index)
    {b c : X.presheaf.stalk (ℱ.componentPoint i)} (hb : b ≠ 0) (hc : c ≠ 0)
    (hg : algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField c * ℱ.ratioN i =
      algebraMap (X.presheaf.stalk (ℱ.componentPoint i)) X.functionField b)
    {m k : ℕ} (hm : Ring.ord (X.presheaf.stalk (ℱ.componentPoint i)) b = m)
    (hk : Ring.ord (X.presheaf.stalk (ℱ.componentPoint i)) c = k) :
    ℱ.orderN i = (m : ℤ) - k :=
  (ℱ.orderN_eq_ord_ratioN i).trans
    (ord_eq_sub_ringOrd (ℱ.coheight_componentPoint i) hb hc hg hm hk)

/-- **The divisor `div_L(s) = ∑_Z ord_{Z, L}(s) [Z]`.** -/
public abbrev weilDivisorL : WeilDivisor X :=
  have := isInvertible_presheaf L
  weilDivisorOfMeromorphicSection (isTrivializedNear_of_isInvertible L) ℱ.sectionL

/-- **The divisor `div_N(t) = ∑_Z ord_{Z, N}(t) [Z]`.** -/
public abbrev weilDivisorN : WeilDivisor X :=
  have := isInvertible_presheaf N
  weilDivisorOfMeromorphicSection (isTrivializedNear_of_isInvertible N) ℱ.sectionN

/-- **`div_L(s)` is supported on the family**: along a prime divisor outside it, `s` generates
`L` and so has order of vanishing zero. Together with
`Stacks.Chow.KeyFormulaSituation.orderL_eq_ord_ratioL` this is the identity
`div_L(s) = ∑ ord_{B_i}(f_i) [Z_i]` of the source. -/
public theorem weilDivisorL_apply_eq_zero_of_notMem (Z : PrimeDivisor X)
    (hZ : ∀ i, ℱ.component i ≠ Z) : ℱ.weilDivisorL.val Z = 0 := by
  have := isInvertible_presheaf L
  rw [weilDivisorOfMeromorphicSection_apply,
    orderOfVanishing_eq (isTrivializedNear_of_isInvertible L Z.genericPoint)
      (ℱ.isCoordinateAt_one_of_notMem Z hZ).1,
    ← map_one (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField)]
  exact Scheme.ord_algebraMap_of_isUnit Z.coheight_genericPoint isUnit_one

/-- **`div_N(t)` is supported on the family**, as in
`Stacks.Chow.KeyFormulaSituation.weilDivisorL_apply_eq_zero_of_notMem`. -/
public theorem weilDivisorN_apply_eq_zero_of_notMem (Z : PrimeDivisor X)
    (hZ : ∀ i, ℱ.component i ≠ Z) : ℱ.weilDivisorN.val Z = 0 := by
  have := isInvertible_presheaf N
  rw [weilDivisorOfMeromorphicSection_apply,
    orderOfVanishing_eq (isTrivializedNear_of_isInvertible N Z.genericPoint)
      (ℱ.isCoordinateAt_one_of_notMem Z hZ).2,
    ← map_one (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField)]
  exact Scheme.ord_algebraMap_of_isUnit Z.coheight_genericPoint isUnit_one

/-! ### The restrictions `s_i|_{Z_i}` and `t_i|_{Z_i}` -/

/-- **The restriction `s_i|_{Z_i}`**, the image of the generator `s_i` in the fibre
`L_{ξ_i} ⊗ κ(ξ_i)`, read as a meromorphic section of `L|_{Z_i}` by its generic value. -/
public def restrictedGeneratorL (i : ℱ.Index) :
    (restrictModule (ℱ.component i).idealSheaf L).presheaf.stalk
      (genericPoint (ℱ.componentScheme i)) :=
  restrictStalk (ℱ.component i).idealSheaf L rfl (ℱ.localGeneratorL i)

/-- **The restriction `t_i|_{Z_i}`**, the image of the generator `t_i` in the fibre
`N_{ξ_i} ⊗ κ(ξ_i)`, read as a meromorphic section of `N|_{Z_i}` by its generic value. -/
public def restrictedGeneratorN (i : ℱ.Index) :
    (restrictModule (ℱ.component i).idealSheaf N).presheaf.stalk
      (genericPoint (ℱ.componentScheme i)) :=
  restrictStalk (ℱ.component i).idealSheaf N rfl (ℱ.localGeneratorN i)

omit [IsLocallyNoetherian X] in
/-- `s_i|_{Z_i}` generates the stalk of `L|_{Z_i}` at the generic point of `Z_i`. -/
public theorem isStalkBasis_restrictedGeneratorL (i : ℱ.Index) :
    IsStalkBasis (restrictModule (ℱ.component i).idealSheaf L)
      (genericPoint (ℱ.componentScheme i)) (ℱ.restrictedGeneratorL i) :=
  isStalkBasis_restrictStalk (ℱ.component i).idealSheaf L rfl
    (ℱ.isStalkBasis_localGeneratorL i)

omit [IsLocallyNoetherian X] in
/-- `t_i|_{Z_i}` generates the stalk of `N|_{Z_i}` at the generic point of `Z_i`. -/
public theorem isStalkBasis_restrictedGeneratorN (i : ℱ.Index) :
    IsStalkBasis (restrictModule (ℱ.component i).idealSheaf N)
      (genericPoint (ℱ.componentScheme i)) (ℱ.restrictedGeneratorN i) :=
  isStalkBasis_restrictStalk (ℱ.component i).idealSheaf N rfl
    (ℱ.isStalkBasis_localGeneratorN i)

omit [IsLocallyNoetherian X] in
/-- **`s_i|_{Z_i}` is a nonzero meromorphic section of `L|_{Z_i}`.** It generates the stalk at
the generic point of `Z_i`, and the zero element generates no module over a nontrivial ring. -/
public theorem restrictedGeneratorL_ne_zero (i : ℱ.Index) : ℱ.restrictedGeneratorL i ≠ 0 := by
  intro h
  have h01 : (0 : (ℱ.componentScheme i).presheaf.stalk (genericPoint (ℱ.componentScheme i))) =
      1 := (ℱ.isStalkBasis_restrictedGeneratorL i).injective (by simp only [h, smul_zero])
  exact zero_ne_one (α := (ℱ.componentScheme i).functionField) h01

omit [IsLocallyNoetherian X] in
/-- **`t_i|_{Z_i}` is a nonzero meromorphic section of `N|_{Z_i}`**, as the source asserts of the
image of `t_i` in the fibre `N_{ξ_i} ⊗ κ(ξ_i)`. -/
public theorem restrictedGeneratorN_ne_zero (i : ℱ.Index) : ℱ.restrictedGeneratorN i ≠ 0 := by
  intro h
  have h01 : (0 : (ℱ.componentScheme i).presheaf.stalk (genericPoint (ℱ.componentScheme i))) =
      1 := (ℱ.isStalkBasis_restrictedGeneratorN i).injective (by simp only [h, smul_zero])
  exact zero_ne_one (α := (ℱ.componentScheme i).functionField) h01

/-! ### The divisors of the restrictions -/

section Base

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

omit [IsLocallyNoetherian X] in
include C p in
/-- Each member of the family is locally Noetherian, being locally of finite type over the
base. -/
public theorem isLocallyNoetherian_componentScheme (i : ℱ.Index) :
    IsLocallyNoetherian (ℱ.componentScheme i) :=
  LocallyOfFiniteType.isLocallyNoetherian ((ℱ.component i).idealSheaf.subschemeι ≫ p)

/-- **The divisor `div_{L|Z_i}(s_i|Z_i)`**, a Weil divisor on `Z_i`. -/
public def restrictedWeilDivisorL (i : ℱ.Index) : WeilDivisor (ℱ.componentScheme i) :=
  letI := ℱ.isLocallyNoetherian_componentScheme C p i
  weilDivisorOfMeromorphicSection
    (isTrivializedNear_restrictModule (ℱ.component i).idealSheaf L)
    (ℱ.restrictedGeneratorL i)

/-- **The divisor `div_{N|Z_i}(t_i|Z_i)`**, a Weil divisor on `Z_i`. -/
public def restrictedWeilDivisorN (i : ℱ.Index) : WeilDivisor (ℱ.componentScheme i) :=
  letI := ℱ.isLocallyNoetherian_componentScheme C p i
  weilDivisorOfMeromorphicSection
    (isTrivializedNear_restrictModule (ℱ.component i).idealSheaf N)
    (ℱ.restrictedGeneratorN i)

end Base

/-! ### The tame symbol -/

/-- **The tame symbol `∂_{B_i}(f_i, g_i) ∈ κ(ξ_i)^*`.** The local ring `B_i = 𝒪_{X, ξ_i}` at a
codimension-one point is a one-dimensional Noetherian local domain with fraction field the
function field of `X`, so Stacks 0EAH attaches to the pair `(f_i, g_i)` a unit of the residue
field `κ(ξ_i)`.

Read in `κ(ξ_i)`, the field of rational functions of `Z_i`, the tame symbols are the rational
functions whose divisors make up the rational equivalence of the key formula Stacks 0AYC. -/
public def tameSymbol (i : ℱ.Index) :
    (IsLocalRing.ResidueField (X.presheaf.stalk (ℱ.componentPoint i)))ˣ :=
  tameSymbolAtCoheightOne (ℱ.coheight_componentPoint i)
    (Units.mk0 (ℱ.ratioL i) (ℱ.ratioL_ne_zero i))
    (Units.mk0 (ℱ.ratioN i) (ℱ.ratioN_ne_zero i))

/-- **Stacks 0EAJ for the tame symbol of the situation.** `∂_{B_i}(f_i, g_i)` and
`∂_{B_i}(g_i, f_i)` are mutually inverse. -/
public theorem tameSymbol_mul_swap (i : ℱ.Index) :
    ℱ.tameSymbol i *
        tameSymbolAtCoheightOne (ℱ.coheight_componentPoint i)
          (Units.mk0 (ℱ.ratioN i) (ℱ.ratioN_ne_zero i))
          (Units.mk0 (ℱ.ratioL i) (ℱ.ratioL_ne_zero i)) = 1 :=
  TameSymbol.skew _ _ _



end KeyFormulaSituation

end Stacks.Chow

end
