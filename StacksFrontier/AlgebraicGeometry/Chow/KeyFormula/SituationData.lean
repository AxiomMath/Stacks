module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Situation
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol

/-!
# The cycle-level data of the situation preceding the key formula

`Stacks.Chow.KeyFormulaSituation` records the sheaf-level situation of Stacks 0AYB — two
invertible modules with nonzero meromorphic sections and a locally finite family `{Z_i}` of prime
divisors with chosen local generators — while `Stacks.Chow.KeyFormulaData` records the
cycle-level data that the statement of the key formula Stacks 0AYC is built from. This file
produces the second from the first.

Every field of `Stacks.Chow.KeyFormulaData` is a quantity the situation already determines: the
family is indexed by the generic points `ξ_i`, the two integers are the orders of vanishing
`ord_{Z_i, L}(s)` and `ord_{Z_i, N}(t)`, the two cycles are the divisors
`div_{L|Z_i}(s_i|Z_i)` and `div_{N|Z_i}(t_i|Z_i)` of the restricted generators, and the rational
function is the tame symbol `∂_{B_i}(f_i, g_i)`. Two re-spellings are needed and both are
available: the prime divisor `Z_i` is the integral closed subscheme attached to its generic point
(`Stacks.Chow.integralComponentAt_genericPointOf`), which is the presentation
`Stacks.Chow.KeyFormulaData` uses, and the residue field `κ(ξ_i)` in which the tame symbol lives
is the field of rational functions of `Z_i`
(`Stacks.Chow.rationalFunctionsUnitsIntegralComponentEquiv`).

The divisor of a restricted generator is `Stacks.Divisors.weilDivisorOfMeromorphicSection` of
`Stacks.Chow.restrictStalk`, read on points by `Stacks.Chow.weilDivisorAlgebraicCycle`. It is the
spelling of `Stacks.Chow.KeyFormulaSituation.restrictedWeilDivisorL` on the integral component at
`ξ_i` rather than on `Z_i` presented by its own ideal sheaf; the two ideal sheaves agree by
`Stacks.Chow.KeyFormulaSituation.integralComponentAt_componentPoint`. That a divisor is supported
in codimension one — the one condition `Stacks.Chow.KeyFormulaData` imposes on its cycles — is
`Stacks.Chow.weilDivisorCoeff_eq_zero_of_coheight_ne_one`.

## Main definitions

* `Stacks.Chow.restrictedWeilDivisorAt` — the divisor `div_{M|Z_ξ}(m|Z_ξ)` of the restriction of
  an element of `M_ξ`, as a Weil divisor on the integral component at `ξ`.
* `Stacks.Chow.KeyFormulaSituation.toKeyFormulaData` — the cycle-level data of the situation.

## Main results

* `Stacks.Chow.KeyFormulaSituation.integralComponentAt_componentPoint` — the member `Z_i` is the
  integral closed subscheme attached to its generic point.
* `Stacks.Chow.val_restrictedDivisor_eq_weilDivisorAlgebraicCycle` — the divisor built here is
  the one `Stacks.Chow.restrictedDivisor` builds, without its delta-dimension hypothesis.
* `Stacks.Chow.coheight_eq_one_of_weilDivisorAlgebraicCycle_ne_zero` — the cycle of a Weil
  divisor is supported in codimension one.
* `Stacks.Chow.weilDivisorOfMeromorphicSection_eq_zero_of_isStalkBasis_germ` — the divisor of a
  global trivialization is zero, and
  `Stacks.Chow.restrictedWeilDivisorAt_eq_zero_of_isStalkBasis_germ` — the same for its
  restriction to an integral component.
* `Stacks.Chow.restrictedWeilDivisorAt_germ_one` — `div_{𝒪_X|Z_ξ}(1|Z_ξ) = 0`, the case of the
  structure sheaf with its unit germ.
* `Stacks.Chow.KeyFormulaSituation.toKeyFormulaData_componentPoint`,
  `Stacks.Chow.KeyFormulaSituation.toKeyFormulaData_orderL`,
  `Stacks.Chow.KeyFormulaSituation.toKeyFormulaData_restrictedDivisorL`,
  `Stacks.Chow.KeyFormulaSituation.toKeyFormulaData_tameSymbol` — the fields of the data.
* `Stacks.Chow.KeyFormulaSituation.toKeyFormulaData_orderL_eq_ord_ratioL` — the first integer is
  the order of vanishing of the ratio `f_i`.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors
open Stacks.Ample (unitModule unitStalkEquiv unitStalkFun_germ)

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### The divisor of a restricted generator on an integral component -/

include C p in
/-- The integral closed subscheme attached to a point is locally Noetherian, being locally of
finite type over the base. -/
theorem isLocallyNoetherian_integralComponentAt (x : X) :
    IsLocallyNoetherian (integralComponentAt x).subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ p)

variable {M : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]

include C p in
/-- **The divisor `div_{M|Z_ξ}(m|Z_ξ)` of a restricted element of `M_ξ`.** The restriction
`m|_{Z_ξ}` of `m` to the integral component `Z_ξ` at `ξ` is a meromorphic section of `M|_{Z_ξ}`,
nonzero when `m` generates `M_ξ`, and this is its Weil divisor on `Z_ξ`. -/
def restrictedWeilDivisorAt (x : X) (m : M.presheaf.stalk x) :
    WeilDivisor (integralComponentAt x).subscheme :=
  letI := isLocallyNoetherian_integralComponentAt C p x
  weilDivisorOfMeromorphicSection (isTrivializedNear_restrictModule (integralComponentAt x) M)
    (restrictStalk (integralComponentAt x) M (genericPointOf_integralComponentAt x) m)

/-- **The cycle of `div_{M|Z_ξ}(m|Z_ξ)` is the restricted divisor of
`Stacks.Chow.restrictedDivisor`.** The latter is the same Weil divisor read as an element of
`Z_{n-1}(Z_ξ)`, so it carries the delta-dimension of `Z_ξ` as a hypothesis while the cycle does
not. -/
theorem val_restrictedDivisor_eq_weilDivisorAlgebraicCycle (x : X) {n : ℤ}
    (hn : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) = (n : EInt))
    (m : M.presheaf.stalk x) :
    letI := isLocallyNoetherian_integralComponentAt C p x
    ((restrictedDivisor (integralComponentAt x) M
          (genericPointOf_integralComponentAt x) C p hn m).val :
        AlgebraicCycle (integralComponentAt x).subscheme ℤ) =
      weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p x m) :=
  rfl

/-- **A divisor is supported in codimension one.** The cycle of a Weil divisor has a nonzero
coefficient only at the generic point of a prime divisor, and such a point has coheight one. -/
theorem coheight_eq_one_of_weilDivisorAlgebraicCycle_ne_zero {Y : Scheme.{u}} (D : WeilDivisor Y)
    {z : Y} (hz : weilDivisorAlgebraicCycle D z ≠ 0) : coheight z = 1 := by
  by_contra h
  exact hz (weilDivisorCoeff_eq_zero_of_coheight_ne_one D.val h)

/-! ### The divisor of a trivializing section -/

section Trivialized

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] {L : Y.Modules}

/-- **A section trivializing `L` everywhere has order of vanishing zero.** If the germs of
`t ∈ Γ(L, U)` are bases of the stalks of `L` then `1` is a coordinate of the generic value of
`t` at every point of `U`, and the order of vanishing of `1` is zero. -/
theorem orderOfVanishing_eq_zero_of_isStalkBasis_germ {U : Y.Opens} {t : Γ(L, U)}
    (ht : ∀ (y : Y) (hy : y ∈ U), IsStalkBasis L y (L.presheaf.germ U y hy t))
    (hη : genericPoint Y ∈ U) {Z : PrimeDivisor Y} (hZ : Z.genericPoint ∈ U) :
    orderOfVanishing L (L.presheaf.germ U (genericPoint Y) hη t) Z = 0 := by
  have hcoord : IsCoordinateAt L Z.genericPoint (L.presheaf.germ U (genericPoint Y) hη t) 1 :=
    ⟨L.presheaf.germ U Z.genericPoint hZ t, ht _ hZ, by rw [one_smul, toGenericStalk_germ]⟩
  rw [orderOfVanishing_eq ⟨U, hZ, t, ht⟩ hcoord,
    ← map_one (algebraMap (Y.presheaf.stalk Z.genericPoint) Y.functionField)]
  exact Scheme.ord_algebraMap_of_isUnit Z.coheight_genericPoint isUnit_one

/-- **The divisor of a global trivialization vanishes.** A section of `L` over an open set
containing every point of `Y` whose germs are bases of the stalks has order of vanishing zero
along every prime divisor, so its Weil divisor is the zero divisor. -/
theorem weilDivisorOfMeromorphicSection_eq_zero_of_isStalkBasis_germ
    (hL : ∀ y : Y, IsTrivializedNear L y) {U : Y.Opens} (hU : ∀ y : Y, y ∈ U) {t : Γ(L, U)}
    (ht : ∀ (y : Y) (hy : y ∈ U), IsStalkBasis L y (L.presheaf.germ U y hy t)) :
    weilDivisorOfMeromorphicSection hL (L.presheaf.germ U (genericPoint Y) (hU _) t) = 0 :=
  Subtype.ext (funext fun _ =>
    orderOfVanishing_eq_zero_of_isStalkBasis_germ ht (hU _) (hU _))

end Trivialized

open Stacks.AlgebraicGeometry.SectionsBaseChange in
include C p in
/-- **`div_{M|Z_ξ}(m|Z_ξ) = 0` for the germ of a global trivialization.** The restriction to
`Z_ξ` of a section of `M` whose germs are bases of the stalks of `M` is again a global
trivialization, now of `M|_{Z_ξ}`, so its divisor vanishes. -/
theorem restrictedWeilDivisorAt_eq_zero_of_isStalkBasis_germ {U : X.Opens}
    (hU : ∀ y : X, y ∈ U) {t : Γ(M, U)}
    (ht : ∀ (y : X) (hy : y ∈ U), IsStalkBasis M y (M.presheaf.germ U y hy t)) (x : X) :
    restrictedWeilDivisorAt C p x (M.presheaf.germ U x (hU x) t) = 0 := by
  have := isLocallyNoetherian_integralComponentAt C p x
  have hU' : ∀ y : (integralComponentAt x).subscheme,
      y ∈ (integralComponentAt x).subschemeι ⁻¹ᵁ U := fun y => hU _
  have hbasis : ∀ (y : (integralComponentAt x).subscheme)
      (hy : y ∈ (integralComponentAt x).subschemeι ⁻¹ᵁ U),
      IsStalkBasis (restrictModule (integralComponentAt x) M) y
        ((restrictModule (integralComponentAt x) M).presheaf.germ
          ((integralComponentAt x).subschemeι ⁻¹ᵁ U) y hy
          (pullbackUnitSections (integralComponentAt x).subschemeι M U t)) := by
    intro y hy
    rw [← pullbackStalk_germ (integralComponentAt x).subschemeι M y U hy t]
    exact (ht _ hy).pullbackStalk
  have hgerm : restrictStalk (integralComponentAt x) M
        (genericPointOf_integralComponentAt x) (M.presheaf.germ U x (hU x) t) =
      (restrictModule (integralComponentAt x) M).presheaf.germ
        ((integralComponentAt x).subschemeι ⁻¹ᵁ U)
        (genericPoint (integralComponentAt x).subscheme) (hU' _)
        (pullbackUnitSections (integralComponentAt x).subschemeι M U t) :=
    pullbackStalkAt_germ (integralComponentAt x).subschemeι M
      (genericPoint (integralComponentAt x).subscheme)
      (genericPointOf_integralComponentAt x) U (hU' _) t
  change weilDivisorOfMeromorphicSection
      (isTrivializedNear_restrictModule (integralComponentAt x) M)
      (restrictStalk (integralComponentAt x) M (genericPointOf_integralComponentAt x)
        (M.presheaf.germ U x (hU x) t)) = 0
  rw [hgerm]
  exact weilDivisorOfMeromorphicSection_eq_zero_of_isStalkBasis_germ _ hU' hbasis

/-! ### The divisor of the unit germ of the structure sheaf -/

namespace UnitModule

/-- **The structure sheaf, read as a module over itself, is invertible**, being the monoidal unit
of `X.Modules`. Instance search does not see through `AlgebraicGeometry.Scheme.ringCatSheaf` to
find this, so it is attached as a file-local instance; the name is qualified because the library
already carries this fact for two other spellings of the unit module. -/
theorem isInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (unitModule X) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit X.sheaf.obj X.ringCatSheaf.property)

end UnitModule

attribute [local instance] UnitModule.isInvertible

/-- **The germ of the unit section `1` is a basis of every stalk of `𝒪_X`.** Multiplication by
it is the inverse of the identification of the stalk of `𝒪_X` as a module over itself with the
local ring, an identification that carries that germ to `1`. -/
theorem isStalkBasis_germ_one (U : X.Opens) (y : X) (hy : y ∈ U) :
    IsStalkBasis (unitModule X) y
      ((unitModule X).presheaf.germ U y hy (show Γ(unitModule X, U) from (1 : Γ(X, U)))) := by
  have he : unitStalkEquiv X y
      ((unitModule X).presheaf.germ U y hy (show Γ(unitModule X, U) from (1 : Γ(X, U)))) = 1 :=
    (unitStalkFun_germ X y U hy _).trans (map_one (X.presheaf.germ U y hy).hom)
  have hsmul : (fun r : X.presheaf.stalk y => r •
        (unitModule X).presheaf.germ U y hy (show Γ(unitModule X, U) from (1 : Γ(X, U)))) =
      fun r => (unitStalkEquiv X y).symm r := by
    refine funext fun r => (unitStalkEquiv X y).injective ?_
    rw [LinearEquiv.apply_symm_apply, map_smul, he, smul_eq_mul, mul_one]
  rw [IsStalkBasis, hsmul]
  exact (unitStalkEquiv X y).symm.bijective

include C p in
/-- **`div_{𝒪_X|Z_ξ}(1|Z_ξ) = 0`.** The unit germ of the structure sheaf is the germ of a global
trivialization of `𝒪_X` as a module over itself, so its restricted divisor on the integral
component at `ξ` is the zero Weil divisor. -/
theorem restrictedWeilDivisorAt_germ_one (x : X) :
    restrictedWeilDivisorAt C p x
        ((unitModule X).presheaf.germ ⊤ x trivial
          (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤)))) = 0 :=
  restrictedWeilDivisorAt_eq_zero_of_isStalkBasis_germ C p (U := ⊤) (fun _ => trivial)
    (isStalkBasis_germ_one ⊤) x

/-! ### The cycle-level data of the situation -/

namespace KeyFormulaSituation

variable [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

omit [LocallyOfFiniteType p] [IsLocallyNoetherian X] in
/-- **The member `Z_i` is the integral closed subscheme attached to its generic point.** This is
the presentation `Stacks.Chow.KeyFormulaData` uses for the members of its family. -/
theorem integralComponentAt_componentPoint (i : ℱ.Index) :
    integralComponentAt (ℱ.componentPoint i) = (ℱ.component i).idealSheaf :=
  integralComponentAt_genericPointOf (ℱ.component i).idealSheaf (ℱ.component i).integral

include C p in
/-- **The cycle-level data of the situation of Stacks 0AYB.** The family is indexed by the
generic points `ξ_i`, the two integers are the orders of vanishing `ord_{Z_i, L}(s)` and
`ord_{Z_i, N}(t)`, the two cycles are the divisors `div_{L|Z_i}(s_i|Z_i)` and
`div_{N|Z_i}(t_i|Z_i)` of the restricted generators, and the rational function on `Z_i` is the
tame symbol `∂_{B_i}(f_i, g_i)` read through `κ(ξ_i) = R(Z_i)`.

This is the term of `Stacks.Chow.KeyFormulaData` whose key formula Stacks 0AYC asserts. -/
def toKeyFormulaData : KeyFormulaData X where
  Index := ℱ.Index
  componentPoint := ℱ.componentPoint
  coheight_componentPoint := ℱ.coheight_componentPoint
  componentPoint_injective _ _ h :=
    ℱ.component_injective (PrimeDivisor.genericPoint_injective h)
  locallyFinite_component := by
    simpa only [PrimeDivisor.support_eq_closure] using ℱ.locallyFinite_component
  orderL := ℱ.orderL
  orderN := ℱ.orderN
  restrictedDivisorL i :=
    weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p (ℱ.componentPoint i)
      (ℱ.localGeneratorL i))
  restrictedDivisorN i :=
    weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p (ℱ.componentPoint i)
      (ℱ.localGeneratorN i))
  coheight_of_restrictedDivisorL _ _ hz :=
    coheight_eq_one_of_weilDivisorAlgebraicCycle_ne_zero _ hz
  coheight_of_restrictedDivisorN _ _ hz :=
    coheight_eq_one_of_weilDivisorAlgebraicCycle_ne_zero _ hz
  tameSymbol i :=
    (rationalFunctionsUnitsIntegralComponentEquiv (ℱ.componentPoint i)).symm (ℱ.tameSymbol i)

/-- The generic points of the data are the generic points `ξ_i` of the situation. -/
@[simp]
theorem toKeyFormulaData_componentPoint (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).componentPoint i = ℱ.componentPoint i :=
  rfl

/-- The member `Z_i` of the data is the integral closed subscheme `Z_i` of the situation. -/
@[simp]
theorem toKeyFormulaData_component (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).component i = (ℱ.component i).idealSheaf :=
  ℱ.integralComponentAt_componentPoint i

/-- The first integer of the data is the order of vanishing `ord_{Z_i, L}(s)`. -/
@[simp]
theorem toKeyFormulaData_orderL (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).orderL i = ℱ.orderL i :=
  rfl

/-- The second integer of the data is the order of vanishing `ord_{Z_i, N}(t)`. -/
@[simp]
theorem toKeyFormulaData_orderN (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).orderN i = ℱ.orderN i :=
  rfl

/-- The first integer of the data is the order of vanishing of the ratio `f_i` at `ξ_i`. -/
theorem toKeyFormulaData_orderL_eq_ord_ratioL (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).orderL i = X.ord (ℱ.ratioL i) (ℱ.componentPoint i) :=
  ℱ.orderL_eq_ord_ratioL i

/-- The second integer of the data is the order of vanishing of the ratio `g_i` at `ξ_i`. -/
theorem toKeyFormulaData_orderN_eq_ord_ratioN (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).orderN i = X.ord (ℱ.ratioN i) (ℱ.componentPoint i) :=
  ℱ.orderN_eq_ord_ratioN i

/-- The first cycle of the data is the divisor `div_{L|Z_i}(s_i|Z_i)` of the restricted
generator. -/
@[simp]
theorem toKeyFormulaData_restrictedDivisorL (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).restrictedDivisorL i =
      weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p (ℱ.componentPoint i)
        (ℱ.localGeneratorL i)) :=
  rfl

/-- The second cycle of the data is the divisor `div_{N|Z_i}(t_i|Z_i)` of the restricted
generator. -/
@[simp]
theorem toKeyFormulaData_restrictedDivisorN (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).restrictedDivisorN i =
      weilDivisorAlgebraicCycle (restrictedWeilDivisorAt C p (ℱ.componentPoint i)
        (ℱ.localGeneratorN i)) :=
  rfl

/-- The rational function of the data is the tame symbol `∂_{B_i}(f_i, g_i)` read through
`κ(ξ_i) = R(Z_i)`. -/
@[simp]
theorem toKeyFormulaData_tameSymbol (i : ℱ.Index) :
    (ℱ.toKeyFormulaData C p).tameSymbol i =
      (rationalFunctionsUnitsIntegralComponentEquiv (ℱ.componentPoint i)).symm
        (ℱ.tameSymbol i) :=
  rfl

end KeyFormulaSituation

end Stacks.Chow

end
