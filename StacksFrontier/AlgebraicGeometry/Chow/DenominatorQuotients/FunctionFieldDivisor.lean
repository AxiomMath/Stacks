module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldOrder
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.OrderOfVanishing
public import StacksFrontier.AlgebraicGeometry.Modules.UnitStalk

/-!
# The divisor of a rational function and the two denominator quotients

Let `X` be an integral locally Noetherian scheme and `g` a nonzero rational function on `X`. The
structure sheaf is invertible as a module over itself, and the germ of `1` is a basis of each of
its stalks, so every rational function is a coordinate of itself: a meromorphic section of `𝒪_X`
whose generic value is `g` has order of vanishing `ord_ξ(g)` along every prime divisor, by the
characterization of Stacks 02SF.

Combined with the multiplicity computation of
`AlgebraicGeometry.sheafMultiplicity_denominator_sub_eq_ord`, this says that at the generic
point of each prime divisor the coefficients of the two denominator quotients differ by the
coefficient of `div(g)` — the claim `[𝒪_X/gI]_k − [𝒪_X/I]_k = div(g)` of the proof of
Stacks 0FDS, read one prime divisor at a time.

## Main definitions

* `Stacks.UnitStalk.one` — the germ of the global section `1` of `𝒪_X` at a point,
  as an element of the stalk of `𝒪_X` regarded as a module over itself.

## Main results

* `AlgebraicGeometry.isInvertible_unitModule` — `𝒪_X` is invertible as a module over itself.
* `AlgebraicGeometry.isStalkBasis_unitModuleGerm` — the germ of `1` is a basis of the stalk.
* `AlgebraicGeometry.isCoordinateAt_unitModule` — a rational function `g` is a coordinate, at
  every point, of the element of the generic stalk it corresponds to.
* `AlgebraicGeometry.orderOfVanishingMeromorphic_unitModule_eq_ord` — a meromorphic section of
  `𝒪_X` with generic value `g` has order of vanishing `ord_ξ(g)` along every prime divisor.
* `AlgebraicGeometry.sheafMultiplicity_denominator_sub_eq_orderOfVanishingMeromorphic` — the
  difference of the multiplicities of the two denominator quotients at the generic point of a
  prime divisor is the order of vanishing of `g` along it.

## Implementation notes

The identification of the stalk of `𝒪_X` as a module over itself with the local ring is
`Stacks.Ample.unitStalkEquiv`; it carries the germ of `1` to `1`, so multiplication by that germ
is the inverse of the identification and in particular bijective, which is what a stalk basis
is. Specialization to the generic point carries the germ of `1` at `x` to the germ of `1` at the
generic point, by `Stacks.Divisors.toGenericStalk_germ` applied on `⊤`; that is why one basis
works at every point at once and no trivialization has to be chosen.

Note that there are two independent definitions named `orderOfVanishingMeromorphic`, over two
independent types named `PrimeDivisor`: one in the `AlgebraicGeometry` namespace and one in
`Stacks.Divisors`. The cycle `Stacks.Chow.divisorOfMeromorphicSectionCycle` of Stacks 02SJ is
built on the `Stacks.Divisors` one, so that is the one used here, and it is written out in full
rather than opened — inside `namespace AlgebraicGeometry` the unqualified name resolves to the
other definition, and the statement then fails to typecheck against
`Stacks.Divisors.PrimeDivisor`.

The generic value of the section is a **hypothesis**, not a computation. For the section
`AlgebraicGeometry.meromorphicSectionOfFunctionField` attached to `g` the equation
`genericValue (unitModule X) s = (unitStalkEquiv X ξ).symm g` is the one remaining gap in the
special case of Stacks 0FDS; see the section below.

## What is not proved

The equation `hgv` is not established for any particular section. It says that the meromorphic
section of `𝒪_X` attached to `g` has generic value `g`, and for
`AlgebraicGeometry.meromorphicSectionOfFunctionField` it amounts to computing
`Stacks.Divisors.genericValue` through
`Stacks.Divisors.toMeromorphicSectionStalk_genericValue`, which needs the stalk at the generic
point of `AlgebraicGeometry.unit_comp_meromorphicUnitToUnit` together with the identification of
`Stacks.Divisors.toMeromorphicSectionStalk` with the stalk of the change-of-rings adjunction
unit. Neither is available. No declaration here carries the tag `0FDS`.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample (unitModule unitStalkEquiv)
open Stacks.Divisors (IsStalkBasis IsCoordinateAt toGenericStalk genericValue)

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- **The structure sheaf is invertible as a module over itself.** This is the monoidal unit
being invertible, transported to the `AlgebraicGeometry` spelling of invertibility. -/
instance isInvertible_unitModule :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (unitModule X) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ (unitModule X)).mp
    (Stacks.SheafOfModules.isInvertible_unit _ _)

variable [IsIntegral X]

omit [IsIntegral X] in
/-- The identification of the stalk of `𝒪_X` with the local ring carries the germ of `1`
to `1`. -/
theorem unitStalkEquiv_unitModuleGerm (x : X) :
    unitStalkEquiv X x (Stacks.UnitStalk.one X x) = 1 :=
  (Stacks.Ample.unitStalkFun_germ X x ⊤ trivial
      (show Γ(unitModule X, ⊤) from (1 : Γ(X, ⊤)))).trans
    (map_one (X.presheaf.germ ⊤ x trivial).hom)

omit [IsIntegral X] in
/-- Multiplication by the germ of `1` is the inverse of the identification of the stalk of
`𝒪_X` with the local ring. -/
theorem smul_unitModuleGerm (x : X) (r : X.presheaf.stalk x) :
    r • Stacks.UnitStalk.one X x = (unitStalkEquiv X x).symm r :=
  (unitStalkEquiv X x).injective <| by
    rw [LinearEquiv.apply_symm_apply, map_smul, unitStalkEquiv_unitModuleGerm, smul_eq_mul,
      mul_one]

omit [IsIntegral X] in
/-- **The germ of `1` is a basis of the stalk of `𝒪_X` at every point**: multiplication by it is
the inverse of the identification with the local ring, hence bijective. -/
theorem isStalkBasis_unitModuleGerm (x : X) :
    IsStalkBasis (unitModule X) x (Stacks.UnitStalk.one X x) := by
  have h : (fun r : X.presheaf.stalk x => r • Stacks.UnitStalk.one X x) =
      fun r => (unitStalkEquiv X x).symm r := funext (smul_unitModuleGerm X x)
  rw [IsStalkBasis, h]
  exact (unitStalkEquiv X x).symm.bijective

/-- Specialization to the generic point carries the germ of `1` at `x` to the germ of `1` at the
generic point: both are germs of the same global section. -/
theorem toGenericStalk_unitModuleGerm (x : X) :
    toGenericStalk (unitModule X) x (Stacks.UnitStalk.one X x) =
      Stacks.UnitStalk.one X (genericPoint X) :=
  Stacks.Divisors.toGenericStalk_germ (L := unitModule X) (W := ⊤) trivial trivial _

/-- **A rational function is its own coordinate.** The element of the generic stalk of `𝒪_X`
corresponding to `g` has `g` as a coordinate at every point of `X`, the germ of `1` being a
basis of the stalk there. -/
theorem isCoordinateAt_unitModule (x : X) (g : X.functionField) :
    IsCoordinateAt (unitModule X) x ((unitStalkEquiv X (genericPoint X)).symm g) g :=
  ⟨Stacks.UnitStalk.one X x, isStalkBasis_unitModuleGerm X x, by
    rw [toGenericStalk_unitModuleGerm, smul_unitModuleGerm]⟩

variable [IsLocallyNoetherian X]

/-- **The order of vanishing of a rational function, Stacks 02SF for `𝒪_X`.** A regular
meromorphic section of `𝒪_X` whose generic value corresponds to the rational function `g` has
order of vanishing `ord_ξ(g)` along every prime divisor `Z`, where `ξ` is the generic point
of `Z`. -/
theorem orderOfVanishingMeromorphic_unitModule_eq_ord (g : X.functionField)
    (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s)
    (hgv : genericValue (unitModule X) s = (unitStalkEquiv X (genericPoint X)).symm g)
    (Z : Stacks.Divisors.PrimeDivisor X) :
    Stacks.Divisors.orderOfVanishingMeromorphic X (unitModule X) s hs Z =
      X.ord g Z.genericPoint :=
  Stacks.Divisors.orderOfVanishingMeromorphic_eq X (unitModule X) s hs
    (by rw [hgv]; exact isCoordinateAt_unitModule X Z.genericPoint g)

/-- **The coefficient of the claim in the proof of Stacks 0FDS at one prime divisor.** At the
generic point of a prime divisor `Z`, the multiplicity of `𝒪_X/gI` minus the multiplicity of
`𝒪_X/I` is the order of vanishing of `g` along `Z`, where `I` is the ideal of denominators of
the meromorphic section of `𝒪_X` attached to `g`.

The hypothesis is that that section has generic value `g`. -/
theorem sheafMultiplicity_denominator_sub_eq_orderOfVanishingMeromorphic
    (g : X.functionFieldˣ)
    (hgv : genericValue (unitModule X) (meromorphicSectionOfFunctionField X g) =
      (unitStalkEquiv X (genericPoint X)).symm (g : X.functionField))
    (Z : Stacks.Divisors.PrimeDivisor X) :
    Stacks.Chow.sheafMultiplicity (cokernel (denominatorIdealMul X (unitModule X)
          (meromorphicSectionOfFunctionField X g))) Z.genericPoint -
        Stacks.Chow.sheafMultiplicity (cokernel (denominatorIdealι X (unitModule X)
          (meromorphicSectionOfFunctionField X g))) Z.genericPoint =
      Stacks.Divisors.orderOfVanishingMeromorphic X (unitModule X)
        (meromorphicSectionOfFunctionField X g)
        (isRegularMeromorphicSection_meromorphicSectionOfFunctionField X g) Z :=
  (sheafMultiplicity_denominator_sub_eq_ord g Z.coheight_genericPoint).trans
    (orderOfVanishingMeromorphic_unitModule_eq_ord X (g : X.functionField) _ _ hgv Z).symm

end AlgebraicGeometry
