module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.OrderOfVanishing

/-!
# A local ratio against a stalk basis is a coordinate of a meromorphic section

Let `W` be a locally Noetherian integral scheme, `M` a quasi-coherent `𝒪_W`-module and `σ` a
meromorphic section of `M`. Suppose that over an open set `U` of `W` there are sections `A`, `B`
of `𝒪_W` and a section `m` of `M` with

  `B · σ|_U = A · m`   in   `Γ(𝒦_W(M), U)`,

that `m` generates the stalk `M_z` at a point `z ∈ U`, and that the germ of `B` at the generic
point of `W` is nonzero. Then `A / B` is a **coordinate of `σ` at `z`** in the sense of
[Stacks, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF): the generic value of `σ` is
`A / B` times the generic value of that generator.

This is the step that turns a local ratio representing a meromorphic section into the rational
function whose order of vanishing is the order of vanishing of the section, and it is what
`Stacks.Divisors.orderOfVanishingMeromorphic_eq` consumes.

## Main definitions

* `Stacks.Chow.meromorphicValue` — the value of a meromorphic section over an open set, read in
  the sheaf of meromorphic sections *as a sheaf of `𝒪_W`-modules*; see the implementation notes.

## Main results

* `Stacks.Chow.isCoordinateAt_of_smul_eq` — the statement above.
* `Stacks.Chow.ord_sub_eq_orderOfVanishingMeromorphic` — consequently, for an invertible `M` and a
  regular `σ`, the difference of the orders of vanishing of `A` and `B` at a point of codimension
  one is the order of vanishing of `σ` along the prime divisor that point generates.

## Implementation notes

The generic value of a meromorphic section is characterized by
`Stacks.Divisors.toMeromorphicSectionStalk_genericValue`, and the map it is characterized through
is bijective at the generic point of an integral scheme, the regular germs there being units. So
the identity to be proved may be pushed into the stalk `𝒦_W(M)_η`, where the hypothesis becomes
`B · g(σ) = A · g(m)` for the germs of `A` and `B` in the function field; the germ of `B` is a
nonzero element of a field, so it is invertible, and the identity is the cancellation of that
unit — `Stacks.Chow.eq_smul_of_smul_eq`, which needs no field structure, only an inverse.

`Stacks.Chow.meromorphicValue` exists because the scalar action in the hypothesis is the action of
`𝒪_W(U)`, which is registered on the sections of
`Stacks.Divisors.meromorphicSectionRestrict` — the sheaf of meromorphic sections read by
restriction of scalars along `𝒪_W ⟶ 𝒦_W`. A type ascription on `σ.val (op U)` does not reach
instance search, which re-infers the type from the term, so the value is produced by a
declaration whose *declared* type is the one carrying the action.
`Stacks.Chow.meromorphicValue_eq` identifies it with `σ.val (op U)`.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace
open Stacks.ModuleStalk

universe u

namespace Stacks.Chow

/-! ### Cancelling an invertible scalar -/

/-- **Cancelling an invertible scalar.** If `b · x = a · y` and `c` is an inverse of `b`, then
`x = (c · a) · y`. No field structure is needed. -/
theorem eq_smul_of_smul_eq {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
    {a b c : R} {x y : N} (hc : c * b = 1) (h : b • x = a • y) : x = (c * a) • y := by
  rw [← one_smul R x, ← hc, mul_smul, h, smul_smul]

/-! ### The value of a meromorphic section as a section of an `𝒪_W`-module -/

variable {W : Scheme.{u}} [AlgebraicGeometry.IsIntegral W] (M : W.Modules)
  (σ : AlgebraicGeometry.MeromorphicSection W.sheaf M)

/-- The value of a meromorphic section over an open set, at the declared type of the sections of
the sheaf of meromorphic sections read as a sheaf of `𝒪_W`-modules; see the implementation
notes. -/
def meromorphicValue (U : W.Opens) :
    ↑((Stacks.Divisors.meromorphicSectionRestrict W.sheaf M).obj (op U)) :=
  res (Stacks.Divisors.meromorphicSectionRestrict W.sheaf M) (le_top : U ≤ ⊤) (σ.val (op ⊤))

omit [AlgebraicGeometry.IsIntegral W] in
/-- `Stacks.Chow.meromorphicValue` is the value of the section over the open set. -/
theorem meromorphicValue_eq (U : W.Opens) : meromorphicValue M σ U = σ.val (op U) :=
  PresheafOfModules.sections_property σ (homOfLE (le_top : U ≤ ⊤)).op

omit [AlgebraicGeometry.IsIntegral W] in
/-- The germ of `Stacks.Chow.meromorphicValue` at a point is the germ of the global value. -/
theorem germ_meromorphicValue {U : W.Opens} {x : W} (hx : x ∈ U) :
    germ (Stacks.Divisors.meromorphicSectionRestrict W.sheaf M) U x hx
        (meromorphicValue M σ U) =
      germ (AlgebraicGeometry.meromorphicSectionSheaf W.sheaf M).val ⊤ x trivial
        (σ.val (op ⊤)) :=
  germ_res (Stacks.Divisors.meromorphicSectionRestrict W.sheaf M) (le_top : U ≤ ⊤) hx
    (σ.val (op ⊤))

/-! ### The coordinate -/

/-- A section of `𝒪_W` at the declared type over which the action on the sections of
`Stacks.Divisors.meromorphicSectionRestrict` is registered; see the implementation notes. -/
def structureScalar (U : W.Opens) (b : Γ(W, U)) : ↑(W.sheaf.presheaf.obj (op U)) := b

variable [M.IsQuasicoherent]

/-- **A local ratio against a stalk basis is a coordinate.** If `B · σ = A · m` over `U`, with `m`
generating the stalk of `M` at `z ∈ U` and the germ of `B` at the generic point nonzero, then
`A / B` is a coordinate of `σ` at `z` in the sense of [Stacks, Tag 02SF]. -/
theorem isCoordinateAt_of_smul_eq [IsLocallyNoetherian W] {U : W.Opens}
    [Nonempty (U : W.Opens)] (hη : genericPoint W ∈ U) {z : W} (hz : z ∈ U)
    {A B : Γ(W, U)} {m : Γ(M, U)}
    (hm : Stacks.Divisors.IsStalkBasis M z ((M.presheaf.germ U z hz).hom m))
    (hB : W.germToFunctionField U B ≠ 0)
    (heq : structureScalar U B • meromorphicValue M σ U =
      structureScalar U A •
        ((Stacks.Divisors.toMeromorphicSectionSheaf W.sheaf M).app (op U)).hom m) :
    Stacks.Divisors.IsCoordinateAt M z (Stacks.Divisors.genericValue M σ)
      (W.germToFunctionField U A / W.germToFunctionField U B) := by
  let α : ↑(W.sheaf.presheaf.stalk (genericPoint W)) :=
    W.germToFunctionField U A / W.germToFunctionField U B
  let _mFg : Module ↑(W.sheaf.presheaf.stalk (genericPoint W))
      ↑((presheafOn M.val).stalk (genericPoint W)) := moduleStalk M.val (genericPoint W)
  let _mKg : Module ↑(W.sheaf.presheaf.stalk (genericPoint W))
      ↑((presheafOn (AlgebraicGeometry.meromorphicSectionSheaf W.sheaf M).val).stalk
        (genericPoint W)) :=
    Stacks.Divisors.moduleStalkMeromorphicSectionSheaf W.sheaf M (genericPoint W)
  have _hloc := Stacks.Divisors.isLocalizedModule_toMeromorphicSectionStalk W.sheaf M
    (genericPoint W)
  have hbij : Function.Bijective
      (Stacks.Divisors.toMeromorphicSectionStalk W.sheaf M (genericPoint W)) :=
    Stacks.Localization.bijective_of_isLocalizedModule_of_isUnit
      (S := Stacks.Divisors.regularGerms W.sheaf (genericPoint W)) _
      fun _ hs => Stacks.Divisors.regularGerms_genericPoint_le_isUnit hs
  have hβ : (W.germToFunctionField U B)⁻¹ * W.germToFunctionField U B = 1 :=
    inv_mul_cancel₀ hB
  have hgerm := congrArg
    (germ (Stacks.Divisors.meromorphicSectionRestrict W.sheaf M) U (genericPoint W) hη) heq
  rw [presheafGerm_smul (Stacks.Divisors.meromorphicSectionRestrict W.sheaf M) hη
      (structureScalar U B) (meromorphicValue M σ U),
    germ_meromorphicValue M σ hη,
    presheafGerm_smul (Stacks.Divisors.meromorphicSectionRestrict W.sheaf M) hη
      (structureScalar U A)
      (((Stacks.Divisors.toMeromorphicSectionSheaf W.sheaf M).app (op U)).hom m)] at hgerm
  refine ⟨(M.presheaf.germ U z hz).hom m, hm, ?_⟩
  rw [Stacks.Divisors.toGenericStalk_germ hz hη m]
  refine hbij.injective
    (Eq.trans (Stacks.Divisors.toMeromorphicSectionStalk_genericValue M σ) ?_)
  refine Eq.trans ?_
    (((Stacks.Divisors.toMeromorphicSectionStalk W.sheaf M (genericPoint W)).map_smul
      α ((M.presheaf.germ U (genericPoint W) hη).hom m)).symm)
  refine Eq.trans ?_ (congrArg
    (fun y : ↑((presheafOn (AlgebraicGeometry.meromorphicSectionSheaf W.sheaf M).val).stalk
        (genericPoint W)) => α • y)
    (stalkMap_germ (Stacks.Divisors.toMeromorphicSectionSheaf W.sheaf M)
      (genericPoint W) U hη m).symm)
  refine Eq.trans (eq_smul_of_smul_eq
    (R := ↑(W.sheaf.presheaf.stalk (genericPoint W))) hβ hgerm) (congrArg
    (fun r : ↑(W.sheaf.presheaf.stalk (genericPoint W)) =>
      r • germ (Stacks.Divisors.meromorphicSectionRestrict W.sheaf M) U (genericPoint W) hη
        (((Stacks.Divisors.toMeromorphicSectionSheaf W.sheaf M).app (op U)).hom m))
    (div_eq_inv_mul (W.germToFunctionField U A) (W.germToFunctionField U B)).symm)

/-! ### The order of vanishing of the section -/

/-- **The difference of the orders of vanishing of the numerator and the denominator of a local
ratio is the order of vanishing of the section.** For an invertible `M` and a regular `σ`
represented over `U` as `A / B` against a generator `m` of `M_z`, with `z` of codimension one, the
order of vanishing of `σ` along the prime divisor generated by `z` is `ord(A) - ord(B)`.

This is `Stacks.Chow.isCoordinateAt_of_smul_eq` fed to
`Stacks.Divisors.orderOfVanishingMeromorphic_eq`, with `AlgebraicGeometry.Scheme.ord_mul`
splitting the order of the quotient. -/
theorem ord_sub_eq_orderOfVanishingMeromorphic [IsLocallyNoetherian W]
    [AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj W.ringCatSheaf.property M]
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection W.sheaf M σ)
    {U : W.Opens} [Nonempty (U : W.Opens)] (hη : genericPoint W ∈ U) {z : W} (hz : z ∈ U)
    (hco : coheight z = 1) {A B : Γ(W, U)} {m : Γ(M, U)}
    (hm : Stacks.Divisors.IsStalkBasis M z ((M.presheaf.germ U z hz).hom m))
    (hA : W.germToFunctionField U A ≠ 0) (hB : W.germToFunctionField U B ≠ 0)
    (heq : structureScalar U B • meromorphicValue M σ U =
      structureScalar U A •
        ((Stacks.Divisors.toMeromorphicSectionSheaf W.sheaf M).app (op U)).hom m) :
    W.ord (W.germToFunctionField U A) z - W.ord (W.germToFunctionField U B) z =
      Stacks.Divisors.orderOfVanishingMeromorphic W M σ hs
        (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco) := by
  have hZ := Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne z hco
  have hcoord := isCoordinateAt_of_smul_eq M σ hη hz hm hB heq
  have hord : Stacks.Divisors.orderOfVanishingMeromorphic W M σ hs
        (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco) =
      W.ord (W.germToFunctionField U A / W.germToFunctionField U B) z := by
    refine Eq.trans (Stacks.Divisors.orderOfVanishingMeromorphic_eq W M σ hs
      (a := W.germToFunctionField U A / W.germToFunctionField U B) ?_) ?_
    · rw [hZ]; exact hcoord
    · rw [hZ]
  have hsplit : W.ord (W.germToFunctionField U A) z =
      W.ord (W.germToFunctionField U A / W.germToFunctionField U B) z +
        W.ord (W.germToFunctionField U B) z := by
    rw [← Scheme.ord_mul (div_ne_zero hA hB) hB, div_mul_cancel₀ _ hB]
  rw [hord, hsplit]
  ring

end Stacks.Chow

end
