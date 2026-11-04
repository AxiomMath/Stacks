module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernComm
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSumsDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.ChernCapSquareZero
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme

/-!
# The first Chern class shift operator of a Picard class

`Stacks.Chow.firstChernShift` makes `c₁(ℒ) ∩ -` a degree-raising endomorphism of the graded
product `Stacks.Chow.ChowGradedProduct` of the Chow groups of `X`. It carries two hypotheses
about `ℒ`, both of which hold for every invertible module:

* `Stacks.Chow.InvertibleChernCapDescends`, Stacks 02TI in every degree, which is
  `Stacks.Chow.firstChernCapFactorsEverywhere`;
* for a pair of modules, `Stacks.Chow.FirstChernCapStepsCommute`, Stacks 02TJ, which is
  `Stacks.Chow.GenuineChern.invCap_capOnChow_comm`.

This file records both, and then assembles the shift operators into a homomorphism out of the
Picard group: by Stacks 02SP (additivity in the tensor product) and the isomorphism invariance of
the cap product, `[ℒ] ↦ c₁(ℒ) ∩ -` is a homomorphism `Pic(X) ⟶ End(A_*(X))`.

## Main definitions

* `Stacks.Chow.picardFirstChernShift` — the homomorphism `Pic(X) →+ AddMonoid.End (A_*(X))`.

## Main results

* `Stacks.Chow.picardFirstChernShift_picardClass` — the homomorphism on the class of `ℒ` is the
  shift operator of `ℒ`.
* `Stacks.Chow.firstChernShift_eq_nsmul_sum_of_picardClass` — a relation
  `[𝒩] = m • ∑ᵢ [ℒᵢ]` in `Pic(X)` gives the relation `c₁(𝒩) = m • ∑ᵢ c₁(ℒᵢ)` between the shift
  operators.

## Implementation notes

The two inputs, `Stacks.Chow.invertibleChernCapDescends` (Stacks 02TI for every invertible
module) and `Stacks.Chow.firstChernCapStepsCommute` (Stacks 02TJ in the shift-operator form),
are the base's, from the module
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSumsDischarge`.

## References

* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### The homomorphism out of the Picard group -/

variable (n : ℤ)

/-- The shift operator of a chosen representative of a Picard class. -/
def picardFirstChernShiftFun (x : X.picardGroup) : AddMonoid.End (ChowGradedProduct C p n) :=
  @firstChernShift C X p _ n
    (Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf x).choose
    (Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf x).choose_spec.choose
    (@invertibleChernCapDescends C X p _ _
      (Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf
        x).choose_spec.choose)

/-- The shift operator of any invertible module computes the chosen one at its class. -/
theorem picardFirstChernShiftFun_picardClass (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    picardFirstChernShiftFun C p n (X.picardClass L hL) =
      firstChernShift C p n L (invertibleChernCapDescends C p L) := by
  set h := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf X.ringCatIsSheaf
    (X.picardClass L hL)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      h.choose := h.choose_spec.choose
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatIsSheaf _ _ _ _).1
    h.choose_spec.choose_spec
  exact firstChernShift_congr C p n _ L e _ _

/-- **The first Chern class as a homomorphism out of the Picard group**, `[ℒ] ↦ c₁(ℒ) ∩ -`. It is
well defined by the isomorphism invariance of the cap product and additive by Stacks 02SP. -/
def picardFirstChernShift : X.picardGroup →+ AddMonoid.End (ChowGradedProduct C p n) :=
  AddMonoidHom.mk' (picardFirstChernShiftFun C p n) fun x y => by
    obtain ⟨L, hL, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf
      X.ringCatIsSheaf x
    obtain ⟨N, hN, rfl⟩ := Stacks.SheafOfModules.exists_picardClass_eq X.presheaf
      X.ringCatIsSheaf y
    have hLN := @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _ _ _ _ _ _ hL hN
    rw [Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ hL hN hLN]
    change picardFirstChernShiftFun C p n (X.picardClass _ hLN) =
      picardFirstChernShiftFun C p n (X.picardClass L hL) +
        picardFirstChernShiftFun C p n (X.picardClass N hN)
    rw [@picardFirstChernShiftFun_picardClass C X p _ n _ hLN,
      @picardFirstChernShiftFun_picardClass C X p _ n L hL,
      @picardFirstChernShiftFun_picardClass C X p _ n N hN]
    have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
      hL
    have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N :=
      hN
    have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
        (Scheme.Modules.tensorObj L N) := hLN
    exact firstChernShift_eq_add_of_iso_tensorObj (C := C) (p := p) (n := n)
      (A := L) (B := N) (D := Scheme.Modules.tensorObj L N) (Iso.refl _) _ _ _

/-- **The homomorphism on the class of `ℒ` is the shift operator of `ℒ`.** -/
theorem picardFirstChernShift_picardClass (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    picardFirstChernShift C p n (X.picardClass L hL) =
      firstChernShift C p n L (invertibleChernCapDescends C p L) :=
  picardFirstChernShiftFun_picardClass C p n L

/-- **A relation in the Picard group is a relation between the shift operators.** If
`[𝒩] = m • ∑ᵢ [ℒᵢ]` in `Pic(X)`, then `c₁(𝒩) ∩ - = m • ∑ᵢ c₁(ℒᵢ) ∩ -` as endomorphisms of the
graded product of the Chow groups. This is the hypothesis `hM` of the hinge of Stacks 0FH9. -/
theorem firstChernShift_eq_nsmul_sum_of_picardClass {r : ℕ} (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (L : Fin r → X.Modules)
    [hL : ∀ i, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (L i)] (m : ℕ)
    (h : X.picardClass M hM = m • ∑ i, X.picardClass (L i) (hL i)) :
    firstChernShift C p n M (invertibleChernCapDescends C p M) =
      m • ∑ i, firstChernShift C p n (L i) (invertibleChernCapDescends C p (L i)) := by
  rw [← picardFirstChernShift_picardClass, h, map_nsmul, map_sum]
  simp only [picardFirstChernShift_picardClass]

end Stacks.Chow

end
