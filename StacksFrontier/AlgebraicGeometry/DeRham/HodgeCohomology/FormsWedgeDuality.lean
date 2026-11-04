module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerWedgeDuality
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula

/-!
# Differential forms of complementary degrees are dual

Let `p : X ⟶ S` be smooth of relative dimension `d`. The sheaf of relative differentials
`Ω_{X/S}` is finite locally free of rank `d` ([Stacks, Tag 02G1]), so for `a + b = d` the wedge
product identifies `Ω^a_{X/S}` with the sheaf-hom `SheafHom(Ω^b_{X/S}, Ω^d_{X/S})`:

`Ω^a_{X/S} ≅ SheafHom(Ω^b_{X/S}, Ω^d_{X/S})`, `ω ↦ (η ↦ ω ∧ η)`.

This is the isomorphism `Ω^d_{X/k} ⊗ (Ω^p_{X/k})^∨ ≅ Ω^{d - p}_{X/k}` of the proof of
[Stacks, Tag 0FW4], in the form `Ω^{d - p} ≅ SheafHom(Ω^p, Ω^d)`; the sheaf-hom is
`AlgebraicGeometry.RingedSite.internalHomSheaf`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.formsWedgeHom`: the wedge pairing
  `Ω^a_{X/S} ⟶ SheafHom(Ω^b_{X/S}, Ω^{a+b}_{X/S})`.
* `AlgebraicGeometry.Scheme.Hom.formsWedgeIso`: it is an isomorphism for `p` smooth of relative
  dimension `a + b`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.formsWedgeHom_eval`: the value of `formsWedgeHom ω` on a form
  `η` over the same open is `ω ∧ η`.
* `AlgebraicGeometry.Scheme.Hom.isIso_formsWedgeHom`: the wedge pairing is an isomorphism for `p`
  smooth of relative dimension `a + b`.

## References

* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The ringed site of opens of a scheme. -/
local notation "𝒳" => Stacks.SheafOfModules.WedgeDuality.toRingedSite
  (Opens.grothendieckTopology X) X.sheaf

/-- **The wedge pairing of differential forms**, `Ω^a_{X/S} ⟶ SheafHom(Ω^b_{X/S}, Ω^{a+b}_{X/S})`,
`ω ↦ (η ↦ ω ∧ η)`. -/
noncomputable def formsWedgeHom (a b : ℤ) :
    relativeDifferentialForms p a ⟶
      RingedSite.internalHomSheaf 𝒳 (relativeDifferentialForms p b)
        (relativeDifferentialForms p (a + b)) :=
  Stacks.SheafOfModules.WedgeDuality.wedgeHom (relativeDifferentialFormsAlgebra p) a b

/-- The value of the wedge pairing of `ω` on a form `η` over the same open is `ω ∧ η`. -/
theorem formsWedgeHom_eval (a b : ℤ) (U : X.Opens)
    (ω : (relativeDifferentialForms p a).val.obj (op U))
    (η : (relativeDifferentialForms p b).val.obj (op U)) :
    ((formsWedgeHom p a b).val.app (op U) ω).app (op (Over.mk (𝟙 U))) η =
      ((relativeDifferentialFormsAlgebra p).mul a b).app (op U) ω η :=
  Stacks.SheafOfModules.WedgeDuality.wedgeHom_eval _ a b U ω η

/-- **For `p` smooth of relative dimension `a + b`, the wedge pairing
`Ω^a_{X/S} ⟶ SheafHom(Ω^b_{X/S}, Ω^{a+b}_{X/S})` is an isomorphism.** -/
theorem isIso_formsWedgeHom (a b : ℕ) [SmoothOfRelativeDimension (a + b) p] :
    IsIso (formsWedgeHom p (a : ℤ) (b : ℤ)) :=
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X) X.sheaf)
      (relativeDifferentials p) (a + b) :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials p (a + b)
  Stacks.SheafOfModules.WedgeDuality.isIso_wedgeHom _
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p)) a b

/-- **Forms of complementary degrees are dual**: for `p` smooth of relative dimension `a + b`,
`Ω^a_{X/S} ≅ SheafHom(Ω^b_{X/S}, Ω^{a+b}_{X/S})` by the wedge pairing. -/
noncomputable def formsWedgeIso (a b : ℕ) [SmoothOfRelativeDimension (a + b) p] :
    relativeDifferentialForms p (a : ℤ) ≅
      RingedSite.internalHomSheaf 𝒳 (relativeDifferentialForms p (b : ℤ))
        (relativeDifferentialForms p ((a : ℤ) + (b : ℤ))) :=
  haveI := isIso_formsWedgeHom p a b
  asIso (formsWedgeHom p (a : ℤ) (b : ℤ))

/-- The forward map of `formsWedgeIso p a b` is the wedge pairing `formsWedgeHom p a b`. -/
@[simp]
theorem formsWedgeIso_hom (a b : ℕ) [SmoothOfRelativeDimension (a + b) p] :
    (formsWedgeIso p a b).hom = formsWedgeHom p (a : ℤ) (b : ℤ) :=
  rfl

end AlgebraicGeometry.Scheme.Hom
