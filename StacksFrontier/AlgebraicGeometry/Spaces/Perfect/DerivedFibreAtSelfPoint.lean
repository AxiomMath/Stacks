module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiNumbers

/-!
# The derived fibre at a field-valued point is read on the field spectrum

Let `Y` be an algebraic space, `K` an object of `D(𝒪_Y)` and `p : Spec(k) ⟶ Y` a field-valued
point.  The derived fibre of `K` at `p` is the derived pullback `Lp^*K` on `Spec(k)`, and
`Spec(k)` has its own tautological field-valued point, the identity of `Spec(k)`.  The
derived-fibre Betti numbers of `K` at `p` are those of `Lp^*K` at that tautological point: this is
the form in which an isomorphism `Lp^*K ≅ L` of objects of `D(𝒪_{Spec(k)})`, such as the base
change isomorphism of Stacks 0A1P, computes the Betti numbers of `K`.

## Main definitions

* `AlgebraicGeometry.Space.FieldValuedPoint.selfPoint`: the tautological field-valued point of
  the algebraic space of the field spectrum of a field-valued point.

## Main results

* `AlgebraicGeometry.Space.FieldValuedPoint.selfPoint_map_toSpace`: its image under
  `p : Spec(k) ⟶ Y` is `p`.
* `AlgebraicGeometry.Space.derivedFibreBettiAt_eq_selfPoint`: the Betti numbers of `K` at `p`
  are those of `Lp^*K` at the tautological point.

## References

* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
/- The standard model of the derived category is forced by
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The tautological field-valued point `Spec(k) ⟶ Spec(k)` of the algebraic space of the field
spectrum of a field-valued point. -/
def FieldValuedPoint.selfPoint {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) : FieldValuedPoint B S hS (schemeSpace p.siteObject).1 where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase
  value := 𝟙 p.siteObject

/-- The tautological point of `Spec(k)` maps to `p` under `p : Spec(k) ⟶ Y`. -/
theorem FieldValuedPoint.selfPoint_map_toSpace {Y : AlgebraicSpaces B S hS}
    (p : FieldValuedPoint B S hS Y.1) :
    p.selfPoint.map B S hS _ p.toSpace.hom = p := by
  cases p
  simp only [FieldValuedPoint.map, FieldValuedPoint.selfPoint, FieldValuedPoint.toSpace]
  congr 1
  change (yonedaEquiv.symm _).app _ (𝟙 _) = _
  simp [yonedaEquiv]

/-- The derived-fibre Betti numbers of `K` at a field-valued point `p : Spec(k) ⟶ Y` are those of
`Lp^*K` at the tautological point of `Spec(k)`. -/
theorem derivedFibreBettiAt_eq_selfPoint (Y : AlgebraicSpaces B S hS)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (n : ℤ)
    (p : FieldValuedPoint B S hS Y.1) :
    derivedFibreBettiAt Y K n p =
      derivedFibreBettiAt (schemeSpace p.siteObject)
        ((smallEtaleDerivedModulePullback B S hS p.toSpace).obj K) n p.selfPoint := by
  rw [derivedFibreBettiAt_derivedPullback Y p.toSpace K n p.selfPoint,
    FieldValuedPoint.selfPoint_map_toSpace]



end AlgebraicGeometry.Space
