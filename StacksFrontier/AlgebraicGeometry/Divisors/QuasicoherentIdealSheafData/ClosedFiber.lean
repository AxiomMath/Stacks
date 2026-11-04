module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ClosedFiberPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.QuasicoherentIdealSheafData.Basic

/-!
# The closed fibre of a divided power scheme exists

A divided power scheme `X` carries a quasi-coherent ideal subsheaf `X.ideal` of `𝒪_{X.scheme}`,
and `Crystalline.DividedPowerScheme.ClosedFiberPresentation X` is the interface for its closed
fibre `X₀ = V(X.ideal)`: a scheme with a closed immersion into `X.scheme` cutting out `X.ideal` on
sections. Everything built on that interface —  the induced map on closed fibres, its
functoriality and the comparison with a fibre product — was stated for an arbitrary presentation,
because no presentation was known to exist.

This file produces one, from the ideal sheaf datum
`Stacks.Divisors.idealSheafDataOfSubmodule X.ideal` and Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme`. Since any two presentations are canonically
isomorphic (`Crystalline.DividedPowerScheme.ClosedFiberPresentation.isoOfPresentations`), this one
may be used as *the* closed fibre.

## Main definitions

* `Crystalline.DividedPowerScheme.closedFiberPresentation`: the canonical presentation of the
  closed fibre of a divided power scheme.
* `Crystalline.DividedPowerScheme.closedFiber` and
  `Crystalline.DividedPowerScheme.closedFiberι`: its underlying scheme and closed immersion.
* `Crystalline.DividedPowerScheme.closedFiberMap`: the map on closed fibres induced by a morphism
  of divided power schemes.

## Main results

* `Crystalline.DividedPowerScheme.closedFiberMap_comp_closedFiberι` and
  `Crystalline.DividedPowerScheme.eq_closedFiberMap`: the induced map is the unique map commuting
  with the closed immersions.
* `Crystalline.DividedPowerScheme.closedFiberMap_id` and
  `Crystalline.DividedPowerScheme.closedFiberMap_comp`: the closed fibre is functorial.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Crystalline.DividedPowerScheme

variable (X : DividedPowerScheme.{u})

/-- **The closed fibre of a divided power scheme.** The divided power ideal is a quasi-coherent
ideal subsheaf of the structure sheaf, hence an `AlgebraicGeometry.Scheme.IdealSheafData`
(`Stacks.Divisors.idealSheafDataOfSubmodule`), and the closed subscheme it cuts out is a
presentation of the closed fibre: it kills every section of the divided power ideal over an
arbitrary open and, over an affine open, nothing else. -/
def closedFiberPresentation : ClosedFiberPresentation X where
  carrier := (Stacks.Divisors.idealSheafDataOfSubmodule X.ideal).subscheme
  ι := (Stacks.Divisors.idealSheafDataOfSubmodule X.ideal).subschemeι
  isClosedImmersion := inferInstance
  app_eq_zero_of_mem V s hs :=
    Stacks.Divisors.subschemeι_app_eq_zero_of_mem X.ideal V s hs
  mem_of_app_eq_zero V s hs :=
    (Stacks.Divisors.subschemeι_app_eq_zero_iff_mem X.ideal V s).1 hs

/-- The underlying scheme of the closed fibre of a divided power scheme. -/
abbrev closedFiber : Scheme.{u} := (closedFiberPresentation X).carrier

/-- The closed immersion of the closed fibre of a divided power scheme into its ambient scheme. -/
abbrev closedFiberι : closedFiber X ⟶ X.scheme := (closedFiberPresentation X).ι

/-- A divided power scheme has a presentation of its closed fibre, so every statement proved for
an arbitrary `Crystalline.DividedPowerScheme.ClosedFiberPresentation` is non-vacuous. -/
instance nonempty_closedFiberPresentation : Nonempty (ClosedFiberPresentation X) :=
  ⟨closedFiberPresentation X⟩

section Map

variable {X Y Z : DividedPowerScheme.{u}}

/-- The map on closed fibres induced by a morphism `f : X ⟶ Y` of divided power schemes: since `f`
carries the divided power ideal of `Y` into that of `X`, the composite `X₀ ⟶ X ⟶ Y` kills the
ideal of `Y` and hence factors uniquely through the closed immersion `Y₀ ⟶ Y`. -/
def closedFiberMap (f : X ⟶ Y) : closedFiber X ⟶ closedFiber Y :=
  ((closedFiberPresentation X).map (closedFiberPresentation Y) f).1

/-- The induced map on closed fibres commutes with the closed immersions. -/
@[reassoc (attr := simp)]
theorem closedFiberMap_comp_closedFiberι (f : X ⟶ Y) :
    closedFiberMap f ≫ closedFiberι Y = closedFiberι X ≫ f.hom :=
  (closedFiberPresentation X).map_comp_ι _ f

/-- The induced map on closed fibres is the unique map commuting with the closed immersions, the
inclusion of a closed fibre being a monomorphism. -/
theorem eq_closedFiberMap (f : X ⟶ Y) (g : closedFiber X ⟶ closedFiber Y)
    (hg : g ≫ closedFiberι Y = closedFiberι X ≫ f.hom) : g = closedFiberMap f :=
  (cancel_mono (closedFiberι Y)).mp (hg.trans (closedFiberMap_comp_closedFiberι f).symm)

/-- The identity of a divided power scheme induces the identity on its closed fibre. -/
@[simp]
theorem closedFiberMap_id : closedFiberMap (𝟙 X) = 𝟙 (closedFiber X) :=
  (closedFiberPresentation X).map_id

/-- The closed fibre is functorial in the divided power scheme. -/
theorem closedFiberMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    closedFiberMap (f ≫ g) = closedFiberMap f ≫ closedFiberMap g :=
  (closedFiberPresentation X).map_comp (closedFiberPresentation Y) (closedFiberPresentation Z) f g

end Map

end Crystalline.DividedPowerScheme

end
