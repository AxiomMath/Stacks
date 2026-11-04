module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohen–Macaulay morphisms

A morphism of schemes whose fibres are locally Noetherian is Cohen–Macaulay at a point of its
source when it is flat there and the local ring of the corresponding fibre is Cohen–Macaulay.
It is a Cohen–Macaulay morphism when this holds at every point of its source.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsCohenMacaulayAt`: Cohen–Macaulayness of a morphism at a point
  of its source.
* `AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay`: Cohen–Macaulayness of a morphism at every point
  of its source.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFinitePresentation`: every fibre of
  a morphism locally of finite presentation is locally Noetherian.

## References

* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Every scheme-theoretic fibre of a morphism locally of finite presentation is locally
Noetherian. -/
public theorem isLocallyNoetherian_fiber_of_locallyOfFinitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (y : S) :
    IsLocallyNoetherian (f.fiber y) := by
  let _ : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField y))
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)

/-- The canonical isomorphism between the fibres of a morphism over two equal points. -/
public noncomputable def fiberIsoOfEq {X S : Scheme.{u}} (f : X ⟶ S)
    {y y' : S} (h : y = y') : f.fiber y ≅ f.fiber y' := by
  cases h
  exact Iso.refl _

/-- The isomorphism `fiberIsoOfEq f h` commutes with the inclusions of the fibres into `X`. -/
@[simp]
theorem fiberIsoOfEq_hom_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    {y y' : S} (h : y = y') :
    (fiberIsoOfEq f h).hom ≫ f.fiberι y' = f.fiberι y := by
  cases h
  rfl

namespace Scheme.Hom

/-- A morphism of schemes with locally Noetherian fibres is Cohen–Macaulay at `x` if it is flat
at `x` and the local ring of the fibre over `f x` at the point corresponding to `x` is
Cohen–Macaulay. -/
@[stacks 045R "part (1)", ega "IV 6.8.1" "(ii)", sga "1 II 4.19"]
public abbrev IsCohenMacaulayAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x : X) : Prop :=
  letI := hf (f x)
  IsFlatAt f.toLRSHom.toShHom x ∧
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

/-- A morphism of schemes with locally Noetherian fibres is Cohen–Macaulay if it is
Cohen–Macaulay at every point of its source. -/
@[stacks 045R "part (2)", ega "IV 6.8.1" "(ii), global"]
public abbrev IsCohenMacaulay {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) : Prop :=
  ∀ x : X, IsCohenMacaulayAt f hf x

end Scheme.Hom

end AlgebraicGeometry
