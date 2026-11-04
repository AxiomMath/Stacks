module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointNeighborhoodLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSections
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspaceGeneralPullback

/-!
# The germ of the pullback of a global function

Let `g : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `s` be a global regular
function on `Y`. Its pullback `g^*s`, which is
`AlgebraicGeometry.Space.globalFunctionsMap` and needs no hypothesis on `g`, has at every
geometric point `x` of `X` the germ that the comparison homomorphism of **Stacks 04NG** sends
the germ of `s` at the image of `x` to.

## Main results

* `AlgebraicGeometry.Space.etaleLocalRingGerm_globalFunctionsMap`: the germ identity, for
  *arbitrary* small étale neighbourhoods on both sides.

## How it is proved

`AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_lift` produces, over the prescribed pointed
chart of `Y`, a pointed chart of `X` at `x`; on such a diagram
`AlgebraicGeometry.Space.etaleLocalRingMap_isEtaleLocalRingMap` is the germ compatibility of
**Stacks 04NG**, and `AlgebraicGeometry.Space.globalFunctionsMap_val_of_factor` says that on a
chart which factors, the pullback of `s` *is* the pullback of its value along the factoring
morphism of schemes. Since the germ of a global function does not depend on the chosen
neighbourhood (`AlgebraicGeometry.Space.etaleLocalRingGerm_chartValue_eq`), the manufactured
chart may be traded for the prescribed one.

The statement is quantified over both neighbourhoods because that is the shape in which both the
hypothesis of **Stacks 06LW** and the hypothesis `AlgebraicGeometry.Stack.FibreIsRegularSequenceAt`
of **Stacks 06MD** are written: each quantifies over the neighbourhoods of its own point, and
matching them is exactly what this identity does.

## References

* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The germ of a pulled-back global function.** Let `g : X ⟶ Y` be a morphism of algebraic
spaces over `S`, let `s` be a global regular function on `Y` and let `x` be a geometric point of
`X`. For every small étale neighbourhood `Nx` of `x` and every small étale neighbourhood `N` of
the image of `x` in `Y`, the germ at `x` of the restriction of `g^*s` to the chart of `Nx` is the
image under the comparison homomorphism of **Stacks 04NG** of the germ at the image of `x` of the
restriction of `s` to the chart of `N`. -/
theorem etaleLocalRingGerm_globalFunctionsMap (g : X ⟶ Y)
    (s : (SheafOfModules.unit (structureRingSheaf B S hS Y)).sections)
    (x : GeometricPoint B S hS X.1) (Nx : SmallEtaleNeighborhood x)
    (N : SmallEtaleNeighborhood (geometricPointMap g.hom x)) :
    etaleLocalRingGerm B S hS X.1 x (op Nx)
        ((globalFunctionsMap B S hS g s).val (op Nx.chart)) =
      etaleLocalRingMap X.2 g.hom x
        (etaleLocalRingGerm B S hS Y.1 (geometricPointMap g.hom x) (op N)
          (s.eval (op N.chart))) := by
  obtain ⟨Nx₀, -, l, hl, hpl⟩ := exists_smallEtaleNeighborhood_lift g.hom
    (nonempty_smallEtaleNeighborhood X.2 x).some N
  have h1 := RingHom.congr_fun
    (etaleLocalRingMap_isEtaleLocalRingMap X.2 g.hom x Nx₀ N l hl hpl) (s.eval (op N.chart))
  have h2 := globalFunctionsMap_val_of_factor B S hS g s N.chart Nx₀.chart l hl.symm
  have h3 := etaleLocalRingGerm_chartValue_eq B S hS X.1 X.2
    (globalFunctionsMap B S hS g s :
      (SheafOfModules.unit (structureRingSheaf B S hS X)).sections) Nx Nx₀
  exact h3.trans ((congrArg (etaleLocalRingGerm B S hS X.1 x (op Nx₀)) h2).trans h1)

/-- The two accessors agree: evaluating a global function of
`AlgebraicGeometry.Space.globalFunctions'` as a section of the structure sheaf of modules is
evaluating it as a compatible family. -/
theorem eval_eq_val (t : (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (V : SmallEtale B S hS X.1) :
    t.eval (op V) = (t : globalFunctions' B S hS X.1).val (op V) := rfl

end AlgebraicGeometry.Space

end
