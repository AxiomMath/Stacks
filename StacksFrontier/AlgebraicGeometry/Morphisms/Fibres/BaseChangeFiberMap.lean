module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The comparison morphism of fibres attached to a commutative square

Let `j ≫ f = fU ≫ i` be a commutative square of schemes and let `t` be a point of the bottom
right corner's source `V`. The fibre of `fU` at `t` and the fibre of `f` at `i t` are pullbacks
over the spectra of the residue fields `κ(t)` and `κ(i t)`, and the map of residue fields
`κ(i t) ⟶ κ(t)` induced by `i`, together with `j`, therefore gives a canonical morphism from the
first to the second.

The pullback square is the case of this that is wanted most often: for `f : X ⟶ Y`, a base
change `g : Y' ⟶ Y` and a point `z` of `Y'`, it compares the fibre of `pullback.snd f g` at `z`
with the fibre of `f` at `g z`. That special case has its own name here, is *defined* as the
general morphism at the pullback square, and its facts are corollaries of the general ones.

## Main definitions

* `AlgebraicGeometry.restrictedFiberMap` is the comparison morphism of a commutative square.
* `AlgebraicGeometry.baseChangeFiberMap` is its value at a pullback square.

## Main results

* `AlgebraicGeometry.restrictedFiberMap_fiberι`,
  `AlgebraicGeometry.baseChangeFiberMap_comp_fiberι`: the comparison morphism is compatible with
  the inclusions of the two fibres into the two total spaces.
* `AlgebraicGeometry.restrictedFiberMap_comp_fiberToSpecResidueField`: it lies over the residue
  field map of `i`.
* `AlgebraicGeometry.restrictedFiberMap_isOpenImmersion`: a square of open immersions gives an
  open immersion of fibres.
* `AlgebraicGeometry.isIso_baseChangeFiberMap`: at a pullback square the comparison morphism is
  an isomorphism as soon as `g` induces an isomorphism of residue fields at `z`.

## Implementation notes

All of this is stated here, with no dependence beyond the construction of fibres and of residue
fields, because the bodies of API built on it are developed independently: the consequences of
the fibre square at `z` being the fibre square at `g z` pulled back along
`Spec κ(z) ⟶ Spec κ(g z)` for an elementary étale neighbourhood, the comparison of the inverse
images of an open subscheme under the two fibre inclusions, the base change of a family of
cycles on fibres, and the restriction of a family of cycles to an open subscheme. No two of the
modules carrying those import each other, so what they share is stated in this leaf rather than
in any one of them. In particular the general square's morphism is stated here rather than in
the relative-cycles module where it was first needed, so that the pullback-square special case
can be its instance without that module's development becoming a prerequisite for the rest.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The morphism of scheme-theoretic fibres induced by a commutative square `j ≫ f = fU ≫ i`:
from the fibre of `fU` at a point `t` of `V` to the fibre of `f` at `i t`. -/
def restrictedFiberMap {X S U V : Scheme.{u}} (f : X ⟶ S)
    (fU : U ⟶ V) (j : U ⟶ X) (i : V ⟶ S)
    (h : j ≫ f = fU ≫ i) (t : V) :
    fU.fiber t ⟶ f.fiber (i t) :=
  pullback.map fU (V.fromSpecResidueField t) f (S.fromSpecResidueField (i t)) j
    (Spec.map (i.residueFieldMap t)) i h.symm (by simp)

/-- The fibre map of a commutative square is compatible with the inclusions of the fibres into
the total spaces. -/
theorem restrictedFiberMap_fiberι {X S U V : Scheme.{u}} (f : X ⟶ S)
    (fU : U ⟶ V) (j : U ⟶ X) (i : V ⟶ S) (h : j ≫ f = fU ≫ i) (t : V) :
    restrictedFiberMap f fU j i h t ≫ f.fiberι (i t) = fU.fiberι t ≫ j := by
  dsimp only [restrictedFiberMap, Scheme.Hom.fiber, Scheme.Hom.fiberι, pullback.map]
  rw [pullback.lift_fst]

/-- The fibre map of a square of open immersions is itself an open immersion. -/
theorem restrictedFiberMap_isOpenImmersion {X S U V : Scheme.{u}} (f : X ⟶ S)
    (fU : U ⟶ V) (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (t : V) :
    IsOpenImmersion (restrictedFiberMap f fU j i h t) := by
  have : IsOpenImmersion (Spec.map (i.residueFieldMap t)) := inferInstance
  show IsOpenImmersion (pullback.map fU (V.fromSpecResidueField t) f
    (S.fromSpecResidueField (i t)) j (Spec.map (i.residueFieldMap t)) i h.symm (by simp))
  infer_instance

/-- The fibre map of a commutative square lies over the residue field map of `i`: it carries the
structure morphism of the fibre of `f` to the structure morphism of the fibre of `fU` followed
by `Spec` of the residue field map of `i` at `t`. -/
theorem restrictedFiberMap_comp_fiberToSpecResidueField {X S U V : Scheme.{u}} (f : X ⟶ S)
    (fU : U ⟶ V) (j : U ⟶ X) (i : V ⟶ S) (h : j ≫ f = fU ≫ i) (t : V) :
    restrictedFiberMap f fU j i h t ≫ f.fiberToSpecResidueField (i t) =
      fU.fiberToSpecResidueField t ≫ Spec.map (i.residueFieldMap t) := by
  show (pullback.lift
    (pullback.fst fU (V.fromSpecResidueField t) ≫ j)
    (pullback.snd fU (V.fromSpecResidueField t) ≫ Spec.map (i.residueFieldMap t))
    _) ≫ pullback.snd f (S.fromSpecResidueField (i t)) =
    pullback.snd fU (V.fromSpecResidueField t) ≫ Spec.map (i.residueFieldMap t)
  rw [pullback.lift_snd]

/-- The canonical morphism from the fibre at `z` of the base change of `f` along `g` to the
fibre of `f` at `g z`, induced by the map of residue fields `κ(g z) ⟶ κ(z)`: the fibre map of
the pullback square. -/
def baseChangeFiberMap {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : Y') :
    (pullback.snd f g).fiber z ⟶ f.fiber (g z) :=
  restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition z

/-- The comparison morphism `AlgebraicGeometry.baseChangeFiberMap` is compatible with the
inclusions of the two fibres into the two total spaces: composing it with the inclusion of the
fibre of `f` at `g z` is the inclusion of the fibre of the base change at `z` followed by the
projection to `X`. -/
@[reassoc]
theorem baseChangeFiberMap_comp_fiberι {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : Y') :
    baseChangeFiberMap f g z ≫ f.fiberι (g z) =
      (pullback.snd f g).fiberι z ≫ pullback.fst f g :=
  restrictedFiberMap_fiberι ..

/-- Base change along a morphism that induces an isomorphism of residue fields at `z` does not
change the fibre over that point: the fibre square at `z` is the fibre square at `g z` pulled
back along the isomorphism `Spec κ(z) ⟶ Spec κ(g z)`, so the comparison morphism is the base
change of an isomorphism. -/
instance isIso_baseChangeFiberMap {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (z : Y')
    [IsIso (g.residueFieldMap z)] : IsIso (baseChangeFiberMap f g z) :=
  (isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) z).isIso_fst_of_isIso

end AlgebraicGeometry
