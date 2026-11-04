module

public import StacksFrontier.CategoryTheory.Shift.TensorRightOfShiftedUnit
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorCommShiftTwo
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 08EU] at every shift of the structure sheaf

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `E ∈ D(𝒪_X)`.  The
projection-formula morphism of [Stacks, Tag 0B53],

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`,

is invertible at `K = 𝒪_Y[0]⟦m⟧` for **every** integer `m`, with no hypothesis at all.  This is
the case the source's proof of [Stacks, Tag 08EU] calls clear — "the statement of the lemma is
clear for shifts of the structure sheaf" — and it is the base case of the dévissage of
[Stacks, Tag 0B54].

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isEquivalence`: the
  derived form of the abstract projection formula.  The projection-formula morphism is invertible
  at any `K` for which tensoring on the right by `K` is an equivalence of `D(𝒪_Y)` and tensoring
  on the right by `Lf^*K` is an equivalence of `D(𝒪_X)`.  No hypothesis on `f` or on `E`.
* `Stacks.Cohomology.DerivedProjectionFormula.isEquivalence_tensorRight_unitShift`: tensoring on
  the right by `𝒪_Z[0]⟦m⟧` is an equivalence of `D(𝒪_Z)` — it is the shift by `m`.
* `Stacks.Cohomology.DerivedProjectionFormula.pullbackUnitShiftIso`:
  `Lf^*(𝒪_Y[0]⟦m⟧) ≅ 𝒪_X[0]⟦m⟧`.
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitShift_unconditional`:
  **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]⟦m⟧`, for every `m`, with no hypothesis.**
* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_singleUnit_degree`: the
  same read at the structure sheaf placed in an arbitrary degree, `K = 𝒪_Y[i]`.

## The route, and why it needs no shift compatibility of the comparison

Passing from invertibility at an object to invertibility at its shifts would need a
`CategoryTheory.NatTrans.CommShift` for the projection-formula morphism, hence a shift
compatibility of the comparison of [Stacks, Tag 079U], which is not available.  Nothing below
transports invertibility along a shift; each shift of the structure sheaf is handled on its own,
by the same argument that handles the structure sheaf itself in a stronger form.

The argument is `Stacks.ProjectionFormula.isIso_adjunctionTensorMap`, the abstract projection
formula already in this repository: for an adjunction `L ⊣ R`, bifunctors `A`, `B` and a
comparison `α`, the map `A (R G, H) ⟶ R (B (G, L H))` is invertible as soon as `α` is invertible
in its first argument at `H` and the two functors `- ⊗ H` and `- ⊗ L H` are equivalences.  It was
written for the *ordinary* projection formula of [Stacks, Tag 0FZE] at an invertible module, it
mentions no geometry and no derived category, and the morphism of [Stacks, Tag 0B53] *is* that
abstract morphism by `projectionFormulaMap_eq`, so it applies verbatim here.  Its three inputs:

* the comparison of [Stacks, Tag 079U] is invertible at every pair — it is the forward map of the
  isomorphism of bifunctors `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`,
  unconditionally;
* `- ⊗^𝐋_{𝒪_Y} 𝒪_Y[0]⟦m⟧` is an equivalence of `D(𝒪_Y)`, because it is isomorphic to the shift
  by `m`.  This is where the shift enters, and the datum it needs is the compatibility of the
  derived tensor product with the shifts in both variables,
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`, which is a statement
  about the *bifunctor* and is proved.  It is the transformation-level `CommShift₂` of the Tag
  079U comparison that is missing, and no such datum is used here;
* `- ⊗^𝐋_{𝒪_X} Lf^*(𝒪_Y[0]⟦m⟧)` is an equivalence of `D(𝒪_X)`, because `Lf^*(𝒪_Y[0]⟦m⟧)` is
  `𝒪_X[0]⟦m⟧`: the derived pullback commutes with the shift
  (`Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift`, it is the left adjoint of
  the derived adjunction and exact) and carries the structure sheaf to the structure sheaf
  (`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`).

The abstract statement over variables is in
`StacksFrontier/CategoryTheory/Shift/TensorRightOfShiftedUnit.lean`; stating it there rather than
inline is not cosmetic.  A goal about the derived tensor product of a ringed space mixes the two
spellings `Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf` and
`structureSheafRing Z` of its sheaf of rings and is therefore not type-correct
at `implicit` transparency, so every `rewrite` on it is rejected outright; applying a lemma whose
categories, functors and objects are all variables runs the conversion at default transparency
instead.

## What is still not proved

The dévissage of [Stacks, Tag 08EU] itself — the reduction of a general `K` in `D_QCoh(𝒪_Y)` to
the shifts of the structure sheaf, by working locally on `Y`, by direct sums and distinguished
triangles, and through the equivalence `D(A) ≌ D_QCoh(𝒪_Y)` over an affine base — is not carried
out, so invertibility at a general `K` in `D_QCoh(𝒪_Y)` is not proved.  What is proved is the
base case of that dévissage, in the generality the base case admits: an arbitrary morphism of
ringed spaces, an arbitrary `E`, no quasi-compactness, no quasi-separatedness and no
quasi-coherence.

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

/-! ### The derived form of the abstract projection formula -/

section General

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The projection-formula morphism of [Stacks, Tag 0B53] is invertible at a `K` by which
tensoring is an equivalence.**  For an arbitrary morphism of ringed spaces `f : X ⟶ Y` and an
arbitrary `E ∈ D(𝒪_X)`,

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism as soon as `- ⊗^𝐋_{𝒪_Y} K` is an equivalence of `D(𝒪_Y)` and
`- ⊗^𝐋_{𝒪_X} Lf^*K` is an equivalence of `D(𝒪_X)`.

This is `Stacks.ProjectionFormula.isIso_adjunctionTensorMap` at the derived adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 079W], the two derived tensor products of [Stacks, Tag 06YU] and
the comparison of [Stacks, Tag 079U]; the third input of that theorem, invertibility of the
comparison, is unconditional here.  It is the derived analogue of
`Stacks.ProjectionFormula.isIso_projectionFormulaMap`, which is [Stacks, Tag 0FZE] for an
invertible module. -/
theorem isIso_projectionFormulaMap_of_isEquivalence
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hY : (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)) K).IsEquivalence)
    (hX : (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      ((derivedPullback f).obj K)).IsEquivalence) :
    IsIso (projectionFormulaMap f E K) :=
  @Stacks.ProjectionFormula.isIso_adjunctionTensorMap _ _ _ _ _ _ (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (pullbackTensorComparison f) E K hY hX
    (fun M => ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso f).app
      (M, K)).isIso_hom)

end General

/-! ### Tensoring by a shift of the structure sheaf -/

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived tensor product of a ringed space commutes with the shifts in both variables.**
This is `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int` ([Stacks, Tag
06YU]) at the structure sheaf of the space, seated by hand because that datum is a `def`, not an
instance. -/
@[instance_reducible]
def derivedTensorCommShift₂ : (derivedTensorProductFunctor Z.sheaf).CommShift₂Int :=
  Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int Z.sheaf

/-- **Tensoring on the right by a shift of the structure sheaf is an equivalence of `D(𝒪_Z)`.**
It is isomorphic to the shift by `m`: the right unit constraint of [Stacks, Tag 0FPT] identifies
`M ⊗^𝐋 𝒪_Z[0]` with `M`, and the commutation of `M ⊗^𝐋 -` with the shift moves the shift out,
naturally in `M` because the datum of [Stacks, Tag 06YU] is a `CommShift₂` of the bifunctor and
not two unrelated one-variable structures. -/
theorem isEquivalence_tensorRight_unitShift (m : ℤ) :
    (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf))
      ((singleUnit Z)⟦m⟧)).IsEquivalence :=
  have := derivedTensorCommShift₂ Z
  Functor.isEquivalence_tensorRightOf_shiftedUnit (derivedTensorProductFunctor Z.sheaf)
    (singleUnit Z) (Stacks.RingedSpace.derivedTensorRightUnitorNatIso Z) m

end OneSpace

/-! ### The base case at every shift -/

section Main

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived pullback of a shift of the structure sheaf**: `Lf^*(𝒪_Y[0]⟦m⟧) ≅ 𝒪_X[0]⟦m⟧`,
for an arbitrary morphism of ringed spaces.  The derived pullback commutes with the shift, being
the left adjoint of the derived adjunction of [Stacks, Tag 079W], and carries `𝒪_Y[0]` to
`𝒪_X[0]` by `Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`. -/
def pullbackUnitShiftIso (m : ℤ) :
    (derivedPullback f).obj ((singleUnit Y)⟦m⟧) ≅ (singleUnit X)⟦m⟧ :=
  ((derivedPullback f).commShiftIso m).app (singleUnit Y) ≪≫
    (shiftFunctor _ m).mapIso (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f)

/-- **[Stacks, Tag 08EU] at `K = 𝒪_Y[0]⟦m⟧`, for every integer `m`.**
For an arbitrary morphism of ringed spaces `f : X ⟶ Y` and an arbitrary `E ∈ D(𝒪_X)`, the derived
projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} 𝒪_Y[0]⟦m⟧ ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*(𝒪_Y[0]⟦m⟧))`

is an isomorphism.

This is the case the source's proof calls clear — "the statement of the lemma is clear for shifts
of the structure sheaf" — and it is the whole base case of the source's dévissage in `K`.  At
`m = 0` it is the case `K = 𝒪_Y[0]` of [Stacks, Tag 08EU] up to the isomorphism `Z⟦0⟧ ≅ Z`.

The morphism `f` is an arbitrary morphism of ringed spaces and `E` is arbitrary. -/
@[stacks 08EU "the case K = 𝒪_Y[0]⟦m⟧, every shift of the structure sheaf: for an arbitrary \
morphism of ringed spaces and an arbitrary E in D(𝒪_X), \
Rf_*E ⊗ᴸ 𝒪_Y[0]⟦m⟧ ⟶ Rf_*(E ⊗ᴸ Lf^*(𝒪_Y[0]⟦m⟧)) is invertible for every integer m"]
theorem isIso_projectionFormulaMap_unitShift_unconditional
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (m : ℤ) :
    IsIso (projectionFormulaMap f E ((singleUnit Y)⟦m⟧)) :=
  isIso_projectionFormulaMap_of_isEquivalence f E _
    (isEquivalence_tensorRight_unitShift Y m)
    (Functor.isEquivalence_tensorRightOf_of_iso (derivedTensorProductFunctor X.sheaf)
      (pullbackUnitShiftIso f m) (isEquivalence_tensorRight_unitShift X m))

/-- **[Stacks, Tag 08EU] at the structure sheaf placed in an arbitrary degree**, `K = 𝒪_Y[i]`,
with no hypothesis.  This is `isIso_projectionFormulaMap_unitShift_unconditional` at `m = -i`
together with `Stacks.Cohomology.ProjectionFormulaPerfect.singleUnitDegreeIso`, the identification
`𝒪_Y[0]⟦-i⟧ ≅ 𝒪_Y[i]` carried by the `CategoryTheory.SingleFunctors` structure of
`DerivedCategory.singleFunctors`. -/
theorem isIso_projectionFormulaMap_singleUnit_degree
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ) :
    IsIso (projectionFormulaMap f E
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) i).obj
        (SheafOfModules.unit (structureSheafRing Y)))) :=
  isIso_projectionFormulaMap_of_iso_right f E
    (((DerivedCategory.singleFunctors (SheafOfModules.{u} (structureSheafRing Y))).shiftIso
      (-i) i 0 (by omega)).app (SheafOfModules.unit (structureSheafRing Y)))
    (isIso_projectionFormulaMap_unitShift_unconditional f E (-i))

end Main

end Stacks.Cohomology.DerivedProjectionFormula

end
