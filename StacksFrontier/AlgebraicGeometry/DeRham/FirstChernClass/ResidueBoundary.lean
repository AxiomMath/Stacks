module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassToDerivedMorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass
public import StacksCore.Tactic.StacksAttribute

/-!
# The boundary map of the residue sequence is the first Chern class map

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, let
`Ω^• = Ω^•_{𝒪_X/A}` be the relative de Rham complex and let `ℒ` be an invertible `𝒪_X`-module.
The weight-zero part of the de Rham complex of the complement `L^⋆` of the zero section of `ℒ`
sits in a short exact sequence of complexes

`0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0`

(Tag 0FUF), whose connecting morphism in the derived category is a map

`δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]`

in `D(f^{-1}𝒪_S)`. **Tag 0FUG identifies `δ` with the morphism of Tag 0FU7 attached to the class
`ξ = c₁^{dR}(ℒ)`**, that is, with cup product by the de Rham first Chern class of `ℒ`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence`: a short exact sequence of complexes
  of sheaves of `A`-modules of the shape `0 → Ω^• → M → Ω^•[-1] → 0`, which is what Tag 0FUF
  produces for the complement of the zero section of an invertible module.
* `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.connecting`: its connecting morphism
  `Ω^•[-1] ⟶ Ω^•[1]` in `D(f^{-1}𝒪_S)`, read off Mathlib's distinguished triangle
  `DerivedCategory.triangleOfSESδ` of a short exact sequence of cochain complexes.
* `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.boundary`: **the boundary map
  `δ : Ω^• ⟶ Ω^•[2]`**, the connecting morphism translated once so that both its source and its
  target are translates of `Ω^•` itself.

## Main results

* `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.boundary_eq_deRhamClassDerivedMorphism`:
  the final step of the proof of Tag 0FUG for an abstract residue sequence: a boundary map which
  lifts to differential graded modules and takes the value `c₁^{dR}(ℒ)` at the unit is the
  morphism of Tag 0FU7 attached to `c₁^{dR}(ℒ)`.
* `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.boundary_eq_boundary`: consequently such
  a boundary map does not depend on the chosen residue sequence.

Tag 0FUG itself, for the concrete residue sequence of the complement of the zero section of a
line bundle and the concrete de Rham first Chern class, is
`Stacks.LineBundle.Situation.residueShiftedSequence_boundary_eq_deRhamClassMorphism` in
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueBoundaryChernClass`.

## Implementation notes

**The degree conventions.** The shift of a complex is Mathlib's `CategoryTheory.shiftFunctor` on
`CochainComplex _ ℤ`; for the shift by `-1` occurring in Tag 0FUF its differential is `-d`, which
is the sign convention of Stacks Tag 011G and the one under which the residue
`Res (ω' + d log s ∧ ω) = ω` is a morphism of complexes
(`LaurentDeRham.deRhamComplexShift_d_succ` in `StacksFrontier.RingTheory.DeRham.LaurentResidue`).
Mathlib's connecting morphism of a short exact sequence `0 → X₁ → X₂ → X₃ → 0` goes
`Q X₃ ⟶ (Q X₁)[1]`, so for the residue sequence it is a map `Ω^•[-1] ⟶ Ω^•[1]`. The map
`δ : Ω^• ⟶ Ω^•[2]` of Tag 0FUG is obtained from it by applying the translation functor `[1]` and
using the canonical isomorphisms `Ω^• ≅ (Ω^•[-1])[1]` and `(Ω^•[1])[1] ≅ Ω^•[2]`, no further sign
being introduced; this is exactly the passage to "the shifted version of the short exact
sequence" with which the proof of Tag 0FUG begins.

**The abstract form.** The declarations of this file take the residue sequence `S`, the lift
`hlift` of its boundary map to right differential graded modules, its value `hev` at the unit,
and a comparison `realizationComparison` of the two realizations of de Rham cohomology as
arguments, and what they prove is the last step of the proof of Tag 0FUG: the uniqueness in
Tag 0FU7, `AlgebraicGeometry.SheafOfModules.eq_deRhamClassDerivedMorphism`. The library
constructs all of these inputs for a line bundle on a scheme:
`Stacks.LineBundle.Situation.residueBaseSequence` is the residue sequence of Tag 0FUF,
`Stacks.LineBundle.Situation.exists_deRhamForgetHom_eq_residueShiftedSequence_boundary` is the
lift, `Stacks.LineBundle.Situation.deRhamEvalOne_residueBoundary_eq_of_cech` the value at the
unit, and `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology` the
comparison of realizations; they are assembled into Tag 0FUG in
`Stacks.LineBundle.Situation.residueShiftedSequence_boundary_eq_deRhamClassMorphism`.

**Universe pinning.** The category has to be given explicitly in
`DerivedCategory.Q (C := _root_.SheafOfModules.{u} (underlyingRingSheaf A))`: without it the
universe of the argument `deRhamComplexInt B D` is defaulted to `0` before the expected type is
known, and the resulting mismatch is reported against `DeRhamDifferential.{0}`.

## References

* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Tag 011G](https://stacks.math.columbia.edu/tag/011G)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The residue sequence and its boundary map -/

/-- **A residue sequence in the shape of Stacks Tag 0FUF**: a short exact sequence

`0 → Ω^•_{𝒪_X/A} → M → Ω^•_{𝒪_X/A}[-1] → 0`

of complexes of sheaves of `A`-modules. For the complement `L^⋆` of the zero section of an
invertible module `ℒ` the middle term is the weight-zero part `Ω^•_{L^⋆/S,0}` of the de Rham
complex of `L^⋆`, the first map is the pullback of forms and the second is the residue
`ω' + d log s ∧ ω ↦ ω`. That sequence is constructed in
`Stacks.LineBundle.Situation.residueBaseSequence`. -/
structure DeRhamResidueSequence where
  /-- The middle term `Ω^•_{L^⋆/S,0}` of the residue sequence. -/
  middle : CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℤ
  /-- The pullback of relative forms `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}`. -/
  incl : deRhamComplexInt B D ⟶ middle
  /-- The residue `Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}[-1]`, locally `Res (ω' + d log s ∧ ω) = ω`. -/
  res : middle ⟶ (deRhamComplexInt B D)⟦(-1 : ℤ)⟧
  /-- The residue kills the forms pulled back from `X`. -/
  incl_comp_res : incl ≫ res = 0
  /-- The sequence is short exact. -/
  shortExact : (ShortComplex.mk incl res incl_comp_res).ShortExact

namespace DeRhamResidueSequence

variable {B D} (S : DeRhamResidueSequence B D)

/-- The residue sequence read as a short complex of complexes of sheaves of `A`-modules. -/
abbrev shortComplex :
    ShortComplex (CochainComplex (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) ℤ) :=
  ShortComplex.mk S.incl S.res S.incl_comp_res

/-- Mathlib's connecting morphism `DerivedCategory.triangleOfSESδ` of the residue sequence: a
morphism `Q(Ω^•_{X/S}[-1]) ⟶ Q(Ω^•_{X/S})[1]` in `D(f^{-1}𝒪_S)`. -/
def connectingOnShift := DerivedCategory.triangleOfSESδ S.shortExact

/-- The connecting morphism `Ω^•_{X/S}[-1] ⟶ Ω^•_{X/S}[1]` of the residue sequence in
`D(f^{-1}𝒪_S)`: `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.connectingOnShift` with
the localization functor commuted past the translation by `-1` on its source. -/
def connecting :
    (deRhamDerivedObject B D)⟦(-1 : ℤ)⟧ ⟶ (deRhamDerivedObject B D)⟦(1 : ℤ)⟧ :=
  ((DerivedCategory.Q (C := _root_.SheafOfModules.{u} (underlyingRingSheaf A))).commShiftIso
    (-1 : ℤ)).inv.app (deRhamComplexInt B D) ≫ S.connectingOnShift

/-- **The boundary map `δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]`** of the residue sequence of Stacks Tag
0FUF, in `D(f^{-1}𝒪_S)`: the connecting morphism
`AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.connecting` translated once, using the
canonical isomorphisms `Ω^• ≅ (Ω^•[-1])[1]` and `(Ω^•[1])[1] ≅ Ω^•[2]`. Translating the sequence
before taking the connecting morphism is how the proof of Tag 0FUG begins, and no sign is
introduced. -/
def boundary : deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦(2 : ℤ)⟧ :=
  ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).app (deRhamDerivedObject B D)).inv ≫
    (shiftFunctor _ (1 : ℤ)).map S.connecting ≫
      ((shiftFunctorAdd' _ (1 : ℤ) 1 2 (by omega)).app (deRhamDerivedObject B D)).inv

/-! ### The identification with cup product by the first Chern class -/

section Chern

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- **The final step of the proof of Stacks Tag 0FUG, for an abstract residue sequence.** If the
boundary map `δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` of a residue sequence `S` lifts to the derived
category of right differential graded `Ω^•_{X/S}`-modules (`hlift`) and its value at the unit is
the image of the de Rham first Chern class `c₁^{dR}(ℒ)` under a map `realizationComparison` of
realizations (`hev`), then `δ` is the morphism of Tag 0FU7 attached to that class. This is the
uniqueness in Tag 0FU7, `AlgebraicGeometry.SheafOfModules.eq_deRhamClassDerivedMorphism`.

Tag 0FUG itself, where the sequence, the lift and the value at the unit are constructed for the
complement of the zero section of a line bundle, is
`Stacks.LineBundle.Situation.residueShiftedSequence_boundary_eq_deRhamClassMorphism`. -/
theorem boundary_eq_deRhamClassDerivedMorphism (c : DeRhamDerivedModuleCorrespondence B D)
    (realizationComparison : deRhamCohomologyAbelian B D 2 →+ deRhamCohomology B D 2)
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hlift : ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D 2,
      c.forget 2 g = S.boundary)
    (hev : c.evalOne 2 S.boundary =
      realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) :
    S.boundary = deRhamClassDerivedMorphism B D c 2
      (realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) :=
  eq_deRhamClassDerivedMorphism B D c 2 _ hlift hev

/-- Two residue sequences whose boundary maps both lift to the derived category of right
differential graded `Ω^•_{X/S}`-modules and both take the value `c₁^{dR}(ℒ)` at the unit have the
same boundary map, both being the morphism of Tag 0FU7 attached to `c₁^{dR}(ℒ)`, by
`AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.boundary_eq_deRhamClassDerivedMorphism`. -/
theorem boundary_eq_boundary (S' : DeRhamResidueSequence B D)
    (c : DeRhamDerivedModuleCorrespondence B D)
    (realizationComparison : deRhamCohomologyAbelian B D 2 →+ deRhamCohomology B D 2)
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hlift : ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D 2,
      c.forget 2 g = S.boundary)
    (hev : c.evalOne 2 S.boundary =
      realizationComparison (deRhamFirstChernClassAbelianOf B D L hL))
    (hlift' : ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D 2,
      c.forget 2 g = S'.boundary)
    (hev' : c.evalOne 2 S'.boundary =
      realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) :
    S.boundary = S'.boundary :=
  (boundary_eq_deRhamClassDerivedMorphism S c realizationComparison L hL hlift hev).trans
    (boundary_eq_deRhamClassDerivedMorphism S' c realizationComparison L hL hlift' hev').symm

end Chern

end DeRhamResidueSequence

end AlgebraicGeometry.SheafOfModules

end
