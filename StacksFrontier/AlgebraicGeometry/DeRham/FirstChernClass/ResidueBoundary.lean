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
  **Stacks Tag 0FUG.** The boundary map of the residue sequence is the morphism of Tag 0FU7
  attached to `c₁^{dR}(ℒ)`.
* `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence.boundary_eq_boundary`: consequently the
  boundary map does not depend on the chosen residue sequence.

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

**The hypotheses carried.** Four inputs of the proof of Tag 0FUG are not available in the library
and are carried as explicit, named hypotheses.

* `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence` itself is Tag 0FUF in its global form.
  What the library proves is the affine local computation,
  `LaurentDeRham.shortExact_residueShortComplex`: the residue sequence of a Laurent polynomial
  algebra `A[T;T⁻¹]` over `R`. Globalizing it over the complement of the zero section is not
  done, so the sequence is a hypothesis rather than a construction.
* `hlift`, that the boundary map lifts to the derived category of right differential graded
  `Ω^•`-modules. In Stacks this is the first half of the proof of Tag 0FUG: the inclusion is a
  homomorphism of differential graded algebras, the residue is a morphism of right differential
  graded modules, and the connecting morphism then descends by Differential Graded Sheaves,
  Section 24.32. That descent is the same input as
  `AlgebraicGeometry.SheafOfModules.DeRhamDerivedModuleCorrespondence`, which Tag 0FU7 already
  carries as a parameter, and it is not in the library.
* `hev`, that the value of the boundary map at the unit is `c₁^{dR}(ℒ)`. This is the second half
  of the proof of Tag 0FUG, proved there by mapping the short exact sequence of abelian sheaves
  `0 → 𝒪_X^* → E → ℤ → 0` into the translated residue sequence; neither the sheaf `E` nor the
  comparison of the resulting boundary map with the Čech description of `Pic(X) = H¹(X, 𝒪_X^*)`
  is in the library.
* `realizationComparison`, the comparison of the two realizations of de Rham cohomology that the
  library carries. The de Rham first Chern class
  `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian` of Tag 0FLE is constructed in
  the abelian-sheaf realization `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian`,
  because `d log` is additive but not `𝒪_X`-linear, while the classes of Tag 0FU7 live in the
  sheaf-of-`A`-modules realization `AlgebraicGeometry.SheafOfModules.deRhamCohomology`. The
  comparison of the two is an artifact of having two realizations rather than a result of the
  Stacks project, and it is not in the library.

Given those, the content of this file is the construction of `δ` and the final step of the proof
of Tag 0FUG: the uniqueness in Tag 0FU7,
`AlgebraicGeometry.SheafOfModules.eq_deRhamClassDerivedMorphism`, which says that a morphism
`Ω^• ⟶ Ω^•[2]` with those two properties is *the* morphism attached to `c₁^{dR}(ℒ)`.

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

/-- **The residue sequence of Stacks Tag 0FUF**, as a hypothesis: a short exact sequence

`0 → Ω^•_{𝒪_X/A} → M → Ω^•_{𝒪_X/A}[-1] → 0`

of complexes of sheaves of `A`-modules. For the complement `L^⋆` of the zero section of an
invertible module `ℒ` the middle term is the weight-zero part `Ω^•_{L^⋆/S,0}` of the de Rham
complex of `L^⋆`, the first map is the pullback of forms and the second is the residue
`ω' + d log s ∧ ω ↦ ω`. The library has the affine local computation of that sequence,
`LaurentDeRham.shortExact_residueShortComplex`, but not its globalization, which is why the
sequence enters here as data. -/
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

/-- **Stacks Project, Tag 0FUG.** **The boundary map

`δ : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]`

of the residue sequence of Tag 0FUF is the morphism of Tag 0FU7 attached to the de Rham first
Chern class `c₁^{dR}(ℒ)`**, that is, cup product by `c₁^{dR}(ℒ)`.

Four inputs of the Stacks proof are hypotheses, because the library does not have them; see the
implementation notes of this file.

* `S`, the residue sequence of Tag 0FUF in its global form: only its affine local computation
  `LaurentDeRham.shortExact_residueShortComplex` is in the library.
* `hlift`, that `δ` lifts to the derived category of right differential graded
  `Ω^•_{X/S}`-modules. In Stacks this comes from the residue sequence being one of right
  differential graded modules together with the descent of Differential Graded Sheaves, Section
  24.32, the same input that
  `AlgebraicGeometry.SheafOfModules.DeRhamDerivedModuleCorrespondence` carries for Tag 0FU7.
* `hev`, that `δ(1) = c₁^{dR}(ℒ)`, which Stacks proves by mapping the short exact sequence of
  abelian sheaves `0 → 𝒪_X^* → E → ℤ → 0` into the translated residue sequence.
* `realizationComparison`, which transports the de Rham first Chern class of Tag 0FLE,
  `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelianOf`, from the abelian-sheaf
  realization of de Rham cohomology, in which it is constructed because `d log` is not
  `𝒪_X`-linear, to the sheaf-of-`A`-modules realization, in which the classes of Tag 0FU7 live.

What is proved is the last step of the Stacks proof: by the uniqueness in Tag 0FU7,
`AlgebraicGeometry.SheafOfModules.eq_deRhamClassDerivedMorphism`, a morphism with those two
properties is the morphism attached to `c₁^{dR}(ℒ)`. -/
@[stacks 0FUG "the boundary map of the residue sequence of 0FUF is the map of 0FU7 for the de
Rham first Chern class; the global form of 0FUF, the lift of the boundary map to right
differential graded modules, its value at the unit, and the comparison of the two realizations of
de Rham cohomology are carried as the explicit named hypotheses S, hlift, hev and
realizationComparison"]
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

/-- **Stacks Project, Tag 0FUG.** The boundary map of the residue sequence does not depend on the
choice of the residue sequence: two residue sequences whose boundary maps both lift to the derived
category of right differential graded `Ω^•_{X/S}`-modules and both take the value `c₁^{dR}(ℒ)` at
the unit have the same boundary map, both being cup product by `c₁^{dR}(ℒ)`. -/
@[stacks 0FUG "the boundary map is independent of the chosen residue sequence"]
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
