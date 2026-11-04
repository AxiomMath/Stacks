module

public import StacksFrontier.Algebra.Homology.DoubleMapFunctor
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence

/-!
# The two-term structure of the pullback of a naive cotangent complex

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces. The
complex `g^*𝖭𝖫_{X/S}` (`Stacks.SheafOfModules.pulledNaiveCotangentComplex`) is obtained by applying
termwise to `𝖭𝖫_{X/S}` first the inverse image of modules along `g` and then extension of scalars
from `g⁻¹𝒪_X` to `𝒪_Y`. Since `𝖭𝖫_{X/S}` is `HomologicalComplex.double` of the conormal map of the
canonical presentation, in degrees `-1` and `0`, the result is again a two-term complex: it is
`HomologicalComplex.double` of the image of that conormal map, in the same two degrees. So
`g^*𝖭𝖫_{X/S}` has the distinguished triangle relating it to its two terms, and therefore a
`AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm` whose underlying object is the
image of `g^*𝖭𝖫_{X/S}` in the derived category of `𝒪_Y`-modules.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.ofIso`: transport of a two-term
  structure along an isomorphism of its underlying object.
* `AlgebraicGeometry.RingedSpaceThickening.inverseImageModulePullback` and
  `AlgebraicGeometry.RingedSpaceThickening.inverseImageExtendScalars`: the two functors whose
  composite is `g^*`, and
  `AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap`, the image under that composite of
  the conormal map of the canonical presentation of `𝒪_X` over `f⁻¹𝒪_S`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTwoTerm`: the two-term structure
  of `g^*𝖭𝖫_{X/S}`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentIsoDouble`: the identification of
  `g^*𝖭𝖫_{X/S}` with `HomologicalComplex.double (pulledConormalMap g f)`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTwoTerm_obj`: the underlying object
  of the two-term structure is the image of `g^*𝖭𝖫_{X/S}` in the derived category, by `rfl`.

## Implementation notes

The identification is the composite of two instances of
`HomologicalComplex.doubleMapFunctorIso`, one for each of the two functors, and the two-term
structure is then `NaiveCotangentTwoTerm.ofDoubleNegOne` of the image of the conormal map,
transported along it. The transport is what pins the underlying object: the distinguished
triangle of a two-term structure may have its third object replaced by an isomorphic one, by
`CategoryTheory.Pretriangulated.mk_mem_distTriang_of_iso_obj₃`, and replacing it by
`g^*𝖭𝖫_{X/S}` itself is what makes `pulledNaiveCotangentTwoTerm_obj` hold by `rfl`.

The ambient abelian category is passed to `DerivedCategory.Q` explicitly: the standard derived
category has universe `max u v` of that category, so a `DerivedCategory.Q` elaborated before the
category is known sends instance search off with the universes of the ringed space still unknown.

## References

* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex as a two-term complex.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom)
open Stacks.SheafOfModules (towerExtendScalars inverseImageMiddleRing ringedSpaceStructureMap
  inverseImageBaseRingOnMiddle canonicalConormalSequence pulledNaiveCotangentComplex)

universe v u v' u'

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### Transport of a two-term structure along an isomorphism -/

section Transport

variable {M : Type u} [Category.{v} M] {D : Type u'} [Category.{v'} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] {single : M ⥤ D}

/-- The two-term structure obtained from `P` by replacing its underlying object with an
isomorphic one: the two terms and the differential are unchanged, and the inclusion and the
projection are composed with the isomorphism. -/
def NaiveCotangentTwoTerm.ofIso (P : NaiveCotangentTwoTerm single) {Z : D} (e : Z ≅ P.obj) :
    NaiveCotangentTwoTerm single where
  conormal := P.conormal
  base := P.base
  d := P.d
  obj := Z
  incl := P.incl ≫ e.inv
  proj := e.hom ≫ P.proj
  distinguished := mk_mem_distTriang_of_iso_obj₃ _ P.distinguished e

namespace NaiveCotangentTwoTerm

variable (P : NaiveCotangentTwoTerm single) {Z : D} (e : Z ≅ P.obj)

/-- The conormal term of `P.ofIso e` is that of `P`. -/
@[simp]
theorem ofIso_conormal : (P.ofIso e).conormal = P.conormal := rfl

/-- The degree `0` term of `P.ofIso e` is that of `P`. -/
@[simp]
theorem ofIso_base : (P.ofIso e).base = P.base := rfl

/-- The differential of `P.ofIso e` is that of `P`. -/
@[simp]
theorem ofIso_d : (P.ofIso e).d = P.d := rfl

/-- The underlying object of `P.ofIso e` is the object `Z`. -/
@[simp]
theorem ofIso_obj : (P.ofIso e).obj = Z := rfl

end NaiveCotangentTwoTerm

end Transport

/-! ### The two-term structure of `g^*𝖭𝖫_{X/S}` -/

variable {X S Y : RingedSpace.{u, u}}

/-- Pullback of modules along `g`, from `𝒪_X`-modules to `g⁻¹𝒪_X`-modules: the first of the two
functors whose composite is `g^*`. -/
abbrev inverseImageModulePullback (g : Y ⟶ X) :=
  _root_.SheafOfModules.pullback.{u} (inverseImageRingHom g.hom.base X.sheaf)

/-- Extension of scalars from `g⁻¹𝒪_X` to `𝒪_Y`: the second of the two functors whose composite
is `g^*`. -/
abbrev inverseImageExtendScalars (g : Y ⟶ X) :=
  towerExtendScalars.{u, u, u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageMiddleRing g) Y.sheaf (ringedSpaceStructureMap g)

/-- `g^*(𝒥/𝒥²) ⟶ g^*Ω`, the image under `g^*` of the conormal map of the canonical presentation
of `𝒪_X` over `f⁻¹𝒪_S`: the differential of `g^*𝖭𝖫_{X/S}`. -/
abbrev pulledConormalMap (g : Y ⟶ X) (f : X ⟶ S) :=
  (inverseImageExtendScalars g).map ((inverseImageModulePullback g).map
    (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRingOnMiddle f) X.sheaf (ringedSpaceStructureMap f)).f)

/-- **`g^*𝖭𝖫_{X/S}` is a two-term complex.** It is `HomologicalComplex.double` of the image
under `g^*` of the conormal map of the canonical presentation of `𝒪_X` over `f⁻¹𝒪_S`, in degrees
`-1` and `0`: the naive cotangent complex is such a `double`, and each of the two functors whose
composite is `g^*` commutes with the construction. -/
def pulledNaiveCotangentIsoDouble (g : Y ⟶ X) (f : X ⟶ S) :
    (HomologicalComplex.double (pulledConormalMap g f)
        ComplexShape.upIntRelNegOneZero :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)) ℤ) ≅
      pulledNaiveCotangentComplex.{u} g f :=
  haveI : (inverseImageExtendScalars g).Additive :=
    Stacks.SheafOfModules.towerExtendScalars_additive.{u, u, u}
      (Opens.grothendieckTopology Y.carrier) (inverseImageMiddleRing g) Y.sheaf
      (ringedSpaceStructureMap g)
  HomologicalComplex.doubleMapFunctorIso (inverseImageExtendScalars g) _
      ComplexShape.upIntRelNegOneZero (by decide) ≪≫
    ((inverseImageExtendScalars g).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (HomologicalComplex.doubleMapFunctorIso (inverseImageModulePullback g) _
        ComplexShape.upIntRelNegOneZero (by decide))

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The two-term structure of `g^*𝖭𝖫_{X/S}`.** Its conormal term is `g^*(𝒥/𝒥²)`, its degree
`0` term is `g^*Ω`, its differential is `pulledConormalMap g f`, and its underlying object is
the image of the complex `g^*𝖭𝖫_{X/S}` itself in the derived category of `𝒪_Y`-modules. -/
def pulledNaiveCotangentTwoTerm (g : Y ⟶ X) (f : X ⟶ S) :
    NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)) 0) :=
  (NaiveCotangentTwoTerm.ofDoubleNegOne (pulledConormalMap g f)).ofIso
    ((DerivedCategory.Q (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology Y.carrier) Y.sheaf))).mapIso
        (pulledNaiveCotangentIsoDouble g f)).symm

variable (g : Y ⟶ X) (f : X ⟶ S)

/-- The underlying object of the two-term structure of `g^*𝖭𝖫_{X/S}` is the image of the complex
`g^*𝖭𝖫_{X/S}` in the derived category of `𝒪_Y`-modules. -/
@[simp]
theorem pulledNaiveCotangentTwoTerm_obj :
    (pulledNaiveCotangentTwoTerm g f).obj =
      (DerivedCategory.Q (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology Y.carrier) Y.sheaf))).obj
          (pulledNaiveCotangentComplex.{u} g f) :=
  rfl

/-- The conormal term of the two-term structure of `g^*𝖭𝖫_{X/S}` is the source of
`pulledConormalMap g f`. -/
@[simp]
theorem pulledNaiveCotangentTwoTerm_conormal :
    (pulledNaiveCotangentTwoTerm g f).conormal =
      (inverseImageExtendScalars g).obj ((inverseImageModulePullback g).obj
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRingOnMiddle f) X.sheaf (ringedSpaceStructureMap f)).X₁) :=
  rfl

/-- The degree `0` term of the two-term structure of `g^*𝖭𝖫_{X/S}` is the target of
`pulledConormalMap g f`. -/
@[simp]
theorem pulledNaiveCotangentTwoTerm_base :
    (pulledNaiveCotangentTwoTerm g f).base =
      (inverseImageExtendScalars g).obj ((inverseImageModulePullback g).obj
        (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRingOnMiddle f) X.sheaf (ringedSpaceStructureMap f)).X₂) :=
  rfl

/-- The differential of the two-term structure of `g^*𝖭𝖫_{X/S}` is `pulledConormalMap g f`. -/
@[simp]
theorem pulledNaiveCotangentTwoTerm_d :
    (pulledNaiveCotangentTwoTerm g f).d = pulledConormalMap g f :=
  rfl

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
