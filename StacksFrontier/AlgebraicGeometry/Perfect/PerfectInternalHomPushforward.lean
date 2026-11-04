module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Producing perfect complexes: the derived direct image of a derived internal Hom

Let `S` be a Noetherian scheme and `f : X ⟶ S` a morphism locally of finite type.  Let `E` be a
perfect object of `D(𝒪_X)` and let `𝒢` be a bounded complex of coherent `𝒪_X`-modules, flat over
`S`, whose support is proper over `S`.  Then `Rf_*RSheafHom(E, 𝒢)` is a perfect object of
`D(𝒪_S)`.  That statement, [Stacks, Tag 0DJR], is
`isPerfect_derivedPushforward_derivedSheafHom_of_flatProperSupport` in the same namespace, in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectInternalHomPushforwardUnconditional.lean`; this
file supplies the objects it is phrased with.

## Main definitions

* `Stacks.Cohomology.PerfectInternalHomPushforward.derivedSheafHomObj` is
  `RSheafHom_{𝒪_X}(E, 𝒢)`, the derived internal Hom of [Stacks, Tag 08DI] out of `E` into the
  class of `𝒢`, read at the `StrictlyPerfect.OXMod` spelling of `𝒪_X`-modules that
  [Stacks, Tag 0DJQ] is stated at.
* `Stacks.Cohomology.PerfectInternalHomPushforward.DualTensorData` is the conclusion of
  [Stacks, Tag 08DQ] for one pair `(E, 𝒢)`: a perfect object `E^∨` of `D(𝒪_X)` together with an
  isomorphism `E^∨ ⊗^L_{𝒪_X} 𝒢 ≅ RSheafHom(E, 𝒢)`.

## Implementation notes

**The source's proof is a reduction to [Stacks, Tag 0DJQ].**  It chooses a dual perfect complex
`E^∨` by [Stacks, Tag 08DQ], rewrites `RSheafHom(E, 𝒢) = E^∨ ⊗^L_{𝒪_X} 𝒢` by that same tag, and
quotes [Stacks, Tag 0DJQ] for the pushforward of the derived tensor product.  So all of the
coherence, support and boundedness work on `RSheafHom(E, 𝒢)` happens inside
[Stacks, Tag 0DJQ], which is proved in
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectPushforward.lean` as
`Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor`.

**What is carried, and why.**  [Stacks, Tag 08DQ] has two assertions, and the repository has
neither at the spelling [Stacks, Tag 0DJQ] is stated at.

* Its first assertion, that the dual of a perfect object is perfect, is proved — as
  `Stacks.SheafOfModules.isPerfect_derivedDual` on a ringed space and as
  `AlgebraicGeometry.RingedSite.isPerfect_derivedDual` on a ringed site — but at
  `AlgebraicGeometry.RingedSite.IsPerfect` with modules in `SheafOfModules.{0}`, whereas
  [Stacks, Tag 0DJQ] is stated at `AlgebraicGeometry.RingedSpace.IsPerfect` with modules in
  `StrictlyPerfect.OXMod.{u, u}`.  No comparison of those two perfectness predicates exists in
  either tree, and the module universe of the proved statement is pinned at `0`, so it does not
  apply to `Scheme.{u}`.
* Its second assertion, that the canonical map `𝒢 ⊗^L_{𝒪_X} E^∨ ⟶ RSheafHom(E, 𝒢)` of
  [Stacks, Tag 08I1] is invertible for perfect `E`, is not proved anywhere: the map itself is
  `Stacks.SheafOfModules.derivedTensorDualToSheafHom`, and its invertibility appears in this
  repository only ever as a hypothesis.

Both are therefore bundled into `DualTensorData`.  The isomorphism is asked for abstractly,
against the derived tensor product `T` that [Stacks, Tag 0DJQ] uses, rather than as invertibility
of the canonical map of [Stacks, Tag 08I1]: that is weaker, and it avoids a comparison between
`T` and the derived tensor product `Stacks.SheafOfModules.derivedTensor` that the canonical map is
written with.

**Spellings.**  `Stacks.SheafOfModules.StructureSheafModules X.sheaf` and
`StrictlyPerfect.OXMod.{u, u} X.toRingedSpace` are the same type: both are sheaves of modules over
the presheaf of rings `X.presheaf ⋙ forget₂ CommRingCat RingCat`, so the derived internal Hom of
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedInternalHom.lean` names an object of
the category [Stacks, Tag 0DJQ] speaks about with no bridge.  The three spellings of the structure
sheaf of rings that meet in [Stacks, Tag 0DJQ] are identified here by the same
`attribute [local implicit_reducible]` that file uses.

## References

* [Stacks Project, Tag 0DJR](https://stacks.math.columbia.edu/tag/0DJR)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.PerfectPushforward
open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)

namespace Stacks.Cohomology.PerfectInternalHomPushforward

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `RSheafHom_{𝒪_X}(E, 𝒢)`, the derived internal Hom of [Stacks, Tag 08DI] out of an object `E`
of `D(𝒪_X)` into the class of a complex `𝒢`.

The category of `𝒪_X`-modules of the derived internal Hom cluster,
`Stacks.SheafOfModules.StructureSheafModules X.sheaf`, is the category
`StrictlyPerfect.OXMod.{u, u} X.toRingedSpace` that the perfect-complex development on a ringed
space uses, so this is an object of `D(𝒪_X)` in the sense of [Stacks, Tag 0DJQ]. -/
abbrev derivedSheafHomObj (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ) :
    DerivedCategory (OXMod.{u, u} X.toRingedSpace) :=
  ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G)

/-- **The conclusion of [Stacks, Tag 08DQ] for one pair `(E, 𝒢)`**: a dual of `E`, perfect, whose
derived tensor product with `𝒢` is the derived internal Hom `RSheafHom(E, 𝒢)`.

The source's proof of [Stacks, Tag 0DJR] uses exactly this, and no more of [Stacks, Tag 08DQ]:
a perfect `E^∨` with `RSheafHom(E, 𝒢) = E^∨ ⊗^L_{𝒪_X} 𝒢`.  The derived tensor product is the one
[Stacks, Tag 0DJQ] is stated at, so that the identification lands where that tag can consume it;
the isomorphism is not required to be the canonical map of [Stacks, Tag 08I1], which is what makes
this weaker than the tag it stands for.

Neither field is available in this repository at this spelling; the implementation notes of this
file say which statement each one is and where the proved version falls short. -/
structure DualTensorData
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      X.toRingedSpace.sheaf).obj M).Additive]
    [∀ K L : CochainComplex
        (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.toRingedSpace.sheaf)
        (ComplexShape.up ℤ)]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ) where
  /-- The dual `E^∨` of `E`. -/
  dual : DerivedCategory (OXMod.{u, u} X.toRingedSpace)
  /-- `E^∨` is perfect: the first assertion of [Stacks, Tag 08DQ]. -/
  isPerfect : RingedSpace.IsPerfect (X := X.toRingedSpace) dual
  /-- `E^∨ ⊗^L_{𝒪_X} 𝒢 ≅ RSheafHom(E, 𝒢)`: the second assertion of [Stacks, Tag 08DQ]. -/
  iso : (T.tensor.obj dual).obj (DerivedCategory.Q.obj G) ≅ derivedSheafHomObj E G

end Stacks.Cohomology.PerfectInternalHomPushforward

end
