module

public import StacksFrontier.AlgebraicGeometry.AmpleLocallyClosed.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reading assertion (B) of Stacks Tag 0D2M as a statement about `g^*(L^{⊗ d})`

Assertion (B) of [Stacks, Tag 0D2M] is stated in this repository for the twist
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule X L F d`, an `abbrev` for
`Stacks.RelativeVeryAmple.tensorModules X F (Stacks.Ample.tensorPowModule X L d)` with `d : ℤ`.
The proof of [Stacks, Tag 0D2N] applies it on the base change `X' = X ×_S Spec 𝒪_{S, y}`, with
`F` the structure sheaf `Stacks.Ample.unitModule X'` and `L' = g^* L` the pullback of an
invertible module along the projection `g : X' ⟶ X`.  Its conclusion then has to be read as a
statement about `g^*(L^{⊗ d})` rather than about `𝒪_{X'} ⊗ (g^*L)^{⊗ d}`.  This file supplies
that reading, as a single isomorphism.

## Main definitions

* `Stacks.AmpleFibreNeighbourhood.twistUnitPullbackIso`: **the degree-`d` twist of the structure
  sheaf by the pullback of an invertible module is the pullback of the degree-`d` power**,
  `𝒪_X ⊗ (g^*M)^{⊗ d} ≅ g^*(M^{⊗ d})`, for every integer `d`.  This is the composite of the two
  facts recalled below, and it is the only new declaration in this file.

## Implementation notes

Three inputs are needed, and **all three already exist in the repository**; this file states
none of them again, and composes two of them.  Each is recorded here with its exact location,
because the shape each one is stated in is what makes the composite a two-line definition.

### The integer tensor power commutes with pullback

`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso`
(`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/HyperplaneTwistSequence.lean`) is
`g^*(M^{⊗ d}) ≅ (g^*M)^{⊗ d}` for an *integer* exponent `d`.  No integer version had to be
built: `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`
(`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean`) is the same isomorphism for
a natural exponent cast to `ℤ`, and the negative degrees are
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleNegSuccIso`, which
identifies both sides as tensor inverses of `(g^*M)^{⊗ (k+1)}` — through [Stacks, Tag 01CD] and
`Stacks.RelativeAmple.pullbackUnitModuleIso` — and appeals to uniqueness of a tensor inverse.
The integer statement splits on `Int.ofNat`/`Int.negSucc` between those two.

It is stated at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling of the pullback, while
`Stacks.AmpleLocallyClosed.pullbackModule` — the spelling Tag 0D2N's base change is written in —
is an `abbrev` for `RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom`.  The two are
definitionally equal, so the isomorphism typechecks at either spelling with no bridge; only
*instance search* fails to cross between them, which is why
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.isInvertibleModule_schemeModulesPullback`
exists alongside `Stacks.InvertiblePullback.isInvertibleModule_pullback`.  Invertibility of
`g^*M` ([Stacks, Tag 0B8L]) is the latter instance and is never written down below.

### The structure sheaf is coherent on a locally Noetherian scheme

`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`
(`StacksFrontier/AlgebraicGeometry/Cohomology/LocallyNoetherian/StructureSheafCoherent.lean`) is
`(Stacks.Ample.unitModule X).IsCoherent` for `X` locally Noetherian, as a **public** theorem:
quasi-coherence plus `SheafOfModules.IsFiniteType` through
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_isQuasicoherent_of_isFiniteType`, which is
(1) ⇔ (2) of [Stacks, Tag 01XZ] (`Stacks.AlgebraicGeometry.CoherentTFAE.`
`isCoherent_iff_isQuasicoherent_and_isFiniteType`), with finite type supplied by
`AlgebraicGeometry.structureSheaf_isFiniteType` — generation by the section `1`.  It applies
verbatim at `Stacks.Ample.unitModule X`, which is an `abbrev` for
`SheafOfModules.unit X.ringCatSheaf`.

A **private** instance `isCoherent_unitModule` at
`StacksFrontier/AlgebraicGeometry/FormalGeometry/ConnectednessApplication.lean` proves the same
thing and is unusable from outside that file; a public restatement here would nevertheless be a
duplicate of `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`, which is already public and
already in the required shape, so none is given.  No global `instance` is registered either: the
repository deliberately discharges this hypothesis by `have`/`haveI` at each use site (see
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersections/Components.lean`,
`StacksFrontier/AlgebraicGeometry/Curves/GlueingSquishing/ElementaryStepBranch.lean`), and turning
it into a global instance would change instance resolution in those files, which this file must
not do.

### Tensoring by the structure sheaf changes nothing

`Stacks.SheafOfModules.tensorSheafUnitLeftIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorUnitSections.lean`) is the left unitor
`𝒪 ⊗_𝒪 A ≅ A` of the tensor product sheaf of [Stacks, Tag 01CA] on a ringed site.  At
`𝒪 = X.presheaf` with the sheaf condition
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X` its type is *literally*
`Stacks.RelativeVeryAmple.tensorModules X (Stacks.Ample.unitModule X) P ≅ P`, both
`tensorModules` and `unitModule` being `abbrev`s for exactly the objects it mentions, so it is
used below with no bridge and is not restated.

`Stacks.AmpleEventualGeneration.unitTensorIsoSelf`
(`StacksFrontier/AlgebraicGeometry/AmpleEventualGeneration/Generation.lean`) states the same
mathematics as `Stacks.Ample.unitModule X ⊗ P ≅ P`, but is **not** usable here: its `⊗` is that
of the local instance `Stacks.SheafInternalHom.schemeMonoidalCategory`, whose tensor product is
*not* `Stacks.RelativeVeryAmple.tensorModules` on the nose — only
`Stacks.PullbackGradedAlgebra.monoidalCategory` has that property, as the module documentation of
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPowerPullbackMul.lean` records:
offering `unitTensorIsoSelf P` for the type below is rejected with
`MonoidalCategoryStruct.tensorObj (unitModule X) P ≅ P` against
`tensorModules X (unitModule X) P ≅ P`.  Hence the unitor of the tensor product *sheaf* is the
one taken, and no monoidal instance is used anywhere in this file — so its statement is
instance-free and no consumer needs a local instance either, exactly as in
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean`.

## The tag

**No `@[stacks]` attribute is attached to anything in this file.** The declaration below states
no assertion of the Stacks project: it is a change of spelling, composing [Stacks, Tag 01CA]'s
left unitor with [Stacks, Tag 01CD] iterated over the integers ([Stacks, Tag 01CU]), both of
which already carry their attributes where they are proved.  Tag 0D2M and Tag 0D2N are
registered on their own statements elsewhere in
`StacksFrontier/AlgebraicGeometry/AmpleFibreNeighbourhood/`; this file is an input to the proof of
Tag 0D2N, not a formalization of a tag.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-- **The degree-`d` twist of the structure sheaf by the pullback of an invertible module is the
pullback of the degree-`d` power of that module**: for `g : X ⟶ Y` a morphism of schemes,
`M` an invertible `𝒪_Y`-module and `d : ℤ`,
`𝒪_X ⊗_{𝒪_X} (g^*M)^{⊗ d} ≅ g^*(M^{⊗ d})`.

This is the form in which assertion (B) of [Stacks, Tag 0D2M] — stated for
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule`, hence for a twist of a *module*
by a power of an invertible module — is read in the proof of [Stacks, Tag 0D2N], where the module
being twisted is the structure sheaf of the base change `X ×_S Spec 𝒪_{S, y}` and the invertible
module is the pullback of the one on `X`.

Two steps, each an existing isomorphism used at its own spelling with no bridge:

* the left unitor `Stacks.SheafOfModules.tensorSheafUnitLeftIso` of the tensor product sheaf of
  [Stacks, Tag 01CA] discards the factor `𝒪_X`, leaving `(g^*M)^{⊗ d}`;
* `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso`, which is
  [Stacks, Tag 01CD] iterated over the integer powers of [Stacks, Tag 01CU], turns that into
  `g^*(M^{⊗ d})` — taken inverted, since it is stated in the other direction.

Invertibility of `g^*M` is [Stacks, Tag 0B8L] in the form of the instance
`Stacks.InvertiblePullback.isInvertibleModule_pullback`, so it does not appear in the binders. -/
@[ega "0 5.4.5" "special case"]
def twistUnitPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules)
    [IsInvertibleModule Y M] (d : ℤ) :
    Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule X
        (Stacks.AmpleLocallyClosed.pullbackModule g M) (unitModule X) d ≅
      Stacks.AmpleLocallyClosed.pullbackModule g (tensorPowModule Y M d) :=
  Stacks.SheafOfModules.tensorSheafUnitLeftIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
      (tensorPowModule X (Stacks.AmpleLocallyClosed.pullbackModule g M) d) ≪≫
    (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso g M d).symm

end Stacks.AmpleFibreNeighbourhood

end
