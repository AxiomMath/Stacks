module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedTensor.TorFlatness
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative

/-!
# A non-degenerate witness for Tag 08BQ

`Stacks.Cohomology.flat_iff_forall_isZero_tor`
(`StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean`) is
[Stacks, Tag 08BQ]: an `𝒪_X`-module `ℱ` on a ringed space is flat exactly when the sheaf
`Tor_1^{𝒪_X}(ℱ, 𝒢)` of Tag 08BP vanishes for every `𝒪_X`-module `𝒢`. This file exhibits a
module at which that equivalence has content, so that the tag's statement is not satisfied
only by degenerate data.

## Main results

* `OXModule.flat_iff_isFlat`: on **any** ringed space, `OXModule.Flat` — the preservation of
  monomorphisms that Tag 08BQ's clause (1) is stated with — is equivalent to exactness of the
  tensor endofunctor, which is Tag 05ND verbatim
  (`AlgebraicGeometry.SheafOfModules.IsFlat`). So clause (1) says what the source says.
  `OXModule.flat_of_isFlat` is the direction used below.
* `OXModule.flat_structureSheafModule`: the structure sheaf, as a module over itself, is a
  flat `𝒪_X`-module. It is the unit of the tensor product, not the zero object, so it is a
  non-degenerate instance of clause (1).
* `Stacks.Cohomology.isZero_tor_one_structureSheafModule`: therefore
  `Tor_1^{𝒪_X}(𝒪_X, 𝒢) = 0` for every `𝒢` — clause (2) read off clause (1) through the tag.
* `Stacks.Cohomology.isZero_tor_one_structureSheafModule_standard`: the same with **no
  typeclass binder at all**, the `HasDerivedCategory` hypothesis of the tag being discharged
  by `CategoryTheory.HasDerivedCategory.standard`, which exists for every abelian category.
  This is what shows the tag's instance binder is satisfiable rather than merely consistent.

## Implementation notes

`OXModule.flat_of_isFlat` generalises the private `oxModuleFlat_of_isFlat`
(`StacksFrontier/AlgebraicGeometry/Flatness/BlowingUp/FlatnessIdeal.lean:269`) from a scheme to an
arbitrary ringed space; that file's single use of its own copy could be read off this one.

## References

* [Stacks Project, Lemma 20.26.16 (Tag 08BQ)](https://stacks.math.columbia.edu/tag/08BQ)
* [Stacks Project, Definition 20.26.15 (Tag 08BP)](https://stacks.math.columbia.edu/tag/08BP)
* [Stacks Project, Definition 17.17.1 (Tag 05ND)](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open StrictlyPerfect
open Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative

universe u d

namespace OXModule

/-- **`OXModule.Flat` is the flatness of Tag 05ND.** Clause (1) of Tag 08BQ is stated with
`OXModule.Flat ℱ`, the preservation of monomorphisms by `- ⊗_{𝒪_X} ℱ`; the source's definition
is the *exactness* of that endofunctor, which is
`AlgebraicGeometry.SheafOfModules.IsFlat`. The endofunctor is right exact, so the two agree —
this is `AlgebraicGeometry.SheafOfModules.sheafTensorRight_exact_iff_preservesMonomorphisms`,
read at a ringed space. -/
theorem flat_iff_isFlat {X : RingedSpace.{u, u}} (F : OXMod.{u, u} X) :
    OXModule.Flat F ↔ AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F := by
  show (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
      F)).PreservesMonomorphisms ↔ _
  exact
    (AlgebraicGeometry.SheafOfModules.sheafTensorRight_exact_iff_preservesMonomorphisms
      X.sheaf F).symm

/-- Exactness of the tensor endofunctor `- ⊗_{𝒪_X} ℱ` — the flatness of Tag 05ND, as
`AlgebraicGeometry.SheafOfModules.IsFlat` states it — implies `OXModule.Flat ℱ`, the
preservation of monomorphisms by that endofunctor. True on any ringed space. -/
theorem flat_of_isFlat {X : RingedSpace.{u, u}} (F : OXMod.{u, u} X)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F) :
    OXModule.Flat F :=
  (flat_iff_isFlat F).2 hF

/-- **The structure sheaf is a flat `𝒪_X`-module.** Tensoring with it is the identity
functor, which is exact. -/
theorem flat_structureSheafModule (X : RingedSpace.{u, u}) :
    OXModule.Flat (structureSheafModule X) :=
  flat_of_isFlat _ (isFlat_structureSheafModule X)

end OXModule

namespace Stacks.Cohomology

attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **`Tor_1^{𝒪_X}(𝒪_X, 𝒢) = 0` for every `𝒪_X`-module `𝒢`.** Clause (2) of Tag 08BQ at the
structure sheaf, obtained from clause (1) — the flatness of the structure sheaf — through
`Stacks.Cohomology.flat_iff_forall_isZero_tor`. -/
theorem isZero_tor_one_structureSheafModule (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (G : OXMod.{u, u} X) :
    IsZero (tor X 1 (structureSheafModule X) G) :=
  (flat_iff_forall_isZero_tor X (structureSheafModule X)).1
    (OXModule.flat_structureSheafModule X) G

attribute [local instance 10000] HasDerivedCategory.standard

/-- The previous statement with **no hypotheses whatsoever**: the derived-category model is the
standard one of `CategoryTheory.HasDerivedCategory.standard`, which exists for every abelian
category, so Tag 08BQ's typeclass binder is satisfiable and the tag is not vacuous. -/
theorem isZero_tor_one_structureSheafModule_standard (X : RingedSpace.{u, u})
    (G : OXMod.{u, u} X) :
    IsZero (tor X 1 (structureSheafModule X) G) :=
  isZero_tor_one_structureSheafModule X G

end Stacks.Cohomology

end
