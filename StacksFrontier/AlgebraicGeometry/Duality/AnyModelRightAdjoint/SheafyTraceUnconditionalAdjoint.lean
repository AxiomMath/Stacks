module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.AnyModelRightAdjoint.QcqsRightAdjointAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom

/-!
# The sheafy trace map with the right adjoint no longer granted

The sheafy trace map of [Stacks, Tag 0B6H] and the isomorphism of global derived Homs it induces,
[Stacks, Tag 0B6I], are stated in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTrace.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceGlobalHom.lean` at
`CategoryTheory.HasDerivedCategory.standard`, with a right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and its adjunction as hypotheses — their existence being
[Stacks, Tag 0A9E], which was not available at that model.

`Stacks.Duality.AnyModel.isLeftAdjoint_restrictedDerivedPushforward` now supplies it, at every
chosen model. This file discharges those two hypotheses for a morphism between quasi-compact and
quasi-separated schemes, at the standard model, so that the trace map is a canonical construction
there and not one depending on a supplied adjoint.

## Main definitions

* `Stacks.Duality.AnyModel.standardTwistedInverseImage` and
  `Stacks.Duality.AnyModel.standardTwistedInverseImageAdjunction` — `f^×` and the adjunction
  `Rf_* ⊣ f^×` at the standard model, in exactly the shape the trace map asks for.
* `Stacks.Duality.AnyModel.canonicalSheafyTrace` — the trace map of [Stacks, Tag 0B6H] with the
  adjoint discharged.

## Main results

* `Stacks.Duality.AnyModel.bijective_comp_canonicalSheafyTrace` — [Stacks, Tag 0B6I] with the
  adjoint discharged: what is still carried is the projection formula of [Stacks, Tag 08EU] and
  part (1) of [Stacks, Tag 08DX], the two inputs of [Stacks, Tag 0A9Q] at every object; the
  instances of them the tag needs are proved in
  `StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceGlobalHomQcqs.lean`, where
  `Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs` states the tag with neither
  carried.

## Implementation notes

**No `@[stacks]` attribute is placed.** [Stacks, Tag 0B6H] is registered on the trace map this
file specialises, and [Stacks, Tag 0B6I] on
`Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs`, which holds for every right
adjoint and so in particular for the one fixed here.

**The `hpush` hypothesis of the trace map is taken from
`Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward`**, which is part (1) of
[Stacks, Tag 08D5] at the standard model and is stated in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/StandardModel.lean`.

**`HasDerivedCategory.standard` is installed at raised priority.** The import closure carries the
locally small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as a global instance, and at
equal priority instance search prefers it, which would elaborate the statements below at a model
different from the one [Stacks, Tag 0B6I] is stated at.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0B6I](https://stacks.math.columbia.edu/tag/0B6I)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality.AnyModel

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **The twisted inverse image `f^×` at the standard model**, for a morphism between
quasi-compact and quasi-separated schemes: the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` whose existence is [Stacks, Tag 0A9E]. -/
abbrev standardTwistedInverseImage :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  letI := isLeftAdjoint_restrictedDerivedPushforward f
    (HasDerivedCategory.standard X.Modules) (HasDerivedCategory.standard Y.Modules)
  (quasiCoherentDerivedPushforward f
    (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)).rightAdjoint

/-- **The adjunction `Rf_* ⊣ f^×` at the standard model**, in the shape the sheafy trace map of
[Stacks, Tag 0B6H] takes as a hypothesis. -/
def standardTwistedInverseImageAdjunction :
    quasiCoherentDerivedPushforward f
        (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f) ⊣
      standardTwistedInverseImage f :=
  letI := isLeftAdjoint_restrictedDerivedPushforward f
    (HasDerivedCategory.standard X.Modules) (HasDerivedCategory.standard Y.Modules)
  Adjunction.ofIsLeftAdjoint _

variable
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))

/-- **The sheafy trace map of [Stacks, Tag 0B6H] with the right adjoint discharged.** For a
morphism `f : X ⟶ Y` between quasi-compact and quasi-separated schemes this is the canonical map

`Rf_*R𝓗om_{𝒪_X}(L, f^×K) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

the adjoint `f^×` being the one [Stacks, Tag 0A9E] produces rather than a supplied one. -/
abbrev canonicalSheafyTrace (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :=
  sheafyTrace f DX DY (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
    (standardTwistedInverseImageAdjunction f) L K

/-- **[Stacks, Tag 0B6I] with the right adjoint discharged.** For a morphism `f : X ⟶ Y` between
quasi-compact and quasi-separated schemes, the sheafy trace map built from the adjoint of
[Stacks, Tag 0A9E] induces, in every degree `n`, a bijection on the morphism groups out of
`𝒪_Y⟦-n⟧` — that is, on the degree-`n` cohomology of the two global derived Homs.

The hypotheses are those of `Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf`: the
projection formula of [Stacks, Tag 08EU] as `h08EU` and the quasi-coherence of
`Lf^*M ⊗^L_{𝒪_X} L` of [Stacks, Tag 08DX] part (1) as `hten`, at every object. The right adjoint
of [Stacks, Tag 0A9E] is not among them. The form with neither hypothesis is
`Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs`. -/
theorem bijective_comp_canonicalSheafyTrace (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y)
    (hten : ∀ (M : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensorProductFunctor X.sheaf).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).obj M.obj)).obj L.obj)).IsQuasicoherent)
    (h08EU : ∀ M : quasiCoherentDerivedCategory Y,
      IsIso (pullbackProjectionFormulaMap f M.obj L.obj))
    (n : ℤ) :
    Function.Bijective (fun g : (ι _).obj (derivedStructureSheafInDegree Y n) ⟶ _ =>
      g ≫ canonicalSheafyTrace f DX DY L K) :=
  bijective_comp_sheafyTrace_structureSheaf f
    (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward f)
    (standardTwistedInverseImageAdjunction f) DX DY L K hten h08EU n

end Stacks.Duality.AnyModel

end
