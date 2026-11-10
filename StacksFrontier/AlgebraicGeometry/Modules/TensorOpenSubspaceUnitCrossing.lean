module

public import StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WhiskerTensorCoherence

/-!
# The tensor crossing of a restriction, on a local section

Let `X` be a ringed space and `U ⊆ X` open. `SheafOfModules.openSubspaceTensorIso` identifies
`(M ⊗ L)|_U` with `M|_U ⊗ L|_U` for `SheafOfModules.openSubspaceRestriction`, and
`StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceRestriction` proves it natural in both
variables. Naturality is what a consumer tensoring a *morphism* with an identity needs; a
consumer which has to know where a *local section* goes — the multiplication
`SheafOfModules.GradedAlgebra.mulSheaf` of a sheaf of graded algebras, which is pinned by its
values on pure tensors (`SheafOfModules.GradedAlgebra.mulSheaf_unit`) — needs instead the value
of the identification on the image of a local section under the sheafification unit. This file
supplies that, and the two further facts about the comparison of the two spellings of restriction
that go with it.

## Main results

* `Stacks.SheafOfModules.TensorPower.whiskerPresheafTensorIso_hom_app_apply`: **the tensorator of
  a restriction of presheaves of modules is the identity on local sections** — not merely on pure
  tensors. Mathlib builds the multiplication constraint of
  `PresheafOfModules.pushforward₀OfCommRingCat` from `Iso.refl` objectwise
  (`Mathlib/Algebra/Category/ModuleCat/Presheaf/PushforwardZeroMonoidal.lean`), so this is `rfl`.
* `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_hom_val_app_whiskerTensorUnit`: **the
  tensorator of a restriction of *sheaves* of modules carries the restricted sheafification unit
  to the sheafification unit of the smaller site**, at a variable site. This is the characterising
  equation `whiskerTensorSheafIso_hom` read on a local section, the tensorator of the presheaves
  having just been found to be the identity there.
* `Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso_hom_val_app_tensorSheafUnit`: the same
  statement at a ringed space, for `Stacks.SheafOfModules.TensorPower.restrictTensorSheafIso` and
  `Stacks.Cohomology.HigherDirectImage.moduleRestriction`.
* `SheafOfModules.openSubspaceRestrictionIsoModuleRestriction_inv_app_val`: **the comparison
  between the two spellings of restriction is the identity *morphism* of presheaves of modules**,
  not merely the identity on each local section. This strengthens
  `SheafOfModules.openSubspaceRestrictionIsoModuleRestriction_inv_app_val_app`, and it is what
  lets a construction *functorial* in the comparison — a tensor product of two copies of it —
  collapse.
* `SheafOfModules.tensorHom_openSubspaceComparison_inv_eq_id`: **the objectwise tensor product
  of two copies of that comparison is the identity**, and
  `SheafOfModules.sheafTensorMap_openSubspaceComparison_inv_eq`: the third leg of
  `SheafOfModules.openSubspaceTensorIso` is the sheafification of that objectwise tensor product,
  so that leg contributes nothing.

## Implementation notes

**Why each statement names only one spelling of the small side.** The three ringed-space results
are stated with the restricted modules spelled by
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, which is the spelling
`restrictTensorSheafIso` is stated at — never mixed with
`SheafOfModules.openSubspaceRestriction` inside a `PresheafOfModules.tensorSheafUnit`. The
mixture is affordable around a *module* and not around the unit of a *tensor product* of two:
```
(tensorSheafUnit ((moduleRestriction X U).obj M)    ((moduleRestriction X U).obj L)).app V z =
(tensorSheafUnit ((openSubspaceRestriction U).obj M) ((openSubspaceRestriction U).obj L)).app V z
```
is `rfl`, and costs **267,731** — past the budget, so it cannot be stated as a lemma, and a
declaration which quotes it inside a larger proof cannot either. (For comparison, the same crossing
around a single module is 21,653, recorded in
`StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceRestriction`.) This is the same
phenomenon that file records for the functor and morphism equalities, one `tensorSheafUnit`
further in.

The consequence for a consumer: the crossing of `openSubspaceTensorIso` on a local section must
*not* be assembled by proving the three legs separately and pasting them, because pasting forces
exactly that bridge. Doing so costs **439,673** and fails. The third leg has to be crossed as
the sheafification of an objectwise tensor product of morphisms
(`sheafTensorMap_openSubspaceComparison_inv_eq`) applied to the unit of a local section, where
the naturality of the sheafification unit moves the spelling, instead of by asking the unifier
for the bridge above. `tensorHom_openSubspaceComparison_inv_eq_id` below is the other half of
that step: it is what identifies the leg with an identity once the spelling has been moved.

**No `@[stacks]` attribute.** Nothing here is a new statement of a tag; these are readings of
[Stacks, Tag 01CA] and [Stacks, Tag 01CU] on a local section, and the tags are carried by the
declarations being read.

## References

* [Stacks Project, Tag 01AD](https://stacks.math.columbia.edu/tag/01AD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.HigherDirectImage (moduleRestriction restrictToOpen)
open Stacks.SheafOfModules.TensorPower (restrictTensorSheafIso whiskerTensorSheafIso
  whiskerPresheafTensorIso whiskerPresheafRestriction whiskerTensorUnit whiskerTensorUnit'
  ringedSpaceIsSheaf)
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)

universe v u v' u' w

namespace Stacks.SheafOfModules.TensorPower

section Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (H : C' ⥤ C) [H.IsContinuous J' J] [H.IsCocontinuous J' J]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The tensorator of a restriction of presheaves of modules is the identity on local
sections.** `Stacks.SheafOfModules.TensorPower.whiskerPresheafRestriction` is
`PresheafOfModules.pushforward₀OfCommRingCat`, whose monoidal structure Mathlib builds with
`μIso _ _ := isoMk (fun _ ↦ Iso.refl _)`: the multiplication constraint is objectwise an identity
isomorphism. Both sides of the equation below are therefore the same section, and this is `rfl`.

Stated on an arbitrary local section rather than on a pure tensor, which is both stronger and
cheaper — a pure tensor would have to be written over one of the two definitionally equal
spellings of the ring of the smaller site, and the `TensorProduct` notation then needs a
`CommSemiring` instance at a spelling instance search does not reach. -/
theorem whiskerPresheafTensorIso_hom_app_apply
    (F G : _root_.SheafOfModules.{w} (structureSheaf O hO)) (V : C'ᵒᵖ)
    (z : ((whiskerPresheafRestriction O H).obj
      (MonoidalCategoryStruct.tensorObj F.val G.val)).obj V) :
    (whiskerPresheafTensorIso O hO H F G).hom.app V z = z :=
  rfl

/-- **The tensorator of a restriction of sheaves of modules carries the restricted sheafification
unit of the objectwise tensor product to the sheafification unit of the smaller site.** This is
the characterising equation `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_hom` read on
a local section: that equation has the comparison of the objectwise tensor products in the way,
and `whiskerPresheafTensorIso_hom_app_apply` has just removed it.

It is the sectionwise counterpart of
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality`, and the form a consumer
pinned by its values on local sections needs — `SheafOfModules.GradedAlgebra.mulSheaf`, whose
`mulSheaf_unit` describes it only on the image of the unit. -/
theorem whiskerTensorSheafIso_hom_val_app_whiskerTensorUnit
    (F G : _root_.SheafOfModules.{w} (structureSheaf O hO)) (V : C'ᵒᵖ)
    (z : ((whiskerPresheafRestriction O H).obj (PresheafOfModules.tensorObj (O := O) F.val
        G.val)).obj V) :
    (whiskerTensorSheafIso (J' := J') O hO H F G).hom.val.app V
        ((whiskerTensorUnit (J' := J') O hO H F G).app V z) =
      (whiskerTensorUnit' (J' := J') O hO H F G).app V z :=
  (congrArg (fun φ => PresheafOfModules.Hom.app φ V z)
      (whiskerTensorSheafIso_hom (J' := J') O hO H F G)).trans
    (congrArg (fun w => (whiskerTensorUnit' (J' := J') O hO H F G).app V w)
      (whiskerPresheafTensorIso_hom_app_apply O hO H F G V z))

end Generic

section RingedSpace

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (M L : _root_.SheafOfModules.{u} (structureSheafRing X))

/-- **`(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` carries the sheafification unit over the image of an open of `U`
to the sheafification unit over that open**, on a ringed space, for restriction along the
open-image functor of `U`. This is
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_hom_val_app_whiskerTensorUnit` at the
open-image functor, the two sheafification units of the general statement being the ringed-space
ones on the nose.

Stated with the restricted modules spelled by
`Stacks.Cohomology.HigherDirectImage.moduleRestriction`, which is the spelling
`restrictTensorSheafIso` itself is stated at; see the implementation notes for why mixing in
`SheafOfModules.openSubspaceRestriction` here is unaffordable. -/
theorem restrictTensorSheafIso_hom_val_app_tensorSheafUnit (V : (Opens ↥U)ᵒᵖ)
    (z : (PresheafOfModules.tensorObj (O := X.presheaf) M.val L.val).obj
      (op (U.isOpenEmbedding.functor.obj V.unop))) :
    (restrictTensorSheafIso X U M L).hom.val.app V
        ((PresheafOfModules.tensorSheafUnit M L).app
          (op (U.isOpenEmbedding.functor.obj V.unop)) z) =
      (PresheafOfModules.tensorSheafUnit ((moduleRestriction X U).obj M)
        ((moduleRestriction X U).obj L)).app V z :=
  whiskerTensorSheafIso_hom_val_app_whiskerTensorUnit X.presheaf (ringedSpaceIsSheaf X)
    U.isOpenEmbedding.functor M L V z

end RingedSpace

end Stacks.SheafOfModules.TensorPower

namespace SheafOfModules

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  (M : SheafOfModules.{u} (structureSheafRing X))

/-- **The comparison between the two spellings of restriction is the identity morphism of
presheaves of modules.** The lemma
`SheafOfModules.openSubspaceRestrictionIsoModuleRestriction_inv_app_val_app`
records that it is the identity on each local section; this says the underlying morphism is the
identity, which is the form a construction *functorial* in the comparison needs — one which
tensors two copies of it cannot be evaluated a section at a time.

The equation typechecks because the two objects are definitionally equal: the statement is that
the comparison is the identity of `((moduleRestriction X U).obj M).val`, read as a morphism to the
definitionally equal `((openSubspaceRestriction U).obj M).val`. -/
theorem openSubspaceRestrictionIsoModuleRestriction_inv_app_val :
    ((openSubspaceRestrictionIsoModuleRestriction U).inv.app M).val =
      CategoryStruct.id _ :=
  rfl

variable (L : SheafOfModules.{u} (structureSheafRing X))

/-- **The objectwise tensor product of two copies of the comparison is the identity.** Each copy
is the identity (`SheafOfModules.openSubspaceRestrictionIsoModuleRestriction_inv_app_val`) and the
tensor product of two identities is the identity (`PresheafOfModules.tensorHom_id`). -/
theorem tensorHom_openSubspaceComparison_inv_eq_id :
    PresheafOfModules.tensorHom (O := (restrictToOpen X U).presheaf)
        ((openSubspaceRestrictionIsoModuleRestriction U).inv.app M).val
        ((openSubspaceRestrictionIsoModuleRestriction U).inv.app L).val =
      CategoryStruct.id _ :=
  PresheafOfModules.tensorHom_id _ _

/-- **The tensor product of two copies of the comparison, as the third leg of
`SheafOfModules.openSubspaceTensorIso` writes it, is the sheafification of their objectwise
tensor product.** Each half of the leg is by definition the sheafification of an objectwise
tensor product of morphisms with an identity, and sheafification and the objectwise tensor
product are functorial. -/
theorem sheafTensorMap_openSubspaceComparison_inv_eq :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).map
        ((openSubspaceRestrictionIsoModuleRestriction U).inv.app M)).app
          ((moduleRestriction X U).obj L) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj
          ((openSubspaceRestriction U).obj M)).map
        ((openSubspaceRestrictionIsoModuleRestriction U).inv.app L) =
      (PresheafOfModules.sheafification
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
            ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩).obj)).map
        (PresheafOfModules.tensorHom (O := (restrictToOpen X U).presheaf)
          ((openSubspaceRestrictionIsoModuleRestriction U).inv.app M).val
          ((openSubspaceRestrictionIsoModuleRestriction U).inv.app L).val) :=
  ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨(restrictToOpen X U).presheaf, (restrictToOpen X U).IsSheaf⟩)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨(restrictToOpen X U).presheaf, (restrictToOpen X
            U).IsSheaf⟩).obj)).map_comp _ _).symm.trans
    (congrArg _ ((PresheafOfModules.tensorHom_comp _ _ _ _).trans
      (congrArg₂ PresheafOfModules.tensorHom (Category.comp_id _) (Category.id_comp _))))

end SheafOfModules

end
