module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# The Picard homomorphism of the associated module of the small étale site

Let `S` be a scheme of a big étale site `B`.  The associated-module functor
`AlgebraicGeometry.SmallEtale.associatedModule` of Stacks 03DU (4) carries the structure sheaf of
the small Zariski site of `S` to the structure sheaf of the small étale site and a tensor product
sheaf of Tag 01CA to the tensor product sheaf of the images.  By
`Stacks.SheafOfModules.Picard.map` those two isomorphisms of objects are all that is needed to
transport Picard classes, so `𝓕 ↦ 𝓕^a` induces a homomorphism of the Picard groups of Tag 01CX

`Pic(𝒪_S) ⟶ Pic(𝒪_{S_étale})`

carrying the class of an invertible `𝒪_S`-module `𝓛` to the class of `𝓛^a`.  Both Picard groups
are `Stacks.SheafOfModules.Picard.PicardGroup`, which is the group Tag 040E produces, so this is
the comparison the étale clause of Tag 03P8 asks for, on the nose and with no hypothesis.

## What the two inputs are

* The unit comparison is `AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit`: the pullback
  of the unit object along the morphism of ringed sites `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` is the
  unit object, the inclusion of the small Zariski site being final.
* The tensor comparison is `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`, which is
  Stacks 03EL at `ε` and carries no hypothesis.

Neither is used with any naturality and no monoidal coherence enters; see the discussion in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PicardTransport.lean`.  The three spellings of the
two structure sheaves are reconciled by `rfl`:
`Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf` for the Zariski one and the definition of
`AlgebraicGeometry.SmallEtale.commRingStructureSheaf` for the étale one, so the statements below
are the ones `Stacks.SheafOfModules.Picard.map` is stated for with nothing transported.

## Main definitions

* `AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf`: the Zariski structure sheaf of `S` in the
  packaging `Stacks.SheafOfModules.Picard.PicardGroup` is stated for.
* `AlgebraicGeometry.SmallEtale.associatedModulePicardUnitIso` and
  `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso'`: the two object-level comparisons, in
  that packaging.
* `AlgebraicGeometry.SmallEtale.associatedModulePicardHom`: **the induced homomorphism
  `Pic(𝒪_S) ⟶ Pic(𝒪_{S_étale})`.**

## Main results

* `AlgebraicGeometry.SmallEtale.isInvertible_associatedModule`: **the associated module of an
  invertible `𝒪_S`-module is invertible on the small étale site.**
* `AlgebraicGeometry.SmallEtale.associatedModulePicardHom_classOf`: the homomorphism sends the
  class of `𝓛` to the class of `𝓛^a`, which fixes it.

## What is not here

That `associatedModulePicardHom` is *bijective*: that is
`AlgebraicGeometry.SmallEtale.associatedModulePicardAddEquiv`, in
`StacksFrontier/AlgebraicGeometry/Picard/SmallEtalePicardIsomorphism.lean`, and the étale
identification `H¹_étale(S, 𝐆_m) = H¹_Zar(S, 𝐆_m) = Pic(S)` of Stacks 03P8 that it feeds is in
`StacksFrontier/AlgebraicGeometry/Picard/SmallEtaleFirstCohomologyComparison.lean`.  No `stacks`
attribute is claimed in this file, which is only the homomorphism.

Both halves of bijectivity are read off the associated-module adjunction, whose unit and counit
are isomorphisms at the modules in play.  The one input that was missing from the library is
*reflection of invertibility* — that the Zariski restriction of an invertible `𝒪`-module on
`S_étale` is invertible, `AlgebraicGeometry.SmallEtale.isInvertible_restrictModule`.
`Stacks.SheafOfModules.Picard.isInvertible_map_obj` does not supply it, because the tensor
comparison of the restriction functor
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso` holds only at *quasi-coherent* arguments
while that lemma asks for one at all arguments; what does supply it is
`Stacks.SheafOfModules.Picard.isInvertible_map_obj_of_tensorIsoOn`, the same transport with the
tensor comparison asked for only on a full subcategory containing the invertible modules.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf condition for the structure presheaf of rings of `S`, in the packaging that
`Stacks.SheafOfModules.Picard.PicardGroup` and the tensor product sheaf of Tag 01CA are stated
for.  `Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf` says that the sheaf of rings it
produces is `AlgebraicGeometry.Scheme.ringCatSheaf`, so the `𝒪_S`-modules here are
`AlgebraicGeometry.Scheme.Modules`. -/
abbrev zariskiStructureIsSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology S)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf S.presheaf) :=
  Stacks.SheafInternalHom.isSheaf_structureRingPresheaf S

/-- **The associated module of the structure sheaf is the structure sheaf.**  This is
`AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit` — the pullback of the unit object along
`ε` is the unit object, the inclusion of the small Zariski site being final — stated in the
packaging of `Stacks.SheafOfModules.Picard.map`. -/
def associatedModulePicardUnitIso :
    Stacks.SheafOfModules.Picard.UnitIso S.presheaf (zariskiStructureIsSheaf S)
      (commRingStructureSheaf B S hS).obj (structure_isSheaf B S hS)
      (associatedModule B S hS) :=
  @asIso _ _ _ _ _ (isIso_pullbackObjUnitToUnit B S hS)

/-- **Stacks 03EL at `ε`, in the packaging of `Stacks.SheafOfModules.Picard.map`**: the associated
module of a tensor product sheaf of Tag 01CA is the tensor product sheaf of the associated modules,
with no hypothesis.  This is `AlgebraicGeometry.SmallEtale.associatedModuleTensorIso`; the two
tensor products it is stated with are the two here by `rfl`, as its own
`tensorSheafBifunctorZariski_obj` and `tensorSheafBifunctorEtale_obj` record. -/
def associatedModuleTensorIso' :
    Stacks.SheafOfModules.Picard.TensorIso S.presheaf (zariskiStructureIsSheaf S)
      (commRingStructureSheaf B S hS).obj (structure_isSheaf B S hS)
      (associatedModule B S hS) := fun L N =>
  associatedModuleTensorIso B S hS L N

/-- **The associated module of an invertible `𝒪_S`-module is an invertible `𝒪`-module on the small
étale site of `S`**, with no hypothesis: `Stacks.SheafOfModules.Picard.isInvertible_map_obj` at the
two comparisons above. -/
theorem isInvertible_associatedModule
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)))
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    Stacks.SheafOfModules.IsInvertible (commRingStructureSheaf B S hS).obj
      (structure_isSheaf B S hS) ((associatedModule B S hS).obj L) :=
  Stacks.SheafOfModules.Picard.isInvertible_map_obj _ _ _ _ _
    (associatedModulePicardUnitIso B S hS) (associatedModuleTensorIso' B S hS) L hL

variable [∀ V : S.Opens, ((Opens.grothendieckTopology S).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : SmallEtale B S hS, ((topology B S hS).over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The abelian group structure on the Picard group of the small Zariski site of `S`, named for
the reason recorded on `Stacks.Picard.ZariskiSite.zariskiPicardGroupAddCommGroup`: instance search
does not find it through the universe constraints in play. -/
local instance zariskiPicardAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup S.presheaf
      (zariskiStructureIsSheaf S)) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup S.presheaf (zariskiStructureIsSheaf S)

/-- The abelian group structure on the Picard group of the small étale site of `S`, named for the
same reason. -/
local instance etalePicardAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup (commRingStructureSheaf B S hS).obj
      (structure_isSheaf B S hS)) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup (commRingStructureSheaf B S hS).obj
    (structure_isSheaf B S hS)

/-- **The homomorphism of Picard groups induced by `𝓕 ↦ 𝓕^a`**, `Pic(𝒪_S) ⟶ Pic(𝒪_{S_étale})`,
with no hypothesis.  Both groups are `Stacks.SheafOfModules.Picard.PicardGroup`, the group Tag 040E
produces. -/
def associatedModulePicardHom :
    Stacks.SheafOfModules.Picard.PicardGroup S.presheaf (zariskiStructureIsSheaf S) →+
      Stacks.SheafOfModules.Picard.PicardGroup (commRingStructureSheaf B S hS).obj
        (structure_isSheaf B S hS) :=
  Stacks.SheafOfModules.Picard.map _ _ _ _ _
    (associatedModulePicardUnitIso B S hS) (associatedModuleTensorIso' B S hS)

omit [∀ V : S.Opens, ((Opens.grothendieckTopology S).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : SmallEtale B S hS, ((topology B S hS).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- **The homomorphism sends the class of `𝓛` to the class of `𝓛^a`.**  This fixes it, rather than
only asserting that some homomorphism exists. -/
theorem associatedModulePicardHom_classOf
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)))
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    associatedModulePicardHom B S hS
        (Stacks.SheafOfModules.Picard.classOf S.presheaf (zariskiStructureIsSheaf S) L hL) =
      Stacks.SheafOfModules.Picard.classOf (commRingStructureSheaf B S hS).obj
        (structure_isSheaf B S hS) ((associatedModule B S hS).obj L)
        (isInvertible_associatedModule B S hS L hL) :=
  Stacks.SheafOfModules.Picard.map_classOf _ _ _ _ _
    (associatedModulePicardUnitIso B S hS) (associatedModuleTensorIso' B S hS) L hL

end AlgebraicGeometry.SmallEtale

end
