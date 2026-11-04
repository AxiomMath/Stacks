module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteLocallyFree
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityOnAnOpenCover
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection formula for a morphism of ringed spaces, locally on the target

For a morphism of ringed spaces `f : Z ⟶ X`,
`StacksFrontier/AlgebraicGeometry/ProjectionFormula/Basic.lean` builds the canonical map

`Stacks.AffineProjectionFormula.projectionFormulaMap f 𝒢 ℋ : f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)`

and `ProjectionFormula/FiniteLocallyFree.lean` proves it invertible, for an arbitrary morphism of
ringed spaces and with no hypothesis on `𝒢`, when `ℋ` is free of finite rank.  This file removes
the globality of that hypothesis **for a morphism of ringed spaces**: the map is invertible as
soon as `ℋ` is free of finite rank on each member of an open covering of the target.

`ProjectionFormula/Locality.lean` proves the same statement for a morphism of *schemes*.  It is
not subsumed by this file and is kept: it is cheaper, and it has consumers which already hold the
scheme spelling of every functor involved.  What this file adds is the generality
[Stacks, Tag 01E8] actually asks for — an arbitrary morphism of ringed spaces.

## The argument, and what was already in the library

The argument is the one of `ProjectionFormula/Locality.lean`, which is in turn the second half of
the tag's own sentence *"This is clear when `ℰ = 𝒪_Y^{⊕ n}`, and follows in general by working
locally on `Y`"*.  Nothing in it is new mathematics, and — this was the surprise — nothing in it
needed new ringed-space geometry either.  Each of the five inputs the scheme proof draws from the
scheme API has a ringed-space counterpart already in the library:

* **invertibility of a morphism of sheaves of modules is local on the space**:
  `Stacks.Cohomology.isIso_of_isIso_jStar_map_of_iSup_eq_top`, for an arbitrary sheaf of rings on
  an arbitrary topological space, in place of
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`;
* **the open subspace and its inclusion**: `Stacks.Cohomology.HigherDirectImage.restrictToOpen`
  and `openSubspaceInclusion`, in place of `V.ι` of a scheme;
* **the restriction functor and its adjunction with invertible counit**:
  `ExtensionByZeroModules.jStar` with `jStarAdjunction` and
  `ExtensionByZeroModules.isIso_jStarAdjunction_counit`, in place of
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`;
* **base change along the restriction square**:
  `Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, in place of
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`;
* **functoriality of the inverse image**: `RingedSpaceModuleAdjunction.modulePullbackComp` and
  `modulePullbackCongr`, in place of `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
  `pullbackCongr`.

The remaining input, the finite-free case
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_free`, was already stated for an
arbitrary morphism of ringed spaces, as was the tensor transport
`Stacks.AffineProjectionFormula.isIso_pullback_tensorSheaf_map` and the three abstract
category-theoretic facts of `ProjectionFormula/Locality.lean`, all of which are reused verbatim.

## Main definitions

* `Stacks.AffineProjectionFormula.moduleRestrictionIsoPullback`: restriction of modules to an
  open subspace is the inverse image along the open-subspace inclusion.
* `Stacks.AffineProjectionFormula.pullbackRestrictSquareIsoRingedSpace`: the two ways of pulling
  back around the square obtained by restricting a morphism of ringed spaces over an open of its
  target agree.
* `Stacks.AffineProjectionFormula.moduleRestrictionFreeIso`: the restriction of a free module to
  an open subspace is free on the same index type.

## Main results

* `Stacks.AffineProjectionFormula.isIso_moduleRestriction_projectionFormulaMap_congr`:
  **invertibility of the restricted projection-formula map is transported along any morphism of
  modules on the target whose own restriction is invertible.**
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_restrict_free_ringedSpace` and
  `isIso_projectionFormulaMap_of_isFiniteLocallyFree_ringedSpace`: **the projection formula for an
  arbitrary morphism of ringed spaces whenever the module on the target is finite locally free**,
  with no hypothesis on the module upstairs and none on the morphism.

## Implementation notes

*The four spellings of restriction to an open are the same functor on the nose.*  The library
carries `ExtensionByZeroModules.jStar V 𝒪` (restriction along the image functor on opens),
`Stacks.Cohomology.HigherDirectImage.moduleRestriction X V` (the same, packaged for a ringed
space), `Stacks.Cohomology.openInclusionSiteRestriction X V` (the same, packaged for the open
immersion `X.ofRestrict`), and `RingedSpaceModuleAdjunction.modulePullback` of the inclusion.  The
first three are equal by `rfl` — all three are `SheafOfModules.pushforward` of an identity along
the image functor of the open embedding, and the three spellings of the restricted sheaf of rings
agree too — so they are used interchangeably below, with the type ascribed where the elaborator
needs it.  The fourth is only *isomorphic* to them, by uniqueness of left adjoints, and that is
`moduleRestrictionIsoPullback`; it is needed because the tensor transport is stated for the
inverse image while the base change along the restriction square is stated for the restriction,
and `isIso_moduleRestriction_map_iff` is the crossing.

*Only naturality of the restriction-square base change is used.*  As in the scheme proof, no
compatibility of the projection-formula map itself with restriction is needed; the transport is
along a morphism in the module on the target, through the naturality square of
`Stacks.AffineProjectionFormula.projectionFormulaNatTrans`.  In particular
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso` is consumed only through
`Stacks.AffineProjectionFormula.isIso_functor_map_of_natIso`, so its description on sections is
not needed either.

*The hypothesis is finite local freeness written out pointwise*, as in
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`: for every
point an open neighbourhood on which the module is isomorphic to `SheafOfModules.free I` for a
finite `I : Type u`.  That is the condition of [Stacks, Tag 01C6]; the passage to the class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, which at schemes is
`Stacks.Modules.isFiniteLocallyFree_iff_localGenerators`, compares local generators data on the
*slice* sites with restriction to *open subspaces* and is not carried out here.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 00A1](https://stacks.math.columbia.edu/tag/00A1)
* [Stacks Project, Tag 00A7](https://stacks.math.columbia.edu/tag/00A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.Cohomology
open Stacks.Cohomology.HigherDirectImage
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

universe u

/-! ### Restriction to an open subspace of a ringed space -/

section Restriction

variable (X : AlgebraicGeometry.RingedSpace.{u, u}) (V : Opens (X : TopCat))

/-- **Restriction of sheaves of modules to an open subspace is the inverse image along the
open-subspace inclusion.**  Both are left adjoint to the direct image along that inclusion —
restriction by `ExtensionByZeroModules.jStarAdjunction`, the inverse image by the
pullback–pushforward adjunction — so this is uniqueness of left adjoints. -/
def moduleRestrictionIsoPullback :
    moduleRestriction X V ≅ pullbackFunctor (openSubspaceInclusion X V) :=
  Stacks.Cohomology.openInclusionModulePullbackIso X V

/-- **Restriction to an open subspace and inverse image along its inclusion carry the same
morphisms to isomorphisms**, being naturally isomorphic by `moduleRestrictionIsoPullback`. -/
theorem isIso_moduleRestriction_map_iff
    {M N : SheafOfModules.{u} (structureRingSheaf X)} (φ : M ⟶ N) :
    IsIso ((moduleRestriction X V).map φ) ↔
      IsIso ((pullbackFunctor (openSubspaceInclusion X V)).map φ) :=
  ⟨fun h => isIso_functor_map_of_natIso (moduleRestrictionIsoPullback X V).symm _ h,
    fun h => isIso_functor_map_of_natIso (moduleRestrictionIsoPullback X V) _ h⟩

/-- The unit of the adjunction `j^* ⊣ j_*` at the inclusion of an open subspace: the canonical
morphism from a module to the direct image of its restriction. -/
abbrev moduleRestrictUnit (M : SheafOfModules.{u} (structureRingSheaf X)) :
    M ⟶ (pushforwardFunctor (openSubspaceInclusion X V)).obj ((moduleRestriction X V).obj M) :=
  (ExtensionByZeroModules.jStarAdjunction V (structureRingSheaf X)).unit.app M

/-- **The unit of the restriction adjunction becomes invertible on the open it restricts to.**
The counit of that adjunction is invertible
(`ExtensionByZeroModules.isIso_jStarAdjunction_counit`), so this is the left triangle
identity. -/
theorem isIso_moduleRestriction_moduleRestrictUnit
    (M : SheafOfModules.{u} (structureRingSheaf X)) :
    IsIso ((moduleRestriction X V).map (moduleRestrictUnit X V M)) :=
  isIso_map_unit_of_isIso_counit
    (ExtensionByZeroModules.jStarAdjunction V (structureRingSheaf X)) M inferInstance

/-- **Tensoring with a fixed module commutes with restriction well enough to transport
invertibility.**  This is `Stacks.AffineProjectionFormula.isIso_pullback_tensorSheaf_map`, the
naturality of the pullback tensor comparison of [Stacks, Tag 01CD], crossed to the restriction
spelling by `isIso_moduleRestriction_map_iff`. -/
theorem isIso_moduleRestriction_tensorSheaf_map
    (A : SheafOfModules.{u} (structureRingSheaf X))
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H')
    (hk : IsIso ((moduleRestriction X V).map k)) :
    IsIso ((moduleRestriction X V).map
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map (𝟙 A ×ₘ k))) :=
  (isIso_moduleRestriction_map_iff X V _).mpr
    (isIso_pullback_tensorSheaf_map (openSubspaceInclusion X V) A k
      ((isIso_moduleRestriction_map_iff X V k).mp hk))

/-- **The restriction of a free sheaf of modules to an open subspace is the free sheaf of modules
on the same index type.**  Restriction is the inverse image by `moduleRestrictionIsoPullback`, and
the inverse image of a free module along an arbitrary morphism of ringed spaces is free. -/
def moduleRestrictionFreeIso (I : Type u) :
    (moduleRestriction X V).obj
        (SheafOfModules.free.{u} (R := structureRingSheaf X) I) ≅
      SheafOfModules.free.{u} (R := structureRingSheaf (restrictToOpen X V)) I :=
  (moduleRestrictionIsoPullback X V).app _ ≪≫
    modulePullbackObjFreeIso (openSubspaceInclusion X V) I

end Restriction

/-! ### Invertibility of a morphism of modules is local on a ringed space -/

section Locality

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- **Invertibility of a morphism of sheaves of modules on a ringed space is local**: a morphism
whose restriction to each member of an open covering is invertible is invertible.  This is
`Stacks.Cohomology.isIso_of_isIso_jStar_map_of_iSup_eq_top`, whose restriction functor
`ExtensionByZeroModules.jStar` is `Stacks.Cohomology.HigherDirectImage.moduleRestriction` on the
nose. -/
theorem isIso_of_isIso_moduleRestriction {ι : Type*} (U : ι → Opens (X : TopCat))
    (hU : iSup U = ⊤) {M N : SheafOfModules.{u} (structureRingSheaf X)} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((moduleRestriction X (U i)).map φ)) :
    IsIso φ :=
  Stacks.Cohomology.isIso_of_isIso_jStar_map_of_iSup_eq_top (structureRingSheaf X) U hU φ h

end Locality

/-! ### The three geometric transports, for a morphism of ringed spaces -/

section Transports

variable {Z X : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X) (V : Opens (X : TopCat))

/-- **The two ways of pulling back around the restriction square agree**: restricting to
`f ⁻¹ V` an inverse image along `f` is the inverse image along `f ∣_ V` of a restriction to `V`.
Both are inverse images along the two equal composites of the square, which are equal by
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion`. -/
def pullbackRestrictSquareIsoRingedSpace :
    pullbackFunctor f ⋙ pullbackFunctor (openSubspaceInclusion Z (preimageOpen f V)) ≅
      pullbackFunctor (openSubspaceInclusion X V) ⋙
        pullbackFunctor (restrictedMorphism f V) :=
  (modulePullbackComp (openSubspaceInclusion Z (preimageOpen f V)) f).symm ≪≫
    modulePullbackCongr (restrictedMorphism_comp_openSubspaceInclusion f V) ≪≫
    modulePullbackComp (restrictedMorphism f V) (openSubspaceInclusion X V)

/-- A functor naturally isomorphic to a composite `G ⋙ K` carries `k` to an isomorphism as soon
as `G` does. -/
private theorem isIso_map_of_natIso_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {P : C ⥤ E} {G : C ⥤ D} {K : D ⥤ E} (θ : P ≅ G ⋙ K) {A B : C} (k : A ⟶ B)
    (hk : IsIso (G.map k)) : IsIso (P.map k) :=
  isIso_functor_map_of_natIso θ k (Functor.map_isIso K _)

/-- **The inverse image commutes with restriction to an open of the target well enough to
transport invertibility**, by `pullbackRestrictSquareIsoRingedSpace`. -/
theorem isIso_moduleRestriction_pullback_map
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H')
    (hk : IsIso ((moduleRestriction X V).map k)) :
    IsIso ((moduleRestriction Z (preimageOpen f V)).map ((pullbackFunctor f).map k)) :=
  (isIso_moduleRestriction_map_iff Z (preimageOpen f V) _).mpr
    (isIso_map_of_natIso_comp (pullbackRestrictSquareIsoRingedSpace f V) k
      ((isIso_moduleRestriction_map_iff X V k).mp hk))

/-- **The direct image commutes with restriction to an open of the target well enough to
transport invertibility**: if the restriction of `m` to `f ⁻¹ V` is invertible, so is the
restriction to `V` of `f_* m`.  This is the naturality of
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, the identification of
`(f_*ℳ)|_V` with `(f ∣_ V)_*(ℳ|_{f⁻¹V})`. -/
theorem isIso_moduleRestriction_pushforward_map
    {M N : SheafOfModules.{u} (structureRingSheaf Z)} (m : M ⟶ N)
    (hm : IsIso ((moduleRestriction Z (preimageOpen f V)).map m)) :
    IsIso ((moduleRestriction X V).map ((pushforwardFunctor f).map m)) :=
  isIso_map_of_natIso_comp (modulePushforwardRestrictIso f V).symm m hm

end Transports

/-! ### The two functors of the projection formula, restricted to an open -/

section Functors

variable {Z X : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X) (V : Opens (X : TopCat))
  (G : SheafOfModules.{u} (structureRingSheaf Z))

/-- The source functor `ℋ ↦ f_*𝒢 ⊗ ℋ` of the projection formula, followed by restriction to an
open of the target, carries a morphism restricting to an isomorphism to an isomorphism. -/
theorem isIso_moduleRestriction_tensorPushforward_map
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H')
    (hk : IsIso ((moduleRestriction X V).map k)) :
    IsIso ((moduleRestriction X V).map ((tensorPushforwardFunctor f G).map k)) :=
  isIso_moduleRestriction_tensorSheaf_map X V ((pushforwardFunctor f).obj G) k hk

/-- The target functor `ℋ ↦ f_*(𝒢 ⊗ f^*ℋ)` of the projection formula, followed by restriction to
an open of the target, carries a morphism restricting to an isomorphism to an isomorphism.  Three
transports, in the order inverse image, tensor product, direct image. -/
theorem isIso_moduleRestriction_pushforwardTensorPullback_map
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H')
    (hk : IsIso ((moduleRestriction X V).map k)) :
    IsIso ((moduleRestriction X V).map ((pushforwardTensorPullbackFunctor f G).map k)) := by
  have hd : IsIso ((moduleRestriction Z (preimageOpen f V)).map
      ((pullbackFunctor f).map k)) :=
    isIso_moduleRestriction_pullback_map f V k hk
  have hB := isIso_moduleRestriction_tensorSheaf_map Z (preimageOpen f V) G
    ((pullbackFunctor f).map k) hd
  exact isIso_moduleRestriction_pushforward_map f V _ hB

/-- **Invertibility of the restricted projection-formula map is transported along any morphism of
modules on the target whose own restriction is invertible.**  This is the naturality square of
`Stacks.AffineProjectionFormula.projectionFormulaNatTrans` whiskered with the restriction to an
open, and it is what replaces a compatibility of the projection-formula map with restriction. -/
theorem isIso_moduleRestriction_projectionFormulaMap_congr
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H')
    (hk : IsIso ((moduleRestriction X V).map k)) :
    IsIso ((moduleRestriction X V).map (projectionFormulaMap f G H)) ↔
      IsIso ((moduleRestriction X V).map (projectionFormulaMap f G H')) :=
  isIso_natTrans_app_iff_of_isIso_map
    (CategoryTheory.Functor.whiskerRight (projectionFormulaNatTrans f G)
      (moduleRestriction X V)) k
    (isIso_moduleRestriction_tensorPushforward_map f V G k hk)
    (isIso_moduleRestriction_pushforwardTensorPullback_map f V G k hk)

end Functors

/-! ### The projection formula at a finite locally free module, for a morphism of ringed spaces -/

section LocallyFree

variable {Z X : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X)
  (G : SheafOfModules.{u} (structureRingSheaf Z))
  (H : SheafOfModules.{u} (structureRingSheaf X))

/-- **The restriction of the projection-formula map to an open on which the module on the target
agrees with one at which the map is already invertible is invertible.**

Three transports along `isIso_moduleRestriction_projectionFormulaMap_congr`: along the
restriction unit at the comparison module `ℰ`, along the direct image of the assumed isomorphism,
and back along the restriction unit at `ℋ`. -/
theorem isIso_moduleRestriction_projectionFormulaMap_of_isIso (V : Opens (X : TopCat))
    (E : SheafOfModules.{u} (structureRingSheaf X))
    (hE : IsIso (projectionFormulaMap f G E))
    (e : (moduleRestriction X V).obj E ≅ (moduleRestriction X V).obj H) :
    IsIso ((moduleRestriction X V).map (projectionFormulaMap f G H)) := by
  have c0 : IsIso ((moduleRestriction X V).map (projectionFormulaMap f G E)) :=
    ((moduleRestriction X V).mapIso (@asIso _ _ _ _ _ hE)).isIso_hom
  have c1 := (isIso_moduleRestriction_projectionFormulaMap_congr f V G
    (moduleRestrictUnit X V E) (isIso_moduleRestriction_moduleRestrictUnit X V E)).mp c0
  have hk2 : IsIso ((moduleRestriction X V).map
      ((pushforwardFunctor (openSubspaceInclusion X V)).map e.hom)) :=
    ((moduleRestriction X V).mapIso
      ((pushforwardFunctor (openSubspaceInclusion X V)).mapIso e)).isIso_hom
  have c2 := (isIso_moduleRestriction_projectionFormulaMap_congr f V G _ hk2).mp c1
  exact (isIso_moduleRestriction_projectionFormulaMap_congr f V G
    (moduleRestrictUnit X V H) (isIso_moduleRestriction_moduleRestrictUnit X V H)).mpr c2

/-- **The projection formula for an arbitrary morphism of ringed spaces at a module on the target
which is free of finite rank on each member of an open covering**: the canonical map
`f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` is an isomorphism, with no hypothesis on `𝒢` and none on
`f`.  Invertibility is local on the target by `isIso_of_isIso_moduleRestriction`, and the
finite-free case is `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_free`. -/
theorem isIso_projectionFormulaMap_of_restrict_free_ringedSpace
    (I : ↥(X : TopCat) → Type u) [∀ x, Finite (I x)]
    (V : ↥(X : TopCat) → Opens (X : TopCat)) (hx : ∀ x, x ∈ V x)
    (e : ∀ x, (moduleRestriction X (V x)).obj H ≅ SheafOfModules.free.{u} (I x)) :
    IsIso (projectionFormulaMap f G H) := by
  refine isIso_of_isIso_moduleRestriction X V ?_ _ fun x =>
    isIso_moduleRestriction_projectionFormulaMap_of_isIso f G H (V x)
      (SheafOfModules.free.{u} (I x))
      (isIso_projectionFormulaMap_free f G (I x))
      (moduleRestrictionFreeIso X (V x) (I x) ≪≫ (e x).symm)
  refine le_antisymm le_top ?_
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, hx x⟩

/-- **The projection formula for an arbitrary morphism of ringed spaces at a finite locally free
module on the target**: for `𝒢` an arbitrary `𝒪_Z`-module and `ℋ` an `𝒪_X`-module such that every
point of `X` has an open neighbourhood on which `ℋ` is free of finite rank, the canonical map
`f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` is an isomorphism.

The hypothesis is the finite local freeness of [Stacks, Tag 01C6] written out pointwise, as in
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`; here there is
no scheme hypothesis on `f`, which is the generality [Stacks, Tag 01E8] asks for.  The form of
the statement taking the class `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, which is
what carries the attribute for the clause, is
`isIso_projectionFormulaMap_of_isFiniteLocallyFree_class_ringedSpace` below. -/
@[ega "0 5.4.10"]
theorem isIso_projectionFormulaMap_of_isFiniteLocallyFree_ringedSpace
    (hH : ∀ x : ↥(X : TopCat), ∃ (V : Opens (X : TopCat)) (_ : x ∈ V) (I : Type u) (_ : Finite I),
      Nonempty ((moduleRestriction X V).obj H ≅ SheafOfModules.free.{u} I)) :
    IsIso (projectionFormulaMap f G H) := by
  choose V hV I hI e using hH
  exact isIso_projectionFormulaMap_of_restrict_free_ringedSpace f G H I V hV fun x => (e x).some

/-- **[Stacks, Tag 01C6], from the class to the pointwise condition, at a ringed space**: a finite
locally free module restricts, on some open neighbourhood of any given point, to a free module on
a finite index type.

The class `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` is phrased through local
generators data on the *slice* sites of `Opens X`, and this is the passage to restriction to
*open subspaces*: `AlgebraicGeometry.RingedSpace.exists_free_iso_over_near` produces the chart on
the slice site, `nonempty_restrictModules_obj_iso_finiteFree` carries it across the equivalence
`AlgebraicGeometry.RingedSpace.overToRestricted` between the two, and
`AlgebraicGeometry.RingedSpace.finiteFreeIsoFree` rewrites `𝒪^{⊕ n}` as the free module on
`ULift (Fin n)`.  `AlgebraicGeometry.RingedSpace.restrictModules` and
`Stacks.Cohomology.HigherDirectImage.moduleRestriction` are the same functor by `rfl`. -/
theorem exists_moduleRestriction_iso_free_of_isFiniteLocallyFree
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (E : SheafOfModules.{u} (structureRingSheaf X))
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (x : ↥(X : TopCat)) :
    ∃ (V : Opens (X : TopCat)) (_ : x ∈ V) (I : Type u) (_ : Finite I),
      Nonempty ((moduleRestriction X V).obj E ≅ SheafOfModules.free.{u} I) := by
  obtain ⟨U, hxU, n, ⟨e⟩⟩ :=
    AlgebraicGeometry.RingedSpace.exists_free_iso_over_near (X := X) (M := E) hE x
  obtain ⟨e'⟩ :=
    AlgebraicGeometry.RingedSpace.nonempty_restrictModules_obj_iso_finiteFree E U n e
  exact ⟨U, hxU, ULift.{u} (Fin n), inferInstance,
    ⟨e' ≪≫ AlgebraicGeometry.RingedSpace.finiteFreeIsoFree (restrictToOpen X U) n⟩⟩

/-- **The projection formula for an arbitrary morphism of ringed spaces at a finite locally free
module on the target**, finite local freeness being the class of [Stacks, Tag 01C6]: for `𝒢` an
arbitrary `𝒪_Z`-module and `ℋ` a finite locally free `𝒪_X`-module, the canonical map
`f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` is an isomorphism.

This is `isIso_projectionFormulaMap_of_isFiniteLocallyFree_ringedSpace` with its pointwise
input supplied by `exists_moduleRestriction_iso_free_of_isFiniteLocallyFree`. -/
@[stacks 01E8 "the q = 0 clause: for a morphism of ringed spaces f, an arbitrary module 𝒢 on \
the source and a finite locally free module ℋ on the target, the projection formula map \
f_*𝒢 ⊗ ℋ ⟶ f_*(𝒢 ⊗ f^*ℋ) is an isomorphism"]
theorem isIso_projectionFormulaMap_of_isFiniteLocallyFree_class_ringedSpace
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} H] :
    IsIso (projectionFormulaMap f G H) :=
  isIso_projectionFormulaMap_of_isFiniteLocallyFree_ringedSpace f G H
    (exists_moduleRestriction_iso_free_of_isFiniteLocallyFree X H)

end LocallyFree

end Stacks.AffineProjectionFormula

end
