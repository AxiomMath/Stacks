module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.MateStalk
public import StacksFrontier.AlgebraicGeometry.Conormal.Stalk
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.InverseImageIdealSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentImmersionDegreeZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal comparison

Let `i : Z ⟶ X` be an immersion of schemes.  Two constructions of `ℐ/ℐ²` are attached to it.

* The **geometric** one, `Stacks.Conormal.conormalSheaf i`: the immersion factors as the closed
  immersion `L = i.liftCoborder : Z ⟶ i.coborderRange` followed by an open immersion, and the
  conormal sheaf is the module pullback along `L` of the ideal sheaf of `L`.
* The **sites** one, `Stacks.Sites.Conormal.conormalSheaf` of the structural homomorphism
  `i^{-1}𝒪_X ⟶ 𝒪_Z` of sheaves of commutative rings on the Zariski site of `Z`: the sheaf
  associated to the presheaf `U ↦ I(U)/I(U)²`, for `I` the kernel of that homomorphism.  This is
  the sheaf occurring in degree `-1` of the naive cotangent complex of `i`.

This file constructs the canonical comparison morphism from the first to the second.

## Main definitions

* `Stacks.Conormal.Sites.coborderUnit`: the ring homomorphism
  `𝒪_{i.coborderRange}(V) ⟶ (i^{-1}𝒪_X)(L ⁻¹ᵁ V)` given by the unit of the
  inverse-image/direct-image adjunction at the open `i.coborderRange.ι ''ᵁ V` of `X`, read
  through `AlgebraicGeometry.Scheme.Hom.liftCoborder_preimage`.
* `Stacks.Conormal.Sites.kernelSection`: the image under `coborderUnit` of a section of the
  ideal sheaf of `L`, as a section of the kernel ideal of the structural homomorphism.
* `Stacks.Conormal.Sites.conormalTransposeApp` and
  `Stacks.Conormal.Sites.conormalTranspose`: the adjoint transpose `ℐ ⟶ L_* (I/I²)` of the
  comparison, sending a section `f` of the ideal sheaf of `L` over `V` to the conormal class of
  `coborderUnit f`.
* `Stacks.Conormal.Sites.conormalComparison`: **the comparison morphism**
  `𝒞_{Z/X} ⟶ I/I²`, the transpose of `conormalTranspose` along the module
  pullback–pushforward adjunction.
* `Stacks.Conormal.Sites.stalkComparison`: the comparison of local rings
  `(i^{-1}𝒪_X)_z ≅ 𝒪_{i.coborderRange, L z}`, and
  `Stacks.Conormal.Sites.cotangentTransport`: the bijection of cotangent modules it induces.
* `Stacks.Conormal.Sites.conormalComparisonIso`: **the comparison isomorphism**
  `𝒞_{Z/X} ≅ I/I²`, and `Stacks.Conormal.Sites.sitesConormalSheafIsoConormalSheaf`: the same
  isomorphism turned around, with its type declared in `AlgebraicGeometry.Scheme.Modules Z`.

## Main results

* `Stacks.Conormal.Sites.coborderUnit_comp_structHom`: the unit followed by the structural
  homomorphism is the map on sections induced by `L`.  This is the single compatibility the
  construction rests on; everything else is bookkeeping.
* `Stacks.Conormal.Sites.conormalComparison_unit`: the comparison morphism carries the canonical
  local section of `𝒞_{Z/X}` attached to a section `f` of the ideal sheaf of `L` — the image of
  `f` under the unit of the module pullback–pushforward adjunction, which is the section the
  stalk identification `Stacks.Conormal.conormalSheafStalkEquivCotangent` is normalised on — to
  the conormal class of `coborderUnit f`.  This pins the comparison down.
* `Stacks.Conormal.Sites.stalkKernelIdeal_eq_comap`: the kernel ideal of the structural
  homomorphism on the stalk at `z` is the inverse image, along the comparison of local rings, of
  the kernel of `𝒪_{i.coborderRange, L z} ⟶ 𝒪_{Z,z}`.
* `Stacks.Conormal.Sites.exists_germ_unit`: every element of the stalk of the geometric conormal
  sheaf is the germ of one of the canonical local sections, which is what makes the germ formula
  for `Stacks.Conormal.conormalSheafStalkEquivCotangent` a complete description.
* `Stacks.Conormal.Sites.conormalSheafStalkLinearEquiv_stalkMap`: the stalk of the comparison,
  read through the two germ-pinned identifications of the stalks with cotangent modules, is
  `Stacks.Conormal.Sites.cotangentTransport`.
* `Stacks.Conormal.Sites.isIso_conormalComparison`: **the comparison is an isomorphism.**

## Route

The only thing to see is that the composite
`𝒪_{i.coborderRange}(V) ⟶ (i^{-1}𝒪_X)(L ⁻¹ᵁ V) ⟶ 𝒪_Z(L ⁻¹ᵁ V)`
of the adjunction unit with the structural homomorphism is the map on sections induced by `L`:
the first factor is pinned by
`Stacks.AlgebraPullbackQcoh.germ_comp_inverseImageStructureMap` and the comparison with `L` by
Mathlib's `AlgebraicGeometry.liftCoborder_app`.  A section of the ideal sheaf of `L` is
therefore carried into the kernel ideal, and a scalar is carried to the scalar it has to act as,
so the conormal classes of the images assemble into a morphism `ℐ ⟶ L_*(I/I²)`, whose adjoint
transpose along the module pullback–pushforward adjunction is the comparison.

For the isomorphy, the two stalks at `z : Z` are cotangent modules of two ideals: the kernel `J`
of `𝒪_{i.coborderRange, L z} ⟶ 𝒪_{Z,z}` on the geometric side
(`Stacks.Conormal.conormalSheafStalkEquivCotangent`) and the kernel `I_z` of
`(i^{-1}𝒪_X)_z ⟶ 𝒪_{Z,z}` on the sites side
(`Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv`), and both identifications are pinned on
the germs of conormal classes.  The comparison of local rings
`(i^{-1}𝒪_X)_z ≅ 𝒪_{i.coborderRange, L z}` carries `I_z` onto `J`, so it induces a bijection of
the two cotangent modules, and the comparison morphism is that bijection read through the two
identifications.  A morphism of sheaves of modules on a space which is bijective on every stalk
is an isomorphism (`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`).

## Implementation notes

The sites-level objects are introduced by reducible abbreviations whose types are *ascribed* at
the `CategoryTheory.Sheaf (Opens.grothendieckTopology …)` spelling rather than the
`TopCat.Sheaf` one.  This is not cosmetic: the two spellings carry different, definitionally
equal, `TopologicalSpace` instances on the carrier, so a `Presheaf.IsLocallySurjective`
instance stated at one of them is invisible to instance search at the other.  The whole
sites-level API of `StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence` takes local
surjectivity as an instance, so the ascription is what makes that API usable here at all.

Sections of the ideal sheaf of `L` over an open `V` of `i.coborderRange` are, after
`Stacks.Conormal.idealSection`, sections of `𝒪_{i.coborderRange}` over `V`, which *are*
sections of `𝒪_X` over `i.coborderRange.ι ''ᵁ V` on the nose (Mathlib's
`AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_obj` is `rfl`).  No transport along that
identification is needed and none is inserted.

Every proof is written as a chain of `Eq.trans` and `congrArg` rather than with `rw`.  This is
forced: the structure sheaf of a scheme carries two definitionally equal spellings of its site,
and goals mixing them are not type-correct at `implicit` transparency, which is the
transparency `rw` builds its motive at.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 0FV2](https://stacks.math.columbia.edu/tag/0FV2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

noncomputable section

namespace Stacks.Conormal.Sites

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-! ### The sites-level data of the structural homomorphism -/

/-- The Zariski site of a scheme: the Grothendieck topology on its opens over which the
sites-level conormal sheaf of the structural homomorphism is formed. -/
abbrev siteJ (Z : Scheme.{u}) : GrothendieckTopology (Opens Z.toRingedSpace.carrier) :=
  Opens.grothendieckTopology Z.toRingedSpace.carrier

/-- `i^{-1}𝒪_X`, as a sheaf of commutative rings on the Zariski site of `Z`. -/
abbrev invSheaf : Sheaf (siteJ Z) CommRingCat.{u} :=
  Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf i.toLRSHom.toShHom

/-- `𝒪_Z`, as a sheaf of commutative rings on the Zariski site of `Z`. -/
abbrev structSheaf (Z : Scheme.{u}) : Sheaf (siteJ Z) CommRingCat.{u} := Z.toRingedSpace.sheaf

/-- The structural homomorphism `i^{-1}𝒪_X ⟶ 𝒪_Z` of a morphism of schemes, with its type
ascribed on the Zariski site of `Z`. -/
abbrev structHom : invSheaf i ⟶ structSheaf Z := AlgebraicGeometry.inverseImageStructureMap i

/-- If `i` is surjective on stalks, the structural homomorphism `i^{-1}𝒪_X ⟶ 𝒪_Z` is locally
surjective on the Zariski site of `Z`. -/
instance isLocallySurjective_structHom [SurjectiveOnStalks i] :
    Presheaf.IsLocallySurjective (siteJ Z) (structHom i).hom :=
  Stacks.NaiveCotangentDegreeZero.isLocallySurjective_inverseImageStructureMap i

/-! ### The germ formula for the stalk of the inverse image of the structure sheaf -/

/-- **The comparison `(i^{-1}𝒪_X)_z ≅ 𝒪_{X, i z}` on germs, in the inverse direction.**  The
germ at `i z` of a section `a` of `𝒪_X` over `W` is carried to the germ at `z` of the image of
`a` under the unit of the inverse-image/direct-image adjunction over `W`.

`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq` writes the inverse of the comparison as the
stalk of that unit followed by `TopCat.Presheaf.stalkPushforward`, and each of those two factors
has a germ formula. -/
@[ega "0 3.7.2" "special case"]
theorem stalkInvIso_inv_germ (z : Z) (W : X.Opens) (hW : i.base z ∈ W)
    (a : ToType (X.presheaf.obj (op W))) :
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z).inv.hom
        ((X.presheaf.germ W (i.base z) hW).hom a) =
      (TopCat.Presheaf.germ (invSheaf i).obj (i ⁻¹ᵁ W) z hW).hom
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
          X.sheaf).hom.app (op W)).hom a) := by
  have h := Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq CommRingCat.{u} i.base X.sheaf z
  refine Eq.trans (congrArg (fun m : X.presheaf.stalk (i.base z) ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} i.base).obj X.sheaf).presheaf.stalk z =>
      m.hom ((X.presheaf.germ W (i.base z) hW).hom a)) h) ?_
  refine Eq.trans (CommRingCat.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg
    (TopCat.Presheaf.stalkPushforward CommRingCat.{u} i.base
      ((TopCat.Sheaf.pullback CommRingCat.{u} i.base).obj X.sheaf).presheaf z).hom
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W (i.base z) hW
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
        X.sheaf).hom a)) ?_
  exact TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat.{u} i.base
    ((TopCat.Sheaf.pullback CommRingCat.{u} i.base).obj X.sheaf).presheaf W z hW _

variable [IsImmersion i]

/-- The sites-level conormal sheaf `I/I²` of the structural homomorphism `i^{-1}𝒪_X ⟶ 𝒪_Z`,
the sheaf occurring in degree `-1` of the naive cotangent complex of `i`. -/
abbrev sitesConormalSheaf :=
  Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u}
    (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)

/-- The ideal sheaf of the canonical closed factor `i.liftCoborder` of an immersion: the sheaf
whose module pullback along that factor is the geometric conormal sheaf. -/
abbrev idealSheafLift := Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom

/-- The inclusion of the ideal sheaf of `i.liftCoborder` into the structure sheaf of the
coborder neighbourhood, as a morphism of sheaves of modules. -/
abbrev idealIota := kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom i.liftCoborder.toLRSHom.toShHom))

/-! ### The unit on sections over an open of the coborder neighbourhood -/

/-- **The unit of the inverse-image/direct-image adjunction over an open of the coborder
neighbourhood.**  For an open `V` of `i.coborderRange` the sections of `𝒪_{i.coborderRange}`
over `V` are the sections of `𝒪_X` over `i.coborderRange.ι ''ᵁ V`, and this is the component of
the adjunction unit there, followed by the restriction along
`AlgebraicGeometry.Scheme.Hom.liftCoborder_preimage`, which identifies
`i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V)` with `i.liftCoborder ⁻¹ᵁ V`. -/
def coborderUnit (V : i.coborderRange.toScheme.Opens) :
    i.coborderRange.toScheme.presheaf.obj (op V) ⟶
      (invSheaf i).obj.obj (op (i.liftCoborder ⁻¹ᵁ V)) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
      X.sheaf).hom.app (op (i.coborderRange.ι ''ᵁ V)) ≫
    (invSheaf i).obj.map (eqToHom (i.liftCoborder_preimage V)).op

/-- **The unit followed by the structural homomorphism is the map on sections induced by the
closed factor.**  This is the compatibility the whole comparison rests on: the composite
`𝒪_{i.coborderRange}(V) ⟶ (i^{-1}𝒪_X)(L ⁻¹ᵁ V) ⟶ 𝒪_Z(L ⁻¹ᵁ V)` is `i.liftCoborder.app V`, so
a section of the ideal sheaf of `L` is carried into the kernel ideal of the structural
homomorphism and a scalar is carried to the scalar it has to act as. -/
theorem coborderUnit_comp_structHom (V : i.coborderRange.toScheme.Opens) :
    coborderUnit i V ≫ (structHom i).hom.app (op (i.liftCoborder ⁻¹ᵁ V)) =
      i.liftCoborder.app V := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m : (invSheaf i).obj.obj (op (i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V))) ⟶
      (structSheaf Z).obj.obj (op (i.liftCoborder ⁻¹ᵁ V)) =>
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
        X.sheaf).hom.app (op (i.coborderRange.ι ''ᵁ V)) ≫ m)
    ((structHom i).hom.naturality (eqToHom (i.liftCoborder_preimage V)).op)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m : X.presheaf.obj (op (i.coborderRange.ι ''ᵁ V)) ⟶
      (structSheaf Z).obj.obj (op (i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V))) =>
      m ≫ (structSheaf Z).obj.map (eqToHom (i.liftCoborder_preimage V)).op)
    (Stacks.AlgebraPullbackQcoh.germ_comp_inverseImageStructureMap i
      (i.coborderRange.ι ''ᵁ V))) ?_
  exact (AlgebraicGeometry.liftCoborder_app i V).symm

/-- `Stacks.Conormal.Sites.coborderUnit_comp_structHom` on a section. -/
theorem coborderUnit_structHom_apply (V : i.coborderRange.toScheme.Opens)
    (r : ToType (i.coborderRange.toScheme.presheaf.obj (op V))) :
    ((structHom i).hom.app (op (i.liftCoborder ⁻¹ᵁ V))).hom ((coborderUnit i V).hom r) =
      (i.liftCoborder.app V).hom r :=
  ConcreteCategory.congr_hom (coborderUnit_comp_structHom i V) r

/-- **The unit carries a section of the ideal sheaf into the kernel ideal.**  The image under
the adjunction unit of the image in `𝒪_{i.coborderRange}` of a section of the ideal sheaf of
the closed factor is killed by the structural homomorphism. -/
theorem coborderUnit_idealSection_mem (V : i.coborderRange.toScheme.Opens)
    (s : (idealSheafLift i).val.obj (op V)) :
    (coborderUnit i V).hom (Stacks.Conormal.idealSection i.liftCoborder V s) ∈
      Stacks.Sites.Conormal.kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V)) :=
  (coborderUnit_structHom_apply i V _).trans
    (Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero
      i.liftCoborder V s)

/-- **The section of the kernel ideal attached to a section of the ideal sheaf of the closed
factor.**  Its conormal class is the value of the adjoint transpose of the comparison. -/
def kernelSection (V : i.coborderRange.toScheme.Opens)
    (s : (idealSheafLift i).val.obj (op V)) :
    Stacks.Sites.Conormal.kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V)) :=
  ⟨(coborderUnit i V).hom (Stacks.Conormal.idealSection i.liftCoborder V s),
    coborderUnit_idealSection_mem i V s⟩

/-- The attached section of the kernel ideal is additive. -/
theorem kernelSection_add (V : i.coborderRange.toScheme.Opens)
    (a b : (idealSheafLift i).val.obj (op V)) :
    kernelSection i V (a + b) = kernelSection i V a + kernelSection i V b :=
  Subtype.ext ((congrArg (coborderUnit i V).hom
    (map_add ((idealIota i).val.app (op V)).hom a b)).trans (map_add _ _ _))

/-- The attached section of the kernel ideal is semilinear over the unit: a scalar `r` of
`𝒪_{i.coborderRange}` acts through its image under `coborderUnit`. -/
theorem kernelSection_smul (V : i.coborderRange.toScheme.Opens)
    (r : ToType ((structureSheafRing i.coborderRange.toScheme.toRingedSpace).obj.obj (op V)))
    (a : (idealSheafLift i).val.obj (op V)) :
    kernelSection i V (r • a) = (coborderUnit i V).hom r • kernelSection i V a :=
  Subtype.ext ((congrArg (coborderUnit i V).hom
    (((idealIota i).val.app (op V)).hom.map_smul r a)).trans (map_mul _ _ _))

/-- **The unit is compatible with restriction.**  Restricting from `V` to `V'` and then applying
the unit is applying the unit and then restricting from `L ⁻¹ᵁ V` to `L ⁻¹ᵁ V'`.

The two restriction maps of `i^{-1}𝒪_X` occurring in the two composites have the same source and
target, so they agree: the morphisms of a preorder category are subsingletons. -/
theorem coborderUnit_naturality {V V' : i.coborderRange.toScheme.Opens} (f : V' ⟶ V) :
    i.coborderRange.toScheme.presheaf.map f.op ≫ coborderUnit i V' =
      coborderUnit i V ≫
        (invSheaf i).obj.map ((Opens.map i.liftCoborder.base).map f).op := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m : X.presheaf.obj (op (i.coborderRange.ι ''ᵁ V)) ⟶
      (invSheaf i).obj.obj (op (i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V'))) =>
      m ≫ (invSheaf i).obj.map (eqToHom (i.liftCoborder_preimage V')).op)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
        X.sheaf).hom.naturality (i.coborderRange.ι.opensFunctor.map f).op)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun m : (invSheaf i).obj.obj (op (i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V))) ⟶
        (invSheaf i).obj.obj (op (i.liftCoborder ⁻¹ᵁ V')) =>
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
        X.sheaf).hom.app (op (i.coborderRange.ι ''ᵁ V)) ≫ m) ?_) (Category.assoc _ _ _).symm
  exact Eq.trans ((invSheaf i).obj.map_comp _ _).symm
    (Eq.trans (congrArg (invSheaf i).obj.map (Subsingleton.elim _
      ((eqToHom (i.liftCoborder_preimage V)).op ≫
        ((Opens.map i.liftCoborder.base).map f).op)))
      ((invSheaf i).obj.map_comp _ _))

/-- `Stacks.Conormal.Sites.coborderUnit_naturality` on a section. -/
theorem coborderUnit_naturality_apply {V V' : i.coborderRange.toScheme.Opens} (f : V' ⟶ V)
    (r : ToType (i.coborderRange.toScheme.presheaf.obj (op V))) :
    (coborderUnit i V').hom ((i.coborderRange.toScheme.presheaf.map f.op).hom r) =
      ((invSheaf i).obj.map ((Opens.map i.liftCoborder.base).map f).op).hom
        ((coborderUnit i V).hom r) :=
  ConcreteCategory.congr_hom (coborderUnit_naturality i f) r

/-- The attached section of the kernel ideal is compatible with restriction. -/
theorem kernelSection_map {V V' : i.coborderRange.toScheme.Opens} (f : V' ⟶ V)
    (s : (idealSheafLift i).val.obj (op V)) :
    ((kernelSection i V' ((idealSheafLift i).val.map f.op s)) :
        ToType ((invSheaf i).obj.obj (op (i.liftCoborder ⁻¹ᵁ V')))) =
      ((invSheaf i).obj.map ((Opens.map i.liftCoborder.base).map f).op).hom
        (kernelSection i V s) :=
  (congrArg (coborderUnit i V').hom
      (PresheafOfModules.naturality_apply (idealIota i).val f.op s)).trans
    (coborderUnit_naturality_apply i f _)

/-! ### The adjoint transpose of the comparison -/

open Stacks.Sites.Conormal in
/-- **The adjoint transpose of the comparison, on sections.**  The conormal class of the image
under `Stacks.Conormal.Sites.coborderUnit` of a section of the ideal sheaf of the closed
factor. -/
def conormalTransposeApp (V : i.coborderRange.toScheme.Opens)
    (s : (idealSheafLift i).val.obj (op V)) :
    ToType ((sitesConormalSheaf i).val.obj (op (i.liftCoborder ⁻¹ᵁ V))) :=
  toAssociatedModule (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)
    (conormalPresheaf (structHom i).hom) (op (i.liftCoborder ⁻¹ᵁ V))
    ((kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V))).toCotangent
      (kernelSection i V s))

open Stacks.Sites.Conormal in
/-- The transpose is additive on sections. -/
theorem conormalTransposeApp_add (V : i.coborderRange.toScheme.Opens)
    (a b : (idealSheafLift i).val.obj (op V)) :
    conormalTransposeApp i V (a + b) =
      conormalTransposeApp i V a + conormalTransposeApp i V b :=
  (congrArg (toAssociatedModule (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)
      (conormalPresheaf (structHom i).hom) (op (i.liftCoborder ⁻¹ᵁ V)))
    ((congrArg (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V))).toCotangent
      (kernelSection_add i V a b)).trans (map_add _ _ _))).trans
    (toAssociatedModule_add (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)
      (conormalPresheaf (structHom i).hom) (op (i.liftCoborder ⁻¹ᵁ V)) _ _)

open Stacks.Sites.Conormal in
/-- **The scalar identification.**  The class modulo the kernel ideal of the image of a scalar
under the unit acts, through the inclusion of the image presheaf into `𝒪_Z`, as the image of
that scalar under the structure-sheaf component of the closed factor.  This is the scalar the
pushforward module structure makes it act as. -/
theorem quotientToRingSheaf_mk_coborderUnit (V : i.coborderRange.toScheme.Opens)
    (r : ToType (i.coborderRange.toScheme.presheaf.obj (op V))) :
    (quotientToRingSheaf (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)).app
        (op (i.liftCoborder ⁻¹ᵁ V))
        (Ideal.Quotient.mk (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V)))
          ((coborderUnit i V).hom r)) =
      ((structureSheafHom i.liftCoborder.toLRSHom.toShHom).hom.app (op V)).hom r :=
  coborderUnit_structHom_apply i V r

open Stacks.Sites.Conormal in
/-- The transpose is semilinear on sections: a scalar of `𝒪_{i.coborderRange}` acts through the
class modulo the kernel ideal of its image under the unit. -/
theorem conormalTransposeApp_smul (V : i.coborderRange.toScheme.Opens)
    (r : ToType ((structureSheafRing i.coborderRange.toScheme.toRingedSpace).obj.obj (op V)))
    (a : (idealSheafLift i).val.obj (op V)) :
    conormalTransposeApp i V (r • a) =
      (quotientToRingSheaf (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)).app
          (op (i.liftCoborder ⁻¹ᵁ V))
          (Ideal.Quotient.mk (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V)))
            ((coborderUnit i V).hom r)) •
        conormalTransposeApp i V a := by
  refine Eq.trans (congrArg (toAssociatedModule (siteJ Z) (invSheaf i) (structSheaf Z)
      (structHom i) (conormalPresheaf (structHom i).hom) (op (i.liftCoborder ⁻¹ᵁ V)))
    (show (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V))).toCotangent
          (kernelSection i V (r • a)) =
        (Ideal.Quotient.mk (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V)))
            ((coborderUnit i V).hom r)) •
          (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V))).toCotangent
            (kernelSection i V a) from ?_)) ?_
  · refine Eq.trans (congrArg (kernelIdeal (structHom i).hom
        (op (i.liftCoborder ⁻¹ᵁ V))).toCotangent (kernelSection_smul i V r a)) ?_
    refine Eq.trans (map_smul _ _ _) ?_
    exact (IsScalarTower.algebraMap_smul
      (ToType ((invSheaf i).obj.obj (op (i.liftCoborder ⁻¹ᵁ V))) ⧸
        kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V))) _ _).symm
  · exact toAssociatedModule_smul (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)
      (conormalPresheaf (structHom i).hom) (op (i.liftCoborder ⁻¹ᵁ V)) _ _

open Stacks.Sites.Conormal in
/-- The transpose is compatible with restriction. -/
theorem conormalTransposeApp_map {V V' : i.coborderRange.toScheme.Opens} (f : V' ⟶ V)
    (s : (idealSheafLift i).val.obj (op V)) :
    conormalTransposeApp i V' ((idealSheafLift i).val.map f.op s) =
      (sitesConormalSheaf i).val.map ((Opens.map i.liftCoborder.base).map f).op
        (conormalTransposeApp i V s) := by
  refine Eq.trans (congrArg (toAssociatedModule (siteJ Z) (invSheaf i) (structSheaf Z)
      (structHom i) (conormalPresheaf (structHom i).hom) (op (i.liftCoborder ⁻¹ᵁ V')))
    (show (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V'))).toCotangent
          (kernelSection i V' ((idealSheafLift i).val.map f.op s)) =
        (conormalPresheaf (structHom i).hom).map
            ((Opens.map i.liftCoborder.base).map f).op
          ((kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V))).toCotangent
            (kernelSection i V s)) from
      congrArg (kernelIdeal (structHom i).hom (op (i.liftCoborder ⁻¹ᵁ V'))).toCotangent
        (Subtype.ext (kernelSection_map i f s)))) ?_
  exact toAssociatedModule_map (siteJ Z) (invSheaf i) (structSheaf Z) (structHom i)
    (conormalPresheaf (structHom i).hom) ((Opens.map i.liftCoborder.base).map f).op _

/-- **The adjoint transpose of the comparison.**  The morphism `ℐ ⟶ L_*(I/I²)` of sheaves of
`𝒪_{i.coborderRange}`-modules carrying a section of the ideal sheaf of the closed factor to the
conormal class of its image under `Stacks.Conormal.Sites.coborderUnit`. -/
def conormalTranspose :
    idealSheafLift i ⟶
      (modulePushforward i.liftCoborder.toLRSHom.toShHom).obj (sitesConormalSheaf i) where
  val :=
    { app := fun V => ModuleCat.ofHom
        (X := (idealSheafLift i).val.obj V)
        (Y := ((modulePushforward i.liftCoborder.toLRSHom.toShHom).obj
          (sitesConormalSheaf i)).val.obj V)
        { toFun := fun s => conormalTransposeApp i V.unop s
          map_add' := conormalTransposeApp_add i V.unop
          map_smul' := fun r a =>
            ((conormalTransposeApp_smul i V.unop r a).trans
              (congrArg (fun t => t • conormalTransposeApp i V.unop a)
                (quotientToRingSheaf_mk_coborderUnit i V.unop r))).trans
              (ModuleCat.restrictScalars.smul_def
                ((structureSheafHom i.liftCoborder.toLRSHom.toShHom).hom.app V).hom
                (M := (sitesConormalSheaf i).val.obj
                  (op (i.liftCoborder ⁻¹ᵁ V.unop))) r
                (conormalTransposeApp i V.unop a)).symm }
      naturality := fun f =>
        ModuleCat.hom_ext (LinearMap.ext fun s => conormalTransposeApp_map i f.unop s) }

/-! ### The comparison -/

/-- **The conormal comparison.**  The canonical morphism from the geometric conormal sheaf of an
immersion to the sites-level conormal sheaf of its structural homomorphism: the adjoint
transpose, along the module pullback–pushforward adjunction of the canonical closed factor, of
`Stacks.Conormal.Sites.conormalTranspose`. -/
def conormalComparison : Stacks.Conormal.conormalSheaf i ⟶ sitesConormalSheaf i :=
  ((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).homEquiv
    (idealSheafLift i) (sitesConormalSheaf i)).symm (conormalTranspose i)

/-- The comparison is the morphism out of the conormal sheaf classified by the transpose. -/
theorem unit_comp_conormalComparison :
    (modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (idealSheafLift i) ≫
        (modulePushforward i.liftCoborder.toLRSHom.toShHom).map (conormalComparison i) =
      conormalTranspose i :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The comparison on the canonical local sections.**  The image under the unit of the module
pullback–pushforward adjunction of a section `s` of the ideal sheaf of the closed factor is the
local section of the geometric conormal sheaf on which
`Stacks.Conormal.conormalSheafStalkEquivCotangent` is normalised, and the comparison carries it
to the conormal class of `Stacks.Conormal.Sites.coborderUnit s`.  This pins the comparison
down. -/
theorem conormalComparison_unit (V : i.coborderRange.toScheme.Opens)
    (s : (idealSheafLift i).val.obj (op V)) :
    (conormalComparison i).val.app (op (i.liftCoborder ⁻¹ᵁ V))
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
            (idealSheafLift i)).val.app (op V) s) =
      conormalTransposeApp i V s :=
  congrArg (fun t : idealSheafLift i ⟶
      (modulePushforward i.liftCoborder.toLRSHom.toShHom).obj (sitesConormalSheaf i) =>
    t.val.app (op V) s) (unit_comp_conormalComparison i)

/-! ### The comparison of local rings -/

/-- The image of `z` under `i` is the point of `X` underlying the image of `z` under the
canonical closed factor.  This is `AlgebraicGeometry.Scheme.Hom.liftCoborder_ι` read on
points. -/
theorem base_liftCoborder (z : Z) : i.base z = (i.liftCoborder.base z).val :=
  congrArg (fun f : Z ⟶ X => f.base z) i.liftCoborder_ι.symm

/-- **The local ring of the coborder neighbourhood is the local ring of `X`.**  The comparison
`𝒪_{X, i z} ≅ 𝒪_{i.coborderRange, L z}`: the transport along
`Stacks.Conormal.Sites.base_liftCoborder` followed by the inverse of Mathlib's stalk comparison
for an open subscheme. -/
def coborderStalkIso (z : Z) :
    X.presheaf.stalk (i.base z) ≅
      i.coborderRange.toScheme.presheaf.stalk (i.liftCoborder.base z) :=
  X.presheaf.stalkCongr (Inseparable.of_eq (base_liftCoborder i z)) ≪≫
    (i.coborderRange.stalkIso (i.liftCoborder.base z)).symm

/-- The comparison of local rings carries the germ at `i z` of a section of `𝒪_X` over
`i.coborderRange.ι ''ᵁ V` to the germ at `L z` of that same section, read over `V`. -/
theorem coborderStalkIso_germ (z : Z) (V : i.coborderRange.toScheme.Opens)
    (hz : i.liftCoborder.base z ∈ V) (hz' : i.base z ∈ i.coborderRange.ι ''ᵁ V)
    (a : ToType (i.coborderRange.toScheme.presheaf.obj (op V))) :
    (coborderStalkIso i z).hom.hom
        ((X.presheaf.germ (i.coborderRange.ι ''ᵁ V) (i.base z) hz').hom a) =
      (i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hz).hom a := by
  refine Eq.trans (CommRingCat.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg
      (i.coborderRange.stalkIso (i.liftCoborder.base z)).inv.hom
    (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hz'
      (Inseparable.of_eq (base_liftCoborder i z)).ge a)) ?_
  exact ConcreteCategory.congr_hom
    (i.coborderRange.germ_stalkIso_inv V (i.liftCoborder.base z) hz) a

/-- **The comparison of local rings is compatible with the stalk maps.**  Followed by the stalk
map of the closed factor it is the stalk map of `i`.  This is
`AlgebraicGeometry.Scheme.Opens.stalkIso_inv`, which identifies the comparison with the stalk map
of the open immersion, together with the composition law for stalk maps read along
`AlgebraicGeometry.Scheme.Hom.liftCoborder_ι`. -/
theorem coborderStalkIso_comp_stalkMap (z : Z) :
    (coborderStalkIso i z).hom ≫ i.liftCoborder.stalkMap z = i.stalkMap z := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m : X.presheaf.stalk (i.liftCoborder.base z).val ⟶
        Z.presheaf.stalk z =>
      (X.presheaf.stalkCongr (Inseparable.of_eq (base_liftCoborder i z))).hom ≫ m)
    (show (i.coborderRange.stalkIso (i.liftCoborder.base z)).inv ≫
          i.liftCoborder.stalkMap z =
        (X.presheaf.stalkCongr (Inseparable.of_eq (base_liftCoborder i z))).inv ≫
          i.stalkMap z from ?_)) ?_
  · refine Eq.trans (congrArg (fun m : X.presheaf.stalk (i.liftCoborder.base z).val ⟶
          i.coborderRange.toScheme.presheaf.stalk (i.liftCoborder.base z) =>
        m ≫ i.liftCoborder.stalkMap z)
      (i.coborderRange.stalkIso_inv (i.liftCoborder.base z))) ?_
    refine Eq.trans (Scheme.Hom.stalkMap_comp i.liftCoborder i.coborderRange.ι z).symm ?_
    exact Scheme.Hom.stalkMap_congr_hom (i.liftCoborder ≫ i.coborderRange.ι) i
      i.liftCoborder_ι z
  · exact Iso.hom_inv_id_assoc _ _

omit [IsImmersion i] in
/-- **The comparison `(i^{-1}𝒪_X)_z ≅ 𝒪_{X, i z}` on germs.**  The germ at `z` of the image of
a section `a` of `𝒪_X` over `W` under the unit of the inverse-image/direct-image adjunction is
carried to the germ at `i z` of `a`.  This is
`Stacks.Conormal.Sites.stalkInvIso_inv_germ` with the isomorphism moved to the other side. -/
theorem stalkInvIso_hom_germ (z : Z) (W : X.Opens) (hW : i.base z ∈ W) (hzW : z ∈ i ⁻¹ᵁ W)
    (a : ToType (X.presheaf.obj (op W))) :
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z).hom.hom
        ((TopCat.Presheaf.germ (invSheaf i).obj (i ⁻¹ᵁ W) z hzW).hom
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
            X.sheaf).hom.app (op W)).hom a)) =
      (X.presheaf.germ W (i.base z) hW).hom a :=
  (congrArg (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z).hom.hom
      (stalkInvIso_inv_germ i z W hW a).symm).trans
    (CategoryTheory.Iso.inv_hom_id_apply
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z) _)
/-! ### The stalkwise comparison and the cotangent transport -/

/-- **The comparison of local rings `(i^{-1}𝒪_X)_z ≅ 𝒪_{i.coborderRange, L z}`.**  The stalk of
the inverse image of the structure sheaf, identified with the local ring of `X` at `i z` and then
with the local ring of the coborder neighbourhood at `L z`. -/
def stalkComparison (z : Z) :
    TopCat.Presheaf.stalk (invSheaf i).obj z ≅
      i.coborderRange.toScheme.presheaf.stalk (i.liftCoborder.base z) :=
  Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z ≪≫ coborderStalkIso i z

/-- **The comparison of local rings is compatible with the structural homomorphism.**  Followed
by the stalk map of the closed factor it is the stalk of `i^{-1}𝒪_X ⟶ 𝒪_Z`.  This is the one
equation the identification of the two kernel ideals on stalks rests on. -/
theorem stalkComparison_comp_stalkMap (z : Z) :
    (stalkComparison i z).hom ≫ i.liftCoborder.stalkMap z =
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} z).map (structHom i).hom := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m : X.presheaf.stalk (i.base z) ⟶ Z.presheaf.stalk z =>
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z).hom ≫ m)
    (coborderStalkIso_comp_stalkMap i z)) ?_
  exact Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap i z

/-- **The two ideals agree on stalks.**  The kernel on the stalk at `z` of the structural
homomorphism is the inverse image, along the comparison of local rings, of the kernel of
`𝒪_{i.coborderRange, L z} ⟶ 𝒪_{Z,z}`.  Immediate from
`Stacks.Conormal.Sites.stalkComparison_comp_stalkMap`. -/
theorem stalkKernelIdeal_eq_comap (z : Z) :
    Stacks.Sites.Conormal.stalkKernelIdeal (structHom i).hom z =
      (RingHom.ker (i.liftCoborder.stalkMap z).hom).comap (stalkComparison i z).hom.hom :=
  (congrArg RingHom.ker
      ((congrArg CommRingCat.Hom.hom (stalkComparison_comp_stalkMap i z).symm).trans
        (CommRingCat.hom_comp _ _))).trans
    (RingHom.comap_ker _ _).symm

/-- **The comparison of local rings on the germs the construction produces.**  It carries the
germ of `Stacks.Conormal.Sites.kernelSection` of a section `s` of the ideal sheaf of the closed
factor to the germ of the image of `s` in `𝒪_{i.coborderRange}`.  These are exactly the two
elements the two stalk identifications of the conormal sheaves are normalised on. -/
theorem stalkComparison_germ_kernelSection (z : Z) (V : i.coborderRange.toScheme.Opens)
    (hz : i.liftCoborder.base z ∈ V) (hzV : z ∈ i.liftCoborder ⁻¹ᵁ V)
    (hzW : i.base z ∈ i.coborderRange.ι ''ᵁ V)
    (s : (idealSheafLift i).val.obj (op V)) :
    (stalkComparison i z).hom.hom
        ((TopCat.Presheaf.germ (invSheaf i).obj (i.liftCoborder ⁻¹ᵁ V) z hzV).hom
          (kernelSection i V s)) =
      (i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hz).hom
        (Stacks.Conormal.idealSection i.liftCoborder V s) := by
  refine Eq.trans (CommRingCat.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg (coborderStalkIso i z).hom.hom
    (show (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z).hom.hom
          ((TopCat.Presheaf.germ (invSheaf i).obj (i.liftCoborder ⁻¹ᵁ V) z hzV).hom
            (kernelSection i V s)) =
        (X.presheaf.germ (i.coborderRange.ι ''ᵁ V) (i.base z) hzW).hom
          (Stacks.Conormal.idealSection i.liftCoborder V s) from ?_)) ?_
  · refine Eq.trans (congrArg
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso i z).hom.hom
      (show (TopCat.Presheaf.germ (invSheaf i).obj (i.liftCoborder ⁻¹ᵁ V) z hzV).hom
            (kernelSection i V s) =
          (TopCat.Presheaf.germ (invSheaf i).obj (i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V)) z hzW).hom
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
              X.sheaf).hom.app (op (i.coborderRange.ι ''ᵁ V))).hom
              (Stacks.Conormal.idealSection i.liftCoborder V s)) from ?_)) ?_
    · exact TopCat.Presheaf.germ_res_apply (invSheaf i).obj
        (eqToHom (i.liftCoborder_preimage V)) z hzV _
    · exact stalkInvIso_hom_germ i z (i.coborderRange.ι ''ᵁ V) hzW hzW _
  · exact coborderStalkIso_germ i z V hz hzW _

attribute [local instance] Stacks.Conormal.idealSheafStalkModule
  Stacks.Conormal.conormalSheafStalkModule Stacks.Conormal.stalkMapAlgebra
  Stacks.Conormal.cotangentStalkModule

/-- **Every element of the stalk of the geometric conormal sheaf is the germ of a canonical local
section.**  Every element of `(𝒞_{Z/X})_z` is the germ at `z` of the image, under the unit of the
module pullback–pushforward adjunction, of a section of the ideal sheaf of the closed factor over
some open neighbourhood of `L z`.

This is what makes the germ formula for
`Stacks.Conormal.conormalSheafStalkEquivCotangent` a complete description of that
identification, and it is what the stalkwise comparison below is proved on.  It comes from the
surjectivity of `Ideal.toCotangent` together with
`Stacks.AlgebraicGeometry.RegularIdealSheaf.stalkIdeal_definingIdealOfHom_eq_ker`: every element
of the kernel on local rings is the germ of a section of the defining ideal sheaf, and such a
section lifts to a section of the ideal sheaf. -/
theorem exists_germ_unit (z : Z)
    (ξ : ToType (TopCat.Presheaf.stalk (C := Ab.{u})
      (Stacks.Conormal.conormalSheaf i).val.presheaf z)) :
    ∃ (V : i.coborderRange.toScheme.Opens) (hz : i.liftCoborder.base z ∈ V)
      (s : (idealSheafLift i).val.obj (op V)),
      ξ = TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf i).val.presheaf
        ((opensMap i.liftCoborder.toLRSHom.toShHom).obj V) z hz
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (idealSheafLift i)).val.app (op V) s) := by
  obtain ⟨b, hb⟩ := (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent_surjective
    (Stacks.Conormal.conormalSheafStalkEquivCotangent i z ξ)
  have hmem := Eq.mpr (congrArg
      (fun I : Ideal (ToType (i.coborderRange.toScheme.presheaf.stalk
          (i.liftCoborder.base z))) => b.1 ∈ I)
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.stalkIdeal_definingIdealOfHom_eq_ker
        i.liftCoborder z)) b.2
  obtain ⟨V, hz, s', hs', hgerm⟩ := (Stacks.RingedSpace.mem_stalkIdeal_iff _).mp hmem
  obtain ⟨x, hx⟩ := Stacks.Conormal.AffineCotangent.Sections.exists_section_of_app_eq_zero
    (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i.liftCoborder.toLRSHom.toShHom)) (op V) s' hs'
  refine ⟨V, hz, x, (Stacks.Conormal.conormalSheafStalkEquivCotangent i z).injective ?_⟩
  refine hb.symm.trans ?_
  refine Eq.trans ?_ (Stacks.Conormal.conormalSheafStalkEquivCotangent_germ i z V hz x).symm
  exact congrArg (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent
    (Subtype.ext (hgerm.symm.trans
      (congrArg (i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hz).hom
        hx.symm)))

/-- The kernel of the map of local rings is carried into the kernel ideal on stalks by the
inverse of the comparison of local rings. -/
theorem ker_le_comap_stalkComparison_inv (z : Z) :
    RingHom.ker (i.liftCoborder.stalkMap z).hom ≤
      (Stacks.Sites.Conormal.stalkKernelIdeal (structHom i).hom z).comap
        (stalkComparison i z).inv.hom := fun {b} hb =>
  Eq.mpr (congrArg (fun I : Ideal (ToType (TopCat.Presheaf.stalk (invSheaf i).obj z)) =>
        (stalkComparison i z).inv.hom b ∈ I) (stalkKernelIdeal_eq_comap i z))
    (Eq.mpr (congrArg
      (fun y : ToType (i.coborderRange.toScheme.presheaf.stalk (i.liftCoborder.base z)) =>
        y ∈ RingHom.ker (i.liftCoborder.stalkMap z).hom)
      (CategoryTheory.Iso.inv_hom_id_apply (stalkComparison i z) b)) hb)

/-- **The transport of cotangent modules along the comparison of local rings.**  The comparison
`(i^{-1}𝒪_X)_z ≅ 𝒪_{i.coborderRange, L z}` carries the kernel ideal on stalks onto the kernel of
the map of local rings, so it induces a bijection of the two cotangent modules.  It is given on
conormal classes by `Stacks.Sites.Conormal.cotangentMap`, and it is an `Equiv` because both
directions are instances of that construction and they are mutually inverse on classes. -/
def cotangentTransport (z : Z) :
    (RingHom.ker (i.liftCoborder.stalkMap z).hom).Cotangent ≃
      (Stacks.Sites.Conormal.stalkKernelIdeal (structHom i).hom z).Cotangent where
  toFun := Stacks.Sites.Conormal.cotangentMap _ _ (stalkComparison i z).inv.hom
    (ker_le_comap_stalkComparison_inv i z)
  invFun := Stacks.Sites.Conormal.cotangentMap _ _ (stalkComparison i z).hom.hom
    (le_of_eq (stalkKernelIdeal_eq_comap i z))
  left_inv x := by
    obtain ⟨y, rfl⟩ := (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent_surjective x
    exact congrArg (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent
      (Subtype.ext (CategoryTheory.Iso.inv_hom_id_apply (stalkComparison i z) y.1))
  right_inv x := by
    obtain ⟨y, rfl⟩ :=
      (Stacks.Sites.Conormal.stalkKernelIdeal (structHom i).hom z).toCotangent_surjective x
    exact congrArg (Stacks.Sites.Conormal.stalkKernelIdeal (structHom i).hom z).toCotangent
      (Subtype.ext (CategoryTheory.Iso.hom_inv_id_apply (stalkComparison i z) y.1))

/-- A point of `Z` whose image under the closed factor lies in an open `V` of the coborder
neighbourhood has its image under `i` in `i.coborderRange.ι ''ᵁ V`. -/
theorem mem_image_of_mem (z : Z) {V : i.coborderRange.toScheme.Opens}
    (hz : i.liftCoborder.base z ∈ V) : i.base z ∈ i.coborderRange.ι ''ᵁ V :=
  Eq.mpr (congrArg (fun y : ↥X => y ∈ i.coborderRange.ι ''ᵁ V) (base_liftCoborder i z))
    ((AlgebraicGeometry.Scheme.Opens.mem_ι_image_iff (U := i.coborderRange)).mpr hz)

/-- **The stalk of the comparison is the transport of cotangent modules.**  Read through the two
germ-pinned identifications of the stalks with cotangent modules —
`Stacks.Conormal.conormalSheafStalkEquivCotangent` on the geometric side and
`Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv` on the sites side — the stalk at `z` of
the conormal comparison is `Stacks.Conormal.Sites.cotangentTransport`.

Both identifications are pinned on the germs of conormal classes, and
`Stacks.Conormal.Sites.exists_germ_unit` says those germs exhaust the stalk, so the two sides
are compared on a single kind of element; there the comparison is
`Stacks.Conormal.Sites.conormalComparison_unit` and the identification of the germs is
`Stacks.Conormal.Sites.stalkComparison_germ_kernelSection`. -/
theorem conormalSheafStalkLinearEquiv_stalkMap (z : Z)
    (ξ : ToType (TopCat.Presheaf.stalk (C := Ab.{u})
      (Stacks.Conormal.conormalSheaf i).val.presheaf z)) :
    Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv (invSheaf i) (structSheaf Z)
        (structHom i) z
      ((AlgebraicGeometry.SheafOfModules.stalkMap.{u}
        (structureSheafRing Z.toRingedSpace) z (conormalComparison i)).hom ξ) =
    cotangentTransport i z (Stacks.Conormal.conormalSheafStalkEquivCotangent i z ξ) := by
  obtain ⟨V, hz, s, rfl⟩ := exists_germ_unit i z ξ
  refine Eq.trans (congrArg (Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv
      (invSheaf i) (structSheaf Z) (structHom i) z)
    ((AlgebraicGeometry.SheafOfModules.stalkMap_germ.{u}
        (structureSheafRing Z.toRingedSpace) z (conormalComparison i)
        (i.liftCoborder ⁻¹ᵁ V) hz _).trans
      (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) (sitesConormalSheaf i).val.presheaf
          (i.liftCoborder ⁻¹ᵁ V) z hz).hom
        (conormalComparison_unit i V s)))) ?_
  refine Eq.trans (Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv_germ_toAssociatedModule
    (invSheaf i) (structSheaf Z) (structHom i) z (i.liftCoborder ⁻¹ᵁ V) hz
    (kernelSection i V s)) ?_
  refine Eq.trans ?_ (congrArg (cotangentTransport i z)
    (Stacks.Conormal.conormalSheafStalkEquivCotangent_germ i z V hz s)).symm
  exact congrArg (Stacks.Sites.Conormal.stalkKernelIdeal (structHom i).hom z).toCotangent
    (Subtype.ext ((CategoryTheory.Iso.hom_inv_id_apply (stalkComparison i z) _).symm.trans
      (congrArg (stalkComparison i z).inv.hom
        (stalkComparison_germ_kernelSection i z V hz hz (mem_image_of_mem i z hz) s))))

/-- **The comparison is bijective on every stalk.**  It is, up to the two identifications with
cotangent modules, the transport `Stacks.Conormal.Sites.cotangentTransport`, which is a
bijection. -/
theorem bijective_stalkMap_conormalComparison (z : Z) :
    Function.Bijective
      (AlgebraicGeometry.SheafOfModules.stalkMap.{u} (structureSheafRing Z.toRingedSpace) z
        (conormalComparison i)).hom := by
  have hb : Function.Bijective
      ((Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv (invSheaf i) (structSheaf Z)
          (structHom i) z) ∘
        (AlgebraicGeometry.SheafOfModules.stalkMap.{u} (structureSheafRing Z.toRingedSpace) z
          (conormalComparison i)).hom) := by
    rw [show (Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv (invSheaf i) (structSheaf Z)
            (structHom i) z) ∘
          (AlgebraicGeometry.SheafOfModules.stalkMap.{u} (structureSheafRing Z.toRingedSpace) z
            (conormalComparison i)).hom =
        (cotangentTransport i z) ∘
          (Stacks.Conormal.conormalSheafStalkEquivCotangent i z) from
      funext (conormalSheafStalkLinearEquiv_stalkMap i z)]
    exact (cotangentTransport i z).bijective.comp
      (Stacks.Conormal.conormalSheafStalkEquivCotangent i z).bijective
  exact (Function.Bijective.of_comp_iff'
    (Stacks.Sites.Conormal.conormalSheafStalkLinearEquiv (invSheaf i) (structSheaf Z)
      (structHom i) z).bijective _).mp hb

/-- **The conormal comparison is an isomorphism.**  A morphism of sheaves of modules on a space
which is bijective on every stalk is an isomorphism. -/
instance isIso_conormalComparison : IsIso (conormalComparison i) :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap (conormalComparison i)).2
    (bijective_stalkMap_conormalComparison i)

/-- **The conormal comparison isomorphism.**  For an immersion of schemes `i : Z ⟶ X` the
geometric conormal sheaf `𝒞_{Z/X}` of [Stacks, Tag 01R2] is the sites-level conormal sheaf
`I/I²` of the structural homomorphism `i^{-1}𝒪_X ⟶ 𝒪_Z`, which is the sheaf occurring in degree
`-1` of the naive cotangent complex of `i`. -/
def conormalComparisonIso : Stacks.Conormal.conormalSheaf i ≅ sitesConormalSheaf i :=
  asIso (conormalComparison i)

/-- **The conormal comparison isomorphism, in the category of modules on `Z`.**  The same
isomorphism as `Stacks.Conormal.Sites.conormalComparisonIso`, turned around and with its type
declared in `AlgebraicGeometry.Scheme.Modules Z`, which is the category the naive cotangent
complex of `i` lives in.  The abbreviations of this file are reducible, so the left-hand side is
the sheaf occurring in degree `-1` of
`AlgebraicGeometry.Scheme.naiveCotangentComplex`'s presentation of `𝒪_Z` over `i^{-1}𝒪_X`,
spelled out.

The local-surjectivity instance is `Stacks.Conormal.Sites.isLocallySurjective_structHom`; a
consumer who writes the sites-level sheaf out with `AlgebraicGeometry.inverseImageStructureMap i`
in place of `Stacks.Conormal.Sites.structHom i` has to supply it by hand, for the reason given in
the implementation notes above. -/
@[sga "6 VII 1.6"]
def sitesConormalSheafIsoConormalSheaf :
    sitesConormalSheaf i ≅ (Stacks.Conormal.conormalSheaf i : Z.Modules) :=
  (conormalComparisonIso i).symm

end Stacks.Conormal.Sites

end

end
