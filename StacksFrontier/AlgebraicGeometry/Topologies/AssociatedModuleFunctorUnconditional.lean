module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSiteAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAssociatedModule

/-!
# The functor `𝓕 ↦ 𝓕ᵃ` of Tag 03DX, with no hypothesis, on all seven sites

`Stacks.Sites.associatedSheafFunctor` builds the functor `𝓕 ↦ 𝓕ᵃ` on a site of schemes over
`S` from two sheaf conditions: that the presheaf of global functions is a sheaf, and that the
presheaf of pullback sections of every quasi-coherent module is a sheaf.  On every site
Tag 03DX mentions both are theorems, because the presenting functor into the schemes over `S`
is continuous for the localized fpqc topology, and restriction along a continuous functor
carries sheaves to sheaves.

This file performs that discharge once, generically, and then instantiates it at the seven
sites of the tag: the big `τ`-sites for `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`
(clause (1)) and the small Zariski and small étale sites (clause (2)).

## Main definitions

* `Stacks.EtaleCohomology.associatedSheafFunctorOfIsContinuous`: `𝓕 ↦ 𝓕ᵃ` as a functor
  `QCoh(𝒪_S) ⥤ Mod(𝒪_C)` on any site `C` of schemes over `S` presented by a functor continuous
  for the localized fpqc topology.  No sheaf condition is a hypothesis.
* `AlgebraicGeometry.overAssociatedModuleFunctor`: the instantiation at the localized big
  `τ`-site, **uniform in `τ`**, i.e. the forward functor of Tag 03DX (1) at all five
  topologies at once.
* `AlgebraicGeometry.SmallZariski.associatedSheafFunctor` and
  `AlgebraicGeometry.SmallEtale.associatedSheafFunctorUnconditional`: the forward functor of
  Tag 03DX (2) at `τ = Zariski` and at `τ = étale`.
* `AlgebraicGeometry.BigEtaleOver.associatedSheafFunctorUnconditional` and
  `AlgebraicGeometry.BigFppfOver.associatedSheafFunctorUnconditional`: the two named big-site
  instances, with no sheaf condition as an argument.

## Main results

* `Stacks.EtaleCohomology.associatedSheafFunctorOfIsContinuous_obj` and its seven site-level
  companions: the value of the functor at `𝓕` is the associated module of Tag 03DU, so the
  functor really is `𝓕 ↦ 𝓕ᵃ` and not merely some functor between the two categories.
* `Stacks.EtaleCohomology.associatedSheafFunctorOfIsContinuous_map_val_app_apply` and its
  companions: on sections over an object `T/S` of the site, the map induced by `φ : 𝓕 ⟶ 𝓖` is
  `Γ(T, T.hom^* φ)`.  This is the morphism clause of Tag 03DX.

## Implementation notes

The three declarations
`AlgebraicGeometry.BigEtaleOver.associatedSheafFunctor`,
`AlgebraicGeometry.SmallEtale.associatedSheafFunctor` and
`AlgebraicGeometry.BigFppfOver.associatedSheafFunctor` of
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor` remain, and carry,
respectively, the fpqc sheaf condition of Tag 03DT and the sheaf condition for the associated
presheaf on the big fppf site as arguments.  Both arguments are theorems —
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'` for the first, and
`AlgebraicGeometry.isSheaf_overAssociatedPresheaf` for the second.  The unconditional versions
are `AlgebraicGeometry.BigEtaleOver.associatedSheafFunctorUnconditional`,
`AlgebraicGeometry.SmallEtale.associatedSheafFunctorUnconditional` and
`AlgebraicGeometry.BigFppfOver.associatedSheafFunctorUnconditional`, defined here with no
argument but `B`, `S` and `hS`, as instances of the generic construction.

Going through `Stacks.EtaleCohomology.structureSheafOfIsContinuous` rather than through each
site's own structure sheaf is what makes the seven instantiations one-liners: that definition is
`Stacks.Sites.siteStructureSheaf` at the continuity-derived sheaf condition, the sheaf condition
is a proposition, and each site's structure sheaf is *defined* as the former, so the types agree
by `rfl` in every case.

No `stacks` attribute is claimed.  Tag 03DX asserts that this functor is an *equivalence*, and
neither its corestriction to the quasi-coherent modules of the site (Tag 03DV), nor its full
faithfulness (Tag 0GN7), nor its essential surjectivity is proved here.  Tag 03DU is the
object-level construction and is tagged where it is built.

Tag 0GN7 itself is discharged elsewhere, for the *pullback* presentation of this same functor —
the one the source's own proof uses, Remark 03FH — at every site the lemma quantifies over:
`AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh` for the big `τ`-site
uniformly in `τ`, `AlgebraicGeometry.SmallEtale.fullyFaithfulAssociatedModuleQcoh'` at the small
étale site, and `AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedModuleQcoh` at the small
Zariski site.  What identifies that presentation with the sections one built here is Tag 070S,
object by object: `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`,
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf` and
`AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`.  At `τ = Zariski` that
identification is available as an isomorphism of *functors*,
`AlgebraicGeometry.SmallZariski.associatedModuleQcohIsoAssociatedSheafFunctor`, which is why
`AlgebraicGeometry.SmallZariski.associatedSheafFunctor` — the small Zariski functor built here —
does carry 0GN7, on
`AlgebraicGeometry.SmallZariski.fullyFaithfulAssociatedSheafFunctor`.  The functor-level
identification is what the other six sites lack, not the full faithfulness.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
  (K : GrothendieckTopology C)
  [toOver.IsContinuous K (Scheme.fpqcTopology.{u}.over S)]

/-- **The functor `𝓕 ↦ 𝓕ᵃ` of Tag 03DX, with no hypothesis.**  On a site of schemes over `S`
presented by a functor continuous for the localized fpqc topology, a quasi-coherent
`𝒪_S`-module `𝓕` is sent to the sheaf of `𝒪`-modules of Tag 03DU, whose sections over an object
`T/S` are `Γ(T, T.hom^* 𝓕)`, and a morphism to the maps induced on those sections.

Both sheaf conditions `Stacks.Sites.associatedSheafFunctor` asks for are supplied by continuity,
so no sheafification occurs and nothing is assumed. -/
public noncomputable def associatedSheafFunctorOfIsContinuous :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheafOfIsContinuous S toOver K) :=
  Stacks.Sites.associatedSheafFunctor S toOver K
    (isSheaf_structurePresheaf_of_isContinuous S toOver K)
    fun M hM => @isSheaf_associatedPresheaf_of_isContinuous S M hM C _ toOver K _

/-- The value of `Stacks.EtaleCohomology.associatedSheafFunctorOfIsContinuous` at `𝓕` is the
associated module `𝓕ᵃ` of Tag 03DU. -/
@[simp]
public theorem associatedSheafFunctorOfIsContinuous_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (associatedSheafFunctorOfIsContinuous S toOver K).obj F =
      @associatedModuleOfIsContinuous S F.obj F.property C _ toOver K _ :=
  rfl

/-- **The morphism clause of Tag 03DX, with no hypothesis.**  On sections over an object `T/S`
of the site, the map `𝓕ᵃ ⟶ 𝓖ᵃ` induced by `φ : 𝓕 ⟶ 𝓖` is the map on global sections of the
pullback of `φ` to `T`. -/
@[simp]
public theorem associatedSheafFunctorOfIsContinuous_map_val_app_apply
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : Cᵒᵖ) (m : ((associatedSheafFunctorOfIsContinuous S toOver K).obj F).val.obj X) :
    (((associatedSheafFunctorOfIsContinuous S toOver K).map φ).val.app X) m =
      ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map φ.hom).app ⊤ m :=
  rfl

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-- **The forward functor of Tag 03DX (1), uniform in `τ`.**  For `τ` ranging over Zariski,
étale, smooth, syntomic and fppf, the assignment `𝓕 ↦ 𝓕ᵃ` of Tag 03DU (3) is a functor from the
quasi-coherent `𝒪_S`-modules to the sheaves of `𝒪`-modules on the big `τ`-site of `S`.

No sheaf condition is a hypothesis: `AlgebraicGeometry.isContinuous_overToSlice_fpqc` supplies
both, uniformly in `τ`. -/
public noncomputable def overAssociatedModuleFunctor :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (overStructureSheaf τ B S hS) :=
  Stacks.EtaleCohomology.associatedSheafFunctorOfIsContinuous S (overToSlice τ B S hS)
    (overTopology τ B S hS)

/-- The value of the big `τ`-site functor at `𝓕` is the associated module `𝓕ᵃ` of
Tag 03DU (3). -/
@[simp]
public theorem overAssociatedModuleFunctor_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (overAssociatedModuleFunctor τ B S hS).obj F =
      @overAssociatedModule τ B S hS F.obj F.property :=
  rfl

/-- **The morphism clause of Tag 03DX (1), uniform in `τ`.**  On sections over an object `T/S`
of the big `τ`-site, the map induced by `φ : 𝓕 ⟶ 𝓖` is `Γ(T, T.hom^* φ)`. -/
@[simp]
public theorem overAssociatedModuleFunctor_map_val_app_apply
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : (Over (base B S hS))ᵒᵖ)
    (m : ((overAssociatedModuleFunctor τ B S hS).obj F).val.obj X) :
    (((overAssociatedModuleFunctor τ B S hS).map φ).val.app X) m =
      ((Scheme.Modules.pullback ((overToSlice τ B S hS).obj X.unop).hom).map φ.hom).app ⊤ m :=
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.BigEtaleOver

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor `𝓕 ↦ 𝓕ᵃ` on the big étale site, with no hypothesis.**  The `τ = étale`
instance of `AlgebraicGeometry.overAssociatedModuleFunctor`.

The conditional version `AlgebraicGeometry.BigEtaleOver.associatedSheafFunctor` carries the
fpqc sheaf condition of Tag 03DT as an argument; that argument is a theorem,
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`, and this one carries none. -/
public noncomputable def associatedSheafFunctorUnconditional :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  overAssociatedModuleFunctor .etale B S hS

/-- The value of the big étale functor at `𝓕` is the associated module of Tag 03DU (3). -/
@[simp]
public theorem associatedSheafFunctorUnconditional_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (associatedSheafFunctorUnconditional B S hS).obj F =
      @overAssociatedModule .etale B S hS F.obj F.property :=
  rfl

/-- The morphism clause of Tag 03DX (1) at `τ = étale`. -/
@[simp]
public theorem associatedSheafFunctorUnconditional_map_val_app_apply
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : (BigEtaleOver B S hS)ᵒᵖ)
    (m : ((associatedSheafFunctorUnconditional B S hS).obj F).val.obj X) :
    (((associatedSheafFunctorUnconditional B S hS).map φ).val.app X) m =
      ((Scheme.Modules.pullback ((Over.post B.inclusion).obj X.unop).hom).map φ.hom).app ⊤ m :=
  rfl

end AlgebraicGeometry.BigEtaleOver

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor `𝓕 ↦ 𝓕ᵃ` on the big fppf site, with no hypothesis.**  The `τ = fppf`
instance of `AlgebraicGeometry.overAssociatedModuleFunctor`.

The conditional version `AlgebraicGeometry.BigFppfOver.associatedSheafFunctor` carries the
sheaf condition for the associated presheaf as an argument, because the route through
`Stacks.Sites.isSheaf_addCommGrpCat_op_comp_of_precoverage` needs the chosen bounded covering
families of the site to be stable under base change.  The route taken here goes through
continuity of `AlgebraicGeometry.overToSlice` instead, which needs cover preservation alone, so
this one carries no argument. -/
public noncomputable def associatedSheafFunctorUnconditional :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  overAssociatedModuleFunctor .fppf B S hS

/-- The value of the big fppf functor at `𝓕` is the associated module of Tag 03DU (3). -/
@[simp]
public theorem associatedSheafFunctorUnconditional_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (associatedSheafFunctorUnconditional B S hS).obj F =
      @overAssociatedModule .fppf B S hS F.obj F.property :=
  rfl

/-- The morphism clause of Tag 03DX (1) at `τ = fppf`. -/
@[simp]
public theorem associatedSheafFunctorUnconditional_map_val_app_apply
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : (BigFppfOver B S hS)ᵒᵖ)
    (m : ((associatedSheafFunctorUnconditional B S hS).obj F).val.obj X) :
    (((associatedSheafFunctorUnconditional B S hS).map φ).val.app X) m =
      ((Scheme.Modules.pullback ((Over.post B.inclusion).obj X.unop).hom).map φ.hom).app ⊤ m :=
  rfl

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The forward functor of Tag 03DX (2) at `τ = Zariski`, with no hypothesis.**  The
assignment `𝓕 ↦ 𝓕ᵃ` of Tag 03DU (4) on the small Zariski site of `S`, as a functor from the
quasi-coherent `𝒪_S`-modules to the sheaves of `𝒪`-modules on `S_Zar`. -/
public noncomputable def associatedSheafFunctor :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  haveI := isContinuous_toOver B S hS
  Stacks.EtaleCohomology.associatedSheafFunctorOfIsContinuous S
    (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion) (topology B S hS)

/-- The value of the small Zariski functor at `𝓕` is the associated module of
Tag 03DU (4). -/
@[simp]
public theorem associatedSheafFunctor_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (associatedSheafFunctor B S hS).obj F =
      @associatedModuleOfSections B S hS F.obj F.property :=
  rfl

/-- **The morphism clause of Tag 03DX (2) at `τ = Zariski`.**  On sections over an open
`T ⊆ S`, the map induced by `φ : 𝓕 ⟶ 𝓖` is the map on global sections of the pullback of `φ`
to `T`. -/
@[simp]
public theorem associatedSheafFunctor_map_val_app_apply
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : (SmallZariski B S hS)ᵒᵖ)
    (m : ((associatedSheafFunctor B S hS).obj F).val.obj X) :
    (((associatedSheafFunctor B S hS).map φ).val.app X) m =
      ((Scheme.Modules.pullback
        ((inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion).obj
          X.unop).hom).map φ.hom).app ⊤ m :=
  rfl

end AlgebraicGeometry.SmallZariski

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The forward functor of Tag 03DX (2) at `τ = étale`, with no hypothesis.**  The assignment
`𝓕 ↦ 𝓕ᵃ` of Tag 03DU (4) on the small étale site of `S`, as a functor from the quasi-coherent
`𝒪_S`-modules to the sheaves of `𝒪`-modules on `S_étale`.

The conditional version `AlgebraicGeometry.SmallEtale.associatedSheafFunctor` carries the
fpqc sheaf condition of Tag 03DT as an argument; that argument is a theorem,
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`, and this one carries none. -/
public noncomputable def associatedSheafFunctorUnconditional :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  haveI := isContinuous_toOver' B S hS
  Stacks.EtaleCohomology.associatedSheafFunctorOfIsContinuous S
    (toOver B S hS) (topology B S hS)

/-- The value of the small étale functor at `𝓕` is the associated module of Tag 03DU (4). -/
@[simp]
public theorem associatedSheafFunctorUnconditional_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (associatedSheafFunctorUnconditional B S hS).obj F =
      @associatedModuleOfSections B S hS F.obj F.property :=
  rfl

/-- **The morphism clause of Tag 03DX (2) at `τ = étale`.**  On sections over an object `T` of
the small étale site, the map induced by `φ : 𝓕 ⟶ 𝓖` is the map on global sections of the
pullback of `φ` to `T`. -/
@[simp]
public theorem associatedSheafFunctorUnconditional_map_val_app_apply
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : (SmallEtale B S hS)ᵒᵖ)
    (m : ((associatedSheafFunctorUnconditional B S hS).obj F).val.obj X) :
    (((associatedSheafFunctorUnconditional B S hS).map φ).val.app X) m =
      ((Scheme.Modules.pullback ((toOver B S hS).obj X.unop).hom).map φ.hom).app ⊤ m :=
  rfl

end AlgebraicGeometry.SmallEtale

end
