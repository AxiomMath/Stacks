module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcOverSiteDichotomy
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf

/-!
# Functoriality of the associated module on a site of schemes

Tag 03DS attaches to a quasi-coherent module `F` on a scheme `S` the abelian presheaf
`T ↦ Γ(T, T.hom⁺ F)` on the schemes over `S`, and Tag 03DU turns its restriction to a site `C`
over `S` into a sheaf of modules `Fᵃ` over the structure sheaf of `C`.  Both are constructions
on a *fixed* `F`.  This file makes them functorial in `F`: a morphism `φ : F ⟶ G` of modules on
`S` induces a morphism `Fᵃ ⟶ Gᵃ`, compatibly with identities and composition.

The resulting functor is the left-hand half of Tag 03DX, whose statement is an equivalence
`QCoh(𝒪_S) ≌ QCoh(𝒪_C)` *given by* `F ↦ Fᵃ`: without functoriality in `F` there is no functor
to compare, and the morphism clauses of the 03DX statement (the maps on sections are the
pullback maps on sections) are exactly `Stacks.Sites.associatedSheafFunctor_map_val_app_apply`
below.

## Main definitions

* `AlgebraicGeometry.pullbackSectionsFunctor` is Tag 03DS as a functor in the module: it sends
  a module on `S` to the abelian presheaf of its pullback sections on the schemes over `S`, and
  a morphism to the pullback maps on global sections.
* `Stacks.Sites.associatedPresheafMap` and `Stacks.Sites.associatedModuleMap` are the induced
  maps of associated presheaves and of associated presheaves of modules on a site.
* `Stacks.Sites.associatedModuleFunctor` is `F ↦ Fᵃ` as a functor from the quasi-coherent
  modules on `S` to the presheaves of modules over the structure presheaf of the site.
* `Stacks.Sites.associatedSheafFunctor` is the same functor with both sheaf conditions
  supplied, landing in sheaves of modules over the structure sheaf.
* `AlgebraicGeometry.BigEtaleOver.associatedSheafFunctor` and
  `AlgebraicGeometry.SmallEtale.associatedSheafFunctor` are the two instances of it which need
  Tag 03DT and nothing else, and `AlgebraicGeometry.BigFppfOver.associatedSheafFunctor` is the
  big fppf one, whose module sheaf condition is a hypothesis of the *declaration* but is no
  longer an open input: see the implementation notes.

## Main results

* `AlgebraicGeometry.pullbackSectionsMap_naturality`: the pullback map on global sections of
  Tag 03DS is natural in the module.  This is the whole content of the file; everything else
  transports it along the restriction of a presheaf to a site and along the module structure.
* `Stacks.Sites.associatedModuleMap_id`, `Stacks.Sites.associatedModuleMap_comp` and
  `Stacks.Sites.associatedModuleMap_zero`: the functor laws for the induced maps of associated
  modules, and additivity at the zero morphism.

## Implementation notes

`AlgebraicGeometry.pullbackSectionsMap` is the `⊤`-component of the unit of the
pullback–pushforward adjunction composed with the comparison morphism
`g.left⁺ (Y.hom⁺ F) ⟶ X.hom⁺ F`, and that shape already has an abstraction in the tree:
`Stacks.Sites.topUnitMap`, with `Stacks.Sites.pullbackSectionsMap_eq_topUnitMap` identifying the
two and `Stacks.Sites.topUnitMap_comp` and `Stacks.Sites.comp_topUnitMap` moving morphisms of
modules across it.  Naturality in the module is proved through those three lemmas, so it reduces
to the naturality of the comparison morphism, which is the naturality of the composition
isomorphism for pullbacks and of the congruence isomorphism for the triangle `Over.w g`.

Going through `Stacks.Sites.topUnitMap` is not only shorter than reproducing the `private`
definition of `StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections`, which is
what the first version of this file did; it is also what makes the proof a sequence of rewrites.
The implementation notes of `StacksFrontier.AlgebraicGeometry.Topologies.FpqcOverSiteDichotomy`
explain why: `Γ((g.left)_* M, ⊤)` and `Γ(M, g.left ⁻¹ᵁ ⊤)` are definitionally but not
syntactically equal, so `rw` on a composite in which that identification is implicit — including
`rw [Category.assoc]` — fails its motive check, and the lemmas there are stated so that no such
composite is ever rewritten.

`Stacks.Sites.associatedSheafFunctor` takes its objects from
`Stacks.Sites.siteAssociatedModule` rather than rebuilding them from
`Stacks.Sites.associatedModuleFunctor`: the sheaf condition supplied is one for the associated
*presheaf*, and converting it to one for the underlying presheaf of the presheaf of modules
unfolds `CategoryTheory.PresheafOfModules.ofPresheaf`, which the kernel does not finish.  Going
through the existing definition reuses the conversion it already performs.

The quasi-coherence instances are passed explicitly with `@` in the functor fields.  They are
instance arguments of the underlying definitions but come from the `property` field of an object
of the full subcategory, which is not an instance.

The three `associatedSheafFunctor` declarations below still take their sheaf conditions as
arguments, but none of those arguments is an open input any more.  `h03DT` is Tag 03DT, proved
unconditionally by `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`
(`StacksFrontier/AlgebraicGeometry/Descent/FpqcHomSheafRefinement.lean:427`); and the big fppf
`hM` is `AlgebraicGeometry.isSheaf_overAssociatedPresheaf` at `τ = fppf`
(`StacksFrontier/AlgebraicGeometry/Topologies/BigSiteAssociatedModule.lean:166`), which reaches the
fppf site through continuity of `AlgebraicGeometry.overToSlice` and therefore needs nothing
about base-change stability of the chosen bounded covering families.  The hypotheses are kept
only so that the signatures are not changed under the consumers of this file.

No tag is claimed.  Tag 03DU is the object-level construction, which is already in the tree, and
Tag 03DX is the equivalence, of which this is the forward functor only: neither its
quasi-coherence on the site, nor full faithfulness, nor essential surjectivity is proved here.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Naturality of the pullback map on sections -/

/-- **Tag 03DS is natural in the module.**  The pullback map on global sections induced by a
morphism `g` of schemes over `S` commutes with the maps on global sections induced by a
morphism `φ : F ⟶ G` of modules on `S`.

Both sides are instances of `Stacks.Sites.topUnitMap`, so the statement reduces to the
naturality in the module of the comparison morphism `g.left⁺ (Y.hom⁺ F) ⟶ X.hom⁺ F`, which is
the naturality of the composition isomorphism for pullbacks and of the congruence isomorphism
for the triangle `CategoryTheory.Over.w g`. -/
public theorem pullbackSectionsMap_naturality {S : Scheme.{u}} {F G : S.Modules} (φ : F ⟶ G)
    {X Y : Over S} (g : X ⟶ Y) :
    pullbackSectionsMap F g ≫ ((Scheme.Modules.pullback X.hom).map φ).app ⊤ =
      ((Scheme.Modules.pullback Y.hom).map φ).app ⊤ ≫ pullbackSectionsMap G g := by
  have hα : (Scheme.Modules.pullback g.left).map ((Scheme.Modules.pullback Y.hom).map φ) ≫
      ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app G ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app G) =
      ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F) ≫
      (Scheme.Modules.pullback X.hom).map φ := by
    have h1 := (Scheme.Modules.pullbackComp g.left Y.hom).hom.naturality φ
    have h2 := (Scheme.Modules.pullbackCongr (Over.w g)).hom.naturality φ
    simp only [Functor.comp_map] at h1 h2
    rw [Category.assoc, ← h2, ← Category.assoc, h1, Category.assoc]
  rw [Stacks.Sites.pullbackSectionsMap_eq_topUnitMap F g,
    Stacks.Sites.pullbackSectionsMap_eq_topUnitMap G g, Stacks.Sites.topUnitMap_comp,
    Stacks.Sites.comp_topUnitMap, hα]

/-! ### Tag 03DS as a functor in the module -/

/-- **Tag 03DS as a functor in the module.**  A module on `S` is sent to the abelian presheaf
of global sections of its pullbacks to the schemes over `S`, and a morphism of modules to the
induced maps on those global sections. -/
public noncomputable def pullbackSectionsFunctor (S : Scheme.{u}) :
    S.Modules ⥤ ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj F := (quasiCoherentPresheafConstruction S F).functor
  map {F G} φ :=
    { app := fun T => ((Scheme.Modules.pullback T.unop.hom).map φ).app ⊤
      naturality := fun _ _ g => pullbackSectionsMap_naturality φ g.unop }
  map_id F := by
    ext T x
    simp
    rfl
  map_comp φ ψ := by
    ext T x
    simp
    rfl

/-- On a quasi-coherent module the functor of Tag 03DS is the presheaf of Tag 03DS. -/
@[simp]
public theorem pullbackSectionsFunctor_obj (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] :
    (pullbackSectionsFunctor S).obj F = quasiCoherentPresheafFunctor S F := rfl

/-- The map of pullback-sections presheaves induced by a morphism of modules is the map on
global sections of its pullback. -/
@[simp]
public theorem pullbackSectionsFunctor_map_app {S : Scheme.{u}} {F G : S.Modules} (φ : F ⟶ G)
    (T : (Over S)ᵒᵖ) :
    ((pullbackSectionsFunctor S).map φ).app T =
      ((Scheme.Modules.pullback T.unop.hom).map φ).app ⊤ := rfl

end AlgebraicGeometry

namespace Stacks.Sites

open AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
variable {F G H : S.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] [H.IsQuasicoherent]

/-! ### The induced map of associated modules -/

/-- The map of associated presheaves on a site induced by a morphism of quasi-coherent modules
on `S`: the functor of Tag 03DS applied to the morphism, restricted along `toOver`. -/
public noncomputable def associatedPresheafMap (φ : F ⟶ G) :
    associatedPresheaf S F toOver ⟶ associatedPresheaf S G toOver :=
  Functor.whiskerLeft toOver.op ((pullbackSectionsFunctor S).map φ)

/-- On an object of the site, `Stacks.Sites.associatedPresheafMap` is the map on global
sections of the pullback of the morphism. -/
@[simp]
public theorem associatedPresheafMap_app (φ : F ⟶ G) (X : Cᵒᵖ) :
    (associatedPresheafMap S toOver φ).app X =
      ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map φ).app ⊤ := rfl

/-- The map of associated presheaves *of modules* on a site induced by a morphism of
quasi-coherent modules on `S`.  Its linearity over the global functions on each object of the
site is `AlgebraicGeometry.Scheme.Modules.Hom.app_smul`. -/
public noncomputable def associatedModuleMap (φ : F ⟶ G) :
    associatedModulePresheaf S F toOver ⟶ associatedModulePresheaf S G toOver :=
  PresheafOfModules.homMk (associatedPresheafMap S toOver φ)
    fun _ r m => Scheme.Modules.Hom.app_smul _ r m

/-- `Stacks.Sites.associatedModuleMap` acts on sections over an object of the site as the map
on global sections of the pullback of the morphism. -/
@[simp]
public theorem associatedModuleMap_app_apply (φ : F ⟶ G) (X : Cᵒᵖ)
    (m : (associatedModulePresheaf S F toOver).obj X) :
    (associatedModuleMap S toOver φ).app X m =
      ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map φ).app ⊤ m := rfl

/-- Equal morphisms of modules induce the same map on global sections. -/
private theorem app_top_apply_congr {Y : Scheme.{u}} {M N : Y.Modules} {f g : M ⟶ N}
    (h : f = g) (x) : (Scheme.Modules.Hom.app f ⊤).hom x = (Scheme.Modules.Hom.app g ⊤).hom x :=
  congrFun (congrArg (fun χ => ⇑(AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app χ ⊤))) h) x

/-- The associated module of the identity is the identity. -/
public theorem associatedModuleMap_id : associatedModuleMap S toOver (𝟙 F) = 𝟙 _ := by
  refine PresheafOfModules.Hom.ext ?_
  ext X x
  exact app_top_apply_congr ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map_id F) x

/-- The associated module of the zero morphism is zero.  With
`Stacks.Sites.associatedModuleMap_comp` this is what makes `F ↦ Fᵃ` carry a complex to a
complex, which is where the right-exactness assertion of Tag 03OJ starts. -/
public theorem associatedModuleMap_zero : associatedModuleMap S toOver (0 : F ⟶ G) = 0 := by
  refine PresheafOfModules.Hom.ext ?_
  ext X x
  change ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map (0 : F ⟶ G)).app ⊤ x = 0
  rw [Functor.map_zero]
  rfl

/-- The associated module of a composite is the composite of the associated modules. -/
public theorem associatedModuleMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    associatedModuleMap S toOver (φ ≫ ψ) =
      associatedModuleMap S toOver φ ≫ associatedModuleMap S toOver ψ := by
  refine PresheafOfModules.Hom.ext ?_
  ext X x
  exact app_top_apply_congr ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map_comp φ ψ) x

/-! ### The functor `F ↦ Fᵃ` -/

/-- **The functor `F ↦ Fᵃ` of Tag 03DX, at the level of presheaves of modules.**  It sends a
quasi-coherent module on `S` to the presheaf of modules over the structure presheaf of the site
whose sections over an object are the global sections of the pullback, and a morphism to the
induced maps on those sections. -/
public noncomputable def associatedModuleFunctor :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      PresheafOfModules.{u} (structurePresheaf S toOver) where
  obj F := @associatedModulePresheaf S F.obj F.property C _ toOver
  map {F G} φ := @associatedModuleMap S C _ toOver F.obj G.obj F.property G.property φ.hom
  map_id F := @associatedModuleMap_id S C _ toOver F.obj F.property
  map_comp {F G H} φ ψ :=
    @associatedModuleMap_comp S C _ toOver F.obj G.obj H.obj F.property G.property H.property
      φ.hom ψ.hom

/-- The value of `Stacks.Sites.associatedModuleFunctor` is the associated presheaf of
modules of Tag 03DU. -/
@[simp]
public theorem associatedModuleFunctor_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (associatedModuleFunctor S toOver).obj F =
      @associatedModulePresheaf S F.obj F.property C _ toOver := rfl

/-- `Stacks.Sites.associatedModuleFunctor` acts on sections over an object of the site as the
map on global sections of the pullback of the morphism. -/
@[simp]
public theorem associatedModuleFunctor_map_app_apply
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : Cᵒᵖ) (m : ((associatedModuleFunctor S toOver).obj F).obj X) :
    ((associatedModuleFunctor S toOver).map φ).app X m =
      ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map φ.hom).app ⊤ m := rfl

variable (J : GrothendieckTopology C)

/-- **The functor `F ↦ Fᵃ` of Tag 03DX, at the level of sheaves of modules.**  Both sheaf
conditions are parameters, exactly as for `Stacks.Sites.siteAssociatedModule`: the structure
presheaf is a sheaf, and the associated presheaf of every quasi-coherent module is a sheaf.  No
sheafification occurs. -/
public noncomputable def associatedSheafFunctor
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver))
    (hM : ∀ (M : S.Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf J (associatedPresheaf S M toOver)) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (siteStructureSheaf S toOver J hR) where
  obj F := @siteAssociatedModule S F.obj F.property C _ toOver J hR (hM F.obj F.property)
  map φ := ⟨(associatedModuleFunctor S toOver).map φ⟩
  map_id F := SheafOfModules.hom_ext ((associatedModuleFunctor S toOver).map_id F)
  map_comp φ ψ := SheafOfModules.hom_ext ((associatedModuleFunctor S toOver).map_comp φ ψ)

/-- The underlying presheaf of modules of `Stacks.Sites.associatedSheafFunctor` is
`Stacks.Sites.associatedModuleFunctor`. -/
@[simp]
public theorem associatedSheafFunctor_obj_val
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver))
    (hM : ∀ (M : S.Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf J (associatedPresheaf S M toOver))
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    ((associatedSheafFunctor S toOver J hR hM).obj F).val =
      (associatedModuleFunctor S toOver).obj F := rfl

/-- **The morphism clause of Tag 03DX.**  On sections over an object `X` of the site, the map
induced by `Stacks.Sites.associatedSheafFunctor` is the map on global sections obtained by
pulling the morphism back to the scheme underlying `X`. -/
@[simp]
public theorem associatedSheafFunctor_map_val_app_apply
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver))
    (hM : ∀ (M : S.Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf J (associatedPresheaf S M toOver))
    {F G : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (X : Cᵒᵖ) (m : ((associatedSheafFunctor S toOver J hR hM).obj F).val.obj X) :
    (((associatedSheafFunctor S toOver J hR hM).map φ).val.app X) m =
      ((Scheme.Modules.pullback (toOver.obj X.unop).hom).map φ.hom).app ⊤ m := rfl

end Stacks.Sites

namespace AlgebraicGeometry.BigEtaleOver

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor `F ↦ Fᵃ` on the big étale site, from Tag 03DT alone.**  Given the fpqc sheaf
condition for the pullback-sections presheaf on the schemes over `S` — which is Tag 03DT — the
associated module of a quasi-coherent module on `S` is a sheaf of modules over the big étale
structure sheaf, functorially in the module. -/
public noncomputable def associatedSheafFunctor
    (h03DT : ∀ (M : S.Modules) [M.IsQuasicoherent],
      Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
        (quasiCoherentPresheafFunctor S M ⋙ CategoryTheory.forget AddCommGrpCat)) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  Stacks.Sites.associatedSheafFunctor (C := BigEtaleOver B S hS) S (Over.post B.inclusion)
    (topology B S hS) (structure_isSheaf B S hS)
    fun M hM => @isSheaf_associatedPresheaf B S hS M hM (@h03DT M hM)

end AlgebraicGeometry.BigEtaleOver

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor `F ↦ Fᵃ` on the small étale site, from Tag 03DT alone.**  The small étale
counterpart of `AlgebraicGeometry.BigEtaleOver.associatedSheafFunctor`. -/
public noncomputable def associatedSheafFunctor
    (h03DT : ∀ (M : S.Modules) [M.IsQuasicoherent],
      Presieve.IsSheaf (Scheme.fpqcTopology.{u}.over S)
        (quasiCoherentPresheafFunctor S M ⋙ CategoryTheory.forget AddCommGrpCat)) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  Stacks.Sites.associatedSheafFunctor S (inclusion B S hS ⋙ Over.post B.inclusion)
    (topology B S hS) (structure_isSheaf B S hS)
    fun M hM => @isSheaf_associatedPresheaf B S hS M hM (@h03DT M hM)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The functor `F ↦ Fᵃ` on the big fppf site.**  The sheaf condition for the associated
presheaf is taken as an argument here because *this file's* route from Tag 03DT, through
`Stacks.Sites.isSheaf_addCommGrpCat_op_comp_of_precoverage`, needs the chosen bounded covering
families of the site to be stable under base change, which they are not known to be.  It is not
an open input: `AlgebraicGeometry.isSheaf_overAssociatedPresheaf` at `τ = fppf` proves it
unconditionally, through continuity of `AlgebraicGeometry.overToSlice` instead. -/
public noncomputable def associatedSheafFunctor
    (hM : ∀ (M : S.Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf (topology B S hS)
        (Stacks.Sites.associatedPresheaf (C := BigFppfOver B S hS) S M
          (Over.post B.inclusion))) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) :=
  Stacks.Sites.associatedSheafFunctor (C := BigFppfOver B S hS) S (Over.post B.inclusion)
    (topology B S hS) (structure_isSheaf B S hS) hM

end AlgebraicGeometry.BigFppfOver

end
