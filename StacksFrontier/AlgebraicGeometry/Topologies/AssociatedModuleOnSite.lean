module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# The associated module of a quasi-coherent module on a site of schemes

Let `S` be a scheme, let `F` be a quasi-coherent module on `S`, and let `C` be a category of
schemes over `S`, presented by a functor `toOver : C ⥤ Over S`.  Tag 03DS gives the
abelian-group-valued presheaf `T ↦ Γ(T, f⁺ F)` on `Over S`; restricting it along `toOver`
gives an abelian presheaf on `C`.  This file equips that presheaf with the action of the
presheaf of global functions, so that it becomes a `PresheafOfModules` over the structure
presheaf of `C`, and packages the two sheaf conditions into a `SheafOfModules` over the
structure sheaf.

This is the coefficient-level substrate of Tag 03DU, and it is what the equivalence of
Tag 03DX and all of its consumers take as input: the right-hand side of 03DX is the category
of quasi-coherent modules over the structure *sheaf of rings* of the site, so `F ↦ Fᵃ` has to
land in `SheafOfModules` and not merely in abelian presheaves.

## Main definitions

* `Stacks.Sites.associatedPresheaf` is the abelian presheaf `X ↦ Γ(toOver X, (toOver X)⁺ F)`
  on `C`.
* `Stacks.Sites.associatedPresheafModule` is the action of `Γ(toOver X, 𝒪)` on its sections.
* `Stacks.Sites.associatedModulePresheaf` is the resulting presheaf of modules over
  `Stacks.Sites.structurePresheaf`.
* `Stacks.Sites.siteStructureSheaf` and `Stacks.Sites.siteAssociatedModule` package a sheaf
  condition for each of the two presheaves into a sheaf of rings and a sheaf of modules over
  it.

## Main results

* `AlgebraicGeometry.pullbackSectionsMap_smul`: the pullback map on sections of Tag 03DS is
  semilinear over the pullback map on functions.  This is the whole content of the module
  structure, and it is proved, not assumed.
* `Stacks.Sites.associatedPresheaf_map_smul`: the same statement read on a site, which is the
  hypothesis of `PresheafOfModules.ofPresheaf`.

## Implementation notes

`AlgebraicGeometry.pullbackSectionsMap` is, by construction, the composite of a morphism of
`𝒪`-modules evaluated at `⊤` with a restriction map along the canonical identification
`⊤ = g ⁻¹ᵁ ⊤`.  Both factors are semilinear — the first by
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`, the second by
`AlgebraicGeometry.Scheme.Modules.map_smul` — and the two scalar reindexings compose to the
identity on `Γ(X, ⊤)`.  The second step needs
`AlgebraicGeometry.Scheme.Modules.presheaf_map_top_eq_id`: the subobjects `⊤` and `g ⁻¹ᵁ ⊤`
are literally equal, so the open sets of a scheme being a poset there is exactly one morphism
between them and the restriction map along it is the identity.  Stating it that way avoids
rewriting under `eqToHom`, which does not typecheck here because the two sections types are
definitionally but not syntactically equal.

The reindexing in the first step — the `Γ(Y, ⊤)`-action on the sections of a pushforward being
the restriction of the `Γ(X, g ⁻¹ᵁ ⊤)`-action — holds by `rfl`, since
`AlgebraicGeometry.Scheme.Modules.pushforward` is defined as a pushforward of abelian
presheaves followed by `ModuleCat.restrictScalars`.  It is recorded as
`AlgebraicGeometry.Scheme.Modules.pushforward_obj_smul` rather than left implicit.

The site universes are those of `Stacks.Sites.structurePresheaf`, namely objects in
`Type (u + 1)` and morphisms in `Type u` for `S : Scheme.{u}`.  All seven sites of Tag 03DX —
the five big sites and the small Zariski and étale sites — are slices or full subcategories of
`Over S` and so sit in those universes; nothing here needs more.

The sheaf conditions are *parameters* here because this is the site-generic layer, not because
they are unavailable.  Both are now discharged on every site of Tag 03DX.  For the structure
presheaf, on all five big sites uniformly by
`AlgebraicGeometry.isSheaf_overStructurePresheaf` and one by one by
`AlgebraicGeometry.Big‹τ›Over.structure_isSheaf`, and on the two small sites by
`AlgebraicGeometry.SmallZariski.structure_isSheaf` and
`AlgebraicGeometry.SmallEtale.structure_isSheaf`.  For the associated presheaf, from Tag 03DT
in its unconditional form `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`
(`StacksFrontier/AlgebraicGeometry/Descent/FpqcHomSheafRefinement.lean:427`): see
`AlgebraicGeometry.isSheaf_overAssociatedPresheaf` for the five big sites and
`AlgebraicGeometry.SmallZariski.isSheaf_associatedPresheaf` and
`AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf'` for the small ones.  The `Fᵃ` of
Tag 03DU with no parameters at all is `AlgebraicGeometry.overAssociatedModule` and its two
small-site companions.

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

/-! ### Semilinearity of the pullback map on sections -/

/-- The restriction map of an `𝒪`-module along the canonical morphism `⊤ ⟶ g ⁻¹ᵁ ⊤` is the
identity.  The two open sets are equal, and the open sets of a scheme form a poset, so that
morphism is the identity and the restriction along it is `𝟙`.

This replaces rewriting with `eqToHom`: the sections of `M` over `⊤` and over `g ⁻¹ᵁ ⊤` are
definitionally but not syntactically the same type, so a rewrite under `eqToHom` produces a
motive that does not typecheck. -/
public theorem Scheme.Modules.presheaf_map_top_eq_id {X Y : Scheme.{u}} (g : X ⟶ Y)
    (e : (⊤ : X.Opens) ⟶ g ⁻¹ᵁ ⊤) (M : X.Modules) : M.presheaf.map e.op = 𝟙 _ :=
  have h : e.op = 𝟙 (op (g ⁻¹ᵁ ⊤)) := Subsingleton.elim _ _
  Eq.trans (congrArg M.presheaf.map h) (M.presheaf.map_id _)

/-- The action of `Γ(Y, U)` on the sections over `U` of the pushforward of an `𝒪_X`-module
along `g : X ⟶ Y` is the restriction, along `g.app U`, of its action as sections over
`g ⁻¹ᵁ U`.  This holds by definition, because `AlgebraicGeometry.Scheme.Modules.pushforward`
is a pushforward of abelian presheaves followed by `ModuleCat.restrictScalars`. -/
public theorem Scheme.Modules.pushforward_obj_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : X.Modules) (U : Y.Opens) (r : Γ(Y, U)) :
    ((Scheme.Modules.pushforward g).obj M).smul r = M.smul (g.app U r) := rfl

/-- A morphism of `𝒪_Y`-modules into a pushforward, evaluated on global sections and followed
by the canonical restriction to `⊤`, is semilinear over `g.appTop`. -/
public theorem appTop_map_smul {X Y : Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) (e : (⊤ : X.Opens) ⟶ g ⁻¹ᵁ ⊤)
    (r : Γ(Y, ⊤)) (m : Γ(M, ⊤)) :
    N.presheaf.map e.op (φ.app ⊤ (r • m)) =
      g.appTop r • N.presheaf.map e.op (φ.app ⊤ m) := by
  simp only [Scheme.Modules.presheaf_map_top_eq_id g e N, Scheme.Modules.Hom.app_smul]
  rfl

/-- **The module structure of Tag 03DS.**  The pullback map on global sections induced by a
morphism `g` of schemes over `S` is semilinear over the pullback map on global functions. -/
public theorem pullbackSectionsMap_smul {S : Scheme.{u}} (F : S.Modules) {X Y : Over S}
    (g : X ⟶ Y) (r : Γ(Y.left, ⊤)) (m : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    pullbackSectionsMap F g (r • m) = g.left.appTop r • pullbackSectionsMap F g m :=
  appTop_map_smul g.left
    ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
        ((Scheme.Modules.pullback Y.hom).obj F) ≫
      (Scheme.Modules.pushforward g.left).map
        ((Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
          (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F))
    (eqToHom (by simp)) r m

end AlgebraicGeometry

namespace Stacks.Sites

open AlgebraicGeometry

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
  {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-! ### The associated presheaf of modules -/

/-- The abelian presheaf of sections of the pullback of `F` to the schemes of a site over `S`:
the object `X` is sent to `Γ(T, T.hom⁺ F)`, where `T` is the scheme over `S` underlying `X`.
This is Tag 03DS restricted along `toOver`. -/
public noncomputable abbrev associatedPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  toOver.op ⋙ quasiCoherentPresheafFunctor S F

/-- Sections of the pullback of `F` over an object of the site are a module over the global
functions on the underlying scheme.  This is the action of
`Stacks.Sites.structurePresheaf` on `Stacks.Sites.associatedPresheaf`. -/
@[instance_reducible]
public noncomputable def associatedPresheafModule (X : Cᵒᵖ) :
    Module ((structurePresheaf S toOver).obj X) ((associatedPresheaf S F toOver).obj X) :=
  inferInstanceAs (Module Γ((toOver.obj X.unop).left, ⊤)
    Γ((Scheme.Modules.pullback (toOver.obj X.unop).hom).obj F, ⊤))

/-- **Tag 03DU, the module restriction maps.**  The restriction maps of the presheaf of
pullback sections are semilinear over the restriction maps of the presheaf of global
functions. -/
@[stacks 03DU "module restriction maps"]
public theorem associatedPresheaf_map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : (structurePresheaf S toOver).obj X) (m : (associatedPresheaf S F toOver).obj X) :
    letI := associatedPresheafModule S F toOver X
    letI := associatedPresheafModule S F toOver Y
    (associatedPresheaf S F toOver).map f (r • m) =
      (structurePresheaf S toOver).map f r • (associatedPresheaf S F toOver).map f m :=
  pullbackSectionsMap_smul F (toOver.map f.unop) r m

/-- The presheaf of modules over `Stacks.Sites.structurePresheaf` associated to a
quasi-coherent module `F` on `S`.  Its sections over an object of the site are the global
sections of the pullback of `F` to the underlying scheme. -/
public noncomputable def associatedModulePresheaf :
    PresheafOfModules.{u} (structurePresheaf S toOver) :=
  letI : ∀ X, Module ((structurePresheaf S toOver).obj X)
      ((associatedPresheaf S F toOver).obj X) := associatedPresheafModule S F toOver
  PresheafOfModules.ofPresheaf (associatedPresheaf S F toOver)
    (fun _ _ f r m => associatedPresheaf_map_smul S F toOver f r m)

/-- The underlying abelian presheaf of `Stacks.Sites.associatedModulePresheaf` is the presheaf
of pullback sections. -/
@[simp]
public theorem associatedModulePresheaf_presheaf :
    (associatedModulePresheaf S F toOver).presheaf = associatedPresheaf S F toOver := rfl

/-! ### Packaging the sheaf conditions -/

variable (J : GrothendieckTopology C)

/-- The structure sheaf of rings of a site of schemes over `S`, given the sheaf condition for
its presheaf of global functions.  No sheafification occurs. -/
public noncomputable def siteStructureSheaf
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver)) : Sheaf J RingCat.{u} :=
  ⟨structurePresheaf S toOver, hR⟩

/-- The underlying presheaf of `Stacks.Sites.siteStructureSheaf` is the presheaf of global
functions. -/
@[simp]
public theorem siteStructureSheaf_obj
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver)) :
    (siteStructureSheaf S toOver J hR).obj = structurePresheaf S toOver := rfl

/-- **The associated module `Fᵃ` of Tag 03DU**, as a sheaf of modules over the structure sheaf
of the site.  Both sheaf conditions are parameters: no sheafification occurs, and the sections
over an object of the site are exactly the global sections of the pullback of `F`. -/
public noncomputable def siteAssociatedModule
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver))
    (hM : Presheaf.IsSheaf J (associatedPresheaf S F toOver)) :
    SheafOfModules.{u} (siteStructureSheaf S toOver J hR) :=
  ⟨associatedModulePresheaf S F toOver, hM⟩

/-- The underlying abelian presheaf of `Stacks.Sites.siteAssociatedModule` is the presheaf of
pullback sections. -/
@[simp]
public theorem siteAssociatedModule_presheaf
    (hR : Presheaf.IsSheaf J (structurePresheaf S toOver))
    (hM : Presheaf.IsSheaf J (associatedPresheaf S F toOver)) :
    (siteAssociatedModule S F toOver J hR hM).val.presheaf =
      associatedPresheaf S F toOver := rfl

end Stacks.Sites

end
